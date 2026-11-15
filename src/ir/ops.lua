local M={}
local BIN={
  ADD="+",SUB="-",MUL="*",DIV="/",MOD="%",POW="^",CONCAT="..",
  LT="<",LE="<=",GT=">",GE=">=",EQ="==",NE="~="
}
local UN={NOT="not",NEG="-",LEN="#"}
M.BIN=BIN
M.UN=UN
local function is_ret_tc(op)
  return op:sub(1,6)=="RETURN" or op:sub(1,8)=="TAILCALL"
end
local function rw(ins,chs)
  local op,a,b,c,d=ins[1],ins[2],ins[3],ins[4],ins[5]
  local rd,wr={},{}
  if op=="LOAD" or op=="NIL" or op=="CLEAR" or op=="TABLE" or op=="VARARG" or op=="GLOBAL" then
    wr[a]=true
  elseif op=="JMP" then
  elseif op=="CLEARS" then
    for _,r in ipairs(a or {}) do wr[r]=true end
  elseif op=="MOVE" or op=="CELL" or op=="GETCELL" or op=="NOT" or op=="NEG" or op=="LEN" then
    rd[b]=true wr[a]=true
  elseif op=="JFALSE" or op=="JTRUE" then
    rd[a]=true
  elseif op=="SETCELL" then
    rd[a]=true rd[b]=true
  elseif op=="GETUP" then
    wr[a]=true
  elseif op=="SETUP" or op=="SETGLOBAL" then
    rd[b]=true
  elseif BIN[op] or op=="GETTABLE" then
    rd[b]=true rd[c]=true wr[a]=true
  elseif op=="SETTABLE" then
    rd[a]=true rd[b]=true rd[c]=true
  elseif op=="TAKE" then
    rd[b]=true wr[a]=true
  elseif op=="EXPAND" then
    rd[a]=true rd[c]=true
  elseif op=="ARGS" then
    for _,r in ipairs(b or {}) do rd[r]=true end
    if c and c~=0 then rd[c]=true end
    wr[a]=true
  elseif op=="CLOSURE" then
    if chs and chs[b] then
      for _,cp in ipairs(chs[b].captures) do
        if cp[1]==0 then rd[cp[2]]=true end
      end
    end
    wr[a]=true
  elseif op=="FORPREP" then
    rd[a]=true rd[b]=true rd[c]=true
    wr[a]=true wr[b]=true wr[c]=true
  elseif op=="FORCHECK" then
    rd[b]=true rd[c]=true rd[d]=true
    wr[a]=true
  elseif op=="CALL0" or op=="CALL1" or op=="CALL2" or op=="CALL3" or op=="CALL" then
    rd[b]=true
    if op=="CALL" then
      rd[c]=true
    else
      for _,r in ipairs(c or {}) do rd[r]=true end
    end
    if d~=0 then wr[a]=true end
  elseif op=="TAILCALL0" or op=="TAILCALL1" or op=="TAILCALL2" or op=="TAILCALL3" or op=="TAILCALL" then
    rd[a]=true
    if op=="TAILCALL" then
      rd[b]=true
    else
      for _,r in ipairs(b or {}) do rd[r]=true end
    end
  elseif op=="RETURN0" then
  elseif op=="RETURN1" or op=="RETURN" then
    rd[a]=true
  elseif op=="RETURN2" then
    rd[a]=true rd[b]=true
  elseif op=="RETURN3" then
    rd[a]=true rd[b]=true rd[c]=true
  else
    error("op:"..tostring(op))
  end
  return rd,wr
end
M.rw=rw
local function eq_s(a,b)
  for k in pairs(a) do if not b[k] then return false end end
  for k in pairs(b) do if not a[k] then return false end end
  return true
end
function M.liveness(pr)
  local cd,chs=pr.code,pr.children
  local n=#cd
  local rds,wrs,succ={},{},{}
  for pc=1,n do
    local ins=cd[pc]
    local rd,wr=rw(ins,chs)
    rds[pc]=rd wrs[pc]=wr
    local op,a,b=ins[1],ins[2],ins[3]
    if op=="JMP" then
      succ[pc]=(a>=1 and a<=n) and {a} or {}
    elseif op=="JFALSE" or op=="JTRUE" then
      local nx={}
      if pc+1<=n then nx[#nx+1]=pc+1 end
      if b>=1 and b<=n then nx[#nx+1]=b end
      succ[pc]=nx
    elseif is_ret_tc(op) then
      succ[pc]={}
    else
      succ[pc]=(pc+1<=n) and {pc+1} or {}
    end
  end
  local lin,lout={},{}
  for pc=1,n do lin[pc]={} lout[pc]={} end
  local ch=true
  while ch do
    ch=false
    for pc=n,1,-1 do
      local no={}
      for _,s in ipairs(succ[pc]) do
        for k in pairs(lin[s]) do no[k]=true end
      end
      local ni={}
      for k in pairs(rds[pc]) do ni[k]=true end
      for k in pairs(no) do if not wrs[pc][k] then ni[k]=true end end
      if not eq_s(no,lout[pc]) or not eq_s(ni,lin[pc]) then
        lout[pc]=no lin[pc]=ni ch=true
      end
    end
  end
  return lin,lout,succ,rds,wrs
end
function M.find_loops(cd)
  local n=#cd
  local lps,ub={},{}
  for pc=1,n do
    local ins=cd[pc]
    local op=ins[1]
    if op=="FORPREP" and pc+2<=n and cd[pc+1][1]=="FORCHECK" and cd[pc+2][1]=="JFALSE" then
      local ep=cd[pc+2][3]
      local bp=ep-1
      if bp>=pc+2 and cd[bp][1]=="JMP" and cd[bp][2]==pc+1 then
        local adv
        for _,off in ipairs({2,3,4}) do
          local ax=bp-off+1
          if ax>=pc+3 and cd[ax][1]=="ADD" and cd[ax][3]==ins[2] and cd[ax][4]==ins[4] then
            adv=ax break
          end
        end
        lps[pc]={"ForNum",ep,adv or bp,pc+1}
        ub[bp]=true
      end
    elseif op=="CALL2" and ins[5]==-1 and pc+4<=n then
      local i1,i2,i3,i4=cd[pc+1],cd[pc+2],cd[pc+3],cd[pc+4]
      if i1[1]=="TAKE" and i1[3]==ins[2] and i1[4]==1
        and (i2[1]=="NIL" or i2[1]=="CLEAR")
        and i3[1]=="EQ" and i3[3]==i1[2] and i3[4]==i2[2]
        and i4[1]=="JTRUE" and i4[2]==i3[2] then
        local ep=i4[3]
        local bp=ep-1
        if bp>=pc+5 and cd[bp][1]=="JMP" and cd[bp][2]==pc then
          lps[pc]={"ForIn",ep,pc}
          ub[bp]=true
        end
      end
    end
  end
  local bbh={}
  for pc=1,n do
    local ins=cd[pc]
    if not ub[pc] and ins[1]=="JMP" and ins[2]<=pc then
      local t=bbh[ins[2]]
      if not t then t={} bbh[ins[2]]=t end
      t[#t+1]=pc
    end
  end
  local hs={}
  for h in pairs(bbh) do hs[#hs+1]=h end
  table.sort(hs)
  for _,h in ipairs(hs) do
    local mb=0
    for _,b in ipairs(bbh[h]) do if b>mb then mb=b end end
    local ep=mb+1
    local k=mb-1
    while k>=h and (cd[k][1]=="CLEAR" or cd[k][1]=="CLEARS" or cd[k][1]=="NIL") do k=k-1 end
    local is_rep=false
    if k>=h and cd[k][1]=="JTRUE" and cd[k][3]==ep then
      local jc
      for j=h,k-1 do if cd[j][1]=="JFALSE" and cd[j][3]==ep then jc=j break end end
      if not jc then lps[h]={"Repeat",ep,k} is_rep=true end
    end
    if not is_rep then
      local jc
      for j=h,mb-1 do if cd[j][1]=="JFALSE" and cd[j][3]==ep then jc=j break end end
      if jc then lps[h]={"While",ep,h,jc} end
    end
  end
  return lps
end
function M.build_webs(pr,lps)
  local cd=pr.code
  local n=#cd
  local prm={}
  for _,p in ipairs(pr.params or {}) do prm[p[1]]=true end
  local lin,lout,succ,rds0,wrs0=M.liveness(pr)
  local rds,wrs,kills={},{},{}
  local ar={}
  for r in pairs(prm) do ar[r]=true end
  for pc=1,n do
    local op=cd[pc][1]
    local rd=rds0[pc]
    local wr,kl={},{}
    for k in pairs(wrs0[pc]) do
      if (op=="CLEAR" or op=="CLEARS" or op=="NIL") and not lout[pc][k] then
        kl[k]=true
      else
        wr[k]=true
      end
    end
    rds[pc]=rd wrs[pc]=wr kills[pc]=kl
    for r in pairs(rd) do ar[r]=true end
    for r in pairs(wr) do ar[r]=true end
  end
  local mi,sp={},{}
  sp[1]=true
  for lpc,li in pairs(lps) do
    local kd=li[1]
    if kd=="ForNum" then
      local ep,ap,cp=li[2],li[3],li[4]
      sp[cp]=true sp[ap]=true sp[ep]=true
      for k=lpc,math.min(lpc+3,n) do mi[k]=true end
      for k=ap,ep-1 do mi[k]=true end
    elseif kd=="ForIn" then
      local ep,cp=li[2],li[3]
      sp[cp]=true sp[ep-1]=true sp[ep]=true
      local j=lpc+5
      local rr=cd[lpc][2]
      local rc=cd[lpc][4][2]
      if j<ep and cd[j][1]=="MOVE" and cd[j][2]==rc then j=j+1 end
      while j<ep-1 and cd[j][1]=="TAKE" and cd[j][3]==rr do
        j=j+1
        if j<ep and (cd[j][1]=="MOVE" or cd[j][1]=="CELL") then j=j+1 end
      end
      sp[j]=true
      for k=lpc,math.min(j-1,n) do mi[k]=true end
      mi[ep-1]=true
    elseif kd=="While" then
      local ep,hp,jc=li[2],li[3],li[4]
      sp[hp]=true sp[jc+1]=true sp[ep-1]=true sp[ep]=true
    elseif kd=="Repeat" then
      local ep,jt=li[2],li[3]
      sp[lpc]=true sp[jt]=true sp[jt+1]=true sp[ep]=true
    end
  end
  for pc=1,n do
    if not mi[pc] then
      local ins=cd[pc]
      local op,a,b=ins[1],ins[2],ins[3]
      if op=="JMP" then
        sp[a]=true sp[pc+1]=true
      elseif op=="JFALSE" or op=="JTRUE" then
        sp[b]=true sp[pc+1]=true
      elseif is_ret_tc(op) then
        sp[pc+1]=true
      end
    end
  end
  local prds={}
  for pc=1,n do prds[pc]={} end
  for pc=1,n do
    for _,s in ipairs(succ[pc]) do
      if s>=1 and s<=n then prds[s][#prds[s]+1]=pc end
    end
  end
  local dw,uw,wi,wid={},{},{},0
  for d=0,n do dw[d]={} end
  for pc=1,n do uw[pc]={} end
  local ars={}
  for r in pairs(ar) do ars[#ars+1]=r end
  table.sort(ars)
  for _,r in ipairs(ars) do
    local rin,rout={},{}
    for pc=1,n do rin[pc]={} rout[pc]={} end
    if n>=1 and prm[r] then rin[1][0]=true end
    local ch=true
    while ch do
      ch=false
      for pc=1,n do
        local ni={}
        if pc==1 and prm[r] then ni[0]=true end
        for _,p in ipairs(prds[pc]) do
          for d in pairs(rout[p]) do ni[d]=true end
        end
        local no={}
        if wrs[pc][r] then
          no[pc]=true
        elseif not kills[pc][r] then
          for d in pairs(ni) do no[d]=true end
        end
        if not eq_s(ni,rin[pc]) or not eq_s(no,rout[pc]) then
          rin[pc]=ni rout[pc]=no ch=true
        end
      end
    end
    local ds={}
    if prm[r] then ds[#ds+1]=0 end
    for pc=1,n do if wrs[pc][r] then ds[#ds+1]=pc end end
    if #ds>0 then
      local par,dset={},{}
      for _,d in ipairs(ds) do par[d]=d dset[d]=true end
      local function find(x)
        while par[x]~=x do par[x]=par[par[x]] x=par[x] end
        return x
      end
      local function uni(a,b)
        local ra,rb=find(a),find(b)
        if ra~=rb then par[rb]=ra end
      end
      for pc=1,n do
        if rds[pc][r] then
          local d0
          for d in pairs(rin[pc]) do
            if dset[d] then
              if not d0 then d0=d else uni(d0,d) end
            end
          end
        end
      end
      local gs,rts={},{}
      for _,d in ipairs(ds) do
        local rt=find(d)
        local g=gs[rt]
        if not g then g={} gs[rt]=g rts[#rts+1]=rt end
        g[d]=true
      end
      table.sort(rts)
      local gw={}
      for _,rt in ipairs(rts) do
        local g=gs[rt]
        wid=wid+1 gw[rt]=wid
        local cnt=0
        for _ in pairs(g) do cnt=cnt+1 end
        local cr=g[0] or cnt>1
        if not cr then
          for l in pairs(sp) do
            if l>=1 and l<=n and not g[l] and lin[l][r] then
              for d in pairs(g) do
                if rin[l][d] then cr=true break end
              end
              if cr then break end
            end
          end
        end
        wi[wid]={r,g,cr}
      end
      for _,d in ipairs(ds) do dw[d][r]=gw[find(d)] end
      for pc=1,n do
        if rds[pc][r] then
          for d in pairs(rin[pc]) do
            if dset[d] then uw[pc][r]=gw[find(d)] break end
          end
        end
      end
    end
  end
  return lin,lout,succ,dw,uw,wi
end
return M
