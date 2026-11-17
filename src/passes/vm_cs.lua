local A=require("src.frontend.ast")
local unp=A.unp
local function bxor(a,b)
  local r,p=0,1
  while a>0 or b>0 do
    local x,y=a%2,b%2
    if x~=y then r=r+p end
    a,b,p=(a-x)/2,(b-y)/2,p*2
  end
  return r
end
local M={}
local KWS={["and"]=true,["break"]=true,["do"]=true,["else"]=true,["elseif"]=true,["end"]=true,["false"]=true,["for"]=true,["function"]=true,["if"]=true,["in"]=true,["local"]=true,["nil"]=true,["not"]=true,["or"]=true,["repeat"]=true,["return"]=true,["then"]=true,["true"]=true,["until"]=true,["while"]=true}
local function v_id(s)
  return type(s)=="string" and s:match("^[%a_][%w_]*$")~=nil and not KWS[s]
end
local function is_ru(e,ru_v)
  e=unp(e)
  if e[1]~="Call" or unp(e[2])[1]~="Var" or unp(e[2])[2]~=ru_v then return nil end
  local ag=e[3]
  if #ag<2 then return nil end
  local ks={}
  for i=3,#ag do
    local k=unp(ag[i])
    if k[1]~="Num" then return nil end
    ks[#ks+1]=k[2]
  end
  local n=unp(ag[2])
  return n[1]=="Num" and n[2] or nil,ks
end
local function rdu(bs,i,n,ks)
  local v,m=0,1
  for j=0,n-1 do
    local k=ks and ks[j+1] or 0
    v=v+bxor(bs[i+j] or 0,k)*m
    m=m*256
  end
  return v
end
local function rdd(bs,j)
  local d1,d2=bs[j] or 0,bs[j+1] or 0
  local sg=d1>127 and -1 or 1
  local ex=(d1%128)*16+math.floor(d2/16)
  if ex==0 then return 0 end
  local mt=d2%16
  for i=2,7 do mt=mt*256+(bs[j+i] or 0) end
  mt=(math.ldexp(mt,-52)+1)*sg
  return math.ldexp(mt,ex-1023)
end
local function dec_b64(data,ec)
  local mp={}
  for i=1,#ec do mp[ec:byte(i)]=i-1 end
  local out,acc,nb={},0,0
  for i=1,#data do
    local c=data:byte(i)
    if c~=61 then
      local v=mp[c]
      if v then
        acc=acc*64+v
        nb=nb+6
        if nb>=8 then
          nb=nb-8
          local bt=math.floor(acc/2^nb)
          acc=acc-bt*2^nb
          out[#out+1]=bt
        end
      end
    end
  end
  return out
end
local function ext_run(fn)
  local ps=fn[2]
  if #ps~=4 or fn[3] then return nil end
  local b=fn[4][2]
  local wn,wi
  for i,s in ipairs(b) do
    if s[1]=="While" and unp(s[2])[1]=="Bool" and unp(s[2])[2]==true then wn=s wi=i break end
  end
  if not wn then return nil end
  local by_v,op_v,k1
  for i=wi-1,1,-1 do
    local s=b[i]
    if s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" then
      local rhs=unp(s[3][1])
      if rhs[1]=="Call" and #rhs[3]==2 and unp(rhs[3][2])[1]=="Num" then
        local a1=unp(rhs[3][1])
        if a1[1]=="Idx" and unp(a1[2])[1]=="Var" then
          op_v=unp(s[2][1])[2]
          by_v=unp(a1[2])[2]
          k1=unp(rhs[3][2])[2]
          break
        end
      end
    end
  end
  if not op_v or not by_v then return nil end
  local st_v,sl_v,lc_v,ev_v,ru_v,cb_v,fp_v,ar_v=nil,nil,nil,ps[3],nil,nil,nil,ps[2]
  for _,s in ipairs(b) do
    if s[1]=="LocalVar" and #s[2]==1 and #s[3]==1 then
      local r=unp(s[3][1])
      if r[1]=="Tbl" and #r[2]==1 and r[2][1][1]=="I" and unp(r[2][1][2])[1]=="Num" and unp(r[2][1][2])[2]==0 and unp(r[2][1][3])[1]=="Var" and unp(r[2][1][3])[2]==ps[4] then
        lc_v=s[2][1]
      elseif r[1]=="Tbl" and #r[2]==0 and not st_v then
        st_v=s[2][1]
      elseif r[1]=="Num" and r[2]==0 and st_v then
        sl_v=s[2][1]
      end
    end
  end
  if not st_v or not sl_v or not lc_v then return nil end
  local hds={}
  for _,s in ipairs(wn[3][2]) do
    if s[1]=="While" then
      local c=unp(s[2])
      if c[1]=="Bin" and c[2]=="==" and unp(c[3])[1]=="Var" and unp(c[3])[2]==op_v and unp(c[4])[1]=="Num" then
        hds[#hds+1]={c[4][2],s[3][2]}
      end
    end
  end
  if #hds==0 then return nil end
  local k2,k3,k4=0,0,0
  local has_k23,has_k4=false,false
  local function scan_ru(node)
    A.walk(node,function(x)
      if x[1]=="Call" and #x[3]>=3 and unp(x[2])[1]=="Var" and unp(x[3][2])[1]=="Num" then
        local nm=unp(x[2])[2]
        local n=unp(x[3][2])[2]
        if n==3 and #x[3]==5 and unp(x[3][3])[1]=="Num" and unp(x[3][4])[1]=="Num" and unp(x[3][5])[1]=="Num" then
          ru_v=nm
          k2,k3,k4=unp(x[3][3])[2],unp(x[3][4])[2],unp(x[3][5])[2]
          has_k23=true has_k4=true
        elseif n==2 and #x[3]==4 and unp(x[3][3])[1]=="Num" and unp(x[3][4])[1]=="Num" then
          if not ru_v then ru_v=nm end
          if not has_k23 then k2,k3=unp(x[3][3])[2],unp(x[3][4])[2] has_k23=true end
        elseif n==1 and #x[3]==3 and unp(x[3][3])[1]=="Num" then
          if not ru_v then ru_v=nm end
          if not has_k4 then k4=unp(x[3][3])[2] has_k4=true end
        end
      end
    end)
  end
  for _,h in ipairs(hds) do
    for _,s in ipairs(h[2]) do scan_ru(s) end
  end
  if not has_k4 then
    for _,h in ipairs(hds) do
      A.walk({"Block",h[2]},function(x)
        if not has_k4 and x[1]=="Call" and #x[3]==2 and unp(x[3][2])[1]=="Num" then
          local a1=unp(x[3][1])
          if a1[1]=="Idx" and unp(a1[2])[1]=="Var" and unp(a1[2])[2]==by_v then
            local a13=unp(a1[3])
            if a13[1]=="Bin" and a13[2]=="+" and unp(a13[4])[1]=="Num" and unp(a13[4])[2]==3 then
              k4=unp(x[3][2])[2] has_k4=true
            end
          end
        end
      end)
    end
  end
  local ops,tags={},{}
  local function is_stk(e)
    e=unp(e)
    return e[1]=="Idx" and unp(e[2])[1]=="Var" and unp(e[2])[2]==st_v
  end
  local function has_w(node,kind)
    local r=false
    A.walk(node,function(x) if x[1]==kind then r=true end end)
    return r
  end
  local function strip_tail(sts)
    local n=#sts
    if n>=4 and sts[n][1]=="Assign" and #sts[n][2]==1 and unp(sts[n][3][1])[1]=="Bool" and unp(sts[n][3][1])[2]==false then
      n=n-4
    end
    local out={}
    for i=1,n do out[i]=sts[i] end
    return out
  end
  local bm={["+"]="ADD",["-"]="SUB",["*"]="MUL",["/"]="DIV",["%"]="MOD",["^"]="POW",[".."]="CONCAT",["=="]="EQ",["~="]="NEQ",["<"]="LT",[">"]="GT",["<="]="LET",[">="]="GET"}
  for _,h in ipairs(hds) do
    local code=h[1]
    local raw=h[2]
    if #raw==1 and raw[1][1]=="Return" then
      local r=raw[1][2][1] and unp(raw[1][2][1])
      if not r then ops[code]="RET3"
      elseif r[1]=="Tbl" and #r[2]==0 then ops[code]="RET3"
      elseif r[1]=="Tbl" and #r[2]==1 then ops[code]="RET2"
      else ops[code]="RET" end
    else
      local bs=strip_tail(raw)
      if #bs==1 and bs[1][1]=="While" and unp(bs[1][2])[1]=="Bool" and unp(bs[1][2])[2]==true then
        ops[code]="CRASH"
      elseif #bs>=1 and has_w({"Block",bs},"If") then
        local ifs
        for _,s in ipairs(bs) do if s[1]=="If" then ifs=s break end end
        local cnd=unp(ifs[2][1][1])
        if cnd[1]=="Bin" and cnd[2]=="or" then
          ops[code]="FORSKIP"
        elseif cnd[1]=="Bin" and cnd[2]=="~=" and unp(cnd[4])[1]=="Nil" then
          ops[code]="FORINSKIP"
        elseif cnd[1]=="Bin" and cnd[2]=="~=" and unp(cnd[4])[1]=="Num" and unp(cnd[4])[2]==0 then
          ops[code]="LOADARGS"
        elseif cnd[1]=="Bin" and cnd[2]==">" and unp(cnd[4])[1]=="Num" and unp(cnd[4])[2]==0 then
          ops[code]="POPTEMPSTACK"
        elseif cnd[1]=="Un" and cnd[2]=="not" then
          ops[code]="LOADCONST"
          local lc_if
          A.walk(ifs,function(x) if not lc_if and x[1]=="If" and #x[2]>=2 then lc_if=x end end)
          if lc_if then
            for _,br in ipairs(lc_if[2]) do
              local bc=unp(br[1])
              if bc[1]=="Bin" and bc[2]=="==" and unp(bc[4])[1]=="Num" then
                local tg=unp(bc[4])[2]
                local bb=br[2]
                if has_w(bb,"ForNum") then tags.str=tg
                elseif #bb[2]==1 and bb[2][1][1]=="Assign" then
                  local rs=unp(bb[2][1][3][1])
                  if rs[1]=="Un" and rs[2]=="-" then tags.n32=tg
                  elseif rs[1]=="Call" and unp(rs[2])[1]=="Var" and unp(rs[2])[2]==ru_v then tags.u32=tg
                  else tags.dbl=tg end
                end
              end
            end
          end
        else
          ops[code]="JMPC"
        end
      elseif #bs>=1 and has_w({"Block",bs},"ForIn") then
        local fi
        for _,s in ipairs(bs) do if s[1]=="ForIn" then fi=s break end end
        local is_pk=false
        for _,s in ipairs(bs) do
          if s[1]=="Assign" and #s[2]==1 and unp(s[2][1])[1]=="Var" and unp(s[2][1])[2]==st_v then is_pk=true break end
        end
        if is_pk then ops[code]="PACK"
        else
          local lh=fi and fi[4][2][1] and fi[4][2][1][1]=="Assign" and unp(fi[4][2][1][2][1])
          if lh and lh[1]=="Idx" and unp(lh[2])[1]=="Idx" then ops[code]="SETTABLE3"
          else ops[code]="UNPACK" end
        end
      elseif #bs>=1 and has_w({"Block",bs},"ForNum") then
        local las=bs[#bs]
        if las[1]=="Assign" and unp(las[2][1])[1]=="Var" and unp(las[2][1])[2]==sl_v and unp(las[3][1])[2]=="+" then
          ops[code]="GETLOCAL"
        else
          local kd="SETLOCAL"
          for _,s in ipairs(bs) do
            if s[1]=="Assign" and unp(s[2][1])[1]=="Idx" and unp(s[3][1])[1]=="Idx" and is_stk(unp(s[3][1])[2]) then
              kd="ASSIGNLOCAL" break
            end
          end
          ops[code]=kd
        end
      elseif #bs==1 then
        local s=bs[1]
        if s[1]=="Assign" and #s[2]==1 then
          local l,r=unp(s[2][1]),unp(s[3][1])
          if l[1]=="Var" and l[2]==ps[1] then ops[code]="JMP"
          elseif l[1]=="Var" and l[2]==lc_v then
            if r[1]=="Tbl" then ops[code]="PUSHSCOPE" else ops[code]="POPSCOPE" end
          elseif l[1]=="Idx" and unp(l[2])[1]=="Var" and unp(l[2])[2]==st_v then
            local ix=unp(l[3])
            if ix[1]=="Bin" and ix[2]=="-" and unp(ix[4])[1]=="Num" and unp(ix[4])[2]==2 then
              ops[code]="FORPREP"
            elseif r[1]=="Un" then
              ops[code]=r[2]=="-" and "NEG" or (r[2]=="not" and "NOT" or "LEN")
            elseif r[1]=="Idx" then
              local rb=unp(r[2])
              if rb[1]=="Var" and rb[2]==ev_v then ops[code]="GETGLOBAL"
              elseif rb[1]=="Idx" and unp(r[3])[1]=="Num" and unp(r[3])[2]==1 then ops[code]="UNPACKFIRST"
              else ops[code]="GETTABLE" end
            end
          end
        elseif s[1]=="Assign" and #s[2]==2 then
          ops[code]="SWAP"
        end
      elseif #bs==2 then
        local s1,s2=bs[1],bs[2]
        local has_k,k_nm=false,nil
        A.walk({"Block",bs},function(x)
          if x[1]=="Call" and #x[3]>=3 and unp(x[3][2])[1]=="Num" then has_k=true end
        end)
        if s1[1]=="Assign" and s2[1]=="Assign" and #s1[2]==1 and unp(s1[2][1])[1]=="Var" and unp(s1[2][1])[2]==st_v and unp(s1[3][1])[1]=="Idx" then
          ops[code]="POPTEMPSTACK2"
        elseif s1[1]=="Assign" and s2[1]=="Assign" and #s1[2]==1 and unp(s1[2][1])[1]=="Var" and unp(s1[2][1])[2]==st_v then
          ops[code]="CLEARSTACK"
        elseif #s1[2]==1 and #s2[2]==1 and unp(s1[2][1])[1]=="Assign" then
        end
        if not ops[code] then
          if s1[1]=="Assign" and #s1[2]==1 and (unp(s1[2][1])[1]=="Field" or (unp(s1[2][1])[1]=="Idx" and unp(unp(s1[2][1])[3])[1]=="Str")) then
            local t1=unp(s2[3][1])
            if t1[1]=="Tbl" and #t1[2]==2 then ops[code]="PUSHTEMPSTACK2" else ops[code]="PUSHTEMPSTACK" end
          elseif s1[1]=="Assign" and #s1[2]==1 and unp(s1[2][1])[1]=="Var" and unp(s1[2][1])[2]==sl_v then
            local rh=unp(s1[3][1])
            if rh[1]=="Bin" and rh[2]=="-" then
              if #s2[2]==2 and s2[1]=="Assign" and s2[1]=="Assign" then
                if s2[1]=="Assign" then
                  local ls=unp(s2[3][1])
                  if ls[1]=="Bin" and bm[ls[2]] then ops[code]=bm[ls[2]]
                  elseif ls[1]=="Call" or (ls[1]=="Tbl" and #ls[2]==1) then ops[code]="CALL"
                  elseif ls[1]=="Idx" then ops[code]="GETTABLE2"
                  else ops[code]="DROP" end
                end
              elseif #s2[2]==1 then ops[code]="DROP" end
            elseif s2[1]=="Assign" and #s2[2]==1 then
              local l2,r2=unp(s2[2][1]),unp(s2[3][1])
              if r2[1]=="Nil" then ops[code]="LOADNIL"
              elseif r2[1]=="Bool" then ops[code]=r2[2] and "LOADTRUE" or "LOADFALSE"
              elseif r2[1]=="Tbl" then ops[code]="NEWTABLE"
              elseif r2[1]=="Var" then ops[code]="DUP"
              elseif r2[1]=="Idx" and unp(r2[2])[1]=="Var" and unp(r2[2])[2]==st_v then ops[code]="DUP"
              elseif r2[1]=="Idx" and unp(r2[2])[1]=="Var" and unp(r2[2])[2]==ar_v then ops[code]="LOADARG"
              elseif r2[1]=="Call" then
                ops[code]="FUNC"
                cb_v=unp(r2[2])[2]
                local fa=unp(r2[3][1])
                if fa[1]=="Idx" and unp(fa[2])[1]=="Var" then fp_v=unp(fa[2])[2] end
              end
            end
          elseif s2[1]=="Assign" and #s2[2]==1 and unp(s2[2][1])[1]=="Idx" and unp(unp(s2[2][1])[2])[1]=="Idx" then
            ops[code]="ASSIGNTABLE"
          elseif s2[1]=="Assign" and #s2[2]==1 and unp(s2[2][1])[1]=="Var" and unp(s2[2][1])[2]==sl_v then
            local rh=unp(s2[3][1])
            if rh[1]=="Bin" and rh[2]=="+" then
              local r1=unp(s1[3][1])
              if r1[1]=="Idx" and unp(r1[2])[1]=="Var" and unp(r1[2])[2]==st_v then ops[code]="DUP"
              elseif r1[1]=="Call" then
                ops[code]="FUNC"
                cb_v=unp(r1[2])[2]
                local fa=unp(r1[3][1])
                if fa[1]=="Idx" and unp(fa[2])[1]=="Var" then fp_v=unp(fa[2])[2] end
              end
            end
          elseif s1[1]=="Assign" and #s1[2]==1 and unp(s1[2][1])[1]=="Var" and unp(s1[2][1])[2]==sl_v then
          end
        end
        if not ops[code] and #bs==2 and s2[1]=="Assign" and #s2[2]==1 and unp(s2[2][1])[1]=="Var" and unp(s2[2][1])[2]==sl_v then
          local r1=unp(s1[3][1])
          if r1[1]=="Nil" then ops[code]="LOADNIL"
          elseif r1[1]=="Bool" then ops[code]=r1[2] and "LOADTRUE" or "LOADFALSE"
          elseif r1[1]=="Idx" and unp(r1[2])[1]=="Var" and unp(r1[2])[2]==st_v then ops[code]="DUP" end
        end
      elseif #bs==3 then
        local has_op
        for _,s in ipairs(bs) do
          if s[1]=="Assign" then
            for _,r in ipairs(s[3]) do
              local u=unp(r)
              if u[1]=="Bin" and bm[u[2]] then
                local lb=unp(u[3])
                if lb[1]=="Idx" and unp(lb[2])[1]=="Var" and unp(lb[2])[2]==st_v then has_op=bm[u[2]] end
              end
            end
          end
        end
        if has_op then ops[code]=has_op
        elseif bs[1][1]=="Assign" and unp(bs[1][2][1])[1]=="Var" and unp(bs[1][2][1])[2]==sl_v then
          local s2=bs[2]
          if s2[1]=="Assign" and #s2[2]==1 and unp(s2[2][1])[1]=="Idx" then
            local lb=unp(unp(s2[2][1])[2])
            if lb[1]=="Var" and lb[2]==ev_v then
              local r2=unp(s2[3][1])
              if r2[1]=="Idx" and unp(r2[2])[1]=="Idx" then ops[code]="ASSIGNGLOBAL" else ops[code]="SETGLOBAL" end
            elseif lb[1]=="Var" and lb[2]==st_v then
              local ix=unp(unp(s2[2][1])[3])
              if ix[1]=="Call" then ops[code]="SETTABLE2" else ops[code]="SETTABLE" end
            elseif lb[1]=="Idx" then
              local ix=unp(unp(s2[2][1])[3])
              if ix[1]=="Call" then ops[code]="SETTABLE2" else ops[code]="SETTABLE" end
            end
          elseif s2[1]=="Assign" and #s2[2]==1 and unp(s2[2][1])[1]=="Var" and unp(s2[2][1])[2]==ar_v then
            ops[code]="SETARGS"
          end
        elseif bs[1][1]=="Assign" and (unp(bs[1][2][1])[1]=="Field" or (unp(bs[1][2][1])[1]=="Idx" and unp(unp(bs[1][2][1])[3])[1]=="Str")) then
          local t1=unp(bs[3][3][1])
          if t1[1]=="Tbl" and #t1[2]==2 then ops[code]="PUSHTEMPSTACK2" else ops[code]="PUSHTEMPSTACK" end
        end
      end
    end
    if not ops[code] then return nil end
  end
  return {by_v=by_v,k1=k1,k2=k2,k3=k3,k4=k4,ops=ops,tags=tags,cb_v=cb_v,fp_v=fp_v}
end
local function ext_cs(b)
  local vars,run_f,info={},nil,nil
  for _,s in ipairs(b[2]) do
    if s[1]=="LocalVar" then
      for i,nm in ipairs(s[2]) do if s[3][i] then vars[nm]=unp(s[3][i]) end end
    elseif s[1]=="LocalFunc" then
      vars[s[2]]={"Func",s[3],s[4],s[5]}
    elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" then
      vars[unp(s[2][1])[2]]=unp(s[3][1])
    end
  end
  for nm,v in pairs(vars) do
    if v[1]=="Func" and #v[2]==4 and not v[3] then
      local r=ext_run(v)
      if r then run_f=nm info=r break end
    end
  end
  if not run_f then return nil end
  local b_e=vars[info.by_v]
  if not b_e or b_e[1]~="Str" then return nil end
  local raw_b=b_e[2]
  local dec_n,ec_n
  for nm,v in pairs(vars) do
    if v[1]=="Func" and #v[2]==0 and not v[3] then
      for _,st in ipairs(v[4][2]) do
        if st[1]=="Assign" and #st[2]==1 and unp(st[2][1])[1]=="Var" and unp(st[2][1])[2]==info.by_v then
          local rh=unp(st[3][1])
          if rh[1]=="Call" and #rh[3]==1 and unp(rh[2])[1]=="Var" and unp(rh[3][1])[1]=="Var" and unp(rh[3][1])[2]==info.by_v then
            dec_n=unp(rh[2])[2]
            break
          end
        end
      end
    end
    if dec_n then break end
  end
  local dec_f=dec_n and vars[dec_n]
  if dec_f and dec_f[1]=="Func" then
    A.walk(dec_f[4],function(x)
      if not ec_n and x[1]=="Call" and #x[3]==2 and unp(x[3][1])[1]=="Var" and unp(x[3][2])[1]=="Var" then
        local fn_nm=unp(x[3][1])[2]
        if vars[fn_nm] and vars[fn_nm][1]=="Str" and #vars[fn_nm][2]==64 then ec_n=fn_nm end
      end
    end)
  end
  local bs
  if ec_n and vars[ec_n] and vars[ec_n][1]=="Str" then
    bs=dec_b64(raw_b,vars[ec_n][2])
  else
    bs={}
    for i=1,#raw_b do bs[i]=raw_b:byte(i) end
  end
  local fn_cnt=rdu(bs,1,3)
  if fn_cnt<1 or fn_cnt>20000 then return nil end
  local off=4
  local fn_pos={}
  for i=0,fn_cnt-1 do fn_pos[i+1]=rdu(bs,off+i*3,3) end
  off=off+fn_cnt*3
  local c_cnt=rdu(bs,off,3)
  local c_pos={}
  for i=0,c_cnt-1 do c_pos[i+1]=rdu(bs,off+3+i*4,4) end
  off=off+c_cnt*4+6
  local i_cnt=rdu(bs,off-3,3)
  if i_cnt<1 or i_cnt>500000 then return nil end
  local c_off=off+i_cnt*4
  local ks234={info.k2,info.k3,info.k4}
  local ks23={info.k2,info.k3}
  local consts={}
  for i=1,c_cnt do
    local p=c_pos[i]+c_off
    local tg=bs[p]
    if tg==info.tags.str then
      local ln=rdu(bs,p+1,4)
      local t={}
      for k=1,ln do t[k]=string.char(bs[p+4+k] or 0) end
      consts[i]={"Str",table.concat(t)}
    elseif tg==info.tags.dbl then
      consts[i]={"Num",rdd(bs,p+1)}
    elseif tg==info.tags.u32 then
      consts[i]={"Num",rdu(bs,p+1,4)}
    elseif tg==info.tags.n32 then
      consts[i]={"Num",-rdu(bs,p+1,4)}
    end
  end
  local insns={}
  for pc=1,i_cnt do
    local p=off+(pc-1)*4
    local op=bxor(bs[p] or 0,info.k1)
    local kd=info.ops[op] or "NOP"
    local a,b_
    if kd=="JMP" or kd=="JMPC" or kd=="LOADCONST" or kd=="FUNC" then
      a=rdu(bs,p+1,3,ks234)
    else
      a=rdu(bs,p+1,2,ks23)
      b_=bxor(bs[p+3] or 0,info.k4)
    end
    insns[pc]={k=kd,a=a,b=b_}
  end
  return {fn_pos=fn_pos,consts=consts,insns=insns}
end
local function to_lhs(t,k)
  k=unp(k)
  if k[1]=="Str" and v_id(k[2]) then return {"Field",t,k[2]} end
  return {"Idx",t,k}
end
local function to_get(t,k)
  k=unp(k)
  if k[1]=="Str" and v_id(k[2]) then return {"Field",t,k[2]} end
  return {"Idx",t,k}
end
local function lift_fn(cs,fid,par_sc,used)
  local ins=cs.insns
  local pc0=cs.fn_pos[fid]
  local p_end=cs.fn_pos[fid+1] and (cs.fn_pos[fid+1]-1) or #ins
  local vc=0
  if not used then
    used={}
    local function add_n(n) vc=vc+1 return n end
    used._c=0
  end
  local function fresh(pfx)
    repeat used._c=used._c+1 until not used[(pfx or "_v")..used._c]
    local nm=(pfx or "_v")..used._c
    used[nm]=true
    return nm
  end
  local root_sc={p=par_sc,vs={},decls={},body_sts=nil}
  local ps={}
  while pc0<=p_end and ins[pc0].k=="NOP" do pc0=pc0+1 end
  while pc0+1<=p_end and ins[pc0].k=="LOADARG" and ins[pc0+1].k=="SETLOCAL" and ins[pc0+1].b==0 do
    local anm=fresh("_a")
    ps[#ps+1]=anm
    root_sc.vs[ins[pc0+1].a]=anm
    pc0=pc0+2
  end
  local np=#ps
  local cur_sc=root_sc
  local sc_d=0
  local va=false
  local function get_sc(df)
    local s=cur_sc
    for _=1,df do if s.p then s=s.p end end
    return s
  end
  local function push_sc(sts)
    sc_d=sc_d+1
    cur_sc={p=cur_sc,vs={},decls={},body_sts=sts}
    return cur_sc
  end
  local function pop_sc()
    local s=cur_sc
    if #s.decls>0 and s.body_sts then
      table.insert(s.body_sts,1,{"LocalVar",s.decls,{}})
    end
    sc_d=sc_d-1
    cur_sc=s.p
  end
  local function res_v(id,df,no_dec)
    local s=get_sc(df)
    if not s.vs[id] then
      local nm=fresh("_v")
      s.vs[id]=nm
      if not no_dec then s.decls[#s.decls+1]=nm end
    end
    return s.vs[id]
  end
  local stk={}
  local tstk={}
  local lp_stk={}
  local function as_e(x)
    if not x then return {"Nil"} end
    if x.pk then return x.pk[1] or {"Nil"} end
    if x.mr then return x.mr end
    return x.ast or {"Nil"}
  end
  local function pack_l(arr)
    local out={}
    for i,x in ipairs(arr) do
      if i==#arr and x.mr then out[#out+1]=x.mr
      else out[#out+1]=as_e(x) end
    end
    return out
  end
  local lift_rng
  local function step_e(pc,lim)
    local ir=ins[pc]
    local k,a,b=ir.k,ir.a,ir.b
    if k=="NOP" then return pc+1
    elseif k=="LOADCONST" then
      stk[#stk+1]={ast=A.cp(cs.consts[a] or {"Nil"}),pc0=pc}
      return pc+1
    elseif k=="LOADNIL" then
      stk[#stk+1]={ast={"Nil"},pc0=pc} return pc+1
    elseif k=="LOADTRUE" then
      stk[#stk+1]={ast={"Bool",true},pc0=pc} return pc+1
    elseif k=="LOADFALSE" then
      stk[#stk+1]={ast={"Bool",false},pc0=pc} return pc+1
    elseif k=="GETGLOBAL" then
      local it=table.remove(stk)
      local key=as_e(it)
      local e=key[1]=="Str" and v_id(key[2]) and {"Var",key[2]} or {"Idx",{"Var","_G"},key}
      stk[#stk+1]={ast=e,pc0=(it and it.pc0) or pc}
      return pc+1
    elseif k=="GETLOCAL" then
      stk[#stk+1]={ast={"Var",res_v(a,b)},pc0=pc}
      return pc+1
    elseif k=="LOADARG" then
      if a>np then va=true end
      stk[#stk+1]={ast={"Vararg"},pc0=pc}
      return pc+1
    elseif k=="LOADARGS" then
      va=true
      stk[#stk+1]={mr={"Vararg"},pc0=pc}
      return pc+1
    elseif k=="FUNC" then
      stk[#stk+1]={ast=lift_fn(cs,a,cur_sc,used),pc0=pc}
      return pc+1
    elseif k=="NEWTABLE" then
      stk[#stk+1]={ast={"Tbl",{}},tb_l=true,ai=1,pc0=pc}
      return pc+1
    elseif k=="SETTABLE2" then
      local v=as_e(table.remove(stk))
      local t=stk[#stk]
      if t and t.tb_l then
        t.ast[2][#t.ast[2]+1]={"V",v}
        t.ai=a+1
      end
      return pc+1
    elseif k=="SETTABLE3" then
      local pk=table.remove(stk)
      local t=stk[#stk]
      if t and t.tb_l and pk and pk.pk then
        for _,v in ipairs(pk.pk) do t.ast[2][#t.ast[2]+1]={"V",v} end
      end
      return pc+1
    elseif k=="GETTABLE" then
      local ky=as_e(table.remove(stk))
      local t=stk[#stk]
      stk[#stk+1]={ast=to_get(as_e(t),ky),sf_b=t and t.sf_b,pc0=(t and t.pc0) or pc}
      return pc+1
    elseif k=="GETTABLE2" then
      local ky=as_e(table.remove(stk))
      local t=table.remove(stk)
      stk[#stk+1]={ast=to_get(as_e(t),ky),pc0=(t and t.pc0) or pc}
      return pc+1
    elseif k=="PUSHTEMPSTACK" then
      tstk[#tstk+1]=stk
      stk={}
      return pc+1
    elseif k=="PUSHTEMPSTACK2" then
      local top=stk[#stk]
      tstk[#tstk+1]=stk
      stk={{ast=top and as_e(top),sf_b=top,pc0=(top and top.pc0) or pc}}
      return pc+1
    elseif k=="POPTEMPSTACK" then
      local top=stk[#stk]
      stk=table.remove(tstk) or {}
      stk[#stk+1]=top or {pk={}}
      return pc+1
    elseif k=="POPTEMPSTACK2" then
      stk=table.remove(tstk) or {}
      return pc+1
    elseif k=="PACK" then
      local p0=stk[1] and stk[1].pc0 or pc
      local list=pack_l(stk)
      stk={{pk=list,pc0=p0}}
      return pc+1
    elseif k=="UNPACK" then
      local top=stk[#stk]
      if top and top.mr then
      elseif top and top.cr then top.mr=top.cr top.cr=nil end
      return pc+1
    elseif k=="UNPACKFIRST" then
      local top=stk[#stk]
      if top and top.cr then stk[#stk]={ast=top.cr,pc0=top.pc0}
      elseif top and top.pk then stk[#stk]={ast=top.pk[1] or {"Nil"},pc0=top.pc0} end
      return pc+1
    elseif k=="SWAP" then
      local n=#stk
      if n>a then stk[n],stk[n-a]=stk[n-a],stk[n] end
      return pc+1
    elseif k=="DROP" then
      table.remove(stk)
      return pc+1
    elseif k=="CLEARSTACK" then
      stk={}
      return pc+1
    elseif k=="CALL" then
      local ag=table.remove(stk)
      local fn=table.remove(stk)
      local args=(ag and ag.pk) or {}
      local cn,p0
      if fn and fn.sf_b and fn.ast and (fn.ast[1]=="Field" or fn.ast[1]=="Idx") then
        local mnm=fn.ast[1]=="Field" and fn.ast[3] or (unp(fn.ast[3])[1]=="Str" and unp(fn.ast[3])[2])
        if mnm and v_id(mnm) and #args>=1 then
          local rest={}
          for i=2,#args do rest[i-1]=args[i] end
          cn={"MCall",fn.ast[2],mnm,rest}
          p0=fn.sf_b.pc0
        end
      end
      if not cn then cn={"Call",as_e(fn),args} end
      stk[#stk+1]={cr=cn,pc0=p0 or (fn and fn.pc0) or pc}
      return pc+1
    elseif k=="DUP" then
      local top=stk[#stk]
      if pc+2<=lim and ins[pc+1].k=="JMPC" and ins[pc+2].k=="DROP" then
        local epc=ins[pc+1].a
        table.remove(stk)
        local cp=pc+3
        while cp<epc do
          local nx=step_e(cp,epc-1)
          if not nx or nx<=cp then break end
          cp=nx
        end
        local rhs=as_e(table.remove(stk))
        stk[#stk+1]={ast={"Bin","or",as_e(top),rhs},pc0=(top and top.pc0) or pc}
        return epc
      elseif pc+3<=lim and ins[pc+1].k=="NOT" and ins[pc+2].k=="JMPC" and ins[pc+3].k=="DROP" then
        local epc=ins[pc+2].a
        table.remove(stk)
        local cp=pc+4
        while cp<epc do
          local nx=step_e(cp,epc-1)
          if not nx or nx<=cp then break end
          cp=nx
        end
        local rhs=as_e(table.remove(stk))
        stk[#stk+1]={ast={"Bin","and",as_e(top),rhs},pc0=(top and top.pc0) or pc}
        return epc
      end
      stk[#stk+1]=top
      return pc+1
    elseif k=="NEG" or k=="NOT" or k=="LEN" then
      local op=k=="NEG" and "-" or (k=="NOT" and "not" or "#")
      local it=table.remove(stk)
      stk[#stk+1]={ast={"Un",op,as_e(it)},pc0=(it and it.pc0) or pc}
      return pc+1
    else
      local bm={["ADD"]="+",["SUB"]="-",["MUL"]="*",["DIV"]="/",["MOD"]="%",["POW"]="^",["CONCAT"]="..",["EQ"]="==",["NEQ"]="~=",["LT"]="<",["GT"]=">",["LET"]="<=",["GET"]=">="}
      if bm[k] then
        local r=as_e(table.remove(stk))
        local lt=table.remove(stk)
        stk[#stk+1]={ast={"Bin",bm[k],as_e(lt),r},pc0=(lt and lt.pc0) or pc}
        return pc+1
      end
    end
    return nil
  end
  local function is_lp_exit(dst)
    for i=#lp_stk,1,-1 do
      if lp_stk[i].ep==dst then return true,"Break" end
      if lp_stk[i].sp==dst then return true,"Continue" end
    end
    return false
  end
  local function is_cond_end(pc,lim)
    if pc+1<=lim and ins[pc].k=="NOT" and ins[pc+1].k=="JMPC" then return pc+1,ins[pc+1].a end
    return nil
  end
  lift_rng=function(s_pc,e_pc,out)
    local pc,stp_c=s_pc,0
    while pc<=e_pc do
      stp_c=stp_c+1
      if stp_c>200000 then error("loop") end
      local ir=ins[pc]
      local k=ir.k
      if k=="NOP" then pc=pc+1
      elseif k=="CLEARSTACK" or k=="DROP" then
        local top=stk[#stk]
        if k=="CLEARSTACK" and top and top.cr then
          out[#out+1]={"CallStmt",top.cr}
        end
        stk={}
        pc=pc+1
      elseif k=="RET3" then
        out[#out+1]={"Return",{}}
        return
      elseif k=="RET2" then
        local v=as_e(table.remove(stk))
        out[#out+1]={"Return",{v}}
        return
      elseif k=="RET" then
        local top=table.remove(stk)
        out[#out+1]={"Return",(top and top.pk) or (top and {as_e(top)}) or {}}
        return
      elseif k=="POPSCOPE" then
        if pc<e_pc and ins[pc+1].k=="JMP" then
          local np=pc
          while np<=e_pc and ins[np].k=="POPSCOPE" do np=np+1 end
          if np<=e_pc and ins[np].k=="JMP" then
            local _,lk=is_lp_exit(ins[np].a)
            if lk then
              out[#out+1]={lk}
              return
            end
          end
        end
        if sc_d>0 then pop_sc() end
        pc=pc+1
      elseif k=="JMP" then
        local _,lk=is_lp_exit(ir.a)
        if lk then out[#out+1]={lk} return end
        return
      elseif k=="PUSHSCOPE" then
        local rep_j
        for j=e_pc,pc+2,-1 do
          if ins[j].k=="JMP" and ins[j].a==pc and ins[j-1].k=="JMPC" and ins[j-1].a==j+1 then
            rep_j=j break
          end
        end
        if rep_j then
          local nb={}
          local rb=push_sc(nb)
          lp_stk[#lp_stk+1]={sp=pc,ep=rep_j+1}
          local cnd_pc=rep_j-2
          while cnd_pc>=pc+1 and ins[cnd_pc].k~="POPSCOPE" do cnd_pc=cnd_pc-1 end
          stk={}
          lift_rng(pc+1,cnd_pc-1,nb)
          local cond=as_e(table.remove(stk))
          while sc_d>0 and cur_sc~=rb do pop_sc() end
          if cur_sc==rb then pop_sc() end
          table.remove(lp_stk)
          out[#out+1]={"Repeat",{"Block",nb},cond}
          stk={}
          pc=rep_j+1
        else
          local depth,end_p=1,nil
          for j=pc+1,e_pc do
            local jk=ins[j].k
            if jk=="PUSHSCOPE" or jk=="FORSKIP" or jk=="FORINSKIP" then depth=depth+1
            elseif jk=="POPSCOPE" then
              depth=depth-1
              if depth==0 then end_p=j break end
            end
          end
          local db={}
          push_sc(db)
          lift_rng(pc+1,(end_p and end_p-1 or e_pc),db)
          if cur_sc.body_sts==db then pop_sc() end
          out[#out+1]={"Do",{"Block",db}}
          stk={}
          pc=(end_p and end_p+1 or e_pc+1)
        end
      elseif k=="FORPREP" then
        local stp=as_e(table.remove(stk))
        local lim=as_e(table.remove(stk))
        local ini=as_e(table.remove(stk))
        if pc+2<=e_pc and ins[pc+1].k=="FORSKIP" and ins[pc+2].k=="JMP" then
          local vid=ins[pc+1].a
          local l_end=ins[pc+2].a
          local fb={}
          local fs=push_sc(fb)
          local vnm=fresh("_v")
          fs.vs[vid]=vnm
          lp_stk[#lp_stk+1]={sp=pc+1,ep=l_end}
          local b_end=l_end-1
          if b_end>=pc+4 and ins[b_end].k=="JMP" and ins[b_end].a==pc+1 then b_end=b_end-1 end
          if b_end>=pc+4 and ins[b_end].k=="POPSCOPE" then b_end=b_end-1 end
          if b_end>=pc+4 and ins[b_end].k=="POPTEMPSTACK2" then b_end=b_end-1 end
          local b_s=ins[pc+3].k=="PUSHTEMPSTACK" and (pc+4) or (pc+3)
          lift_rng(b_s,b_end,fb)
          while sc_d>0 and cur_sc~=fs do pop_sc() end
          if cur_sc==fs then pop_sc() end
          table.remove(lp_stk)
          local s_e=(stp[1]=="Num" and stp[2]==1) and false or stp
          out[#out+1]={"ForNum",vnm,ini,lim,s_e,{"Block",fb}}
          stk={}
          pc=ins[l_end].k=="CLEARSTACK" and (l_end+1) or l_end
        else
          pc=pc+1
        end
      elseif k=="FORINSKIP" then
        local pk=table.remove(stk)
        local exps=(pk and pk.pk) or {}
        if pc+1<=e_pc and ins[pc+1].k=="JMP" then
          local l_end=ins[pc+1].a
          local fb={}
          local fs=push_sc(fb)
          local vs={}
          local p=pc+2
          while p+2<=l_end and ins[p].k=="LOADCONST" and ins[p+1].k=="GETTABLE" and ins[p+2].k=="SETLOCAL" do
            local vnm=fresh("_v")
            fs.vs[ins[p+2].a]=vnm
            vs[#vs+1]=vnm
            p=p+3
          end
          if p<=l_end and ins[p].k=="DROP" then p=p+1 end
          if p<=l_end and ins[p].k=="PUSHTEMPSTACK" then p=p+1 end
          lp_stk[#lp_stk+1]={sp=pc,ep=l_end}
          local b_end=l_end-1
          if b_end>=p and ins[b_end].k=="JMP" and ins[b_end].a==pc then b_end=b_end-1 end
          if b_end>=p and ins[b_end].k=="POPSCOPE" then b_end=b_end-1 end
          if b_end>=p and ins[b_end].k=="POPTEMPSTACK2" then b_end=b_end-1 end
          lift_rng(p,b_end,fb)
          while sc_d>0 and cur_sc~=fs do pop_sc() end
          if cur_sc==fs then pop_sc() end
          table.remove(lp_stk)
          out[#out+1]={"ForIn",vs,exps,{"Block",fb}}
          stk={}
          pc=ins[l_end].k=="CLEARSTACK" and (l_end+1) or l_end
        else
          pc=pc+1
        end
      elseif k=="SETGLOBAL" then
        local val=as_e(table.remove(stk))
        local key=as_e(table.remove(stk))
        local lhs=(key[1]=="Str" and v_id(key[2])) and {"Var",key[2]} or {"Idx",{"Var","_G"},key}
        out[#out+1]={"Assign",{lhs},{val}}
        stk={}
        pc=pc+1
      elseif k=="SETLOCAL" then
        local val=as_e(table.remove(stk))
        local lr=unp(val)
        local sc=get_sc(ir.b)
        if lr[1]=="Func" and ir.b==0 and not sc.vs[ir.a] then
          local nm=fresh("_v")
          sc.vs[ir.a]=nm
          out[#out+1]={"LocalFunc",nm,lr[2],lr[3],lr[4]}
        else
          local nm=res_v(ir.a,ir.b)
          out[#out+1]={"Assign",{{"Var",nm}},{val}}
        end
        stk={}
        pc=pc+1
      elseif k=="SETTABLE" then
        local val=as_e(table.remove(stk))
        local ky=as_e(table.remove(stk))
        local tb=stk[#stk]
        if tb and tb.tb_l then
          local uk=unp(ky)
          if uk[1]=="Str" and v_id(uk[2]) then tb.ast[2][#tb.ast[2]+1]={"F",uk[2],val}
          else tb.ast[2][#tb.ast[2]+1]={"I",ky,val} end
          pc=pc+1
        else
          table.remove(stk)
          out[#out+1]={"Assign",{to_lhs(as_e(tb),ky)},{val}}
          stk[#stk+1]={stale=true}
          pc=pc+1
        end
      elseif k=="ASSIGNTABLE" or ((k=="LOADCONST" and pc+1<=e_pc and (ins[pc+1].k=="ASSIGNLOCAL" or ins[pc+1].k=="ASSIGNGLOBAL")) and stk[#stk] and stk[#stk].pk) then
        local lhss={}
        local p=pc
        local is_lv=true
        local rhs_pk
        while p<=e_pc do
          local pk_i=ins[p].k
          if pk_i=="LOADCONST" and p+1<=e_pc and (ins[p+1].k=="ASSIGNLOCAL" or ins[p+1].k=="ASSIGNGLOBAL") then
            local c_v=cs.consts[ins[p].a]
            local nx=ins[p+1]
            if nx.k=="ASSIGNLOCAL" then
              if nx.b~=0 then is_lv=false end
              lhss[#lhss+1]={k="L",id=nx.a,df=nx.b}
            else
              is_lv=false
              lhss[#lhss+1]={k="G",nm=c_v and c_v[2] or ""}
            end
            p=p+2
          elseif pk_i=="ASSIGNTABLE" then
            is_lv=false
            local b_idx=#stk-ins[p].b
            local tb_e=stk[b_idx] and as_e(stk[b_idx]) or {"Nil"}
            local ix_e=stk[b_idx+1] and as_e(stk[b_idx+1]) or {"Nil"}
            lhss[#lhss+1]={k="T",lhs=to_lhs(tb_e,ix_e)}
            p=p+1
          else
            break
          end
        end
        rhs_pk=stk[#stk] and stk[#stk].pk or {}
        if is_lv then
          for _,lh in ipairs(lhss) do
            local s=get_sc(lh.df)
            if s.vs[lh.id] then is_lv=false break end
          end
        end
        if is_lv and #lhss>0 and p<=e_pc and ins[p].k=="DROP" then
          local nms={}
          for i,lh in ipairs(lhss) do nms[i]=res_v(lh.id,lh.df,true) end
          out[#out+1]={"LocalVar",nms,rhs_pk}
          p=p+1
        elseif #lhss>0 then
          local ast_lhs={}
          for i,lh in ipairs(lhss) do
            if lh.k=="L" then ast_lhs[i]={"Var",res_v(lh.id,lh.df)}
            elseif lh.k=="G" then ast_lhs[i]=v_id(lh.nm) and {"Var",lh.nm} or {"Idx",{"Var","_G"},{"Str",lh.nm}}
            else ast_lhs[i]=lh.lhs end
          end
          out[#out+1]={"Assign",ast_lhs,rhs_pk}
          if p<=e_pc and (ins[p].k=="CLEARSTACK" or ins[p].k=="DROP") then p=p+1 end
        end
        stk={}
        pc=p>pc and p or (pc+1)
      else
        local np=step_e(pc,e_pc)
        if np then
          pc=np
          if pc+1<=e_pc and ins[pc].k=="NOT" and ins[pc+1].k=="JMPC" and #stk>=1 then
            local top=stk[#stk]
            if top and top.ast and not (ins[pc-1] and ins[pc-1].k=="DUP") then
              local c_pc=top.pc0 or (pc-1)
              local c_expr=as_e(table.remove(stk))
              local l_nx=ins[pc+1].a
              local body_p=pc+2
              local is_w=l_nx-1>=body_p and ins[l_nx-1].k=="JMP" and ins[l_nx-1].a==c_pc
              if is_w then
                local wb={}
                local has_sc=ins[body_p] and ins[body_p].k=="PUSHSCOPE"
                local ws=has_sc and push_sc(wb) or nil
                lp_stk[#lp_stk+1]={sp=c_pc,ep=l_nx}
                local w_start=has_sc and (body_p+1) or body_p
                local w_end=l_nx-2
                if has_sc and w_end>=w_start and ins[w_end].k=="POPSCOPE" then w_end=w_end-1 end
                lift_rng(w_start,w_end,wb)
                if ws then while sc_d>0 and cur_sc~=ws do pop_sc() end if cur_sc==ws then pop_sc() end end
                table.remove(lp_stk)
                out[#out+1]={"While",c_expr,{"Block",wb}}
                stk={}
                pc=l_nx
              else
                local l_end=l_nx
                local tail=ins[l_nx-1]
                if tail and tail.k=="JMP" and tail.a>l_nx and tail.a<=e_pc+1 and not is_lp_exit(tail.a) then
                  l_end=tail.a
                end
                local function lift_br(b0,b1)
                  local bb={}
                  if b0<=b1 then
                    local has_sc=ins[b0].k=="PUSHSCOPE"
                    local bs=has_sc and push_sc(bb) or nil
                    local bs0=has_sc and (b0+1) or b0
                    local bs1=b1
                    if bs1>=bs0 and ins[bs1].k=="JMP" and ins[bs1].a==l_end then bs1=bs1-1 end
                    if has_sc and bs1>=bs0 and ins[bs1].k=="POPSCOPE" then bs1=bs1-1 end
                    lift_rng(bs0,bs1,bb)
                    if bs then while sc_d>0 and cur_sc~=bs do pop_sc() end if cur_sc==bs then pop_sc() end end
                  end
                  return {"Block",bb}
                end
                local brs={{c_expr,lift_br(body_p,l_nx-1)}}
                local cur=l_nx
                local el=false
                while cur<l_end do
                  if ins[cur].k=="PUSHSCOPE" then
                    el=lift_br(cur,l_end-1)
                    break
                  end
                  stk={}
                  local sp=cur
                  local found_jmpc
                  while sp<l_end do
                    if sp+1<l_end and ins[sp].k=="NOT" and ins[sp+1].k=="JMPC" and #stk>=1 then
                      found_jmpc=sp break
                    end
                    local nx=step_e(sp,l_end-1)
                    if not nx then break end
                    sp=nx
                  end
                  if found_jmpc then
                    local ec=as_e(table.remove(stk))
                    local nxt=ins[found_jmpc+1].a
                    if nxt<=l_end and nxt>cur then
                      brs[#brs+1]={ec,lift_br(found_jmpc+2,nxt-1)}
                      cur=nxt
                    else
                      el=lift_br(cur,l_end-1)
                      break
                    end
                  else
                    el=lift_br(cur,l_end-1)
                    break
                  end
                end
                out[#out+1]={"If",brs,el}
                stk={}
                pc=l_end
              end
            end
          end
        else
          pc=pc+1
        end
      end
    end
  end
  local body={}
  root_sc.body_sts=body
  lift_rng(pc0,p_end,body)
  if #root_sc.decls>0 then table.insert(body,1,{"LocalVar",root_sc.decls,{}}) end
  return {"Func",ps,va,{"Block",body}}
end
function M.lift_cs(b)
  local ok,cs=pcall(ext_cs,b)
  if not ok or not cs then return nil end
  local ok2,fn=pcall(lift_fn,cs,1,nil,nil)
  if not ok2 or not fn or fn[1]~="Func" then return nil end
  return fn[4]
end
return M