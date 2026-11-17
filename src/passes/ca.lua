local A=require("src.frontend.ast")
local M_misc=require("src.passes.misc")
local M={}
local unp=A.unp
local fl,sb,sc=math.floor,string.byte,string.char
local function lit_v(e)
  e=unp(e)
  local k=e[1]
  if k=="Nil" then return true,nil
  elseif k=="Bool" or k=="Num" or k=="Str" then return true,e[2]
  elseif k=="Un" and e[2]=="-" and unp(e[3])[1]=="Num" then return true,-unp(e[3])[2] end
  return false,nil
end
local function lit_n(v)
  if v==nil then return {"Nil"} end
  local t=type(v)
  if t=="boolean" then return {"Bool",v}
  elseif t=="number" then return {"Num",v}
  elseif t=="string" then return {"Str",v} end
  return {"Nil"}
end
local function b64(s,mp)
  local out={}
  local v,cnt,i,n=0,0,1,#s
  while i<=n do
    local ch=s:sub(i,i)
    local cd=mp[ch]
    if cd then
      v=v+cd*(64^(3-cnt))
      cnt=cnt+1
      if cnt==4 then
        cnt=0
        local c1=fl(v/65536)
        local c2=fl(v%65536/256)
        local c3=v%256
        out[#out+1]=sc(c1,c2,c3)
        v=0
      end
    elseif ch=="=" then
      out[#out+1]=sc(fl(v/65536))
      if i>=n or s:sub(i+1,i+1)~="=" then
        out[#out+1]=sc(fl(v%65536/256))
      end
      break
    end
    i=i+1
  end
  return table.concat(out)
end
local function b85(s,mp)
  local out={}
  local i,n=1,#s
  while i<=n do
    local rem=n-i+1
    local cnt=rem>=5 and 5 or rem
    local v,ok=0,cnt>1
    for j=0,4 do
      local cd
      if j<cnt then
        cd=mp[s:sub(i+j,i+j)]
        if not cd then ok=false break end
      else
        cd=84
      end
      v=v*85+cd
    end
    if ok then
      local b1=fl(v/16777216)%256
      local b2=fl(v/65536)%256
      local b3=fl(v/256)%256
      local b4=v%256
      if cnt==5 then out[#out+1]=sc(b1,b2,b3,b4)
      elseif cnt==4 then out[#out+1]=sc(b1,b2,b3)
      elseif cnt==3 then out[#out+1]=sc(b1,b2)
      elseif cnt==2 then out[#out+1]=sc(b1) end
    end
    i=i+cnt
  end
  return table.concat(out)
end
local function unrot(arr,n,ps)
  for k=1,#ps do
    local l,r=ps[k][1],ps[k][2]
    while l<r do
      arr[l],arr[r]=arr[r],arr[l]
      l=l+1 r=r-1
    end
  end
end
local function lit_e(e,env)
  local ok,v=lit_v(e)
  if ok then return true,v end
  e=unp(e)
  if env and e[1]=="Var" and env[e[2]]~=nil then return true,env[e[2]] end
  return false,nil
end
local function parse_lkp(t,env)
  t=unp(t)
  if t[1]~="Tbl" then return nil end
  local mp,cnt={},0
  for _,f in ipairs(t[2]) do
    local k,v
    if f[1]=="F" then k=f[2] local ok,nv=lit_e(f[3],env) if not ok or type(nv)~="number" then return nil end v=nv
    elseif f[1]=="I" then
      local ok1,kv=lit_e(f[2],env) local ok2,nv=lit_e(f[3],env)
      if not ok1 or not ok2 or type(kv)~="string" or type(nv)~="number" then return nil end
      k,v=kv,nv
    else return nil end
    if #k~=1 then return nil end
    mp[k]=v cnt=cnt+1
  end
  if cnt==64 or cnt==85 then return mp,cnt end
  return nil
end
local function parse_rot(s,an)
  if s[1]=="Do" then
    local bs=s[2][2]
    local ps={}
    local i=1
    local lv,rv
    while i<=#bs-1 do
      local s1,s2=bs[i],bs[i+1]
      local l0,r0
      if s1[1]=="LocalVar" and #s1[2]==2 and #s1[3]==2 then
        local ok1,v1=lit_v(s1[3][1]) local ok2,v2=lit_v(s1[3][2])
        if ok1 and ok2 and type(v1)=="number" and type(v2)=="number" then
          lv,rv=s1[2][1],s1[2][2]
          l0,r0=v1,v2
        end
      elseif s1[1]=="Assign" and #s1[2]==2 and #s1[3]==2 and unp(s1[2][1])[1]=="Var" and unp(s1[2][2])[1]=="Var" and unp(s1[2][1])[2]==lv and unp(s1[2][2])[2]==rv then
        local ok1,v1=lit_v(s1[3][1]) local ok2,v2=lit_v(s1[3][2])
        if ok1 and ok2 and type(v1)=="number" and type(v2)=="number" then l0,r0=v1,v2 end
      end
      if l0 and s2[1]=="While" then
        local wc=unp(s2[2])
        if wc[1]=="Bin" and wc[2]=="<" and unp(wc[3])[1]=="Var" and unp(wc[3])[2]==lv and unp(wc[4])[1]=="Var" and unp(wc[4])[2]==rv then
          local ref=false
          A.walk(s2[3],function(x) if x[1]=="Var" and x[2]==an then ref=true end end)
          if ref then ps[#ps+1]={l0,r0} i=i+2 else return nil end
        else return nil end
      else return nil end
    end
    if #ps>=2 and i>#bs then return ps end
    return nil
  end
  if s[1]~="ForIn" or #s[3]~=1 then return nil end
  local c=unp(s[3][1])
  if c[1]~="Call" or unp(c[2])[1]~="Var" or unp(c[2])[2]~="ipairs" or #c[3]~=1 then return nil end
  local pt=unp(c[3][1])
  if pt[1]~="Tbl" or #pt[2]==0 then return nil end
  local ref=false
  A.walk(s[4],function(x) if x[1]=="Var" and x[2]==an then ref=true end end)
  if not ref then return nil end
  local ps={}
  for i,f in ipairs(pt[2]) do
    if f[1]~="V" then return nil end
    local pr=unp(f[2])
    if pr[1]~="Tbl" or #pr[2]~=2 or pr[2][1][1]~="V" or pr[2][2][1]~="V" then return nil end
    local ok1,l=lit_v(pr[2][1][2])
    local ok2,r=lit_v(pr[2][2][2])
    if not ok1 or not ok2 or type(l)~="number" or type(r)~="number" then return nil end
    ps[i]={l,r}
  end
  return ps
end
local function parse_dec(s,an)
  if s[1]~="Do" then return nil end
  local bs=s[2][2]
  local has_arr=false
  for _,st in ipairs(bs) do
    if st[1]=="LocalVar" then
      for _,v in ipairs(st[3]) do
        if unp(v)[1]=="Var" and unp(v)[2]==an then has_arr=true end
      end
    end
  end
  if not has_arr then return nil end
  local t64,t85,n64,n85
  for _,st in ipairs(bs) do
    if st[1]=="LocalVar" and #st[2]==1 and #st[3]==1 then
      local mp,cnt=parse_lkp(st[3][1])
      if cnt==64 then t64,n64=mp,st[2][1]
      elseif cnt==85 then t85,n85=mp,st[2][1] end
    end
  end
  if not t64 and not t85 then return nil end
  local p64,p85
  A.walk(s,function(x)
    if x[1]=="If" then
      for _,br in ipairs(x[2]) do
        local c=unp(br[1])
        local ch
        if c[1]=="Bin" and c[2]=="==" then
          local l,r=unp(c[3]),unp(c[4])
          if r[1]=="Str" and #r[2]==1 then ch=r[2]
          elseif l[1]=="Str" and #l[2]==1 then ch=l[2] end
        end
        if ch then
          local u64,u85=false,false
          A.walk(br[2],function(y)
            if y[1]=="Num" then
              if y[2]==64 then u64=true elseif y[2]==85 or y[2]==16777216 then u85=true end
            elseif y[1]=="Idx" and unp(y[2])[1]=="Var" then
              local vn=unp(y[2])[2]
              if vn==n64 then u64=true elseif vn==n85 then u85=true end
            end
          end)
          if u64 and not u85 then p64=ch
          elseif u85 and not u64 then p85=ch end
        end
      end
    end
  end)
  return {t64=t64,t85=t85,p64=p64,p85=p85}
end
local function parse_wrap_expr(e,p,an)
  e=unp(e)
  if e[1]~="Idx" then return nil end
  if unp(e[2])[1]~="Var" or unp(e[2])[2]~=an then return nil end
  local k=unp(e[3])
  if k[1]=="Bin" then
    local op,l,r=k[2],unp(k[3]),unp(k[4])
    if op=="-" and l[1]=="Var" and l[2]==p then
      local ok,v=lit_v(r)
      if ok and type(v)=="number" then return function(x) return x-v end,-v end
    elseif op=="+" and l[1]=="Var" and l[2]==p then
      local ok,v=lit_v(r)
      if ok and type(v)=="number" then return function(x) return x+v end,v end
    elseif op=="+" and r[1]=="Var" and r[2]==p then
      local ok,v=lit_v(l)
      if ok and type(v)=="number" then return function(x) return v+x end,v end
    end
  elseif k[1]=="Var" and k[2]==p then
    return function(x) return x end,0
  end
  return nil
end
local function parse_wrap(s,an)
  local nm,ps,va,b
  if s[1]=="LocalFunc" then nm,ps,va,b=s[2],s[3],s[4],s[5]
  elseif s[1]=="LocalVar" and #s[2]==1 and #s[3]==1 and unp(s[3][1])[1]=="Func" then
    local f=unp(s[3][1])
    nm,ps,va,b=s[2][1],f[2],f[3],f[4]
  elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" and unp(s[3][1])[1]=="Func" then
    local f=unp(s[3][1])
    nm,ps,va,b=unp(s[2][1])[2],f[2],f[3],f[4]
  else return nil end
  if #ps<1 or va or #b[2]~=1 or b[2][1][1]~="Return" or #b[2][1][2]~=1 then return nil end
  local fn,off=parse_wrap_expr(b[2][1][2][1],ps[1],an)
  if not fn then return nil end
  return nm,fn,off
end
local function parse_lw_fn(f,wn)
  f=unp(f)
  if f[1]~="Func" or f[3] or #f[2]==0 or #f[4][2]~=1 or f[4][2][1][1]~="Return" or #f[4][2][1][2]~=1 then return nil end
  local ret=unp(f[4][2][1][2][1])
  if ret[1]~="Call" or unp(ret[2])[1]~="Var" or unp(ret[2])[2]~=wn or #ret[3]~=1 then return nil end
  local arg=unp(ret[3][1])
  local pm={}
  for i,p in ipairs(f[2]) do pm[p]=i end
  if arg[1]=="Var" and pm[arg[2]] then
    return pm[arg[2]],0
  elseif arg[1]=="Bin" then
    local op,l,r=arg[2],unp(arg[3]),unp(arg[4])
    if op=="+" then
      if l[1]=="Var" and pm[l[2]] then
        local ok,v=lit_v(r)
        if ok and type(v)=="number" then return pm[l[2]],v end
      elseif r[1]=="Var" and pm[r[2]] then
        local ok,v=lit_v(l)
        if ok and type(v)=="number" then return pm[r[2]],v end
      end
    elseif op=="-" and l[1]=="Var" and pm[l[2]] then
      local ok,v=lit_v(r)
      if ok and type(v)=="number" then return pm[l[2]],-v end
    end
  end
  return nil
end
local function parse_lw_tbl(s,wn)
  local nm
  if s[1]=="LocalVar" and #s[2]==1 and #s[3]==1 then nm=s[2][1]
  elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" then nm=unp(s[2][1])[2]
  else return nil end
  local t=unp(s[3][1])
  if t[1]~="Tbl" or #t[2]==0 then return nil end
  local lws={}
  for _,f in ipairs(t[2]) do
    local k,val
    if f[1]=="F" then k,val=f[2],f[3]
    elseif f[1]=="I" and unp(f[2])[1]=="Str" then k,val=unp(f[2])[2],f[3]
    else return nil end
    local ai,off=parse_lw_fn(val,wn)
    if not ai then return nil end
    lws[k]={ai,off}
  end
  return nm,lws
end
local function sub_blk(b,wn,wfn,arr,an,sk)
  sk=sk or 0
  local lwm={}
  local function sb(blk,ws,lws)
    local ws2=ws
    local lw2={} for k2,v in pairs(lws) do lw2[k2]=v end
    local function se(e)
      local k=e[1]
      if k=="Call" then
        local fn=unp(e[2])
        if not ws2 and fn[1]=="Var" and fn[2]==wn and #e[3]>=1 then
          local ok,v=lit_v(e[3][1])
          if ok and type(v)=="number" then
            local ix=wfn(v)
            if ix>=1 and ix<=an and fl(ix)==ix then return lit_n(arr[ix]) end
          end
        end
        if fn[1]=="Field" or fn[1]=="Idx" then
          local tb=unp(fn[2])
          local key
          if fn[1]=="Field" then key=fn[3]
          elseif unp(fn[3])[1]=="Str" then key=unp(fn[3])[2] end
          if key and tb[1]=="Var" and lw2[tb[2]] and lw2[tb[2]][key] then
            local spec=lw2[tb[2]][key]
            local ai,off=spec[1],spec[2]
            if ai<=#e[3] then
              local ok,v=lit_v(e[3][ai])
              if ok and type(v)=="number" then
                local ix=wfn(v+off)
                if ix>=1 and ix<=an and fl(ix)==ix then return lit_n(arr[ix]) end
              end
            end
          end
        end
        local as={} for i,a in ipairs(e[3]) do as[i]=se(a) end
        return {"Call",se(e[2]),as}
      elseif k=="MCall" then
        local as={} for i,a in ipairs(e[4]) do as[i]=se(a) end
        return {"MCall",se(e[2]),e[3],as}
      elseif k=="Paren" then return {"Paren",se(e[2])}
      elseif k=="Un" then return {"Un",e[2],se(e[3])}
      elseif k=="Bin" then return {"Bin",e[2],se(e[3]),se(e[4])}
      elseif k=="Idx" then return {"Idx",se(e[2]),se(e[3])}
      elseif k=="Field" then return {"Field",se(e[2]),e[3]}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(e[2]) do
          if f[1]=="V" then fs[i]={"V",se(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],se(f[3])}
          else fs[i]={"I",se(f[2]),se(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local cs={} for i,c in ipairs(e[2]) do cs[i]={se(c[1]),se(c[2])} end
        return {"IfExpr",cs,se(e[3])}
      elseif k=="Func" then
        local ws3=ws2
        local lw3={} for k2,v in pairs(lw2) do lw3[k2]=v end
        for _,p in ipairs(e[2]) do
          if p==wn then ws3=true end
          lw3[p]=nil
        end
        return {"Func",e[2],e[3],sb(e[4],ws3,lw3)}
      end
      return e
    end
    local ns={}
    local lw_decl={}
    for _,s in ipairs(blk[2]) do
      local k=s[1]
      if k=="LocalVar" then
        local lnm,lt=nil,nil
        if not ws2 then lnm,lt=parse_lw_tbl(s,wn) end
        if lnm then
          lw2[lnm]=lt
          lw_decl[#ns+1]=lnm
          ns[#ns+1]=s
        else
          local vs={} for i,v in ipairs(s[3]) do vs[i]=se(v) end
          ns[#ns+1]={"LocalVar",s[2],vs}
          local bare=#s[3]==0
          if not bare then
            bare=true
            for _,v in ipairs(s[3]) do if unp(v)[1]~="Nil" then bare=false break end end
          end
          for _,nm in ipairs(s[2]) do
            if nm==wn then
              if bare and sk>0 then sk=sk-1 else ws2=true end
            end
            lw2[nm]=nil
          end
        end
      elseif k=="LocalFunc" then
        if s[2]==wn then ws2=true end
        lw2[s[2]]=nil
        local wf=ws2
        local lf={} for k2,v in pairs(lw2) do lf[k2]=v end
        for _,p in ipairs(s[3]) do if p==wn then wf=true end lf[p]=nil end
        ns[#ns+1]={"LocalFunc",s[2],s[3],s[4],sb(s[5],wf,lf)}
      elseif k=="FuncStmt" then
        local wf=ws2
        local lf={} for k2,v in pairs(lw2) do lf[k2]=v end
        for _,p in ipairs(s[4]) do if p==wn then wf=true end lf[p]=nil end
        if s[3] then if wn=="self" then wf=true end lf.self=nil end
        ns[#ns+1]={"FuncStmt",se(s[2]),s[3],s[4],s[5],sb(s[6],wf,lf)}
      elseif k=="Assign" then
        local lnm,lt=nil,nil
        if not ws2 then lnm,lt=parse_lw_tbl(s,wn) end
        if lnm then
          lw2[lnm]=lt
          lw_decl[#ns+1]=lnm
          ns[#ns+1]=s
        else
          local ls,rs={},{}
          for i,l in ipairs(s[2]) do ls[i]=se(l) end
          for i,r in ipairs(s[3]) do rs[i]=se(r) end
          ns[#ns+1]={"Assign",ls,rs}
        end
      elseif k=="CAssign" then ns[#ns+1]={"CAssign",s[2],se(s[3]),se(s[4])}
      elseif k=="Do" then ns[#ns+1]={"Do",sb(s[2],ws2,lw2)}
      elseif k=="While" then ns[#ns+1]={"While",se(s[2]),sb(s[3],ws2,lw2)}
      elseif k=="Repeat" then
        local nb=sb(s[2],ws2,lw2)
        ns[#ns+1]={"Repeat",nb,se(s[3])}
      elseif k=="If" then
        local cs={} for i,c in ipairs(s[2]) do cs[i]={se(c[1]),sb(c[2],ws2,lw2)} end
        ns[#ns+1]={"If",cs,s[3] and sb(s[3],ws2,lw2) or false}
      elseif k=="ForNum" then
        local wf=ws2 or s[2]==wn
        local lf={} for k2,v in pairs(lw2) do lf[k2]=v end lf[s[2]]=nil
        ns[#ns+1]={"ForNum",s[2],se(s[3]),se(s[4]),s[5] and se(s[5]) or false,sb(s[6],wf,lf)}
      elseif k=="ForIn" then
        local es={} for i,e in ipairs(s[3]) do es[i]=se(e) end
        local wf=ws2
        local lf={} for k2,v in pairs(lw2) do lf[k2]=v end
        for _,v in ipairs(s[2]) do if v==wn then wf=true end lf[v]=nil end
        ns[#ns+1]={"ForIn",s[2],es,sb(s[4],wf,lf)}
      elseif k=="Return" then
        local es={} for i,e in ipairs(s[2]) do es[i]=se(e) end
        ns[#ns+1]={"Return",es}
      elseif k=="CallStmt" then ns[#ns+1]={"CallStmt",se(s[2])}
      else ns[#ns+1]=s end
    end
    local out={}
    for i,s in ipairs(ns) do
      local lnm=lw_decl[i]
      if lnm and not M_misc.has_use(ns,i+1,lnm) then
      else out[#out+1]=s end
    end
    return {"Block",out}
  end
  return sb(b,false,lwm)
end
local function live_use(nm,sts)
  local rd_b_ref
  local function rd_e(n)
    if type(n)~="table" then return false end
    local k=n[1]
    if type(k)~="string" then
      for _,x in ipairs(n) do if rd_e(x) then return true end end
      return false
    end
    if k=="Var" then return n[2]==nm end
    if k=="Func" then
      for _,p in ipairs(n[2]) do if p==nm then return false end end
      return rd_b_ref(n[4][2])==true
    end
    if k=="LocalFunc" then
      if n[2]==nm then return false end
      for _,p in ipairs(n[3]) do if p==nm then return false end end
      return rd_b_ref(n[5][2])==true
    end
    for i=2,#n do if rd_e(n[i]) then return true end end
    return false
  end
  local function rd_lhs(l)
    local u=unp(l)
    if u[1]=="Var" then return false
    elseif u[1]=="Idx" then return rd_e(u[2]) or rd_e(u[3])
    elseif u[1]=="Field" then return rd_e(u[2]) end
    return rd_e(u)
  end
  local function wr_nm(l)
    local u=unp(l)
    return u[1]=="Var" and u[2]==nm
  end
  local function rd_s(s)
    local k=s[1]
    if k=="LocalVar" then
      for _,v in ipairs(s[3]) do if rd_e(v) then return 1 end end
      for _,v in ipairs(s[2]) do if v==nm then return 0 end end
    elseif k=="LocalFunc" then
      if s[2]==nm then return 0 end
      for _,p in ipairs(s[3]) do if p==nm then return 2 end end
      if rd_b_ref(s[5][2]) then return 1 end
    elseif k=="FuncStmt" then
      if rd_e(s[2]) then return 1 end
      local sh=s[3] and nm=="self"
      for _,p in ipairs(s[4]) do if p==nm then sh=true end end
      if not sh and rd_b_ref(s[6][2]) then return 1 end
    elseif k=="Assign" then
      for _,r in ipairs(s[3]) do if rd_e(r) then return 1 end end
      for _,l in ipairs(s[2]) do if rd_lhs(l) then return 1 end end
      for _,l in ipairs(s[2]) do if wr_nm(l) then return 0 end end
    elseif k=="CAssign" then
      if rd_e(s[3]) or rd_e(s[4]) then return 1 end
    elseif k=="Do" then
      local r=rd_b_ref(s[2][2])
      if r~=nil then return r and 1 or 0 end
    elseif k=="While" then
      if rd_e(s[2]) or rd_b_ref(s[3][2]) then return 1 end
    elseif k=="Repeat" then
      local sh=false
      for _,st in ipairs(s[2][2]) do
        if st[1]=="LocalVar" then for _,v in ipairs(st[2]) do if v==nm then sh=true end end
        elseif st[1]=="LocalFunc" and st[2]==nm then sh=true end
      end
      if rd_b_ref(s[2][2]) or (not sh and rd_e(s[3])) then return 1 end
    elseif k=="If" then
      for _,br in ipairs(s[2]) do if rd_e(br[1]) or rd_b_ref(br[2][2]) then return 1 end end
      if s[3] and rd_b_ref(s[3][2]) then return 1 end
    elseif k=="ForNum" then
      if rd_e(s[3]) or rd_e(s[4]) or (s[5] and rd_e(s[5])) then return 1 end
      if s[2]~=nm and rd_b_ref(s[6][2]) then return 1 end
    elseif k=="ForIn" then
      for _,e in ipairs(s[3]) do if rd_e(e) then return 1 end end
      local sh=false for _,v in ipairs(s[2]) do if v==nm then sh=true end end
      if not sh and rd_b_ref(s[4][2]) then return 1 end
    elseif k=="Return" then
      for _,e in ipairs(s[2]) do if rd_e(e) then return 1 end end
    elseif k=="CallStmt" then
      if rd_e(s[2]) then return 1 end
    end
    return 2
  end
  rd_b_ref=function(bs)
    for _,s in ipairs(bs) do
      local r=rd_s(s)
      if r==1 then return true elseif r==0 then return false end
    end
    return nil
  end
  return rd_b_ref(sts)==true
end
local CA_HLP={string={len=1,sub=1,char=1},math={floor=1},table={insert=1,concat=1}}
local function is_ca_hlp(r)
  r=unp(r)
  if parse_lkp(r) then return true end
  if r[1]=="Var" and r[2]=="type" then return true end
  if (r[1]=="Field" or r[1]=="Idx") and unp(r[2])[1]=="Var" then
    local b=unp(r[2])[2]
    local k=r[1]=="Field" and r[3] or (unp(r[3])[1]=="Str" and unp(r[3])[2] or nil)
    if k and CA_HLP[b] and CA_HLP[b][k] then return true end
  end
  return false
end
local function ext_pairs(e)
  e=unp(e)
  if e[1]~="Tbl" or #e[2]==0 then return nil end
  local ps={}
  for i,f in ipairs(e[2]) do
    if f[1]~="V" then return nil end
    local pr=unp(f[2])
    if pr[1]~="Tbl" or #pr[2]~=2 or pr[2][1][1]~="V" or pr[2][2][1]~="V" then return nil end
    local ok1,l=lit_v(pr[2][1][2])
    local ok2,r=lit_v(pr[2][2][2])
    if not ok1 or not ok2 or type(l)~="number" or type(r)~="number" then return nil end
    ps[i]={l,r}
  end
  return ps
end
local function ext_mpf(blk,v64,v85)
  local p64,p85
  local cs={}
  local cv={}
  local function h64(n)
    local hit=false
    A.walk(n,function(y)
      if v64 and y[1]=="Var" and y[2]==v64 then hit=true
      elseif y[1]=="Num" and (y[2]==64 or y[2]==65536) then hit=true end
    end)
    return hit
  end
  local function h85(n)
    local hit=false
    A.walk(n,function(y)
      if v85 and y[1]=="Var" and y[2]==v85 then hit=true
      elseif y[1]=="Num" and (y[2]==84 or y[2]==85 or y[2]==16777216) then hit=true end
    end)
    return hit
  end
  local function eq1(c)
    c=unp(c)
    if c[1]=="Bin" and c[2]=="==" then
      local l,r=unp(c[3]),unp(c[4])
      if r[1]=="Str" and #r[2]==1 then return r[2]
      elseif l[1]=="Str" and #l[2]==1 then return l[2] end
    end
    return nil
  end
  A.walk(blk,function(x)
    if x[1]=="LocalVar" or x[1]=="Assign" then
      for i=1,math.min(#x[2],#x[3]) do
        local nm=type(x[2][i])=="string" and x[2][i] or (unp(x[2][i])[1]=="Var" and unp(x[2][i])[2] or nil)
        if nm then
          local ch=eq1(x[3][i])
          cv[nm]=ch
        end
      end
    elseif x[1]=="If" then
      for _,br in ipairs(x[2]) do
        local c=unp(br[1])
        local ch=eq1(c) or (c[1]=="Var" and cv[c[2]] or nil)
        if ch then
          cs[#cs+1]=ch
          local u6,u8=h64(br[2]),h85(br[2])
          if u6 and not u8 then p64=ch
          elseif u8 and not u6 then p85=ch end
        end
      end
    end
  end)
  if not p64 and not p85 and #cs>=2 then p64,p85=cs[1],cs[2] end
  return p64,p85
end
local function u_for(e)
  e=unp(e)
  if e[1]=="Bin" and e[2]=="or" then
    local l=unp(e[3])
    if l[1]=="Call" and unp(l[2])[1]=="Var" and unp(l[2])[2]=="tonumber" and #l[3]==1 then return unp(l[3][1]) end
  elseif e[1]=="Call" and unp(e[2])[1]=="Var" and unp(e[2])[2]=="tonumber" and #e[3]==1 then
    return unp(e[3][1])
  end
  return e
end
local function dec_raw(raw,ps,t64,t85,p64,p85)
  local n=#raw
  local ur={} for i=1,n do ur[i]=raw[i] end
  if ps and #ps>0 then unrot(ur,n,ps) end
  if t64 and t85 then
    local pm={}
    if p64 and p85 and p64~=p85 then
      pm[p64]="B64" pm[p85]="B85"
    else
      local byp={}
      for i=1,n do
        if type(ur[i])=="string" and #ur[i]>=1 then
          local p=ur[i]:sub(1,1)
          byp[p]=byp[p] or {}
          byp[p][#byp[p]+1]=ur[i]:sub(2)
        end
      end
      for p,subs in pairs(byp) do
        local is64=true
        for _,s in ipairs(subs) do
          if #s%4~=0 then is64=false break end
          for k=1,#s do
            local ch=s:sub(k,k)
            if not t64[ch] and ch~="=" then is64=false break end
          end
          if not is64 then break end
        end
        pm[p]=is64 and "B64" or "B85"
      end
    end
    for i=1,n do
      if type(ur[i])=="string" and #ur[i]>=1 then
        if pm[ur[i]:sub(1,1)]=="B64" then ur[i]=b64(ur[i]:sub(2),t64)
        else ur[i]=b85(ur[i]:sub(2),t85) end
      end
    end
  elseif t64 then
    for i=1,n do if type(ur[i])=="string" then ur[i]=b64(ur[i],t64) end end
  elseif t85 then
    for i=1,n do if type(ur[i])=="string" then ur[i]=b85(ur[i],t85) end end
  end
  return ur
end
local function vars_f(n)
  local vs={}
  A.walk(n,function(x) if x[1]=="Var" then vs[x[2]]=true end end)
  return vs
end
local function bare_lv(s)
  if s[1]~="LocalVar" then return false end
  if #s[3]==0 then return true end
  for _,v in ipairs(s[3]) do if unp(v)[1]~="Nil" then return false end end
  return true
end
local function has_use_nb(sts,nm)
  local sub={}
  for _,s in ipairs(sts) do if not bare_lv(s) then sub[#sub+1]=s end end
  return M_misc.has_use(sub,1,nm)
end
local function clean_bare(sts,rm)
  local out={}
  local function cb(s)
    local k=s[1]
    if k=="Block" then return {"Block",clean_bare(s[2],rm)}
    elseif k=="LocalFunc" then return {"LocalFunc",s[2],s[3],s[4],cb(s[5])}
    elseif k=="FuncStmt" then return {"FuncStmt",s[2],s[3],s[4],s[5],cb(s[6])}
    elseif k=="Do" then return {"Do",cb(s[2])}
    elseif k=="While" then return {"While",s[2],cb(s[3])}
    elseif k=="Repeat" then return {"Repeat",cb(s[2]),s[3]}
    elseif k=="If" then
      local cs={} for i,c in ipairs(s[2]) do cs[i]={c[1],cb(c[2])} end
      return {"If",cs,s[3] and cb(s[3]) or false}
    elseif k=="ForNum" then return {"ForNum",s[2],s[3],s[4],s[5],cb(s[6])}
    elseif k=="ForIn" then return {"ForIn",s[2],s[3],cb(s[4])} end
    return s
  end
  local csts={} for i,s in ipairs(sts) do csts[i]=cb(s) end
  for i,s in ipairs(csts) do
    if s[1]=="LocalVar" and (#s[3]==0 or (#s[2]==1 and #s[3]==1 and unp(s[3][1])[1]=="Nil")) then
      local kl={}
      for _,nm in ipairs(s[2]) do
        if not rm[nm] or M_misc.has_use(csts,i+1,nm) then kl[#kl+1]=nm end
      end
      if #kl>0 then out[#out+1]={"LocalVar",kl,#s[3]==0 and {} or s[3]} end
    else
      out[#out+1]=s
    end
  end
  return out
end
local function lhs1(s)
  if s[1]=="LocalVar" and #s[2]==1 and #s[3]==1 then return s[2][1],unp(s[3][1])
  elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" then
    return unp(s[2][1])[2],unp(s[3][1])
  end
  return nil
end
local function find_cff_ca(sts)
  local n=#sts
  local arrs,wraps={},{}
  local envs={}
  local cur_e={}
  local function clr_w(nd)
    A.walk(nd,function(x)
      if x[1]=="Assign" then
        for _,l in ipairs(x[2]) do if unp(l)[1]=="Var" then cur_e[unp(l)[2]]=nil end end
      elseif x[1]=="LocalVar" then
        for _,nm in ipairs(x[2]) do cur_e[nm]=nil end
      elseif x[1]=="ForNum" then cur_e[x[2]]=nil
      elseif x[1]=="ForIn" then for _,nm in ipairs(x[2]) do cur_e[nm]=nil end end
    end)
  end
  for i=1,n do
    local s=sts[i]
    local snap={} for k,v in pairs(cur_e) do snap[k]=v end
    envs[i]=snap
    local an,tb=lhs1(s)
    if an and tb[1]=="Tbl" and #tb[2]>0 then
      local ok=true
      local raw={}
      for j,f in ipairs(tb[2]) do
        if f[1]~="V" then ok=false break end
        local ov,vv=lit_e(f[2],snap)
        if not ov then ok=false break end
        raw[j]=vv
      end
      if ok then arrs[an]={i,raw} end
    end
    local wn,wfn,off=parse_wrap(s,nil)
    local fn_a
    if not wn then
      local fn
      if s[1]=="LocalFunc" then wn,fn=s[2],{"Func",s[3],s[4],s[5]}
      else local ln,rh=lhs1(s) if ln and rh[1]=="Func" then wn,fn=ln,rh end end
      if wn and fn and not fn[3] and #fn[2]>=1 and #fn[4][2]==1 and fn[4][2][1][1]=="Return" and #fn[4][2][1][2]==1 then
        local rt=unp(fn[4][2][1][2][1])
        if rt[1]=="Idx" and unp(rt[2])[1]=="Var" then
          local ca_n=unp(rt[2])[2]
          local wf=parse_wrap_expr(rt,fn[2][1],ca_n)
          if wf then fn_a=ca_n wfn=wf end
        end
      end
    end
    if wn and wfn and fn_a then wraps[#wraps+1]={i,wn,fn_a,wfn} end
    if s[1]=="LocalVar" or s[1]=="Assign" then
      for j,lhs in ipairs(s[2]) do
        local nm=s[1]=="LocalVar" and lhs or (unp(lhs)[1]=="Var" and unp(lhs)[2] or nil)
        if nm then
          local rh=s[3][j]
          local ok,v
          if rh then ok,v=lit_e(rh,snap) end
          if ok then cur_e[nm]=v else cur_e[nm]=nil end
        end
      end
    elseif s[1]=="LocalFunc" then
      cur_e[s[2]]=nil
    else
      clr_w(s)
    end
  end
  for _,w in ipairs(wraps) do
    local idx_w,wn,an,wfn=w[1],w[2],w[3],w[4]
    local ai=arrs[an]
    if ai then
      local idx_a,raw=ai[1],ai[2]
      local rm_i={[idx_a]=true,[idx_w]=true}
      local rm_v={[an]=true,[wn]=true}
      local ps
      for k=1,n do
        if not rm_i[k] then
          local rp=parse_rot(sts[k],an)
          if rp then ps=rp rm_i[k]=true break end
        end
      end
      if not ps then
        for k=1,n do
          if not rm_i[k] then
            local kv,rhs=lhs1(sts[k])
            if kv and rhs[1]=="Tbl" and #rhs[2]==1 and rhs[2][1][1]=="V" then
              local ca=unp(rhs[2][1][2])
              if ca[1]=="Call" and unp(ca[2])[1]=="Var" and unp(ca[2])[2]=="ipairs" and #ca[3]==1 then
                local parg=ca[3][1]
                local pv_i,pv_n
                local cps=ext_pairs(parg)
                if not cps and unp(parg)[1]=="Var" then
                  pv_n=unp(parg)[2]
                  for d=k-1,1,-1 do
                    local ln,rh=lhs1(sts[d])
                    if ln==pv_n then cps=ext_pairs(rh) pv_i=d break end
                  end
                end
                if cps then
                  local w_i
                  for j=k+1,math.min(n,k+10) do
                    local sj=sts[j]
                    if sj[1]=="While" and unp(sj[2])[1]=="Bool" and unp(sj[2])[2]==true and M_misc.has_use({sj},1,an) then
                      w_i=j break
                    end
                  end
                  if w_i then
                    local mvars={[kv]=true}
                    local kv_sub={}
                    local rm_m={[k]=true,[w_i]=true}
                    local mok=true
                    for m=k+1,w_i-1 do
                      local sm=sts[m]
                      local ln,rh=lhs1(sm)
                      if ln and rh[1]=="Idx" and unp(rh[2])[1]=="Var" and unp(rh[2])[2]==kv then
                        mvars[ln]=true kv_sub[ln]=true rm_m[m]=true
                      elseif bare_lv(sm) then
                      else mok=false break end
                    end
                    local uses_sub=false
                    for v,_ in pairs(kv_sub) do
                      if M_misc.has_use({sts[w_i]},1,v) then uses_sub=true break end
                    end
                    if mok and (uses_sub or M_misc.has_use({sts[w_i]},1,kv)) then
                      local tail={} for m=w_i+1,n do tail[#tail+1]=sts[m] end
                      local ok_live=true
                      for v,_ in pairs(mvars) do if live_use(v,tail) then ok_live=false break end end
                      if ok_live and pv_n and live_use(pv_n,tail) then ok_live=false end
                      if ok_live then
                        ps=cps
                        for m,_ in pairs(rm_m) do rm_i[m]=true end
                        for v,_ in pairs(mvars) do rm_v[v]=true end
                        if pv_i then rm_i[pv_i]=true rm_v[pv_n]=true end
                        break
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
      local t64,t85,p64,p85
      for k=1,n do
        if not rm_i[k] and sts[k][1]=="Do" and M_misc.has_use({sts[k]},1,an) then
          local dc=parse_dec(sts[k],an)
          if dc then t64,t85,p64,p85=dc.t64,dc.t85,dc.p64,dc.p85 rm_i[k]=true break end
        end
      end
      if not t64 and not t85 then
        for k=1,n do
          local sk=sts[k]
          local is_fn=(not rm_i[k] and sk[1]=="ForNum")
          local is_wh=(not rm_i[k] and sk[1]=="While" and unp(sk[2])[1]=="Bool" and unp(sk[2])[2]==true)
          if is_fn or is_wh then
            local arr_v
            local di={[k]=true}
            local dv={}
            local lp_b
            if is_fn then
              local sv0,svv=lit_v(u_for(sk[3]))
              local eb=u_for(sk[4])
              lp_b=sk[6]
              if sv0 and svv==1 then
                if eb[1]=="Un" and eb[2]=="#" and unp(eb[3])[1]=="Var" then
                  arr_v=unp(eb[3])[2]
                elseif eb[1]=="Var" then
                  for d=k-1,1,-1 do
                    if not rm_i[d] then
                      local ln,rh=lhs1(sts[d])
                      if ln==eb[2] then
                        if rh[1]=="Un" and rh[2]=="#" and unp(rh[3])[1]=="Var" then
                          arr_v=unp(rh[3])[2]
                          local tail={} for m=d+1,n do if not rm_i[m] and not di[m] then tail[#tail+1]=sts[m] end end
                          if not live_use(ln,tail) then di[d]=true dv[ln]=true end
                        end
                        break
                      end
                    end
                  end
                end
              end
            else
              lp_b=sk[3]
              local has_str,has_m=false,false
              A.walk(sk[3],function(x)
                if x[1]=="Str" and x[2]=="string" then has_str=true
                elseif x[1]=="Num" and (x[2]==64 or x[2]==85 or x[2]==65536 or x[2]==16777216) then has_m=true end
              end)
              if has_str and has_m then
                for d=k-1,math.max(1,k-8),-1 do
                  if not rm_i[d] then
                    local ln,rh=lhs1(sts[d])
                    if ln and rh[1]=="Un" and rh[2]=="#" and unp(rh[3])[1]=="Var" then
                      arr_v=unp(rh[3])[2]
                      local tail={} for m=d+1,n do if not rm_i[m] and not di[m] then tail[#tail+1]=sts[m] end end
                      if not live_use(ln,tail) then di[d]=true dv[ln]=true end
                      break
                    end
                  end
                end
              end
            end
            if arr_v then
              local has_a=(arr_v==an)
              local t64k,t85k,v64,v85
              A.walk(sk,function(x)
                local mp,cnt=parse_lkp(x,envs[k])
                if cnt==64 then t64k=mp elseif cnt==85 then t85k=mp end
              end)
              local need=vars_f(sk)
              for d=k-1,1,-1 do
                if not rm_i[d] then
                  local ln,rh=lhs1(sts[d])
                  if ln and need[ln] then
                    local mp,cnt=parse_lkp(rh,envs[d])
                    local ia=(rh[1]=="Var" and rh[2]==an)
                    local is_hlp=is_ca_hlp(rh) or (rh[1]=="Var" and need[rh[2]])
                    if mp or ia or is_hlp then
                      local tail={} for m=d+1,n do if not rm_i[m] and not di[m] then tail[#tail+1]=sts[m] end end
                      if not live_use(ln,tail) then
                        di[d]=true dv[ln]=true
                        for u,_ in pairs(vars_f(rh)) do need[u]=true end
                        if ia then has_a=true end
                        if cnt==64 then t64k,v64=mp,ln elseif cnt==85 then t85k,v85=mp,ln end
                      end
                    end
                  end
                end
              end
              if has_a and (t64k or t85k) then
                t64,t85=t64k,t85k
                p64,p85=ext_mpf(lp_b,v64,v85)
                for d,_ in pairs(di) do rm_i[d]=true end
                for v,_ in pairs(dv) do rm_v[v]=true end
                break
              end
            end
          end
        end
      end
      local rem={} for m=1,n do if not rm_i[m] then rem[#rem+1]=sts[m] end end
      if not has_use_nb(rem,an) then
        local skc=0
        for m=1,idx_w-1 do
          if not rm_i[m] and bare_lv(sts[m]) then
            for _,v in ipairs(sts[m][2]) do if v==wn then skc=skc+1 end end
          end
        end
        local dec=dec_raw(raw,ps,t64,t85,p64,p85)
        return rem,wn,wfn,dec,rm_v,skc
      end
    end
  end
  return nil
end
local function parse_hdr(sts,i)
  local s=sts[i]
  if s[1]~="LocalVar" or #s[2]~=1 or #s[3]~=1 or unp(s[3][1])[1]~="Tbl" then return nil end
  local t=unp(s[3][1])
  local an=s[2][1]
  local arr={}
  if #t[2]==0 then return nil end
  for k,f in ipairs(t[2]) do
    if f[1]~="V" then return nil end
    local okv,vv=lit_v(f[2])
    if not okv then return nil end
    arr[k]=vv
  end
  local rot_ps,dec_cfg,wn,wfn
  local j=i+1
  while j<=#sts and j<=i+5 do
    local st=sts[j]
    local rp=parse_rot(st,an)
    if rp and not rot_ps then rot_ps=rp j=j+1
    else
      local dc=parse_dec(st,an)
      if dc and not dec_cfg then dec_cfg=dc j=j+1
      else
        local w1,wf1=parse_wrap(st,an)
        if w1 and not wn then wn,wfn=w1,wf1 j=j+1
        else break end
      end
    end
  end
  if not (wn and wfn) then return nil end
  return {i0=i,i1=j,an=an,arr=arr,n=#t[2],rot=rot_ps,dec=dec_cfg,wn=wn,wfn=wfn}
end
local function proc_ca_blk(b)
  local sts=b[2]
  local i=1
  while i<=#sts do
    local ok_hdr=false
    local h=parse_hdr(sts,i)
    if h then
      local arr,n,an,wn,wfn=h.arr,h.n,h.an,h.wn,h.wfn
      if h.rot then unrot(arr,n,h.rot) end
      local dec_cfg=h.dec
      if dec_cfg then
        for k=1,n do
          if type(arr[k])=="string" then
            local sv=arr[k]
            if dec_cfg.t64 and dec_cfg.t85 then
              local p=sv:sub(1,1)
              if p==dec_cfg.p64 then arr[k]=b64(sv:sub(2),dec_cfg.t64)
              elseif p==dec_cfg.p85 then arr[k]=b85(sv:sub(2),dec_cfg.t85) end
            elseif dec_cfg.t64 then
              arr[k]=b64(sv,dec_cfg.t64)
            elseif dec_cfg.t85 then
              if dec_cfg.p85 and sv:sub(1,1)==dec_cfg.p85 then arr[k]=b85(sv:sub(2),dec_cfg.t85)
              else arr[k]=b85(sv,dec_cfg.t85) end
            end
          end
        end
      end
      local tail={}
      for k=h.i1,#sts do tail[#tail+1]=sts[k] end
      local sub_t=sub_blk({"Block",tail},wn,wfn,arr,n)[2]
      local used=M_misc.has_use(sub_t,1,wn) or M_misc.has_use(sub_t,1,an)
      if not used then
        local new_sts={}
        for k=1,i-1 do new_sts[#new_sts+1]=sts[k] end
        for _,st in ipairs(sub_t) do new_sts[#new_sts+1]=st end
        sts=new_sts
        ok_hdr=true
      end
    end
    if not ok_hdr then i=i+1 end
  end
  while true do
    local rem,wn,wfn,dec,rmv,sk=find_cff_ca(sts)
    if not rem then break end
    local sub_r=sub_blk({"Block",rem},wn,wfn,dec,#dec,sk)[2]
    local o2=clean_bare(sub_r,rmv)
    if not has_use_nb(o2,wn) then
      sts=o2
    else
      break
    end
  end
  return {"Block",sts}
end
function M.inv_ca(ast)
  local function walk_b(b)
    local function we(e)
      local k=e[1]
      if k=="Func" then return {"Func",e[2],e[3],walk_b(e[4])}
      elseif k=="Paren" then return {"Paren",we(e[2])}
      elseif k=="Un" then return {"Un",e[2],we(e[3])}
      elseif k=="Bin" then return {"Bin",e[2],we(e[3]),we(e[4])}
      elseif k=="Idx" then return {"Idx",we(e[2]),we(e[3])}
      elseif k=="Field" then return {"Field",we(e[2]),e[3]}
      elseif k=="Call" then
        local as={} for i,a in ipairs(e[3]) do as[i]=we(a) end
        return {"Call",we(e[2]),as}
      elseif k=="MCall" then
        local as={} for i,a in ipairs(e[4]) do as[i]=we(a) end
        return {"MCall",we(e[2]),e[3],as}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(e[2]) do
          if f[1]=="V" then fs[i]={"V",we(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],we(f[3])}
          else fs[i]={"I",we(f[2]),we(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local cs={} for i,c in ipairs(e[2]) do cs[i]={we(c[1]),we(c[2])} end
        return {"IfExpr",cs,we(e[3])}
      end
      return e
    end
    local ns={}
    for idx,s in ipairs(b[2]) do
      local k=s[1]
      if k=="LocalFunc" then ns[idx]={"LocalFunc",s[2],s[3],s[4],walk_b(s[5])}
      elseif k=="FuncStmt" then ns[idx]={"FuncStmt",we(s[2]),s[3],s[4],s[5],walk_b(s[6])}
      elseif k=="Do" then ns[idx]={"Do",walk_b(s[2])}
      elseif k=="While" then ns[idx]={"While",we(s[2]),walk_b(s[3])}
      elseif k=="Repeat" then ns[idx]={"Repeat",walk_b(s[2]),we(s[3])}
      elseif k=="If" then
        local cs={} for j,c in ipairs(s[2]) do cs[j]={we(c[1]),walk_b(c[2])} end
        ns[idx]={"If",cs,s[3] and walk_b(s[3]) or false}
      elseif k=="ForNum" then ns[idx]={"ForNum",s[2],we(s[3]),we(s[4]),s[5] and we(s[5]) or false,walk_b(s[6])}
      elseif k=="ForIn" then
        local es={} for j,e in ipairs(s[3]) do es[j]=we(e) end
        ns[idx]={"ForIn",s[2],es,walk_b(s[4])}
      elseif k=="LocalVar" then
        local vs={} for j,v in ipairs(s[3]) do vs[j]=we(v) end
        ns[idx]={"LocalVar",s[2],vs}
      elseif k=="Assign" then
        local ls,rs={},{}
        for j,l in ipairs(s[2]) do ls[j]=we(l) end
        for j,r in ipairs(s[3]) do rs[j]=we(r) end
        ns[idx]={"Assign",ls,rs}
      elseif k=="Return" then
        local es={} for j,e in ipairs(s[2]) do es[j]=we(e) end
        ns[idx]={"Return",es}
      elseif k=="CallStmt" then ns[idx]={"CallStmt",we(s[2])}
      else ns[idx]=s end
    end
    return proc_ca_blk({"Block",ns})
  end
  return walk_b(ast)
end
function M.find_hdr(sts)
  for i=1,#sts do
    local h=parse_hdr(sts,i)
    if h then return h end
  end
  return nil
end
M.b64=b64
M.b85=b85
M.unrot=unrot
return M
