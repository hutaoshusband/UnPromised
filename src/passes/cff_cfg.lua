local A=require("src.frontend.ast")
local G=require("src.ir.cfg")
local C=require("src.passes.cff")
local F=require("src.frontend.fold")
local M_misc=require("src.passes.misc")
local M={}
local unp,eq,cp=A.unp,A.eq,A.cp
local function neg_c(c)
  c=unp(c)
  if c[1]=="Un" and c[2]=="not" then return c[3] end
  if c[1]=="Bin" then
    local op=c[2]
    if op=="==" then return {"Bin","~=",c[3],c[4]}
    elseif op=="~=" then return {"Bin","==",c[3],c[4]}
    elseif op=="<" then return {"Bin",">=",c[3],c[4]}
    elseif op=="<=" then return {"Bin",">",c[3],c[4]}
    elseif op==">" then return {"Bin","<=",c[3],c[4]}
    elseif op==">=" then return {"Bin","<",c[3],c[4]} end
  end
  return {"Un","not",c}
end
local sub_s,sub_b
local function sub_e(e,mp)
  local k=e[1]
  if k=="Var" and mp[e[2]]~=nil then return cp(mp[e[2]])
  elseif k=="Paren" then return {"Paren",sub_e(e[2],mp)}
  elseif k=="Un" then return {"Un",e[2],sub_e(e[3],mp)}
  elseif k=="Bin" then return {"Bin",e[2],sub_e(e[3],mp),sub_e(e[4],mp)}
  elseif k=="Idx" then return {"Idx",sub_e(e[2],mp),sub_e(e[3],mp)}
  elseif k=="Field" then return {"Field",sub_e(e[2],mp),e[3]}
  elseif k=="Call" then
    local as={} for i,a in ipairs(e[3]) do as[i]=sub_e(a,mp) end
    return {"Call",sub_e(e[2],mp),as}
  elseif k=="MCall" then
    local as={} for i,a in ipairs(e[4]) do as[i]=sub_e(a,mp) end
    return {"MCall",sub_e(e[2],mp),e[3],as}
  elseif k=="Tbl" then
    local fs={}
    for i,f in ipairs(e[2]) do
      if f[1]=="V" then fs[i]={"V",sub_e(f[2],mp)}
      elseif f[1]=="F" then fs[i]={"F",f[2],sub_e(f[3],mp)}
      else fs[i]={"I",sub_e(f[2],mp),sub_e(f[3],mp)} end
    end
    return {"Tbl",fs}
  elseif k=="IfExpr" then
    local cs={} for i,c in ipairs(e[2]) do cs[i]={sub_e(c[1],mp),sub_e(c[2],mp)} end
    return {"IfExpr",cs,sub_e(e[3],mp)}
  elseif k=="Func" then
    local m2={} for k2,v in pairs(mp) do m2[k2]=v end
    for _,p in ipairs(e[2]) do m2[p]=nil end
    if not next(m2) then return e end
    return {"Func",e[2],e[3],sub_b(e[4],m2)}
  end
  return e
end
sub_b=function(blk,mp)
  local m2={} for k,v in pairs(mp) do m2[k]=v end
  local ns={}
  for i,s in ipairs(blk[2]) do
    if not next(m2) then
      for j=i,#blk[2] do ns[#ns+1]=blk[2][j] end
      break
    end
    local k=s[1]
    if k=="LocalVar" then
      local vs={} for j,v in ipairs(s[3]) do vs[j]=sub_e(v,m2) end
      ns[#ns+1]={"LocalVar",s[2],vs}
      for _,nm in ipairs(s[2]) do m2[nm]=nil end
    elseif k=="LocalFunc" then
      m2[s[2]]=nil
      local m3={} for k2,v in pairs(m2) do m3[k2]=v end
      for _,p in ipairs(s[3]) do m3[p]=nil end
      ns[#ns+1]={"LocalFunc",s[2],s[3],s[4],next(m3) and sub_b(s[5],m3) or s[5]}
    elseif k=="FuncStmt" then
      local m3={} for k2,v in pairs(m2) do m3[k2]=v end
      for _,p in ipairs(s[4]) do m3[p]=nil end
      if s[3] then m3.self=nil end
      ns[#ns+1]={"FuncStmt",sub_e(s[2],m2),s[3],s[4],s[5],next(m3) and sub_b(s[6],m3) or s[6]}
    else
      ns[#ns+1]=sub_s(s,m2)
    end
  end
  return {"Block",ns}
end
sub_s=function(s,mp)
  local k=s[1]
  if k=="Assign" then
    local ls,rs={},{}
    for i,l in ipairs(s[2]) do
      if l[1]=="Var" then ls[i]=l else ls[i]=sub_e(l,mp) end
    end
    for i,r in ipairs(s[3]) do rs[i]=sub_e(r,mp) end
    return {"Assign",ls,rs}
  elseif k=="LocalVar" then
    local vs={} for i,v in ipairs(s[3]) do vs[i]=sub_e(v,mp) end
    return {"LocalVar",s[2],vs}
  elseif k=="CAssign" then
    local l=s[3][1]=="Var" and s[3] or sub_e(s[3],mp)
    return {"CAssign",s[2],l,sub_e(s[4],mp)}
  elseif k=="CallStmt" then return {"CallStmt",sub_e(s[2],mp)}
  elseif k=="Return" then
    local es={} for i,e in ipairs(s[2]) do es[i]=sub_e(e,mp) end
    return {"Return",es}
  elseif k=="If" then
    local cs={} for i,c in ipairs(s[2]) do cs[i]={sub_e(c[1],mp),sub_b(s[2][i][2],mp)} end
    return {"If",cs,s[3] and sub_b(s[3],mp) or false}
  elseif k=="While" then return {"While",sub_e(s[2],mp),sub_b(s[3],mp)}
  elseif k=="Repeat" then return {"Repeat",sub_b(s[2],mp),sub_e(s[3],mp)}
  elseif k=="Do" then return {"Do",sub_b(s[2],mp)}
  elseif k=="ForNum" then
    local m3={} for k2,v in pairs(mp) do m3[k2]=v end m3[s[2]]=nil
    return {"ForNum",s[2],sub_e(s[3],mp),sub_e(s[4],mp),s[5] and sub_e(s[5],mp) or false,sub_b(s[6],m3)}
  elseif k=="ForIn" then
    local es={} for i,e in ipairs(s[3]) do es[i]=sub_e(e,mp) end
    local m3={} for k2,v in pairs(mp) do m3[k2]=v end for _,v in ipairs(s[2]) do m3[v]=nil end
    return {"ForIn",s[2],es,sub_b(s[4],m3)}
  end
  return s
end
local function is_pack_fn(f)
  if not f[3] or #f[2]~=0 or #f[4][2]~=1 then return false end
  local r=f[4][2][1]
  if r[1]~="Return" or #r[2]~=1 then return false end
  local t=unp(r[2][1])
  if t[1]~="Tbl" then return false end
  for _,fld in ipairs(t[2]) do
    if fld[1]=="I" and unp(fld[2])[1]=="Str" and unp(fld[2])[2]=="n" then return true end
    if fld[1]=="F" and fld[2]=="n" then return true end
  end
  return false
end
local function is_unpack_expr(u,env)
  u=unp(u)
  if u[1]=="Var" and u[2]=="unpack" then return true end
  if u[1]=="Field" and u[3]=="unpack" then return true end
  if u[1]=="Bin" and u[2]=="or" and is_unpack_expr(u[3],env) then return true end
  if u[1]=="Var" and env and env[u[2]] then return is_unpack_expr(env[u[2]],nil) end
  return false
end
local function is_unpack_fn(f,env)
  if f[3] or #f[2]~=1 or #f[4][2]~=1 then return false end
  local r=f[4][2][1]
  if r[1]~="Return" or #r[2]~=1 then return false end
  local c=unp(r[2][1])
  if c[1]=="Call" and #c[3]==3 then
    if is_unpack_expr(c[2],env) then return true end
  end
  return false
end
local function is_alloc_fn(f)
  if f[3] or #f[2]~=0 or #f[4][2]~=3 then return nil end
  local s1,s2,s3=f[4][2][1],f[4][2][2],f[4][2][3]
  if s1[1]=="Assign" and #s1[2]==1 and s1[2][1][1]=="Var" and s2[1]=="Assign" and #s2[2]==1 and s2[2][1][1]=="Idx" and s3[1]=="Return" and #s3[2]==1 and s3[2][1][1]=="Var" and s3[2][1][2]==s1[2][1][2] then
    return s1[2][1][2],unp(s2[2][1][2])[2]
  end
  return nil
end
local function is_gc_one(f,ref_n)
  if not ref_n or f[3] or #f[2]~=1 or #f[4][2]~=2 then return nil end
  local s1,s2=f[4][2][1],f[4][2][2]
  if s1[1]=="Assign" and s2[1]=="If" and #s2[2]==1 and #s2[2][1][2][2]==1 then
    local as=s2[2][1][2][2][1]
    if as[1]=="Assign" and #as[2]==2 and as[2][1][1]=="Idx" and as[2][2][1]=="Idx" then
      local t1,t2=unp(as[2][1][2]),unp(as[2][2][2])
      if t1[1]=="Var" and t2[1]=="Var" then
        if t1[2]==ref_n then return t2[2] elseif t2[2]==ref_n then return t1[2] end
      end
    end
  end
  return nil
end
local function is_gc_batch(f,ref_n)
  if not ref_n or f[3] or #f[2]~=1 or #f[4][2]~=2 then return nil end
  local s2=f[4][2][2]
  if s2[1]=="While" then
    local ctbl
    A.walk(s2[3],function(x)
      if x[1]=="If" and #x[2]==1 and #x[2][1][2][2]==1 then
        local as=x[2][1][2][2][1]
        if as[1]=="Assign" and #as[2]==2 and as[2][1][1]=="Idx" and as[2][2][1]=="Idx" then
          local t1,t2=unp(as[2][1][2]),unp(as[2][2][2])
          if t1[1]=="Var" and t2[1]=="Var" then
            if t1[2]==ref_n then ctbl=t2[2] elseif t2[2]==ref_n then ctbl=t1[2] end
          end
        end
      end
    end)
    return ctbl
  end
  return nil
end
local function is_gf_fn(f,env)
  if not f[3] or #f[2]~=2 then return false end
  local bs=f[4][2]
  if #bs==2 and bs[1][1]=="If" and bs[2][1]=="Return" and bs[2][2][1][1]=="Call" then
    return true
  end
  return false
end
local function is_wrap_gc(f)
  local has_gc=false
  A.walk(f[4],function(x)
    if (x[1]=="Str" and x[2]=="__gc") or (x[1]=="F" and x[2]=="__gc") then has_gc=true end
  end)
  return has_gc
end
local function parse_mk_cls(f,main_n)
  if f[3] or #f[2]<2 or #f[2]>3 then return nil end
  local fn_p,va_f=nil,nil
  A.walk(f[4],function(x)
    if x[1]=="Func" then
      local r=x[4][2][1]
      if r and r[1]=="Return" and #r[2]==1 and r[2][1][1]=="Call" and unp(r[2][1][2])[1]=="Var" and unp(r[2][1][2])[2]==main_n then
        fn_p=x[2]
        va_f=x[3]
      end
    end
  end)
  if fn_p then return {ps=fn_p,va=va_f} end
  return nil
end
local function parse_ctx(fn_e,args)
  if fn_e[1]~="Func" then return nil end
  local ps,va,body=fn_e[2],fn_e[3],fn_e[4]
  local sts=body[2]
  if #sts<2 then return nil end
  local ret_s=sts[#sts]
  if ret_s[1]~="Return" or #ret_s[2]~=1 then return nil end
  local env={}
  for i,p in ipairs(ps) do
    if args[i] then env[p]=args[i] else env[p]={"Nil"} end
  end
  local bnd={}
  for i=1,#sts-1 do
    local s=sts[i]
    if s[1]=="Assign" then
      for j,l in ipairs(s[2]) do
        if l[1]=="Var" and s[3][j] then bnd[l[2]]=unp(s[3][j]) end
      end
    elseif s[1]=="LocalVar" then
      for j,nm in ipairs(s[2]) do
        if s[3][j] then bnd[nm]=unp(s[3][j]) end
      end
    elseif s[1]=="LocalFunc" then
      bnd[s[2]]={"Func",s[3],s[4],s[5]}
    end
  end
  local main_n,main_f
  for nm,v in pairs(bnd) do
    if v[1]=="Func" and (#v[2]==4 or #v[2]==5) then
      local cs=C.find_cff(v[4])
      if #cs>=1 then
        main_n=nm
        main_f=v
        break
      end
    end
  end
  if not main_n then return nil end
  local disp_info=C.find_cff(main_f[4])[1]
  local ctx={
    env=env,
    bnd=bnd,
    main_n=main_n,
    main_f=main_f,
    pv=disp_info.pv,
    route=disp_info.route,
    p_args=main_f[2][2],
    p_upvs=main_f[2][3],
    mk_cls={},
    gc_fns={},
  }
  local mf_locs={}
  for _,p in ipairs(main_f[2]) do mf_locs[p]=true end
  for _,st in ipairs(main_f[4][2]) do
    if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do mf_locs[nm]=true end
    elseif st[1]=="LocalFunc" then mf_locs[st[2]]=true end
  end
  ctx.mf_locs=mf_locs
  for nm,v in pairs(bnd) do
    if nm~=main_n and v[1]=="Func" then
      local cnt,ref=is_alloc_fn(v)
      if cnt then
        ctx.alloc_fn=nm ctx.cnt_n=cnt ctx.ref_n=ref
      elseif is_pack_fn(v) then
        ctx.pack_fn=nm
      elseif is_unpack_fn(v,env) then
        ctx.unpack_fn=nm
      elseif is_gf_fn(v,env) then
        ctx.gf_fn=nm
      end
    elseif v[1]=="Tbl" and #v[2]==0 then
    end
  end
  for nm,v in pairs(bnd) do
    if nm~=main_n and v[1]=="Func" then
      local ct1=is_gc_one(v,ctx.ref_n)
      if ct1 then ctx.cells_n=ct1 ctx.gc_fns[nm]=true
      else
        local ct2=is_gc_batch(v,ctx.ref_n)
        if ct2 then ctx.cells_n=ct2 ctx.gc_fns[nm]=true
        elseif is_wrap_gc(v) then ctx.wrap_gc=nm
        else
          local mc=parse_mk_cls(v,main_n)
          if mc then ctx.mk_cls[nm]=mc end
        end
      end
    end
  end
  local env_sub,asgn={},{}
  for i=1,#sts-1 do
    local nd=sts[i]
    if nd[1]=="Assign" then
      for _,l in ipairs(nd[2]) do if l[1]=="Var" then asgn[l[2]]=true end end
    elseif nd[1]=="LocalVar" then
      for _,nm in ipairs(nd[2]) do asgn[nm]=true end
    elseif nd[1]=="LocalFunc" then
      asgn[nd[2]]=true
    end
  end
  ctx.env_vars={}
  for i,p in ipairs(ps) do
    local a=args[i]
    if a and not mf_locs[p] then
      local has_e=false
      A.walk(a,function(x) if x[1]=="Var" and (x[2]=="_ENV" or x[2]=="getfenv" or x[2]=="_G") then has_e=true end end)
      if has_e and a[1]~="Var" then ctx.env_vars[p]=true end
      if a[1]=="Var" and a[2]=="_ENV" then ctx.env_vars[p]=true end
    end
  end
  for k,v in pairs(env) do
    if not asgn[k] and not bnd[k] then
      local u=unp(v)
      if u[1]=="Var" or u[1]=="Field" or u[1]=="Nil" or u[1]=="Bool" or u[1]=="Num" or u[1]=="Str" then
        if k~=ctx.pv then env_sub[k]=u end
      end
    end
  end
  for _,p in ipairs(main_f[2]) do env_sub[p]=nil end
  for _,st in ipairs(main_f[4][2]) do
    if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do env_sub[nm]=nil end
    elseif st[1]=="LocalFunc" then env_sub[st[2]]=nil end
  end
  local function drop_asg(n)
    if type(n)~="table" then return end
    local k=n[1]
    if k=="Func" or k=="LocalFunc" or k=="FuncStmt" then return end
    if k=="Assign" then
      for _,l in ipairs(n[2]) do local u=unp(l) if u[1]=="Var" then env_sub[u[2]]=nil end end
    elseif k=="CAssign" then
      local u=unp(n[3]) if u[1]=="Var" then env_sub[u[2]]=nil end
    end
    for i=2,#n do drop_asg(n[i]) end
  end
  drop_asg(main_f[4])
  ctx.spills={}
  for _,st in ipairs(main_f[4][2]) do
    if st[1]=="While" then break end
    if st[1]=="LocalVar" then
      for ix,nm in ipairs(st[2]) do
        if st[3][ix] and unp(st[3][ix])[1]=="Tbl" and #unp(st[3][ix])[2]==0 and nm~=ctx.cells_n then
          ctx.spills[nm]=true
        end
      end
    elseif st[1]=="Assign" and #st[2]==1 and #st[3]==1 and unp(st[2][1])[1]=="Var" and unp(st[3][1])[1]=="Tbl" and #unp(st[3][1])[2]==0 then
      local nm=unp(st[2][1])[2]
      if nm~=ctx.cells_n then ctx.spills[nm]=true end
    end
  end
  for nm,_ in pairs(ctx.spills) do mf_locs[nm]=true end
  ctx.env_sub=env_sub
  ctx.top_env={}
  local mf_ps={}
  for _,p in ipairs(main_f[2]) do mf_ps[p]=true end
  for k,v in pairs(env) do
    if not asgn[k] and not bnd[k] and env_sub[k]==nil and k~=ctx.pv and not mf_ps[k] then
      local hv=false
      A.walk(v,function(x) if x[1]=="Vararg" then hv=true end end)
      if not hv then ctx.top_env[k]=v end
    end
  end
  local mf_sts=main_f[4][2]
  local last_s=mf_sts[#mf_sts]
  if last_s and last_s[1]=="Return" and #last_s[2]==1 then
    local rc=unp(last_s[2][1])
    if rc[1]=="Call" and unp(rc[2])[1]=="Var" and #rc[3]==1 and unp(rc[3][1])[1]=="Var" then
      local fn_n,rt_n=unp(rc[2])[2],unp(rc[3][1])[2]
      if fn_n==ctx.unpack_fn or (env[fn_n] and is_unpack_expr(env[fn_n],env)) then
        ctx.ret_tbl=rt_n
        ctx.ret_unpack=fn_n==ctx.unpack_fn and "unpack" or fn_n
      end
    end
  end
  local re=unp(ret_s[2][1])
  local top_call=false
  if re[1]=="Call" and unp(re[2])[1]=="Call" then
    top_call=true
    re=unp(re[2])
  end
  if re[1]=="Call" and unp(re[2])[1]=="Var" then
    local fn=unp(re[2])[2]
    local pc0=C.lnum(re[3][1])
    if pc0 and (ctx.mk_cls[fn] or fn==main_n) then
      ctx.init_pc=pc0
      ctx.top_call=top_call
      ctx.top_mk=ctx.mk_cls[fn]
      if #main_f[2]==5 and re[3][3] then
        local a3=unp(re[3][3])
        if a3[1]=="Var" and env[a3[2]] then a3=env[a3[2]] end
        ctx.top_env[main_f[2][5]]=a3
        local he=false
        A.walk(a3,function(x) if x[1]=="Var" and (x[2]=="_ENV" or x[2]=="getfenv" or x[2]=="_G") then he=true end end)
        if he then ctx.env_vars[main_f[2][5]]=true end
      end
      return ctx
    end
  end
  return nil
end
local KW_LUA={["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,["false"]=1,["for"]=1,["function"]=1,["if"]=1,["in"]=1,["local"]=1,["nil"]=1,["not"]=1,["or"]=1,["repeat"]=1,["return"]=1,["then"]=1,["true"]=1,["until"]=1,["while"]=1}
local function is_id(s) return type(s)=="string" and s:match("^[%a_][%w_]*$")~=nil and not KW_LUA[s] end
local function rw_nat_in(e,px,ev,vs,ne_n,sh)
  if type(e)~="table" then return e end
  local k=e[1]
  if type(k)~="string" then
    local r={}
    for i=1,#e do r[i]=type(e[i])=="table" and rw_nat_in(e[i],px,ev,vs,ne_n,sh) or e[i] end
    return r
  end
  if k=="NatExpr" then
    return {"NatExpr",e[2],rw_nat_in(e[3],px,ev,vs,ne_n,sh),rw_nat_in(e[4],px,ev,vs,ne_n,sh)}
  elseif k=="Idx" then
    local ut,uk=unp(e[2]),unp(e[3])
    if ut[1]=="Var" and ut[2]==vs and not (sh and sh[vs]) and uk[1]=="Idx" then
      local u2t,u2k=unp(uk[2]),unp(uk[3])
      if u2t[1]=="Var" and u2t[2]==px and not (sh and sh[px]) and u2k[1]=="Num" and math.floor(u2k[2])==u2k[2] and u2k[2]>=1 and u2k[2]<=ne_n then
        return {"NatCell",u2k[2]}
      end
    end
    if ut[1]=="Var" and ut[2]==ev and not (sh and sh[ev]) then
      if uk[1]=="Str" and is_id(uk[2]) then return {"Var",uk[2]} end
      return {"Idx",{"NatEnv"},rw_nat_in(e[3],px,ev,vs,ne_n,sh)}
    end
    return {"Idx",rw_nat_in(e[2],px,ev,vs,ne_n,sh),rw_nat_in(e[3],px,ev,vs,ne_n,sh)}
  elseif k=="Field" then
    local ut=unp(e[2])
    if ut[1]=="Var" and ut[2]==ev and not (sh and sh[ev]) then
      if is_id(e[3]) then return {"Var",e[3]} end
      return {"Idx",{"NatEnv"},{"Str",e[3]}}
    end
    return {"Field",rw_nat_in(e[2],px,ev,vs,ne_n,sh),e[3]}
  elseif k=="Var" and e[2]==ev and not (sh and sh[ev]) then
    return {"NatEnv"}
  elseif k=="Func" then
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    for _,p in ipairs(e[2]) do s2[p]=true end
    return {"Func",e[2],e[3],rw_nat_in(e[4],px,ev,vs,ne_n,s2)}
  elseif k=="LocalFunc" then
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    s2[e[2]]=true for _,p in ipairs(e[3]) do s2[p]=true end
    return {"LocalFunc",e[2],e[3],e[4],rw_nat_in(e[5],px,ev,vs,ne_n,s2)}
  elseif k=="FuncStmt" then
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    for _,p in ipairs(e[4]) do s2[p]=true end
    if e[3] then s2.self=true end
    return {"FuncStmt",rw_nat_in(e[2],px,ev,vs,ne_n,sh),e[3],e[4],e[5],rw_nat_in(e[6],px,ev,vs,ne_n,s2)}
  elseif k=="ForNum" then
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    s2[e[2]]=true
    return {"ForNum",e[2],rw_nat_in(e[3],px,ev,vs,ne_n,sh),rw_nat_in(e[4],px,ev,vs,ne_n,sh),e[5] and rw_nat_in(e[5],px,ev,vs,ne_n,sh) or false,rw_nat_in(e[6],px,ev,vs,ne_n,s2)}
  elseif k=="ForIn" then
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    for _,v in ipairs(e[2]) do s2[v]=true end
    return {"ForIn",e[2],rw_nat_in(e[3],px,ev,vs,ne_n,sh),rw_nat_in(e[4],px,ev,vs,ne_n,s2)}
  elseif k=="Repeat" then
    local nb=rw_nat_in(e[2],px,ev,vs,ne_n,sh)
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    for _,st in ipairs(nb[2]) do
      if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
      elseif st[1]=="LocalFunc" then s2[st[2]]=true end
    end
    return {"Repeat",nb,rw_nat_in(e[3],px,ev,vs,ne_n,s2)}
  elseif k=="Block" then
    local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
    local ns={}
    for i,st in ipairs(e[2]) do
      ns[i]=rw_nat_in(st,px,ev,vs,ne_n,s2)
      if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
      elseif st[1]=="LocalFunc" then s2[st[2]]=true end
    end
    return {"Block",ns}
  end
  local r={k}
  for i=2,#e do r[i]=type(e[i])=="table" and rw_nat_in(e[i],px,ev,vs,ne_n,sh) or e[i] end
  return r
end
local function norm_stmt(s,ctx,closures)
  local ne,ne_b,ne_s
  local function csh(sh)
    local r={} if sh then for k,v in pairs(sh) do r[k]=v end end return r
  end
  ne=function(e,sh)
    local k=e[1]
    if k=="Call" then
      local fn=unp(e[2])
      if #e[3]==3 and fn[1]=="Func" and #fn[2]==3 and not fn[3] then
        local px,ev,vs=fn[2][1],fn[2][2],fn[2][3]
        local fs=fn[4][2]
        local ex
        if #fs==2 and fs[1][1]=="LocalVar" and #fs[1][2]==1 and #fs[1][3]==1 and fs[2][1]=="Return" and #fs[2][2]==1 and unp(fs[2][2][1])[1]=="Var" and unp(fs[2][2][1])[2]==fs[1][2][1] then
          ex=fs[1][3][1]
        elseif #fs==3 and fs[1][1]=="LocalVar" and #fs[1][2]==1 and #fs[1][3]==1 and fs[3][1]=="Return" and #fs[3][2]==1 and unp(fs[3][2][1])[1]=="Var" and unp(fs[3][2][1])[2]==fs[1][2][1] then
          local rs=fs[1][2][1]
          local ifs=fs[2]
          if ifs[1]=="If" and #ifs[2]==1 and not ifs[3] then
            local tb=ifs[2][1][2][2]
            if #tb==1 and tb[1][1]=="CallStmt" and tb[1][2][1]=="Call" and #tb[1][2][3]==2 and unp(tb[1][2][3][1])[1]=="Var" and unp(tb[1][2][3][1])[2]==rs and unp(tb[1][2][3][2])[1]=="Var" and unp(tb[1][2][3][2])[2]==ev then
              ex=fs[1][3][1]
            end
          end
        end
        if ex then
          local ua=ne(e[3][3],sh)
          local c_sh=ctx.mf_locs and ctx.cells_n and ctx.mf_locs[ctx.cells_n]
          if not ctx.cells_n or (not c_sh and unp(ua)[1]=="Var" and unp(ua)[2]==ctx.cells_n) then
            local pa=unp(e[3][1])
            local ents
            if pa[1]=="Nil" then
              ents={}
            elseif pa[1]=="Call" and unp(pa[2])[1]=="Var" and (unp(pa[2])[2]==ctx.wrap_gc or (ctx.gc_fns and ctx.gc_fns[unp(pa[2])[2]])) and not (sh and sh[unp(pa[2])[2]]) and not (ctx.mf_locs and ctx.mf_locs[unp(pa[2])[2]]) and #pa[3]==1 then
              local tb=unp(pa[3][1])
              if tb[1]=="Tbl" then
                local ok=true
                ents={}
                for i,f in ipairs(tb[2]) do
                  if f[1]~="V" then ok=false break end
                  ents[i]=ne(f[2],sh)
                end
                if not ok then ents=nil end
              end
            end
            if ents then
              local s2=csh(sh) s2[px]=true s2[ev]=true s2[vs]=true
              return {"NatExpr",rw_nat_in(ne(ex,s2),px,ev,vs,#ents,{}),ents,ne(e[3][2],sh)}
            end
          end
        end
      end
      if fn[1]=="Var" and not (sh and sh[fn[2]]) and not (ctx.mf_locs and ctx.mf_locs[fn[2]]) then
        local nm=fn[2]
        if nm==ctx.gf_fn and #e[3]>=1 then
          local tgt=ne(e[3][1],sh)
          local as={} for i=3,#e[3] do as[i-2]=ne(e[3][i],sh) end
          return {"Call",tgt,as}
        elseif nm==ctx.unpack_fn and #e[3]==1 then
          local a=unp(ne(e[3][1],sh))
          if a[1]=="Var" and a[2]==ctx.p_args then
            if ctx.is_root and ctx.fwds and #ctx.fwds>0 then return {"__FWDVA__"} end
            return {"Vararg"}
          end
          return {"Call",{"Var","unpack"},{a,{"Num",1},{"Idx",cp(a),{"Str","n"}}}}
        elseif ctx.mk_cls[nm] and #e[3]>=2 then
          local pc=C.lnum(e[3][1])
          if pc then
            local cid=#closures+1
            local ups={}
            local u_t=unp(e[3][2])
            if u_t[1]=="Tbl" then
              for i,f in ipairs(u_t[2]) do
                if f[1]=="V" then ups[i]=ne(f[2],sh) end
              end
            end
            closures[cid]={pc=pc,ps=ctx.mk_cls[nm].ps,va=ctx.mk_cls[nm].va,ups=ups}
            return {"__CLS__",cid}
          end
        end
      end
      local as={} for i,a in ipairs(e[3]) do as[i]=ne(a,sh) end
      return {"Call",ne(e[2],sh),as}
    elseif k=="MCall" then
      local as={} for i,a in ipairs(e[4]) do as[i]=ne(a,sh) end
      return {"MCall",ne(e[2],sh),e[3],as}
    elseif k=="Paren" then return {"Paren",ne(e[2],sh)}
    elseif k=="Un" then return {"Un",e[2],ne(e[3],sh)}
    elseif k=="Bin" then return {"Bin",e[2],ne(e[3],sh),ne(e[4],sh)}
    elseif k=="Idx" then
      local tb,kx=ne(e[2],sh),ne(e[3],sh)
      local ut,uk=unp(tb),unp(kx)
      if ut[1]=="Var" and not (sh and sh[ut[2]]) then
        if ctx.env_vars and ctx.env_vars[ut[2]] and uk[1]=="Str" and is_id(uk[2]) then
          return {"Var",uk[2]}
        end
        if ctx.spills and ctx.spills[ut[2]] and uk[1]=="Num" and math.floor(uk[2])==uk[2] and uk[2]>=1 then
          return {"Var","_sp_"..uk[2]}
        end
      end
      return {"Idx",tb,kx}
    elseif k=="Field" then return {"Field",ne(e[2],sh),e[3]}
    elseif k=="Tbl" then
      local fs={}
      for i,f in ipairs(e[2]) do
        if f[1]=="V" then fs[i]={"V",ne(f[2],sh)}
        elseif f[1]=="F" then fs[i]={"F",f[2],ne(f[3],sh)}
        else fs[i]={"I",ne(f[2],sh),ne(f[3],sh)} end
      end
      return {"Tbl",fs}
    elseif k=="IfExpr" then
      local cs={} for i,c in ipairs(e[2]) do cs[i]={ne(c[1],sh),ne(c[2],sh)} end
      return {"IfExpr",cs,ne(e[3],sh)}
    elseif k=="Func" then
      local s2=csh(sh)
      for _,p in ipairs(e[2]) do s2[p]=true end
      return {"Func",e[2],e[3],ne_b(e[4],s2)}
    end
    return e
  end
  ne_b=function(b,sh)
    local s2=csh(sh)
    local ns={}
    for i,st in ipairs(b[2]) do
      local r=ne_s(st,s2)
      ns[i]=r
      if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
      elseif st[1]=="LocalFunc" then s2[st[2]]=true end
    end
    return {"Block",ns}
  end
  ne_s=function(st,sh)
    local sk=st[1]
    if sk=="Assign" then
      local ls,rs={},{}
      for i,l in ipairs(st[2]) do ls[i]=ne(l,sh) end
      for i,r in ipairs(st[3]) do rs[i]=ne(r,sh) end
      return {"Assign",ls,rs}
    elseif sk=="LocalVar" then
      local vs={} for i,v in ipairs(st[3]) do vs[i]=ne(v,sh) end
      return {"LocalVar",st[2],vs}
    elseif sk=="LocalFunc" then
      local s2=csh(sh) s2[st[2]]=true for _,p in ipairs(st[3]) do s2[p]=true end
      return {"LocalFunc",st[2],st[3],st[4],ne_b(st[5],s2)}
    elseif sk=="FuncStmt" then
      local s2=csh(sh) for _,p in ipairs(st[4]) do s2[p]=true end if st[3] then s2.self=true end
      return {"FuncStmt",ne(st[2],sh),st[3],st[4],st[5],ne_b(st[6],s2)}
    elseif sk=="CAssign" then return {"CAssign",st[2],ne(st[3],sh),ne(st[4],sh)}
    elseif sk=="CallStmt" then return {"CallStmt",ne(st[2],sh)}
    elseif sk=="Return" then
      local es={} for i,e in ipairs(st[2]) do es[i]=ne(e,sh) end
      return {"Return",es}
    elseif sk=="If" then
      local cs={} for i,c in ipairs(st[2]) do cs[i]={ne(c[1],sh),ne_b(c[2],sh)} end
      return {"If",cs,st[3] and ne_b(st[3],sh) or false}
    elseif sk=="While" then return {"While",ne(st[2],sh),ne_b(st[3],sh)}
    elseif sk=="Repeat" then
      local s2=csh(sh)
      for _,x in ipairs(st[2][2]) do
        if x[1]=="LocalVar" then for _,nm in ipairs(x[2]) do s2[nm]=true end
        elseif x[1]=="LocalFunc" then s2[x[2]]=true end
      end
      return {"Repeat",ne_b(st[2],sh),ne(st[3],s2)}
    elseif sk=="Do" then return {"Do",ne_b(st[2],sh)}
    elseif sk=="ForNum" then
      local s2=csh(sh) s2[st[2]]=true
      return {"ForNum",st[2],ne(st[3],sh),ne(st[4],sh),st[5] and ne(st[5],sh) or false,ne_b(st[6],s2)}
    elseif sk=="ForIn" then
      local es={} for i,e in ipairs(st[3]) do es[i]=ne(e,sh) end
      local s2=csh(sh) for _,v in ipairs(st[2]) do s2[v]=true end
      return {"ForIn",st[2],es,ne_b(st[4],s2)}
    end
    return st
  end
  s=sub_s(s,ctx.env_sub)
  local k=s[1]
  if k=="Assign" then
    if #s[2]==1 and #s[3]==1 then
      local rc=unp(s[3][1])
      if rc[1]=="Call" and unp(rc[2])[1]=="Var" and ctx.gc_fns[unp(rc[2])[2]] and not (ctx.mf_locs and ctx.mf_locs[unp(rc[2])[2]]) then return nil end
    end
    local ls,rs={},{}
    for i,l in ipairs(s[2]) do ls[i]=ne(l) end
    for i,r in ipairs(s[3]) do rs[i]=ne(r) end
    return {"Assign",ls,rs}
  elseif k=="LocalVar" then
    local vs={} for i,v in ipairs(s[3]) do vs[i]=ne(v) end
    return {"LocalVar",s[2],vs}
  elseif k=="CallStmt" then
    local c=unp(s[2])
    if c[1]=="Call" and unp(c[2])[1]=="Var" and ctx.gc_fns[unp(c[2])[2]] and not (ctx.mf_locs and ctx.mf_locs[unp(c[2])[2]]) then return nil end
    return {"CallStmt",ne(s[2])}
  elseif k=="Return" then
    if #s[2]==1 then
      local r=unp(s[2][1])
      if r[1]=="Call" and unp(r[2])[1]=="Var" and unp(r[2])[2]==ctx.unpack_fn and not (ctx.mf_locs and ctx.mf_locs[ctx.unpack_fn]) and #r[3]==1 then
        local a=unp(r[3][1])
        if a[1]=="Tbl" then
          local es={}
          for _,f in ipairs(a[2]) do
            if f[1]=="V" then es[#es+1]=ne(f[2]) end
          end
          return {"Return",es}
        end
      end
    end
    local es={} for i,e in ipairs(s[2]) do es[i]=ne(e) end
    return {"Return",es}
  end
  return s
end
local KW_GLB={_G=1,_ENV=1,print=1,type=1,pairs=1,ipairs=1,next=1,tonumber=1,tostring=1,pcall=1,xpcall=1,error=1,assert=1,select=1,unpack=1,table=1,string=1,math=1,bit32=1,bit=1,os=1,io=1,coroutine=1,debug=1,loadstring=1,load=1,setmetatable=1,getmetatable=1,rawget=1,rawset=1,rawequal=1,rawlen=1,require=1,getfenv=1,setfenv=1}
local function parse_term_rhs(e,ctx)
  e=unp(e)
  if e[1]=="Nil" then return {"Exit"} end
  if ctx and ctx.env_vars and e[1]=="Idx" then
    local tb,kx=unp(e[2]),unp(e[3])
    if tb[1]=="Var" and ctx.env_vars[tb[2]] and kx[1]=="Str" and #kx[2]>=6 and not KW_GLB[kx[2]] then
      return {"Exit"}
    end
  end
  local n=C.lnum(e)
  if n then return {"Jmp",n} end
  if e[1]=="Bin" and e[2]=="or" then
    local l,r=unp(e[3]),unp(e[4])
    if l[1]=="Bin" and l[2]=="and" then
      local t,f=C.lnum(l[4]),C.lnum(r)
      if t and f then return {"Branch",l[3],t,f} end
    elseif r[1]=="Bin" and r[2]=="and" then
      local f,t=C.lnum(l),C.lnum(r[4])
      if t and f then return {"Branch",neg_c(r[3]),t,f} end
    end
  elseif e[1]=="Bin" and e[2]=="and" then
    local t=C.lnum(e[4])
    if t then return {"Branch",e[3],t,"__EXIT__"} end
  end
  return nil
end
local function rm_pv_slot(st,p)
  local ls,rs={},{}
  for k=1,#st[2] do
    if k~=p then
      ls[#ls+1]=st[2][k]
      if st[3][k] then rs[#rs+1]=st[3][k] end
    end
  end
  if #ls==0 then return nil end
  return {"Assign",ls,rs}
end
local function find_pv_asg(st,pv)
  if st[1]~="Assign" then return nil end
  for k=1,#st[2] do
    if st[2][k][1]=="Var" and st[2][k][2]==pv then
      return k,st[3][k] or {"Nil"}
    end
  end
  return nil
end
local function ext_cfg_raw(ctx,pc0,closures,bcs)
  local bs={}
  local q={pc0}
  local seen={[pc0]=true}
  local bcn=0
  while #q>0 do
    local id=table.remove(q,1)
    if id~="__EXIT__" then
      local lb=ctx.route(id)
      if lb then
        local raw=lb[2]
        local sts={}
        local term
        if #raw>0 and raw[#raw][1]=="Return" then
          for i=1,#raw-1 do
            local ns=norm_stmt(raw[i],ctx,closures)
            if ns then sts[#sts+1]=ns end
          end
          local nr=norm_stmt(raw[#raw],ctx,closures)
          term={"Ret",nr and nr[2] or {}}
        else
          local pv_ix,pv_slot,pv_ix0,pv_slot0,bc_nm,bc_ex
          for i=#raw,1,-1 do
            local p,rhs=find_pv_asg(raw[i],ctx.pv)
            if p then
              local vals={}
              for j=1,i-1 do
                local sj=raw[j]
                if sj[1]=="Assign" then
                  for k=1,#sj[2] do
                    if sj[2][k][1]=="Var" then
                      local vn=sj[2][k][2]
                      local rv=sj[3][k] and unp(sj[3][k])
                      if rv and (C.lnum(rv) or rv[1]=="Nil" or rv[1]=="Str") then vals[vn]=rv
                      else vals[vn]=nil end
                    end
                  end
                end
              end
              local ru=unp(rhs)
              local tr=parse_term_rhs(ru,ctx)
              if not tr and ru[1]=="Bin" and ru[2]=="or" and unp(ru[3])[1]=="Var" and unp(ru[3])[2]==ctx.pv then
                local vf_e=unp(ru[4])
                if vf_e[1]=="Var" and vals[vf_e[2]] then vf_e=vals[vf_e[2]] end
                local fn_id=C.lnum(vf_e)
                if fn_id then
                  for j=i-1,1,-1 do
                    local p0,rhs0=find_pv_asg(raw[j],ctx.pv)
                    if p0 then
                      local r0=unp(rhs0)
                      if r0[1]=="Bin" and r0[2]=="and" then
                        local vt_e=unp(r0[4])
                        local v0={}
                        for qk=1,j-1 do
                          local sq=raw[qk]
                          if sq[1]=="Assign" then
                            for kk=1,#sq[2] do
                              if sq[2][kk][1]=="Var" and sq[3][kk] then
                                local rv=unp(sq[3][kk])
                                if C.lnum(rv) then v0[sq[2][kk][2]]=rv else v0[sq[2][kk][2]]=nil end
                              end
                            end
                          end
                        end
                        if vt_e[1]=="Var" and v0[vt_e[2]] then vt_e=v0[vt_e[2]] end
                        local tn_id=C.lnum(vt_e)
                        if tn_id then
                          pv_ix0,pv_slot0=j,p0
                          bcn=bcn+1
                          bc_nm="_bc"..bcn
                          bc_ex=r0[3]
                          if bcs then bcs[bc_nm]=true end
                          tr={"Branch",{"Var",bc_nm},tn_id,fn_id}
                        end
                      end
                      break
                    end
                  end
                end
              end
              if tr then
                if tr[1]=="Branch" and i<#raw and not pv_ix0 then
                  bcn=bcn+1
                  bc_nm="_bc"..bcn
                  bc_ex=tr[2]
                  if bcs then bcs[bc_nm]=true end
                  tr={"Branch",{"Var",bc_nm},tr[3],tr[4]}
                end
                pv_ix=i pv_slot=p term=tr break
              end
            end
          end
          for i=1,#raw do
            local st=raw[i]
            if i==pv_ix then
              st=rm_pv_slot(st,pv_slot)
              if st then
                local ns=norm_stmt(st,ctx,closures)
                if ns then sts[#sts+1]=ns end
              end
              if bc_nm and not pv_ix0 then
                sts[#sts+1]=norm_stmt({"Assign",{{"Var",bc_nm}},{bc_ex}},ctx,closures)
              end
              st=nil
            elseif i==pv_ix0 then
              st=rm_pv_slot(st,pv_slot0)
              if st then
                local ns=norm_stmt(st,ctx,closures)
                if ns then sts[#sts+1]=ns end
              end
              sts[#sts+1]=norm_stmt({"Assign",{{"Var",bc_nm}},{bc_ex}},ctx,closures)
              st=nil
            end
            if st then
              local ns=norm_stmt(st,ctx,closures)
              if ns then sts[#sts+1]=ns end
            end
          end
          if not term then term={"Jmp",id} end
        end
        if term[1]=="Exit" and ctx.ret_tbl then
          local ls=#sts>0 and sts[#sts]
          if ls and ls[1]=="Assign" and #ls[2]==1 and #ls[3]==1 and ls[2][1][1]=="Var" and ls[2][1][2]==ctx.ret_tbl then
            local rh=unp(ls[3][1])
            if rh[1]=="Call" and unp(rh[2])[1]=="Var" and unp(rh[2])[2]==ctx.pack_fn then
              table.remove(sts)
              term={"Ret",rh[3]}
            elseif rh[1]=="Tbl" then
              local es={}
              for _,f in ipairs(rh[2]) do
                if f[1]=="V" then es[#es+1]=f[2] end
              end
              if #es==1 and unp(es[1])[1]=="Call" and unp(unp(es[1])[2])[1]=="Var" and (unp(unp(es[1])[2])[2]=="unpack" or unp(unp(es[1])[2])[2]==ctx.ret_unpack) and #unp(es[1])[3]==1 then
                local inner=unp(unp(es[1])[3][1])
                if inner[1]=="Var" and #sts>=2 and sts[#sts-1][1]=="Assign" and #sts[#sts-1][2]==1 and sts[#sts-1][2][1][1]=="Var" and sts[#sts-1][2][1][2]==inner[2] and unp(sts[#sts-1][3][1])[1]=="Tbl" then
                  local fs2=unp(sts[#sts-1][3][1])[2]
                  if #fs2==1 and fs2[1][1]=="V" then
                    table.remove(sts)
                    table.remove(sts)
                    term={"Ret",{fs2[1][2]}}
                  else
                    table.remove(sts)
                    term={"Ret",es}
                  end
                else
                  table.remove(sts)
                  term={"Ret",es}
                end
              else
                table.remove(sts)
                term={"Ret",es}
              end
            else
              term={"Ret",{{"Call",{"Var","unpack"},{{"Var",ctx.ret_tbl},{"Num",1},{"Idx",{"Var",ctx.ret_tbl},{"Str","n"}}}}}}
            end
          else
            term={"Ret",{{"Call",{"Var","unpack"},{{"Var",ctx.ret_tbl},{"Num",1},{"Idx",{"Var",ctx.ret_tbl},{"Str","n"}}}}}}
          end
        end
        if term[1]=="Jmp" then
          if not seen[term[2]] then seen[term[2]]=true q[#q+1]=term[2] end
        elseif term[1]=="Branch" then
          if not seen[term[3]] then seen[term[3]]=true q[#q+1]=term[3] end
          if term[4]~="__EXIT__" and not seen[term[4]] then seen[term[4]]=true q[#q+1]=term[4] end
        end
        bs[id]={id=id,stmts=sts,term=term}
      end
    end
  end
  if seen["__EXIT__"] then bs["__EXIT__"]={id="__EXIT__",stmts={},term={"Exit"}} end
  return bs
end
local function extract_vars_e(e,out,cls)
  A.walk(e,function(x)
    if x[1]=="Var" then out[x[2]]=true
    elseif x[1]=="__CLS__" and cls and cls[x[2]] then
      for _,u in ipairs(cls[x[2]].ups) do extract_vars_e(u,out,cls) end
    end
  end)
end
local function has_cls_n(n)
  local f=false
  A.walk(n,function(x) if x[1]=="__CLS__" then f=true end end)
  return f
end
local function cls_uses_v(n,v,cls)
  if not cls then return false end
  local f=false
  A.walk(n,function(x)
    if x[1]=="__CLS__" and cls[x[2]] then
      for _,u in ipairs(cls[x[2]].ups) do
        local us={} extract_vars_e(u,us,cls)
        if us[v] then f=true end
      end
    end
  end)
  return f
end
local function has_alloc(e)
  local fl=false
  A.walk(e,function(x)
    local k=x[1]
    if k=="__CLS__" or k=="Tbl" or k=="Func" then fl=true end
  end)
  return fl
end
local function pure_tmp_e(e)
  e=unp(e)
  local k=e[1]
  if k=="Nil" or k=="Bool" or k=="Num" or k=="Str" or k=="Var" or k=="GVar" or k=="Vararg" or k=="__CLS__" then return true end
  if k=="Un" then return pure_tmp_e(e[3]) end
  if k=="Bin" then return pure_tmp_e(e[3]) and pure_tmp_e(e[4]) end
  if k=="Tbl" then
    for _,f in ipairs(e[2]) do
      if f[1]=="V" then if not pure_tmp_e(f[2]) then return false end
      elseif f[1]=="F" then if not pure_tmp_e(f[3]) then return false end
      else if not pure_tmp_e(f[2]) or not pure_tmp_e(f[3]) then return false end end
    end
    return true
  end
  return false
end
local function pure_s(s)
  local k=s[1]
  if k=="Assign" then
    for _,l in ipairs(s[2]) do if l[1]~="Var" then return false end end
    for _,r in ipairs(s[3]) do if not pure_tmp_e(r) then return false end end
    return true
  elseif k=="LocalVar" then
    for _,r in ipairs(s[3]) do if not pure_tmp_e(r) then return false end end
    return true
  end
  return false
end
local function stmt_rw(s,locs,cls)
  local rd,wr={},{}
  local k=s[1]
  if k=="Assign" then
    for _,r in ipairs(s[3]) do extract_vars_e(r,rd,cls) end
    for _,l in ipairs(s[2]) do
      if l[1]=="Var" then wr[l[2]]=true
      else extract_vars_e(l,rd,cls) end
    end
  elseif k=="LocalVar" then
    for _,r in ipairs(s[3]) do extract_vars_e(r,rd,cls) end
    for _,nm in ipairs(s[2]) do wr[nm]=true end
  elseif k=="CAssign" then
    extract_vars_e(s[3],rd,cls) extract_vars_e(s[4],rd,cls)
    if s[3][1]=="Var" then wr[s[3][2]]=true end
  elseif k=="CallStmt" then extract_vars_e(s[2],rd,cls)
  elseif k=="Return" then
    for _,e in ipairs(s[2]) do extract_vars_e(e,rd,cls) end
  elseif k=="ForNum" then
    extract_vars_e(s[3],rd,cls) extract_vars_e(s[4],rd,cls) if s[5] then extract_vars_e(s[5],rd,cls) end
  elseif k=="ForIn" then
    for _,e in ipairs(s[3]) do extract_vars_e(e,rd,cls) end
  end
  return rd,wr
end
local function liveness_cfg(bs,locs,cls)
  local li,lo={},{}
  for id,_ in pairs(bs) do li[id]={} lo[id]={} end
  local chg=true
  while chg do
    chg=false
    for id,b in pairs(bs) do
      local nlo={}
      for _,s in ipairs(G.succs(b)) do
        if li[s] then for v,_ in pairs(li[s]) do nlo[v]=true end end
      end
      lo[id]=nlo
      local cur={}
      for v,_ in pairs(nlo) do cur[v]=true end
      if b.term[1]=="Branch" then extract_vars_e(b.term[2],cur,cls)
      elseif b.term[1]=="Ret" then
        for _,e in ipairs(b.term[2]) do extract_vars_e(e,cur,cls) end
      end
      for i=#b.stmts,1,-1 do
        local rd,wr=stmt_rw(b.stmts[i],locs,cls)
        for v,_ in pairs(wr) do cur[v]=nil end
        for v,_ in pairs(rd) do cur[v]=true end
      end
      local diff=false
      for v,_ in pairs(cur) do if not li[id][v] then diff=true break end end
      if not diff then for v,_ in pairs(li[id]) do if not cur[v] then diff=true break end end end
      if diff then li[id]=cur chg=true end
    end
  end
  return li,lo
end
local function dse_block(b,out_live,locs,cls)
  local live={}
  for v,_ in pairs(out_live) do live[v]=true end
  if b.term[1]=="Branch" then extract_vars_e(b.term[2],live,cls)
  elseif b.term[1]=="Ret" then
    for _,e in ipairs(b.term[2]) do extract_vars_e(e,live,cls) end
  end
  local keep={}
  local chg=false
  for i=#b.stmts,1,-1 do
    local s=b.stmts[i]
    local drop=false
    if s[1]=="Assign" and #s[2]==1 and s[2][1][1]=="Var" then
      local v=s[2][1][2]
      if locs[v] and not live[v] then
        local ru=unp(s[3][1])
        if pure_tmp_e(s[3][1]) then drop=true chg=true
        elseif ru[1]=="Call" or ru[1]=="MCall" then s={"CallStmt",ru} chg=true end
      end
    elseif s[1]=="Assign" and #s[2]>1 and #s[2]==#s[3] then
      local all_v,seen=true,{}
      for _,l in ipairs(s[2]) do
        if l[1]~="Var" or seen[l[2]] then all_v=false break end
        seen[l[2]]=true
      end
      if all_v then
        local nls,nrs={},{}
        for k=1,#s[2] do
          local v=s[2][k][2]
          if locs[v] and not live[v] and pure_tmp_e(s[3][k]) then
            chg=true
          else
            nls[#nls+1]=s[2][k]
            nrs[#nrs+1]=s[3][k]
          end
        end
        if #nls==0 then drop=true
        elseif #nls<#s[2] then s={"Assign",nls,nrs} end
      end
    end
    if not drop then
      keep[#keep+1]=s
      local rd,wr=stmt_rw(s,locs,cls)
      for v,_ in pairs(wr) do live[v]=nil end
      for v,_ in pairs(rd) do live[v]=true end
    end
  end
  local ns={}
  for i=#keep,1,-1 do ns[#ns+1]=keep[i] end
  b.stmts=ns
  return chg
end
local function is_lit_s(e)
  e=unp(e)
  local k=e[1]
  return k=="Nil" or k=="Bool" or k=="Num" or k=="Str" or (k=="Un" and e[2]=="-" and unp(e[3])[1]=="Num")
end
local function lhs_overwrites(s,v)
  if s[1]=="Assign" then
    for _,l in ipairs(s[2]) do
      if unp(l)[1]=="Var" and unp(l)[2]==v then return true end
    end
  end
  return false
end
local function inline_temps_blk(b,out_live,locs,ctx)
  local cls=ctx and ctx.cls_reqs
  local sts=b.stmts
  local chg=false
  do
    local ns={}
    for _,s in ipairs(sts) do
      if s[1]=="Assign" and #s[2]>1 and #s[2]==#s[3] and not has_cls_n(s) then
        local lv_s,ok_d={},true
        for ix,l in ipairs(s[2]) do
          local u=unp(l)
          if u[1]=="Var" then
            if lv_s[u[2]] then ok_d=false break end
            lv_s[u[2]]=true
          elseif not (u[1]=="Idx" and unp(u[2])[1]=="Var" and is_lit_s(u[3])) then
            ok_d=false break
          end
        end
        if ok_d then
          local rem,sch={},{}
          for ix=1,#s[2] do rem[ix]=ix end
          while #rem>0 do
            local pk
            for ri,ix in ipairs(rem) do
              local u=unp(s[2][ix])
              local wn=u[1]=="Var" and u[2] or unp(u[2])[2]
              local clash=false
              for rj,jx in ipairs(rem) do
                if ri~=rj then
                  local d1,d2={},{}
                  extract_vars_e(s[3][jx],d1,cls)
                  if d1[wn] then clash=true break end
                  local uj=unp(s[2][jx])
                  if uj[1]=="Idx" then
                    extract_vars_e(uj,d2,cls)
                    if d2[wn] then clash=true break end
                    if u[1]~="Var" and unp(uj[2])[2]==wn then clash=true break end
                  elseif u[1]~="Var" and uj[2]==wn then clash=true break end
                end
              end
              if not clash and u[1]=="Var" then
                local dl={} extract_vars_e(s[2][ix],dl,cls)
                for rj,jx in ipairs(rem) do
                  if ri~=rj then
                    local uj=unp(s[2][jx])
                    if uj[1]=="Var" and uj[2]==wn then clash=true break end
                  end
                end
              end
              if not clash then pk=ri break end
            end
            if not pk then break end
            local ix=table.remove(rem,pk)
            sch[#sch+1]={"Assign",{s[2][ix]},{s[3][ix]}}
          end
          if #rem==0 and #sch>1 then
            for _,ss in ipairs(sch) do ns[#ns+1]=ss end
            chg=true
          else ns[#ns+1]=s end
        else ns[#ns+1]=s end
      else ns[#ns+1]=s end
    end
    sts=ns
    b.stmts=sts
  end
  local function live_after_stmt(v,st_i)
    if lhs_overwrites(sts[st_i],v) then return false end
    for k=st_i+1,#sts do
      local rk,wk=stmt_rw(sts[k],locs,cls)
      if rk[v] then return true end
      if wk[v] then return false end
    end
    if b.term[1]=="Branch" then
      local tr={} extract_vars_e(b.term[2],tr,cls) if tr[v] then return true end
    elseif b.term[1]=="Ret" then
      local tr={} for _,e in ipairs(b.term[2]) do extract_vars_e(e,tr,cls) end if tr[v] then return true end
    end
    return out_live[v] or false
  end
  local i=1
  while i<=#sts do
    local s=sts[i]
    if s[1]=="Assign" and #s[2]==1 and s[2][1][1]=="Var" and #s[3]==1 then
      local v=s[2][1][2]
      local rhs=s[3][1]
      if locs[v] then
        if is_lit_s(rhs) then
          local redef,j_uses=false,{}
          for j=i+1,#sts do
            local rj,wj=stmt_rw(sts[j],locs,cls)
            if rj[v] then j_uses[#j_uses+1]=j end
            if wj[v] then redef=true break end
          end
          local ok_sub=true
          for _,ju in ipairs(j_uses) do if cls_uses_v(sts[ju],v,cls) then ok_sub=false break end end
          if ok_sub and (#j_uses>0 or (not redef and out_live[v]) or true) then
            local all_d=#j_uses>0
            if all_d then
              for _,ju in ipairs(j_uses) do sts[ju]=sub_s(sts[ju],{[v]=rhs}) end
              chg=true
            end
            if not redef then
              local b_t=false
              if b.term[1]=="Branch" then
                local tr={} extract_vars_e(b.term[2],tr,cls)
                if tr[v] and not cls_uses_v(b.term[2],v,cls) then b.term[2]=sub_e(b.term[2],{[v]=rhs}) chg=true b_t=true end
              elseif b.term[1]=="Ret" then
                local es={}
                for k,e in ipairs(b.term[2]) do
                  local tr={} extract_vars_e(e,tr,cls)
                  if tr[v] and not cls_uses_v(e,v,cls) then es[k]=sub_e(e,{[v]=rhs}) chg=true b_t=true else es[k]=e end
                end
                if b_t then b.term[2]=es end
              end
            end
            local still_u=false
            for _,ju in ipairs(j_uses) do
              local rj=stmt_rw(sts[ju],locs,cls)
              if rj[v] then still_u=true break end
            end
            if not still_u and not redef then
              if b.term[1]=="Branch" then
                local tr={} extract_vars_e(b.term[2],tr,cls) if tr[v] then still_u=true end
              elseif b.term[1]=="Ret" then
                local tr={} for _,e in ipairs(b.term[2]) do extract_vars_e(e,tr,cls) end if tr[v] then still_u=true end
              end
            end
            if not still_u and (redef or not out_live[v]) then
              table.remove(sts,i) chg=true
            else i=i+1 end
          else i=i+1 end
        else
          local is_p=pure_tmp_e(rhs)
          local deps={}
          extract_vars_e(rhs,deps,cls)
          if not deps[v] then
            local rd_next=nil
            local clobber=false
            for j=i+1,#sts do
              local rj,wj=stmt_rw(sts[j],locs,cls)
              if rj[v] then rd_next=j break end
              if wj[v] then clobber=true break end
              if not is_p and not pure_s(sts[j]) then clobber=true break end
              for d,_ in pairs(deps) do
                if wj[d] then clobber=true break end
              end
              if clobber then break end
            end
            local use_in_term=false
            if not rd_next and not clobber then
              if b.term[1]=="Branch" then
                local tr={} extract_vars_e(b.term[2],tr,cls)
                if tr[v] then use_in_term=true end
              elseif b.term[1]=="Ret" then
                local tr={} for _,e in ipairs(b.term[2]) do extract_vars_e(e,tr,cls) end
                if tr[v] then use_in_term=true end
              end
            end
            if rd_next and not cls_uses_v(sts[rd_next],v,cls) then
              local uses_cnt=0
              local function cr(nd) A.walk(nd,function(x) if x[1]=="Var" and x[2]==v then uses_cnt=uses_cnt+1 end end) end
              local sr=sts[rd_next]
              if sr[1]=="Assign" then
                for _,l in ipairs(sr[2]) do if unp(l)[1]~="Var" then cr(l) end end
                cr(sr[3])
              elseif sr[1]=="CAssign" then
                if unp(sr[3])[1]~="Var" then cr(sr[3]) end
                cr(sr[4])
              else
                cr(sr)
              end
              local after_live=live_after_stmt(v,rd_next)
              if is_p and (not after_live or (uses_cnt==1 and not has_alloc(rhs))) then
                sts[rd_next]=sub_s(sts[rd_next],{[v]=rhs})
                chg=true
                if not after_live then table.remove(sts,i) else i=i+1 end
              elseif not is_p and uses_cnt==1 and not after_live then
                local ru=unp(rhs)
                local ir=(ru[1]=="Call" or ru[1]=="MCall" or ru[1]=="Vararg") and {"Paren",cp(rhs)} or rhs
                sts[rd_next]=sub_s(sts[rd_next],{[v]=ir})
                table.remove(sts,i)
                chg=true
              else i=i+1 end
            elseif use_in_term and not cls_uses_v(b.term,v,cls) then
              local uses_cnt=0
              if b.term[1]=="Branch" then
                A.walk(b.term[2],function(x) if x[1]=="Var" and x[2]==v then uses_cnt=uses_cnt+1 end end)
              else
                for _,e in ipairs(b.term[2]) do A.walk(e,function(x) if x[1]=="Var" and x[2]==v then uses_cnt=uses_cnt+1 end end) end
              end
              if (is_p or uses_cnt==1) and not out_live[v] then
                local mp={[v]=rhs}
                if b.term[1]=="Branch" then b.term[2]=sub_e(b.term[2],mp)
                else
                  local es={} for k,e in ipairs(b.term[2]) do es[k]=sub_e(e,mp) end
                  b.term[2]=es
                end
                table.remove(sts,i)
                chg=true
              else i=i+1 end
            else i=i+1 end
          else i=i+1 end
        end
      else i=i+1 end
    else i=i+1 end
  end
  return chg
end
local function is_unp_tv(e,tv)
  e=unp(e)
  if e[1]=="Call" and unp(e[2])[1]=="Var" and unp(e[2])[2]=="unpack" and #e[3]>=1 then
    local a=unp(e[3][1])
    if a[1]=="Var" and a[2]==tv then return true end
  end
  return false
end
local function cnt_tv_in(node,tv)
  local tot,unp_n=0,0
  local function w(x)
    if type(x)~="table" then return end
    if is_unp_tv(x,tv) then
      local u=unp(x)
      local in_u=0
      for _,ag in ipairs(u[3]) do
        A.walk(ag,function(y) if y[1]=="Var" and y[2]==tv then in_u=in_u+1 end end)
      end
      unp_n=unp_n+in_u
      tot=tot+in_u
      return
    end
    if x[1]=="Var" and x[2]==tv then tot=tot+1 return end
    for i=1,#x do w(x[i]) end
  end
  w(node)
  return tot,unp_n
end
local repl_unp_e
local function repl_unp_list(xs,tv,args,wrap_f)
  local nxs={}
  local did=false
  for i=1,#xs do
    local x=xs[i]
    local raw_x=wrap_f and (x[1]=="V" and x[2] or nil) or x
    if raw_x and is_unp_tv(raw_x,tv) then
      did=true
      if i==#xs then
        for _,a in ipairs(args) do
          nxs[#nxs+1]=wrap_f and {"V",cp(a)} or cp(a)
        end
      elseif #args==1 then
        local a=unp(args[1])
        local rep=(a[1]=="Call" or a[1]=="MCall" or a[1]=="Vararg") and {"Paren",cp(args[1])} or cp(args[1])
        nxs[#nxs+1]=wrap_f and {"V",rep} or rep
      elseif #args==0 then
        nxs[#nxs+1]=wrap_f and {"V",{"Nil"}} or {"Nil"}
      else
        nxs[#nxs+1]=x
        did=false
      end
    else
      nxs[#nxs+1]=repl_unp_e(x,tv,args)
    end
  end
  return nxs
end
repl_unp_e=function(e,tv,args)
  if type(e)~="table" then return e end
  local k=e[1]
  if k=="Call" then
    return {"Call",repl_unp_e(e[2],tv,args),repl_unp_list(e[3],tv,args,false)}
  elseif k=="MCall" then
    return {"MCall",repl_unp_e(e[2],tv,args),e[3],repl_unp_list(e[4],tv,args,false)}
  elseif k=="Tbl" then
    local fs,last_v={},nil
    for i,f in ipairs(e[2]) do
      if f[1]=="V" and is_unp_tv(f[2],tv) and i==#e[2] then
        last_v=true
        for _,a in ipairs(args) do fs[#fs+1]={"V",cp(a)} end
      elseif f[1]=="V" then fs[#fs+1]={"V",repl_unp_e(f[2],tv,args)}
      elseif f[1]=="F" then fs[#fs+1]={"F",f[2],repl_unp_e(f[3],tv,args)}
      else fs[#fs+1]={"I",repl_unp_e(f[2],tv,args),repl_unp_e(f[3],tv,args)} end
    end
    return {"Tbl",fs}
  elseif k=="Paren" then return {"Paren",repl_unp_e(e[2],tv,args)}
  elseif k=="Un" then return {"Un",e[2],repl_unp_e(e[3],tv,args)}
  elseif k=="Bin" then return {"Bin",e[2],repl_unp_e(e[3],tv,args),repl_unp_e(e[4],tv,args)}
  elseif k=="Idx" then return {"Idx",repl_unp_e(e[2],tv,args),repl_unp_e(e[3],tv,args)}
  elseif k=="Field" then return {"Field",repl_unp_e(e[2],tv,args),e[3]}
  elseif k=="V" then return {"V",repl_unp_e(e[2],tv,args)}
  elseif k=="Return" then return {"Return",repl_unp_list(e[2],tv,args,false)}
  elseif k=="Ret" then return {"Ret",repl_unp_list(e[2],tv,args,false)}
  elseif k=="Assign" then
    local ls,rs={},{}
    for i,l in ipairs(e[2]) do ls[i]=repl_unp_e(l,tv,args) end
    rs=repl_unp_list(e[3],tv,args,false)
    return {"Assign",ls,rs}
  elseif k=="CallStmt" then return {"CallStmt",repl_unp_e(e[2],tv,args)}
  end
  return e
end
local function dead_tv_after(sts,j,term,ol,tv,cls)
  if ol and ol[tv] then return false end
  for k=j+1,#sts do
    local rk,wk=stmt_rw(sts[k],{},cls)
    if rk[tv] then return false end
    if wk[tv] then return true end
  end
  if term[1]=="Branch" then
    local tr={} extract_vars_e(term[2],tr,cls)
    if tr[tv] then return false end
  elseif term[1]=="Ret" then
    local tr={} for _,e in ipairs(term[2]) do extract_vars_e(e,tr,cls) end
    if tr[tv] then return false end
  end
  return true
end
local function unpack_pack_cfg(bs,ctx,lo)
  if not ctx.pack_fn then return false end
  local cls=ctx.cls_reqs
  local chg=false
  for id,b in pairs(bs) do
    local ol=lo and lo[id]
    local sts=b.stmts
    local i=1
    while i<=#sts do
      local s=sts[i]
      if s[1]=="Assign" and #s[2]==1 and #s[3]==1 and s[2][1][1]=="Var" then
        local tv=s[2][1][2]
        local pk=unp(s[3][1])
        if pk[1]=="Call" and unp(pk[2])[1]=="Var" and unp(pk[2])[2]==ctx.pack_fn and not (ctx.mf_locs and ctx.mf_locs[ctx.pack_fn]) then
          local args=pk[3]
          local lhs,maxk,j={},0,i+1
          while j<=#sts do
            local sj=sts[j]
            if sj[1]=="Assign" and #sj[2]==1 and #sj[3]==1 then
              local rj=unp(sj[3][1])
              if rj[1]=="Idx" and unp(rj[2])[1]=="Var" and unp(rj[2])[2]==tv and unp(rj[3])[1]=="Num" then
                local kx=unp(rj[3])[2]
                lhs[kx]=sj[2][1]
                if kx>maxk then maxk=kx end
                j=j+1
              elseif sj[2][1][1]=="Var" and sj[2][1][2]==tv and unp(sj[3][1])[1]=="Nil" then
                j=j+1 break
              else break end
            else break end
          end
          if maxk>=1 and #args==1 then
            local all_ok=true
            local olhs={}
            for k=1,maxk do
              if not lhs[k] then all_ok=false break end
              olhs[k]=lhs[k]
            end
            if all_ok then
              sts[i]={"Assign",olhs,{unp(args[1])}}
              for _=i+1,j-1 do table.remove(sts,i+1) end
              chg=true
            end
          else
            local deps={}
            local all_p=true
            for _,a in ipairs(args) do
              extract_vars_e(a,deps,cls)
              if not pure_tmp_e(a) then all_p=false end
            end
            local rd_k,clob=nil,false
            for k=i+1,#sts do
              local rk,wk=stmt_rw(sts[k],{},cls)
              if rk[tv] then rd_k=k break end
              if wk[tv] then break end
              if not all_p and not pure_s(sts[k]) then clob=true break end
              for d,_ in pairs(deps) do if wk[d] then clob=true break end end
              if clob then break end
            end
            local done=false
            if rd_k and not clob and not has_cls_n(sts[rd_k]) then
              local tot,unp_n=cnt_tv_in(sts[rd_k],tv)
              if unp_n>0 and tot==unp_n and dead_tv_after(sts,rd_k,b.term,ol,tv,cls) then
                local sub=repl_unp_e(sts[rd_k],tv,args)
                sts[rd_k]=sub
                table.remove(sts,i)
                done=true
                chg=true
                i=i-1
              end
            elseif not rd_k and not clob and b.term[1]=="Ret" then
              local tot,unp_n=cnt_tv_in(b.term,tv)
              if unp_n>0 and tot==unp_n then
                local sub=repl_unp_e(b.term,tv,args)
                b.term=sub
                table.remove(sts,i)
                done=true
                chg=true
                i=i-1
              end
            end
            if not done and ol and not ol[tv] and dead_tv_after(sts,i,b.term,ol,tv,cls) then
              if #args==1 and (unp(args[1])[1]=="Call" or unp(args[1])[1]=="MCall" or unp(args[1])[1]=="Vararg") then
                sts[i]={"CallStmt",unp(args[1])}
                chg=true
              elseif all_p then
                table.remove(sts,i)
                chg=true
                i=i-1
              end
            end
          end
        end
      end
      i=i+1
    end
  end
  return chg
end
local function merge_cfg(bs,ent)
  local chg=true
  while chg do
    chg=false
    for _,b in pairs(bs) do
      if b.term[1]=="Branch" then
        local c=unp(b.term[2])
        if c[1]=="Bool" or c[1]=="Nil" then
          b.term={"Jmp",(c[1]=="Bool" and c[2]) and b.term[3] or b.term[4]}
          chg=true
        end
      end
    end
    local pr=G.preds(bs)
    for id,b in pairs(bs) do
      if b.term[1]=="Jmp" then
        local nx=b.term[2]
        if nx~=ent and nx~=id and bs[nx] and pr[nx] and #pr[nx]==1 and pr[nx][1]==id then
          local nb=bs[nx]
          for _,st in ipairs(nb.stmts) do b.stmts[#b.stmts+1]=st end
          b.term=nb.term
          bs[nx]=nil
          chg=true
          break
        end
      end
    end
  end
  return G.prune(bs,ent)
end
local function opt_cfg(bs,ent,locs,ctx)
  local cls=ctx and ctx.cls_reqs
  unpack_pack_cfg(bs,ctx,nil)
  for _=1,12 do
    local chg=false
    local _,lo=liveness_cfg(bs,locs,cls)
    if unpack_pack_cfg(bs,ctx,lo) then
      chg=true
      _,lo=liveness_cfg(bs,locs,cls)
    end
    for id,b in pairs(bs) do
      if dse_block(b,lo[id],locs,cls) then chg=true end
      if inline_temps_blk(b,lo[id],locs,ctx) then chg=true end
    end
    bs=merge_cfg(bs,ent)
    _,lo=liveness_cfg(bs,locs,cls)
    for id,b in pairs(bs) do
      if dse_block(b,lo[id],locs,cls) then chg=true end
    end
    if unpack_pack_cfg(bs,ctx,lo) then chg=true end
    if not chg then break end
  end
  return merge_cfg(bs,ent)
end
local function is_for_err(e,msg)
  e=unp(e)
  if e[1]=="Bin" and e[2]=="or" then
    local l,r=unp(e[3]),unp(e[4])
    if l[1]=="Call" and unp(l[2])[1]=="Var" and unp(l[2])[2]=="tonumber" and #l[3]==1 and r[1]=="Call" and unp(r[2])[1]=="Var" and unp(r[2])[2]=="error" and #r[3]==1 and unp(r[3][1])[1]=="Str" and unp(r[3][1])[2]==msg then
      return l[3][1]
    end
  end
  return nil
end
local function find_for_idx(hb,pb,idx_s,ns)
  for _,s in ipairs(hb.stmts) do
    if s[1]=="Assign" then
      for k=1,#s[2] do
        if s[2][k][1]=="Var" and s[3][k] then
          local rh=unp(s[3][k])
          local cn=s[2][k][2]
          if rh[1]=="Bin" and rh[2]=="+" then
            local a,b=unp(rh[3]),unp(rh[4])
            if (a[1]=="Var" and a[2]==cn) or (b[1]=="Var" and b[2]==cn) then return cn end
          end
        end
      end
    end
  end
  for k=idx_s+1,#pb.stmts do
    local s=pb.stmts[k]
    if s[1]=="Assign" then
      for j=1,#s[2] do
        if s[2][j][1]=="Var" and s[3][j] and unp(s[3][j])[1]=="Bin" and unp(s[3][j])[2]=="-" then
          return s[2][j][2]
        end
      end
    end
  end
  return nil
end
local function sub_cfg_e(e,mp,cls_reqs)
  if type(e)~="table" then return e end
  local k=e[1]
  if k=="__CLS__" and cls_reqs and cls_reqs[e[2]] then
    for i,u in ipairs(cls_reqs[e[2]].ups) do cls_reqs[e[2]].ups[i]=sub_cfg_e(u,mp,cls_reqs) end
    return e
  elseif k=="Var" and mp[e[2]]~=nil then return cp(mp[e[2]])
  elseif k=="Func" then
    local m2={} for k2,v in pairs(mp) do m2[k2]=v end
    for _,p in ipairs(e[2]) do m2[p]=nil end
    if not next(m2) then return e end
    return {"Func",e[2],e[3],sub_b(e[4],m2)}
  elseif type(k)~="string" then
    local r={}
    for i=1,#e do r[i]=type(e[i])=="table" and sub_cfg_e(e[i],mp,cls_reqs) or e[i] end
    return r
  end
  local r={k}
  for i=2,#e do
    if type(e[i])=="table" then
      r[i]=sub_cfg_e(e[i],mp,cls_reqs)
    else
      r[i]=e[i]
    end
  end
  return r
end
local function match_for_loops(bs,ent,cls_reqs)
  local lps=G.nat_loops(bs,ent)
  local pr=G.preds(bs)
  local for_hdrs={}
  local fi_n=0
  for hdr,lp in pairs(lps) do
    local pres={}
    for _,p in ipairs(pr[hdr]) do
      if not lp.body[p] then pres[#pres+1]=p end
    end
    if #pres==1 then
      local pb=bs[pres[1]]
      if pb and pb.term[1]=="Jmp" and pb.term[2]==hdr and #pb.stmts>=5 then
        local sts=pb.stmts
        local ni,nl,ns
        local xi,xl,xs
        local idx_i,idx_l,idx_s
        for k=#sts,1,-1 do
          local s=sts[k]
          if s[1]=="Assign" and #s[2]==1 and s[2][1][1]=="Var" then
            if not ns then local ex=is_for_err(s[3][1],"'for' step must be a number") if ex then ns=s[2][1][2] idx_s=k xs=ex end end
            if not nl then local ex=is_for_err(s[3][1],"'for' limit must be a number") if ex then nl=s[2][1][2] idx_l=k xl=ex end end
            if not ni then local ex=is_for_err(s[3][1],"'for' initial value must be a number") if ex then ni=s[2][1][2] idx_i=k xi=ex end end
          end
        end
        if ni and nl and ns and idx_i<idx_l and idx_l<idx_s then
          local init_e=xi
          local lim_e=xl
          local step_e=xs
          local hb=bs[hdr]
          local idx_v=hb and find_for_idx(hb,pb,idx_s,ns)
          if hb and hb.term[1]=="Branch" then
            local t1,f1=hb.term[3],hb.term[4]
            local body_id,exit_id
            if lp.body[t1] and not lp.body[f1] then body_id,exit_id=t1,f1
            elseif lp.body[f1] and not lp.body[t1] then body_id,exit_id=f1,t1 end
            if body_id and exit_id then
              local lv
              local bb=bs[body_id]
              if idx_v and bb then
                local rd_seen={}
                for si=1,#bb.stmts do
                  local bs1=bb.stmts[si]
                  if bs1[1]=="Assign" and #bs1[2]==#bs1[3] then
                    for k=1,#bs1[2] do
                      local lk,rk=bs1[2][k],unp(bs1[3][k])
                      if lk[1]=="Var" and lk[2]~=idx_v and rk[1]=="Var" and rk[2]==idx_v and not rd_seen[lk[2]] then
                        lv=lk[2]
                        if #bs1[2]==1 then table.remove(bb.stmts,si)
                        else
                          local nls,nrs={},{}
                          for j=1,#bs1[2] do if j~=k then nls[#nls+1]=bs1[2][j] nrs[#nrs+1]=bs1[3][j] end end
                          bb.stmts[si]={"Assign",nls,nrs}
                        end
                        break
                      end
                    end
                    if lv then break end
                  end
                  local rd,wr=stmt_rw(bs1,{},cls_reqs)
                  for v,_ in pairs(rd) do rd_seen[v]=true end
                  if wr[idx_v] then break end
                end
              end
              if not lv then
                fi_n=fi_n+1
                lv="_fi"..fi_n
              end
              if idx_v and lv~=idx_v then
                local mp={[idx_v]={"Var",lv}}
                for bid,_ in pairs(lp.body) do
                  if bid~=hdr and bs[bid] then
                    local bk=bs[bid]
                    for j,st in ipairs(bk.stmts) do
                      if st[1]=="Assign" then
                        local nls,nrs={},{}
                        for q=1,#st[2] do
                          nls[q]=st[2][q][1]=="Var" and st[2][q] or sub_cfg_e(st[2][q],mp,cls_reqs)
                        end
                        for q=1,#st[3] do nrs[q]=sub_cfg_e(st[3][q],mp,cls_reqs) end
                        bk.stmts[j]={"Assign",nls,nrs}
                      elseif st[1]=="CallStmt" then bk.stmts[j]={"CallStmt",sub_cfg_e(st[2],mp,cls_reqs)} end
                    end
                    if bk.term[1]=="Branch" then bk.term[2]=sub_cfg_e(bk.term[2],mp,cls_reqs)
                    elseif bk.term[1]=="Ret" then
                      for q,e in ipairs(bk.term[2]) do bk.term[2][q]=sub_cfg_e(e,mp,cls_reqs) end
                    end
                  end
                end
              end
              for _=idx_i,#sts do table.remove(sts,idx_i) end
              for_hdrs[hdr]={pre=pres[1],v=lv,a=init_e,b=lim_e,s=step_e,body=body_id,exit=exit_id,lp=lp}
            end
          end
        end
      end
    end
  end
  return for_hdrs
end
local function track_cells(bs,ent,ctx,cls_reqs)
  if not ctx.alloc_fn or not ctx.cells_n or (ctx.mf_locs and (ctx.mf_locs[ctx.alloc_fn] or ctx.mf_locs[ctx.cells_n])) then return {} end
  local cell_vs={}
  local ord=G.rpo(bs,ent)
  local sites={}
  local function is_ak(s)
    return s[1]=="Assign" and #s[2]==1 and #s[3]==1 and s[2][1][1]=="Var" and s[3][1][1]=="Call" and #s[3][1][3]==0 and unp(s[3][1][2])[1]=="Var" and unp(s[3][1][2])[2]==ctx.alloc_fn
  end
  for _,id in ipairs(ord) do
    for si,s in ipairs(bs[id].stmts) do
      if is_ak(s) then
        ctx.cid_n=(ctx.cid_n or 0)+1
        local cv="_c"..ctx.cid_n
        sites[id..":"..si]=cv
        cell_vs[cv]=true
      end
    end
  end
  local pr=G.preds(bs)
  local inm,outm={},{}
  local function step_s(cur,id,si,s)
    local sk=sites[id..":"..si]
    if sk then
      cur[s[2][1][2]]=sk
    elseif s[1]=="Assign" then
      if #s[2]==1 and #s[3]==1 and s[2][1][1]=="Var" and unp(s[3][1])[1]=="Var" then
        cur[s[2][1][2]]=cur[unp(s[3][1])[2]] or false
      else
        for _,l in ipairs(s[2]) do if l[1]=="Var" then cur[l[2]]=false end end
      end
    elseif s[1]=="LocalVar" then
      for _,nm in ipairs(s[2]) do cur[nm]=false end
    end
  end
  for _=1,24 do
    local chg=false
    for _,id in ipairs(ord) do
      local inc={}
      if id~=ent then
        local ps=pr[id] or {}
        local p0
        for _,p in ipairs(ps) do if outm[p] then p0=p break end end
        if p0 then
          for k,v in pairs(outm[p0]) do inc[k]=v end
          for _,p in ipairs(ps) do
            if outm[p] then
              for k,v in pairs(inc) do
                if v and outm[p][k]~=v then inc[k]="?" end
              end
              for k,v in pairs(outm[p]) do
                if v and inc[k]==nil then inc[k]="?" end
              end
            end
          end
        end
      end
      inm[id]=inc
      local cur={} for k,v in pairs(inc) do cur[k]=v end
      for si,s in ipairs(bs[id].stmts) do step_s(cur,id,si,s) end
      local prev=outm[id]
      local diff=not prev
      if not diff then
        for k,v in pairs(cur) do if prev[k]~=v then diff=true break end end
        if not diff then for k,v in pairs(prev) do if cur[k]~=v then diff=true break end end end
      end
      if diff then outm[id]=cur chg=true end
    end
    if not chg then break end
  end
  local function tc_e(e,cur)
    local k=e[1]
    if k=="Idx" then
      local t,ix=unp(e[2]),unp(e[3])
      if t[1]=="Var" and t[2]==ctx.cells_n and ix[1]=="Var" then
        local c=cur[ix[2]]
        if c and c~="?" then return {"Var",c} end
      end
      return {"Idx",tc_e(e[2],cur),tc_e(e[3],cur)}
    elseif k=="Field" then return {"Field",tc_e(e[2],cur),e[3]}
    elseif k=="Paren" then return {"Paren",tc_e(e[2],cur)}
    elseif k=="Un" then return {"Un",e[2],tc_e(e[3],cur)}
    elseif k=="Bin" then return {"Bin",e[2],tc_e(e[3],cur),tc_e(e[4],cur)}
    elseif k=="Call" then
      local as={} for i,a in ipairs(e[3]) do as[i]=tc_e(a,cur) end
      return {"Call",tc_e(e[2],cur),as}
    elseif k=="MCall" then
      local as={} for i,a in ipairs(e[4]) do as[i]=tc_e(a,cur) end
      return {"MCall",tc_e(e[2],cur),e[3],as}
    elseif k=="Tbl" then
      local fs={}
      for i,f in ipairs(e[2]) do
        if f[1]=="V" then fs[i]={"V",tc_e(f[2],cur)}
        elseif f[1]=="F" then fs[i]={"F",f[2],tc_e(f[3],cur)}
        else fs[i]={"I",tc_e(f[2],cur),tc_e(f[3],cur)} end
      end
      return {"Tbl",fs}
    elseif k=="__CLS__" then
      if cls_reqs and cls_reqs[e[2]] then
        local req=cls_reqs[e[2]]
        for i,u in ipairs(req.ups) do
          if u[1]=="Var" and cur[u[2]] and cur[u[2]]~="?" then
            req.ups[i]={"Var",cur[u[2]]}
          end
        end
      end
      return e
    elseif k=="NatExpr" then
      local es={}
      for i,u in ipairs(e[3]) do
        local uu=unp(u)
        if uu[1]=="Var" and cur[uu[2]] and cur[uu[2]]~="?" then es[i]={"Var",cur[uu[2]]}
        else es[i]=tc_e(u,cur) end
      end
      return {"NatExpr",e[2],es,tc_e(e[4],cur)}
    end
    return e
  end
  for _,id in ipairs(ord) do
    local b=bs[id]
    local cur={} for k,v in pairs(inm[id] or {}) do cur[k]=v end
    local ns={}
    for si,s in ipairs(b.stmts) do
      if sites[id..":"..si] then
        step_s(cur,id,si,s)
      else
        if s[1]=="Assign" then
          local ls,rs={},{}
          for i,l in ipairs(s[2]) do ls[i]=tc_e(l,cur) end
          for i,r in ipairs(s[3]) do rs[i]=tc_e(r,cur) end
          ns[#ns+1]={"Assign",ls,rs}
        elseif s[1]=="CallStmt" then ns[#ns+1]={"CallStmt",tc_e(s[2],cur)}
        else ns[#ns+1]=s end
        step_s(cur,id,si,s)
      end
    end
    b.stmts=ns
    if b.term[1]=="Branch" then b.term[2]=tc_e(b.term[2],cur)
    elseif b.term[1]=="Ret" then
      for i,e in ipairs(b.term[2]) do b.term[2][i]=tc_e(e,cur) end
    end
  end
  return cell_vs
end
local ext_closure
local function only_ret(bs,s)
  local q,vis,has_r={s},{[s]=true},false
  while #q>0 do
    local x=table.remove(q)
    local b=bs[x]
    if not b or b.term[1]=="Exit" then return false end
    if b.term[1]=="Ret" then has_r=true
    else
      for _,nx in ipairs(G.succs(b)) do
        if not vis[nx] then vis[nx]=true q[#q+1]=nx end
      end
    end
  end
  return has_r
end
local function find_loop_exit(bs,lp,act)
  local ex={}
  for id,_ in pairs(lp.body) do
    for _,s in ipairs(G.succs(bs[id])) do
      if not lp.body[s] and not (act and act[s]) then ex[s]=true end
    end
  end
  local hb=bs[lp.hdr]
  if hb and hb.term[1]=="Branch" then
    local t1,t2=hb.term[3],hb.term[4]
    if ex[t2] and not ex[t1] then return t2 end
    if ex[t1] and not ex[t2] then return t1 end
  end
  if #lp.latches==1 then
    local lb=bs[lp.latches[1]]
    if lb and lb.term[1]=="Branch" then
      local t1,t2=lb.term[3],lb.term[4]
      if t1==lp.hdr and ex[t2] then return t2 end
      if t2==lp.hdr and ex[t1] then return t1 end
    end
  end
  for s,_ in pairs(ex) do
    if not only_ret(bs,s) then return s end
  end
  return nil
end
local function cset(t,x)
  local r={}
  if t then for k,v in pairs(t) do r[k]=v end end
  if x~=nil then r[x]=true end
  return r
end
local function struct_cfg(bs,ent,for_hdrs)
  local lps=G.nat_loops(bs,ent)
  local ipdom=G.pdoms(bs)
  local pre_map={}
  for hdr,fh in pairs(for_hdrs) do pre_map[fh.pre]=fh end
  local function emit_reg(u,stop,lhdr,lexit,fst,act)
    local out={}
    local steps=0
    act=act or {}
    while u and (fst or (u~=stop and not act[u])) and bs[u] do
      fst=false
      steps=steps+1
      if steps>5000 then break end
      local fh=for_hdrs[u]
      if fh and u~=lhdr and not act[u] then
        local bblk=emit_reg(fh.body,u,u,fh.exit,false,cset(act,u))
        out[#out+1]={"ForNum",fh.v,fh.a,fh.b,fh.s,{"Block",bblk}}
        u=fh.exit
      elseif lps[u] and u~=lhdr and not act[u] then
        local lp=lps[u]
        local a2=cset(act,u)
        local lex=find_loop_exit(bs,lp,act)
        local hb=bs[u]
        if hb.term[1]=="Branch" and (hb.term[4]==lex or hb.term[3]==lex) then
          local cond,t_id,f_id=hb.term[2],hb.term[3],hb.term[4]
          if #hb.stmts==0 and f_id==lex and lp.body[t_id] then
            local bblk=emit_reg(t_id,u,u,lex,false,a2)
            out[#out+1]={"While",cond,{"Block",bblk}}
            u=lex
          elseif #hb.stmts==0 and t_id==lex and lp.body[f_id] then
            local bblk=emit_reg(f_id,u,u,lex,false,a2)
            out[#out+1]={"While",neg_c(cond),{"Block",bblk}}
            u=lex
          elseif f_id==lex and lp.body[t_id] then
            local body={}
            for _,s in ipairs(hb.stmts) do body[#body+1]=s end
            body[#body+1]={"If",{{neg_c(cond),{"Block",{{"Break"}}}}},false}
            for _,s in ipairs(emit_reg(t_id,u,u,lex,false,a2)) do body[#body+1]=s end
            out[#out+1]={"While",{"Bool",true},{"Block",body}}
            u=lex
          elseif t_id==lex and lp.body[f_id] then
            local body={}
            for _,s in ipairs(hb.stmts) do body[#body+1]=s end
            body[#body+1]={"If",{{cond,{"Block",{{"Break"}}}}},false}
            for _,s in ipairs(emit_reg(f_id,u,u,lex,false,a2)) do body[#body+1]=s end
            out[#out+1]={"While",{"Bool",true},{"Block",body}}
            u=lex
          else
            local body=emit_reg(u,u,u,lex,true,a2)
            out[#out+1]={"While",{"Bool",true},{"Block",body}}
            u=lex
          end
        else
          local rep_b
          if #lp.latches==1 then
            local lb=bs[lp.latches[1]]
            if lb and lb.term[1]=="Branch" and lb.term[3]==u and lb.term[4]==lex then
              rep_b={cond=neg_c(lb.term[2]),lat=lb}
            elseif lb and lb.term[1]=="Branch" and lb.term[4]==u and lb.term[3]==lex then
              rep_b={cond=lb.term[2],lat=lb}
            end
          end
          if rep_b then
            local sv=rep_b.lat.term
            rep_b.lat.term={"Jmp",u}
            local bblk=emit_reg(u,u,u,lex,true,a2)
            rep_b.lat.term=sv
            out[#out+1]={"Repeat",{"Block",bblk},rep_b.cond}
            u=lex
          else
            local body=emit_reg(u,u,u,lex,true,a2)
            out[#out+1]={"While",{"Bool",true},{"Block",body}}
            u=lex
          end
        end
      else
        local b=bs[u]
        for _,s in ipairs(b.stmts) do out[#out+1]=s end
        if pre_map[u] then
          local fh=pre_map[u]
          local bblk=emit_reg(fh.body,fh.exit==stop and stop or b.term[2],b.term[2],fh.exit,false,cset(act,b.term[2]))
          out[#out+1]={"ForNum",fh.v,fh.a,fh.b,fh.s,{"Block",bblk}}
          u=fh.exit
        else
          local tm=b.term
          if tm[1]=="Exit" then break
          elseif tm[1]=="Ret" then
            out[#out+1]={"Return",tm[2]}
            break
          elseif tm[1]=="Jmp" then
            local nx=tm[2]
            if nx==lexit then out[#out+1]={"Break"} break
            elseif nx==lhdr or act[nx] then break
            elseif nx==stop then break
            else u=nx end
          elseif tm[1]=="Branch" then
            local cond,t_id,f_id=tm[2],tm[3],tm[4]
            if f_id==lexit and t_id~=lexit then
              out[#out+1]={"If",{{neg_c(cond),{"Block",{{"Break"}}}}},false}
              u=t_id
            elseif t_id==lexit and f_id~=lexit then
              out[#out+1]={"If",{{cond,{"Block",{{"Break"}}}}},false}
              u=f_id
            else
              local m=ipdom[u]
              if m=="__EXIT__" or not m or not bs[m] then m=stop end
              if m==t_id then
                local eb=emit_reg(f_id,m,lhdr,lexit,false,act)
                out[#out+1]={"If",{{neg_c(cond),{"Block",eb}}},false}
                u=m
              elseif m==f_id then
                local tb=emit_reg(t_id,m,lhdr,lexit,false,act)
                out[#out+1]={"If",{{cond,{"Block",tb}}},false}
                u=m
              else
                local tb=emit_reg(t_id,m,lhdr,lexit,false,act)
                local eb=emit_reg(f_id,m,lhdr,lexit,false,act)
                local brs={{cond,{"Block",tb}}}
                if #eb==1 and eb[1][1]=="If" then
                  local sub=eb[1]
                  for _,b2 in ipairs(sub[2]) do brs[#brs+1]=b2 end
                  eb=sub[3]
                elseif #eb==0 then eb=false
                else eb={"Block",eb} end
                out[#out+1]={"If",brs,eb}
                u=m
              end
            end
          else break end
        end
      end
    end
    return out
  end
  return {"Block",emit_reg(ent,nil,nil,nil,false,{})}
end
ext_closure=function(ctx,pc0,ps,va,upv_map)
  local cls_reqs={}
  local bcs={}
  local sv_rt=ctx.is_root
  ctx.is_root=not upv_map
  local bs=ext_cfg_raw(ctx,pc0,cls_reqs,bcs)
  ctx.is_root=sv_rt
  local locs={}
  for k,_ in pairs(bcs) do locs[k]=true end
  for _,p in ipairs(ctx.main_f[4][2]) do
    if p[1]=="LocalVar" then for _,nm in ipairs(p[2]) do locs[nm]=true end end
  end
  locs[ctx.pv]=true
  locs[ctx.p_args]=true
  if ctx.p_upvs then locs[ctx.p_upvs]=true end
  for _,b in pairs(bs) do
    for _,s in ipairs(b.stmts) do
      A.walk(s,function(x)
        if x[1]=="Var" and x[2]:sub(1,4)=="_sp_" then locs[x[2]]=true end
      end)
    end
  end
  local cell_vs=track_cells(bs,pc0,ctx,cls_reqs)
  for cv,_ in pairs(cell_vs) do locs[cv]=true end
  if upv_map and ctx.p_upvs then
    local mp={}
    for idx,unm in ipairs(upv_map) do mp[idx]=unm end
    local function r_upv_e(e)
      local k=e[1]
      if k=="Idx" then
        local t,ix=unp(e[2]),unp(e[3])
        if t[1]=="Var" and t[2]==ctx.p_upvs and ix[1]=="Num" and mp[ix[2]] then
          return cp(mp[ix[2]])
        end
        if t[1]=="Var" and t[2]==ctx.cells_n and ix[1]=="Idx" and unp(ix[2])[1]=="Var" and unp(ix[2])[2]==ctx.p_upvs and unp(ix[3])[1]=="Num" and mp[unp(ix[3])[2]] then
          return cp(mp[unp(ix[3])[2]])
        end
        return {"Idx",r_upv_e(e[2]),r_upv_e(e[3])}
      elseif k=="Field" then return {"Field",r_upv_e(e[2]),e[3]}
      elseif k=="Paren" then return {"Paren",r_upv_e(e[2])}
      elseif k=="Un" then return {"Un",e[2],r_upv_e(e[3])}
      elseif k=="Bin" then return {"Bin",e[2],r_upv_e(e[3]),r_upv_e(e[4])}
      elseif k=="Call" then
        local as={} for i,a in ipairs(e[3]) do as[i]=r_upv_e(a) end
        return {"Call",r_upv_e(e[2]),as}
      elseif k=="MCall" then
        local as={} for i,a in ipairs(e[4]) do as[i]=r_upv_e(a) end
        return {"MCall",r_upv_e(e[2]),e[3],as}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(e[2]) do
          if f[1]=="V" then fs[i]={"V",r_upv_e(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],r_upv_e(f[3])}
          else fs[i]={"I",r_upv_e(f[2]),r_upv_e(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="__CLS__" then
        if cls_reqs[e[2]] then
          for i,u in ipairs(cls_reqs[e[2]].ups) do cls_reqs[e[2]].ups[i]=r_upv_e(u) end
        end
        return e
      elseif k=="NatExpr" then
        local es={}
        for i,u in ipairs(e[3]) do es[i]=r_upv_e(u) end
        return {"NatExpr",e[2],es,r_upv_e(e[4])}
      end
      return e
    end
    for _,b in pairs(bs) do
      for i,s in ipairs(b.stmts) do
        if s[1]=="Assign" then
          for j,l in ipairs(s[2]) do s[2][j]=r_upv_e(l) end
          for j,r in ipairs(s[3]) do s[3][j]=r_upv_e(r) end
        elseif s[1]=="CallStmt" then s[2]=r_upv_e(s[2]) end
      end
      if b.term[1]=="Branch" then b.term[2]=r_upv_e(b.term[2])
      elseif b.term[1]=="Ret" then for j,e in ipairs(b.term[2]) do b.term[2][j]=r_upv_e(e) end end
    end
  end
  local safe_ps={}
  if #ps>0 then
    local avoid={}
    for k,_ in pairs(locs) do avoid[k]=true end
    if #ctx.main_f[2]>=5 then avoid[ctx.main_f[2][5]]=true end
    if ctx.top_env then for k,_ in pairs(ctx.top_env) do avoid[k]=true end end
    if ctx.env_vars then for k,_ in pairs(ctx.env_vars) do avoid[k]=true end end
    if ctx.env_sub then
      for _,v in pairs(ctx.env_sub) do
        A.walk(v,function(x) if x[1]=="Var" then avoid[x[2]]=true end end)
      end
    end
    if upv_map then
      for _,u in ipairs(upv_map) do
        A.walk(u,function(x) if x[1]=="Var" then avoid[x[2]]=true end end)
      end
    end
    local pmap={}
    for i,p in ipairs(ps) do
      local sp=avoid[p] and ("_pa"..i) or p
      safe_ps[i]=sp
      pmap[i]=sp
      locs[sp]=true
    end
    for _,b in pairs(bs) do
      for _,s in ipairs(b.stmts) do
        if s[1]=="Assign" then
          for j,r in ipairs(s[3]) do
            if r[1]=="Idx" and unp(r[2])[1]=="Var" and unp(r[2])[2]==ctx.p_args and unp(r[3])[1]=="Num" then
              local pn=pmap[unp(r[3])[2]]
              if pn then s[3][j]={"Var",pn} end
            elseif r[1]=="NatExpr" then
              for ui,u in ipairs(r[3]) do
                if u[1]=="Idx" and unp(u[2])[1]=="Var" and unp(u[2])[2]==ctx.p_args and unp(u[3])[1]=="Num" then
                  local pn=pmap[unp(u[3])[2]]
                  if pn then r[3][ui]={"Var",pn} end
                end
              end
            end
          end
        end
      end
    end
  end
  local function sub_nat_t(n,ents,nv)
    if type(n)~="table" then return n end
    local k=n[1]
    if k=="NatCell" then
      local v=ents and ents[n[2]]
      return v and cp(v) or {"Nil"}
    elseif k=="NatEnv" then
      return nv and cp(nv) or {"Var","_ENV"}
    elseif k=="NatExpr" then
      local es={}
      for i,u in ipairs(n[3]) do es[i]=sub_nat_t(u,ents,nv) end
      local ea=sub_nat_t(n[4],ents,nv)
      return sub_nat_t(n[2],es,ea)
    elseif type(k)~="string" then
      local r={} for i=1,#n do r[i]=type(n[i])=="table" and sub_nat_t(n[i],ents,nv) or n[i] end return r
    end
    local r={k} for i=2,#n do r[i]=type(n[i])=="table" and sub_nat_t(n[i],ents,nv) or n[i] end return r
  end
  for _,b in pairs(bs) do
    for i,s in ipairs(b.stmts) do b.stmts[i]=sub_nat_t(s) end
    b.term=sub_nat_t(b.term)
  end
  for _,req in ipairs(cls_reqs) do
    for i,u in ipairs(req.ups) do req.ups[i]=sub_nat_t(u) end
  end
  local sv_cls=ctx.cls_reqs
  ctx.cls_reqs=cls_reqs
  bs=opt_cfg(bs,pc0,locs,ctx)
  ctx.cls_reqs=sv_cls
  if ctx.env_vars and next(ctx.env_vars) then
    local function re_e(e,sh)
      if type(e)~="table" then return e end
      local k=e[1]
      if k=="Idx" then
        local tb,kx=re_e(e[2],sh),re_e(e[3],sh)
        local ut,uk=unp(tb),unp(kx)
        if ut[1]=="Var" and ctx.env_vars[ut[2]] and not (sh and sh[ut[2]]) and uk[1]=="Str" and is_id(uk[2]) then
          return {"GVar",uk[2]}
        end
        return {"Idx",tb,kx}
      elseif k=="Func" then
        local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
        for _,p in ipairs(e[2]) do s2[p]=true end
        return {"Func",e[2],e[3],re_e(e[4],s2)}
      elseif k=="Block" then
        local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
        local ns={}
        for i,st in ipairs(e[2]) do
          ns[i]=re_e(st,s2)
          if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
          elseif st[1]=="LocalFunc" then s2[st[2]]=true end
        end
        return {"Block",ns}
      elseif k=="LocalFunc" then
        local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
        s2[e[2]]=true for _,p in ipairs(e[3]) do s2[p]=true end
        return {"LocalFunc",e[2],e[3],e[4],re_e(e[5],s2)}
      elseif k=="ForNum" then
        local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
        s2[e[2]]=true
        return {"ForNum",e[2],re_e(e[3],sh),re_e(e[4],sh),e[5] and re_e(e[5],sh) or false,re_e(e[6],s2)}
      elseif k=="ForIn" then
        local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
        for _,v in ipairs(e[2]) do s2[v]=true end
        local es={} for i,x in ipairs(e[3]) do es[i]=re_e(x,sh) end
        return {"ForIn",e[2],es,re_e(e[4],s2)}
      elseif k=="Repeat" then
        local nb=re_e(e[2],sh)
        local s2={} if sh then for u,v in pairs(sh) do s2[u]=v end end
        for _,st in ipairs(nb[2]) do
          if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
          elseif st[1]=="LocalFunc" then s2[st[2]]=true end
        end
        return {"Repeat",nb,re_e(e[3],s2)}
      end
      if type(k)~="string" then
        local r={}
        for i=1,#e do r[i]=type(e[i])=="table" and re_e(e[i],sh) or e[i] end
        return r
      end
      local r={k}
      for i=2,#e do r[i]=type(e[i])=="table" and re_e(e[i],sh) or e[i] end
      return r
    end
    local sh0={[ctx.p_args]=true}
    if ctx.p_upvs then sh0[ctx.p_upvs]=true end
    if ctx.cells_n then sh0[ctx.cells_n]=true end
    for _,p in ipairs(safe_ps) do sh0[p]=true end
    if upv_map then for _,u in ipairs(upv_map) do if u[1]=="Var" then sh0[u[2]]=true end end end
    for _,b in pairs(bs) do
      for i,s in ipairs(b.stmts) do b.stmts[i]=re_e(s,sh0) end
      b.term=re_e(b.term,sh0)
    end
    for _,req in ipairs(cls_reqs) do
      for i,u in ipairs(req.ups) do req.ups[i]=re_e(u,sh0) end
    end
  end
  local did_fw=not upv_map and ((ctx.fwds and #ctx.fwds>0) or va)
  if did_fw then
    local fw={}
    if ctx.fwds and #ctx.fwds>0 then fw=ctx.fwds
    else for i,sp in ipairs(safe_ps) do fw[i]={"Var",sp} end end
    local nf=#fw
    local function is_up(nd)
      local u=unp(nd)
      if u[1]=="__FWDVA__" then return true end
      if u[1]=="Call" and unp(u[2])[1]=="Var" and unp(u[2])[2]=="unpack" and #u[3]>=1 then
        local a1=unp(u[3][1])
        if a1[1]=="Var" and a1[2]==ctx.p_args then
          if #u[3]==1 then return true end
          if #u[3]==3 and unp(u[3][2])[1]=="Num" and unp(u[3][2])[2]==1 then
            local a3=unp(u[3][3])
            if a3[1]=="Idx" and unp(a3[2])[1]=="Var" and unp(a3[2])[2]==ctx.p_args and unp(a3[3])[1]=="Str" and a3[3][2]=="n" then return true end
          end
        end
      end
      return false
    end
    local function exp_l(es,tbl)
      local n=#es
      if n>0 then
        local t=es[n][1]
        if t=="__FWDVA__" or t=="__FWDVAF__" then
          local k0=t=="__FWDVAF__" and es[n][2] or 1
          local r={}
          for i=1,n-1 do r[i]=es[i] end
          for i=k0,nf do r[#r+1]=tbl and {"V",cp(fw[i])} or cp(fw[i]) end
          r[#r+1]=tbl and {"V",{"Vararg"}} or {"Vararg"}
          return r
        end
      end
      return es
    end
    local function rw_fw(n)
      if type(n)~="table" then return n end
      local k=n[1]
      if type(k)~="string" then
        local r={} for i=1,#n do r[i]=type(n[i])=="table" and rw_fw(n[i]) or n[i] end return r
      end
      if k=="__FWDVA__" then return {"Vararg"} end
      if k=="Idx" then
        local t,ix=unp(n[2]),unp(n[3])
        if t[1]=="Var" and t[2]==ctx.p_args then
          if ix[1]=="Num" and ix[2]>=1 then
            if ix[2]<=nf then return cp(fw[ix[2]]) end
            if va then return {"Call",{"Var","select"},{{"Num",ix[2]-nf},{"Vararg"}}} end
          elseif ix[1]=="Str" and ix[2]=="n" then
            return {"Bin","+",{"Call",{"Var","select"},{{"Str","#"},{"Vararg"}}},{"Num",nf}}
          end
        end
      elseif k=="Call" then
        if is_up(n) then return {"__FWDVA__"} end
        local fn=unp(n[2])
        if fn[1]=="Var" and fn[2]=="select" and #n[3]==2 and unp(n[3][1])[1]=="Num" and is_up(n[3][2]) then
          local idx=unp(n[3][1])[2]
          if idx>=1 and math.floor(idx)==idx then
            if idx<=nf then return {"__FWDVAF__",idx} end
            if idx==nf+1 then return va and {"__FWDVAF__",nf+1} or {"Nil"} end
            return {"Call",{"Var","select"},{{"Num",idx-nf},{"Vararg"}}}
          end
        end
        return {"Call",rw_fw(n[2]),exp_l(rw_fw(n[3]))}
      elseif k=="MCall" then return {"MCall",rw_fw(n[2]),n[3],exp_l(rw_fw(n[4]))}
      elseif k=="Return" or k=="Ret" then return {k,exp_l(rw_fw(n[2]))}
      elseif k=="Assign" then return {"Assign",rw_fw(n[2]),exp_l(rw_fw(n[3]))}
      elseif k=="LocalVar" then return {"LocalVar",n[2],exp_l(rw_fw(n[3]))}
      elseif k=="Tbl" then
        local fs=rw_fw(n[2])
        if #fs>0 and fs[#fs][1]=="V" and (fs[#fs][2][1]=="__FWDVA__" or fs[#fs][2][1]=="__FWDVAF__") then
          local k0=fs[#fs][2][1]=="__FWDVAF__" and fs[#fs][2][2] or 1
          local nr={} for i=1,#fs-1 do nr[i]=fs[i] end
          for i=k0,nf do nr[#nr+1]={"V",cp(fw[i])} end
          nr[#nr+1]={"V",{"Vararg"}}
          fs=nr
        end
        return {"Tbl",fs}
      end
      local r={k} for i=2,#n do r[i]=type(n[i])=="table" and rw_fw(n[i]) or n[i] end return r
    end
    for _,b in pairs(bs) do
      for i,s in ipairs(b.stmts) do b.stmts[i]=rw_fw(s) end
      b.term=rw_fw(b.term)
    end
    for _,req in ipairs(cls_reqs) do
      for i,u in ipairs(req.ups) do req.ups[i]=rw_fw(u) end
    end
    locs[ctx.p_args]=nil
  end
  if not va and not (not upv_map and ctx.fwds and #ctx.fwds>0) and #safe_ps>0 then
    local p_ix={}
    for i,p in ipairs(safe_ps) do p_ix[p]=i end
    local mx=0
    local function su(nd)
      A.walk(nd,function(x)
        if x[1]=="Var" and p_ix[x[2]] and p_ix[x[2]]>mx then mx=p_ix[x[2]] end
      end)
    end
    for _,b in pairs(bs) do
      for _,s in ipairs(b.stmts) do su(s) end
      su(b.term)
    end
    for _,req in ipairs(cls_reqs) do
      for _,u in ipairs(req.ups) do su(u) end
    end
    for i=mx+1,#safe_ps do locs[safe_ps[i]]=nil safe_ps[i]=nil end
  end
  local fh=match_for_loops(bs,pc0,cls_reqs)
  local blk=struct_cfg(bs,pc0,fh)
  local wr={}
  A.walk(blk,function(n)
    local k=n[1]
    if k=="Assign" then
      for _,l in ipairs(n[2]) do local u=unp(l) if u[1]=="Var" then wr[u[2]]=true end end
    elseif k=="ForNum" then wr[n[2]]=true
    elseif k=="ForIn" then for _,v in ipairs(n[2]) do wr[v]=true end
    elseif k=="LocalVar" then for _,v in ipairs(n[2]) do wr[v]=true end
    elseif k=="LocalFunc" then wr[n[2]]=true end
  end)
  for k,_ in pairs(locs) do if not wr[k] then locs[k]=nil end end
  local pset={} for _,p in ipairs(safe_ps) do pset[p]=true end
  if upv_map then for _,u in ipairs(upv_map) do if u[1]=="Var" then pset[u[2]]=true end end end
  local function ins_loc_b(b,sc_in,ext_u)
    local sc,ns,pre={}, {}, {}
    local sts_b=b[2]
    local suf_u={}
    local acc={}
    for v,_ in pairs(ext_u) do acc[v]=true end
    for i=#sts_b,1,-1 do
      local cp_u={} for v,_ in pairs(acc) do cp_u[v]=true end
      suf_u[i]=cp_u
      A.walk(sts_b[i],function(x) if x[1]=="Var" then acc[x[2]]=true elseif x[1]=="__CLS__" and cls_reqs[x[2]] then for _,u in ipairs(cls_reqs[x[2]].ups) do extract_vars_e(u,acc,cls_reqs) end end end)
    end
    local function add_vars(nd,mp)
      A.walk(nd,function(x)
        if x[1]=="Var" then mp[x[2]]=true
        elseif x[1]=="__CLS__" and cls_reqs[x[2]] then for _,u in ipairs(cls_reqs[x[2]].ups) do extract_vars_e(u,mp,cls_reqs) end end
      end)
    end
    local function loop_carried(lb,extra_e)
      local eu={} for v,_ in pairs(suf_u[1] or ext_u) do end
      local cset_u={}
      local rd_first,wr_first={},{}
      for _,ls in ipairs(lb[2]) do
        if ls[1]=="Assign" then
          for _,r in ipairs(ls[3]) do
            local rds={} extract_vars_e(r,rds,cls_reqs)
            for v,_ in pairs(rds) do if not wr_first[v] then rd_first[v]=true end end
          end
          for _,l in ipairs(ls[2]) do
            if l[1]=="Var" then if not rd_first[l[2]] then wr_first[l[2]]=true end
            else
              local rds={} extract_vars_e(l,rds,cls_reqs)
              for v,_ in pairs(rds) do if not wr_first[v] then rd_first[v]=true end end
            end
          end
        else
          local rds={} add_vars(ls,rds)
          for v,_ in pairs(rds) do if not wr_first[v] then rd_first[v]=true end end
        end
      end
      if extra_e then
        local rds={} extract_vars_e(extra_e,rds,cls_reqs)
        for v,_ in pairs(rds) do if not wr_first[v] then rd_first[v]=true end end
      end
      for v,_ in pairs(rd_first) do cset_u[v]=true end
      return cset_u
    end
    for i,s in ipairs(sts_b) do
      local k=s[1]
      if k=="Assign" then
        local all_v=true
        local nms={}
        for j,l in ipairs(s[2]) do
          if l[1]~="Var" or not locs[l[2]] or sc_in[l[2]] or sc[l[2]] or pre[l[2]] or pset[l[2]] or ext_u[l[2]] then all_v=false break end
          nms[j]=l[2]
        end
        if all_v and #nms>=1 then
          local rhs_u={}
          for _,r in ipairs(s[3]) do extract_vars_e(r,rhs_u,cls_reqs) end
          for _,nm in ipairs(nms) do if rhs_u[nm] then all_v=false break end end
        end
        if all_v and #nms>=1 then
          local seen_nm={}
          for _,nm in ipairs(nms) do
            if seen_nm[nm] then all_v=false break end
            seen_nm[nm]=true
          end
        end
        if all_v and #nms>=1 then
          for _,nm in ipairs(nms) do sc[nm]=true end
          ns[#ns+1]={"LocalVar",nms,s[3]}
        else
          ns[#ns+1]=s
        end
      elseif k=="ForNum" or k=="ForIn" or k=="While" or k=="Repeat" or k=="Do" or k=="If" then
        local eu={}
        for v,_ in pairs(pre) do eu[v]=true end
        for v,_ in pairs(suf_u[i]) do eu[v]=true end
        local sc2={} for v,_ in pairs(sc_in) do sc2[v]=true end for v,_ in pairs(sc) do sc2[v]=true end
        if k=="ForNum" then
          local eu2={} for v,_ in pairs(eu) do eu2[v]=true end
          add_vars(s[3],eu2) add_vars(s[4],eu2) if s[5] then add_vars(s[5],eu2) end
          for v,_ in pairs(loop_carried(s[6],nil)) do eu2[v]=true end
          sc2[s[2]]=true
          ns[#ns+1]={"ForNum",s[2],s[3],s[4],s[5],ins_loc_b(s[6],sc2,eu2)}
        elseif k=="ForIn" then
          local eu2={} for v,_ in pairs(eu) do eu2[v]=true end
          for _,e in ipairs(s[3]) do add_vars(e,eu2) end
          for v,_ in pairs(loop_carried(s[4],nil)) do eu2[v]=true end
          for _,vn in ipairs(s[2]) do sc2[vn]=true end
          ns[#ns+1]={"ForIn",s[2],s[3],ins_loc_b(s[4],sc2,eu2)}
        elseif k=="While" then
          local eu2={} for v,_ in pairs(eu) do eu2[v]=true end
          add_vars(s[2],eu2)
          for v,_ in pairs(loop_carried(s[3],s[2])) do eu2[v]=true end
          ns[#ns+1]={"While",s[2],ins_loc_b(s[3],sc2,eu2)}
        elseif k=="Repeat" then
          local eu2={} for v,_ in pairs(eu) do eu2[v]=true end
          for v,_ in pairs(loop_carried(s[2],s[3])) do eu2[v]=true end
          ns[#ns+1]={"Repeat",ins_loc_b(s[2],sc2,eu2),s[3]}
        elseif k=="Do" then
          ns[#ns+1]={"Do",ins_loc_b(s[2],sc2,eu)}
        elseif k=="If" then
          local eu2={} for v,_ in pairs(eu) do eu2[v]=true end
          for _,br in ipairs(s[2]) do add_vars(br[1],eu2) end
          local ncs={}
          for bi,br in ipairs(s[2]) do
            local eu3={} for v,_ in pairs(eu2) do eu3[v]=true end
            for bj,br2 in ipairs(s[2]) do if bj~=bi then add_vars(br2[2],eu3) end end
            if s[3] then add_vars(s[3],eu3) end
            ncs[bi]={br[1],ins_loc_b(br[2],sc2,eu3)}
          end
          local nels=false
          if s[3] then
            local eu3={} for v,_ in pairs(eu2) do eu3[v]=true end
            for _,br in ipairs(s[2]) do add_vars(br[2],eu3) end
            nels=ins_loc_b(s[3],sc2,eu3)
          end
          ns[#ns+1]={"If",ncs,nels}
        end
      else
        ns[#ns+1]=s
      end
      add_vars(s,pre)
    end
    local rem={}
    local unb={}
    local function cp_s(s) local r={} for k,v in pairs(s) do r[k]=v end return r end
    local function sc_n(nd,bnd)
      if type(nd)~="table" then return end
      local k=nd[1]
      if type(k)~="string" then for _,x in ipairs(nd) do sc_n(x,bnd) end return end
      if k=="Var" then
        if not bnd[nd[2]] then unb[nd[2]]=true end
      elseif k=="Block" then
        local b2=cp_s(bnd)
        for _,st in ipairs(nd[2]) do sc_n(st,b2) end
      elseif k=="Do" then
        sc_n(nd[2],cp_s(bnd))
      elseif k=="While" then
        sc_n(nd[2],bnd) sc_n(nd[3],cp_s(bnd))
      elseif k=="Repeat" then
        local b2=cp_s(bnd)
        for _,st in ipairs(nd[2][2]) do sc_n(st,b2) end
        sc_n(nd[3],b2)
      elseif k=="If" then
        for _,br in ipairs(nd[2]) do sc_n(br[1],bnd) sc_n(br[2],cp_s(bnd)) end
        if nd[3] then sc_n(nd[3],cp_s(bnd)) end
      elseif k=="ForNum" then
        sc_n(nd[3],bnd) sc_n(nd[4],bnd) sc_n(nd[5],bnd)
        local b2=cp_s(bnd) b2[nd[2]]=true sc_n(nd[6],b2)
      elseif k=="ForIn" then
        sc_n(nd[3],bnd)
        local b2=cp_s(bnd) for _,v in ipairs(nd[2]) do b2[v]=true end sc_n(nd[4],b2)
      elseif k=="LocalVar" then
        sc_n(nd[3],bnd)
        for _,v in ipairs(nd[2]) do bnd[v]=true end
      elseif k=="LocalFunc" then
        bnd[nd[2]]=true
        local b2=cp_s(bnd) for _,p in ipairs(nd[3]) do b2[p]=true end sc_n(nd[5],b2)
      elseif k=="Func" then
        local b2=cp_s(bnd) for _,p in ipairs(nd[2]) do b2[p]=true end sc_n(nd[4],b2)
      else
        for i=2,#nd do sc_n(nd[i],bnd) end
      end
    end
    local b0={}
    for v,_ in pairs(sc_in) do b0[v]=true end
    for v,_ in pairs(sc) do b0[v]=true end
    for _,st in ipairs(ns) do sc_n(st,b0) end
    local seen_r={}
    for nm,_ in pairs(pre) do
      if locs[nm] and not sc_in[nm] and not sc[nm] and not pset[nm] and not ext_u[nm] and unb[nm] then
        if not seen_r[nm] then seen_r[nm]=true rem[#rem+1]=nm end
      end
    end
    if not next(sc_in) then
      for _,req in ipairs(cls_reqs) do
        for _,u in ipairs(req.ups) do
          if u[1]=="Var" and locs[u[2]] and not pre[u[2]] and not sc[u[2]] and not pset[u[2]] and not seen_r[u[2]] then
            seen_r[u[2]]=true rem[#rem+1]=u[2]
          end
        end
      end
    end
    if va and not sc_in[ctx.p_args] and not sc[ctx.p_args] and (pre[ctx.p_args] or seen_r[ctx.p_args]) then
      local nrem={}
      for _,v in ipairs(rem) do if v~=ctx.p_args then nrem[#nrem+1]=v end end
      rem=nrem
      table.sort(rem)
      for k=1,#rem,50 do
        local sub={}
        for j=k,math.min(k+49,#rem) do sub[#sub+1]=rem[j] end
        table.insert(ns,1,{"LocalVar",sub,{}})
      end
      local avs={}
      for _,sp in ipairs(safe_ps) do avs[#avs+1]={"V",{"Var",sp}} end
      avs[#avs+1]={"V",{"Vararg"}}
      table.insert(ns,1,{"LocalVar",{ctx.p_args},{{"Tbl",avs}}})
    else
      table.sort(rem)
      for k=1,#rem,50 do
        local sub={}
        for j=k,math.min(k+49,#rem) do sub[#sub+1]=rem[j] end
        table.insert(ns,1,{"LocalVar",sub,{}})
      end
    end
    return {"Block",ns}
  end
  blk=ins_loc_b(blk,{},{})
  if ctx.pack_fn and not (ctx.mf_locs and ctx.mf_locs[ctx.pack_fn]) then
    local pk=ctx.pack_fn
    local function rw_pk(e,sh)
      if type(e)~="table" then return e end
      local k=e[1]
      if k=="Call" and not sh and unp(e[2])[1]=="Var" and unp(e[2])[2]==pk then
        local args={}
        for i,a in ipairs(e[3]) do args[i]=rw_pk(a,sh) end
        if #args==0 then return {"Tbl",{{"F","n",{"Num",0}}}} end
        local n_as={{"Str","#"}}
        for _,a in ipairs(args) do n_as[#n_as+1]=cp(a) end
        local fs={{"F","n",{"Call",{"Var","select"},n_as}}}
        for _,a in ipairs(args) do fs[#fs+1]={"V",a} end
        return {"Tbl",fs}
      elseif k=="Block" then
        local sh2=sh
        local ns={}
        for i,st in ipairs(e[2]) do
          ns[i]=rw_pk(st,sh2)
          if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do if nm==pk then sh2=true end end
          elseif st[1]=="LocalFunc" and st[2]==pk then sh2=true end
        end
        return {"Block",ns}
      elseif k=="Func" then
        local sh2=sh
        for _,p in ipairs(e[2]) do if p==pk then sh2=true end end
        return {"Func",e[2],e[3],rw_pk(e[4],sh2)}
      elseif type(k)~="string" then
        local r={} for i=1,#e do r[i]=rw_pk(e[i],sh) end return r
      end
      local r={k} for i=2,#e do r[i]=rw_pk(e[i],sh) end return r
    end
    blk=rw_pk(blk,false)
  end
  if #cls_reqs>0 then
    local cls_fn={}
    for cid,req in ipairs(cls_reqs) do
      local cblk,cps=ext_closure(ctx,req.pc,req.ps,req.va,req.ups)
      cls_fn[cid]={"Func",cps,req.va,cblk}
    end
    local function r_cls(e)
      if type(e)~="table" then return e end
      if e[1]=="__CLS__" then return cls_fn[e[2]] end
      local r={} for i=1,#e do r[i]=r_cls(e[i]) end
      return r
    end
    blk=r_cls(blk)
  end
  local sts=blk[2]
  local function is_eu(e)
    local u=unp(e)
    if u[1]~="Call" then return false end
    local fn=unp(u[2])
    if not ((fn[1]=="Var" or fn[1]=="GVar") and fn[2]=="unpack" and #u[3]>=1) then return false end
    local t=unp(u[3][1])
    return t[1]=="Tbl" and #t[2]==0
  end
  for i=1,#sts do
    if sts[i][1]=="Return" and #sts[i][2]==1 and is_eu(sts[i][2][1]) then sts[i]={"Return",{}} end
  end
  if #sts>0 and sts[#sts][1]=="Return" and #sts[#sts][2]==0 then
    table.remove(sts,#sts)
  end
  return blk,safe_ps
end
local function ext_fwd(e)
  local fn=unp(e[2])
  if fn[1]=="Func" and fn[3] and #fn[4][2]==1 and fn[4][2][1][1]=="Return" and #fn[4][2][1][2]==1 then
    local inn=unp(fn[4][2][1][2][1])
    if inn[1]=="Call" and (#fn[2]>0 or (#e[3]>0 and unp(e[3][#e[3]])[1]=="Vararg")) then
      local fw={}
      if #fn[2]>0 then for i=1,math.min(#fn[2],#e[3]) do fw[i]=e[3][i] end
      else for i=1,#e[3]-1 do fw[i]=e[3][i] end end
      return inn,fw
    end
  end
  return nil
end
local function unwrap_cff_call(e)
  e=unp(e)
  if e[1]~="Call" then return nil end
  local fn=unp(e[2])
  local ctx=parse_ctx(fn,e[3])
  if not ctx then
    local inn,fw=ext_fwd(e)
    if inn then
      ctx=parse_ctx(unp(inn[2]),inn[3])
      if ctx then ctx.fwds=fw end
    end
  end
  if not ctx then return nil end
  local ps={}
  local va=true
  if ctx.top_mk then ps=ctx.top_mk.ps va=ctx.top_mk.va end
  local b,sps=ext_closure(ctx,ctx.init_pc,ps,va,nil)
  if ctx.top_env and next(ctx.top_env) then
    local td={}
    local function cpb(s) local r={} for k,v in pairs(s) do r[k]=v end return r end
    local function sc_te(nd,bnd)
      if type(nd)~="table" then return end
      local k=nd[1]
      if type(k)~="string" then for _,x in ipairs(nd) do sc_te(x,bnd) end return end
      if k=="Var" then
        if not bnd[nd[2]] and ctx.top_env[nd[2]] then td[nd[2]]=true end
      elseif k=="GVar" then
      elseif k=="Block" then
        local b2=cpb(bnd)
        for _,st in ipairs(nd[2]) do sc_te(st,b2) end
      elseif k=="Do" then sc_te(nd[2],cpb(bnd))
      elseif k=="While" then sc_te(nd[2],bnd) sc_te(nd[3],cpb(bnd))
      elseif k=="Repeat" then
        local b2=cpb(bnd)
        for _,st in ipairs(nd[2][2]) do sc_te(st,b2) end
        sc_te(nd[3],b2)
      elseif k=="If" then
        for _,br in ipairs(nd[2]) do sc_te(br[1],bnd) sc_te(br[2],cpb(bnd)) end
        if nd[3] then sc_te(nd[3],cpb(bnd)) end
      elseif k=="ForNum" then
        sc_te(nd[3],bnd) sc_te(nd[4],bnd) sc_te(nd[5],bnd)
        local b2=cpb(bnd) b2[nd[2]]=true sc_te(nd[6],b2)
      elseif k=="ForIn" then
        sc_te(nd[3],bnd)
        local b2=cpb(bnd) for _,v in ipairs(nd[2]) do b2[v]=true end sc_te(nd[4],b2)
      elseif k=="LocalVar" then
        sc_te(nd[3],bnd)
        for _,v in ipairs(nd[2]) do bnd[v]=true end
      elseif k=="LocalFunc" then
        bnd[nd[2]]=true
        local b2=cpb(bnd) for _,p in ipairs(nd[3]) do b2[p]=true end sc_te(nd[5],b2)
      elseif k=="Func" then
        local b2=cpb(bnd) for _,p in ipairs(nd[2]) do b2[p]=true end sc_te(nd[4],b2)
      else
        for i=2,#nd do sc_te(nd[i],bnd) end
      end
    end
    local b0={} for _,p in ipairs(sps) do b0[p]=true end
    sc_te(b,b0)
    local ks={}
    for k,_ in pairs(td) do ks[#ks+1]=k end
    table.sort(ks)
    for k=#ks,1,-1 do
      table.insert(b[2],1,{"LocalVar",{ks[k]},{cp(ctx.top_env[ks[k]])}})
    end
  end
  local function lv_gv(nd)
    if type(nd)~="table" then return nd end
    if nd[1]=="GVar" then return {"Var",nd[2]} end
    local r={}
    for i=1,#nd do r[i]=lv_gv(nd[i]) end
    return r
  end
  b=lv_gv(b)
  if ctx.top_call or not ctx.top_mk then
    return b
  end
  return {"Func",sps,va,b}
end
function M.inv_cff(ast,fold)
  local chg=false
  local function rw_b(b)
    local ns={}
    local function rw_e(e)
      local k=e[1]
      if k=="Call" then
        local r=unwrap_cff_call(e)
        if r and r[1]=="Func" then chg=true return r end
        local as={} for i,a in ipairs(e[3]) do as[i]=rw_e(a) end
        return {"Call",rw_e(e[2]),as}
      elseif k=="Func" then return {"Func",e[2],e[3],rw_b(e[4])}
      elseif k=="Paren" then return {"Paren",rw_e(e[2])}
      elseif k=="Un" then return {"Un",e[2],rw_e(e[3])}
      elseif k=="Bin" then return {"Bin",e[2],rw_e(e[3]),rw_e(e[4])}
      elseif k=="Idx" then return {"Idx",rw_e(e[2]),rw_e(e[3])}
      elseif k=="Field" then return {"Field",rw_e(e[2]),e[3]}
      elseif k=="MCall" then
        local as={} for i,a in ipairs(e[4]) do as[i]=rw_e(a) end
        return {"MCall",rw_e(e[2]),e[3],as}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(e[2]) do
          if f[1]=="V" then fs[i]={"V",rw_e(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],rw_e(f[3])}
          else fs[i]={"I",rw_e(f[2]),rw_e(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local cs={} for i,c in ipairs(e[2]) do cs[i]={rw_e(c[1]),rw_e(c[2])} end
        return {"IfExpr",cs,rw_e(e[3])}
      end
      return e
    end
    for _,s in ipairs(b[2]) do
      local k=s[1]
      if k=="Return" and #s[2]==1 then
        local r=unwrap_cff_call(s[2][1])
        if r and r[1]=="Block" then
          chg=true
          for _,bs in ipairs(r[2]) do ns[#ns+1]=bs end
        elseif r and r[1]=="Func" then
          chg=true
          ns[#ns+1]={"Return",{r}}
        else
          ns[#ns+1]={"Return",{rw_e(s[2][1])}}
        end
      elseif k=="CallStmt" then
        local r=unwrap_cff_call(s[2])
        if r and r[1]=="Block" then
          chg=true
          for _,bs in ipairs(r[2]) do ns[#ns+1]=bs end
        else
          ns[#ns+1]={"CallStmt",rw_e(s[2])}
        end
      elseif k=="LocalFunc" then ns[#ns+1]={"LocalFunc",s[2],s[3],s[4],rw_b(s[5])}
      elseif k=="FuncStmt" then ns[#ns+1]={"FuncStmt",rw_e(s[2]),s[3],s[4],s[5],rw_b(s[6])}
      elseif k=="Do" then ns[#ns+1]={"Do",rw_b(s[2])}
      elseif k=="While" then ns[#ns+1]={"While",rw_e(s[2]),rw_b(s[3])}
      elseif k=="Repeat" then ns[#ns+1]={"Repeat",rw_b(s[2]),rw_e(s[3])}
      elseif k=="If" then
        local cs={} for i,c in ipairs(s[2]) do cs[i]={rw_e(c[1]),rw_b(c[2])} end
        ns[#ns+1]={"If",cs,s[3] and rw_b(s[3]) or false}
      elseif k=="ForNum" then ns[#ns+1]={"ForNum",s[2],rw_e(s[3]),rw_e(s[4]),s[5] and rw_e(s[5]) or false,rw_b(s[6])}
      elseif k=="ForIn" then
        local es={} for i,e in ipairs(s[3]) do es[i]=rw_e(e) end
        ns[#ns+1]={"ForIn",s[2],es,rw_b(s[4])}
      elseif k=="LocalVar" then
        local vs={} for i,v in ipairs(s[3]) do vs[i]=rw_e(v) end
        ns[#ns+1]={"LocalVar",s[2],vs}
      elseif k=="Assign" then
        local ls,rs={},{}
        for i,l in ipairs(s[2]) do ls[i]=rw_e(l) end
        for i,r in ipairs(s[3]) do rs[i]=rw_e(r) end
        ns[#ns+1]={"Assign",ls,rs}
      else ns[#ns+1]=s end
    end
    return {"Block",ns}
  end
  local cur=M_misc.inv_pool(fold and fold(ast) or ast)
  for _=1,12 do
    chg=false
    local nxt=rw_b(cur)
    if not chg then break end
    cur=M_misc.inv_pool(fold and fold(nxt) or nxt)
  end
  return fold and fold(cur) or cur
end
return M
