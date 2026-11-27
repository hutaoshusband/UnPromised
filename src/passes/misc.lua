local A=require("src.frontend.ast")
local S=require("src.frontend.scope")
local M={}
local unp=A.unp
local MM={__add="+",__sub="-",__mul="*",__div="/",__mod="%",__pow="^",__concat="..",__idiv="//",__index="IDX"}
local PURE_V={setmetatable=1,getmetatable=1,unpack=1,newproxy=1,getfenv=1,select=1,tostring=1,tonumber=1,type=1,pairs=1,ipairs=1,next=1,math=1,string=1,table=1,coroutine=1,_ENV=1,_G=1}
local KW_M={["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,["false"]=1,["for"]=1,["function"]=1,["if"]=1,["in"]=1,["local"]=1,["nil"]=1,["not"]=1,["or"]=1,["repeat"]=1,["return"]=1,["then"]=1,["true"]=1,["until"]=1,["while"]=1}
local function is_id(s) return type(s)=="string" and s:match("^[%a_][%w_]*$")~=nil and not KW_M[s] end
local function is_env_e(e,sh)
  e=unp(e)
  if e[1]=="Var" then return (e[2]=="_ENV" or e[2]=="_G") and not sh[e[2]]
  elseif e[1]=="Call" and #e[3]==0 then
    local f=unp(e[2])
    return f[1]=="Var" and f[2]=="getfenv" and not sh.getfenv
  elseif e[1]=="Bin" and (e[2]=="and" or e[2]=="or") then
    local l=unp(e[3])
    local lok=is_env_e(l,sh) or (l[1]=="Var" and l[2]=="getfenv" and not sh.getfenv)
    return lok and is_env_e(e[4],sh)
  end
  return false
end
local function norm_env(ast)
  local function cps(sh) local r={} for k,v in pairs(sh) do r[k]=v end return r end
  local nb,ns,ne
  ne=function(e,sh)
    if type(e)~="table" then return e end
    local k=e[1]
    if k=="Idx" then
      local b,kx=ne(e[2],sh),ne(e[3],sh)
      local uk=unp(kx)
      if is_env_e(b,sh) and uk[1]=="Str" and is_id(uk[2]) and not sh[uk[2]] then
        return {"Var",uk[2]}
      end
      return {"Idx",b,kx}
    elseif k=="Field" then
      local b=ne(e[2],sh)
      if is_env_e(b,sh) and is_id(e[3]) and not sh[e[3]] then
        return {"Var",e[3]}
      end
      return {"Field",b,e[3]}
    elseif k=="Func" then
      local s2=cps(sh) for _,p in ipairs(e[2]) do s2[p]=true end
      return {"Func",e[2],e[3],nb(e[4],s2)}
    elseif k=="Paren" then return {"Paren",ne(e[2],sh)}
    elseif k=="Un" then return {"Un",e[2],ne(e[3],sh)}
    elseif k=="Bin" then return {"Bin",e[2],ne(e[3],sh),ne(e[4],sh)}
    elseif k=="Call" then
      local as={} for i,a in ipairs(e[3]) do as[i]=ne(a,sh) end
      return {"Call",ne(e[2],sh),as}
    elseif k=="MCall" then
      local as={} for i,a in ipairs(e[4]) do as[i]=ne(a,sh) end
      return {"MCall",ne(e[2],sh),e[3],as}
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
    end
    return e
  end
  ns=function(s,sh)
    local k=s[1]
    if k=="LocalVar" then
      local vs={} for i,v in ipairs(s[3]) do vs[i]=ne(v,sh) end
      return {"LocalVar",s[2],vs}
    elseif k=="LocalFunc" then
      local s2=cps(sh) s2[s[2]]=true for _,p in ipairs(s[3]) do s2[p]=true end
      return {"LocalFunc",s[2],s[3],s[4],nb(s[5],s2)}
    elseif k=="FuncStmt" then
      local s2=cps(sh) for _,p in ipairs(s[4]) do s2[p]=true end if s[3] then s2.self=true end
      return {"FuncStmt",ne(s[2],sh),s[3],s[4],s[5],nb(s[6],s2)}
    elseif k=="Assign" then
      local ls,rs={},{}
      for i,l in ipairs(s[2]) do ls[i]=ne(l,sh) end
      for i,r in ipairs(s[3]) do rs[i]=ne(r,sh) end
      return {"Assign",ls,rs}
    elseif k=="CAssign" then return {"CAssign",s[2],ne(s[3],sh),ne(s[4],sh)}
    elseif k=="Do" then return {"Do",nb(s[2],cps(sh))}
    elseif k=="While" then return {"While",ne(s[2],sh),nb(s[3],cps(sh))}
    elseif k=="Repeat" then
      local b2,s2=nb(s[2],cps(sh)),cps(sh)
      for _,st in ipairs(s[2][2]) do
        if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
        elseif st[1]=="LocalFunc" then s2[st[2]]=true end
      end
      return {"Repeat",b2,ne(s[3],s2)}
    elseif k=="If" then
      local cs={} for i,c in ipairs(s[2]) do cs[i]={ne(c[1],sh),nb(c[2],cps(sh))} end
      return {"If",cs,s[3] and nb(s[3],cps(sh)) or false}
    elseif k=="ForNum" then
      local s2=cps(sh) s2[s[2]]=true
      return {"ForNum",s[2],ne(s[3],sh),ne(s[4],sh),s[5] and ne(s[5],sh) or false,nb(s[6],s2)}
    elseif k=="ForIn" then
      local es={} for i,e in ipairs(s[3]) do es[i]=ne(e,sh) end
      local s2=cps(sh) for _,v in ipairs(s[2]) do s2[v]=true end
      return {"ForIn",s[2],es,nb(s[4],s2)}
    elseif k=="Return" then
      local es={} for i,e in ipairs(s[2]) do es[i]=ne(e,sh) end
      return {"Return",es}
    elseif k=="CallStmt" then return {"CallStmt",ne(s[2],sh)}
    end
    return s
  end
  nb=function(b,sh)
    local s2=cps(sh)
    local out={}
    for i,s in ipairs(b[2]) do
      out[i]=ns(s,s2)
      if s[1]=="LocalVar" then for _,nm in ipairs(s[2]) do s2[nm]=true end
      elseif s[1]=="LocalFunc" then s2[s[2]]=true end
    end
    return {"Block",out}
  end
  return nb(ast,{})
end
local function uv_e(e,nm)
  if type(e)~="table" then return false end
  local k=e[1]
  if k=="Var" then return e[2]==nm
  elseif k=="Paren" or k=="Un" then return uv_e(e[2],nm) or (k=="Un" and uv_e(e[3],nm))
  elseif k=="Bin" then return uv_e(e[3],nm) or uv_e(e[4],nm)
  elseif k=="Idx" then return uv_e(e[2],nm) or uv_e(e[3],nm)
  elseif k=="Field" then return uv_e(e[2],nm)
  elseif k=="Call" then
    if uv_e(e[2],nm) then return true end
    for _,a in ipairs(e[3]) do if uv_e(a,nm) then return true end end
  elseif k=="MCall" then
    if uv_e(e[2],nm) then return true end
    for _,a in ipairs(e[4]) do if uv_e(a,nm) then return true end end
  elseif k=="Tbl" then
    for _,f in ipairs(e[2]) do
      if f[1]=="V" then if uv_e(f[2],nm) then return true end
      elseif f[1]=="F" then if uv_e(f[3],nm) then return true end
      else if uv_e(f[2],nm) or uv_e(f[3],nm) then return true end end
    end
  elseif k=="IfExpr" then
    for _,c in ipairs(e[2]) do if uv_e(c[1],nm) or uv_e(c[2],nm) then return true end end
    return uv_e(e[3],nm)
  elseif k=="Func" then
    for _,p in ipairs(e[2]) do if p==nm then return false end end
    return M.has_use(e[4][2],1,nm)
  end
  return false
end
local function inl(ls,nm)
  for _,v in ipairs(ls) do if v==nm then return true end end
  return false
end
function M.has_use(sts,i0,nm)
  for i=i0,#sts do
    local s=sts[i]
    local k=s[1]
    if k=="LocalVar" then
      for _,v in ipairs(s[3]) do if uv_e(v,nm) then return true end end
      if inl(s[2],nm) then return false end
    elseif k=="LocalFunc" then
      if s[2]==nm then return false end
      if not inl(s[3],nm) and M.has_use(s[5][2],1,nm) then return true end
    elseif k=="FuncStmt" then
      if uv_e(s[2],nm) then return true end
      if not inl(s[4],nm) and not (s[3] and nm=="self") and M.has_use(s[6][2],1,nm) then return true end
    elseif k=="Assign" then
      for _,l in ipairs(s[2]) do if uv_e(l,nm) then return true end end
      for _,r in ipairs(s[3]) do if uv_e(r,nm) then return true end end
    elseif k=="CAssign" then
      if uv_e(s[3],nm) or uv_e(s[4],nm) then return true end
    elseif k=="Do" then
      if M.has_use(s[2][2],1,nm) then return true end
    elseif k=="While" then
      if uv_e(s[2],nm) or M.has_use(s[3][2],1,nm) then return true end
    elseif k=="Repeat" then
      if M.has_use(s[2][2],1,nm) then return true end
      local sh=false
      for _,st in ipairs(s[2][2]) do
        if st[1]=="LocalVar" and inl(st[2],nm) then sh=true
        elseif st[1]=="LocalFunc" and st[2]==nm then sh=true end
      end
      if not sh and uv_e(s[3],nm) then return true end
    elseif k=="If" then
      for _,c in ipairs(s[2]) do
        if uv_e(c[1],nm) or M.has_use(c[2][2],1,nm) then return true end
      end
      if s[3] and M.has_use(s[3][2],1,nm) then return true end
    elseif k=="ForNum" then
      if uv_e(s[3],nm) or uv_e(s[4],nm) or (s[5] and uv_e(s[5],nm)) then return true end
      if s[2]~=nm and M.has_use(s[6][2],1,nm) then return true end
    elseif k=="ForIn" then
      for _,e in ipairs(s[3]) do if uv_e(e,nm) then return true end end
      if not inl(s[2],nm) and M.has_use(s[4][2],1,nm) then return true end
    elseif k=="Return" then
      for _,e in ipairs(s[2]) do if uv_e(e,nm) then return true end end
    elseif k=="CallStmt" then
      if uv_e(s[2],nm) then return true end
    end
  end
  return false
end
local function pure_e(e)
  e=unp(e)
  local k=e[1]
  if k=="Nil" or k=="Bool" or k=="Num" or k=="Str" or k=="Func" then return true end
  if k=="Var" and PURE_V[e[2]] then return true end
  if k=="Field" then return pure_e(e[2]) end
  if k=="Un" then return pure_e(e[3]) end
  if k=="Bin" then return pure_e(e[3]) and pure_e(e[4]) end
  if k=="Call" and #e[3]==0 then
    local f=unp(e[2])
    if f[1]=="Var" and f[2]=="getfenv" then return true end
  end
  if k=="Tbl" then
    for _,f in ipairs(e[2]) do
      if f[1]=="V" then if not pure_e(f[2]) then return false end
      elseif f[1]=="F" then if not pure_e(f[3]) then return false end
      else if not pure_e(f[2]) or not pure_e(f[3]) then return false end end
    end
    return true
  end
  return false
end
local function map_blk(n,fn)
  local function me(e)
    local k=e[1]
    if k=="Func" then return {"Func",e[2],e[3],fn(map_blk(e[4],fn))}
    elseif k=="Paren" then return {"Paren",me(e[2])}
    elseif k=="Un" then return {"Un",e[2],me(e[3])}
    elseif k=="Bin" then return {"Bin",e[2],me(e[3]),me(e[4])}
    elseif k=="Idx" then return {"Idx",me(e[2]),me(e[3])}
    elseif k=="Field" then return {"Field",me(e[2]),e[3]}
    elseif k=="Call" then
      local as={} for i,a in ipairs(e[3]) do as[i]=me(a) end
      return {"Call",me(e[2]),as}
    elseif k=="MCall" then
      local as={} for i,a in ipairs(e[4]) do as[i]=me(a) end
      return {"MCall",me(e[2]),e[3],as}
    elseif k=="Tbl" then
      local fs={}
      for i,f in ipairs(e[2]) do
        if f[1]=="V" then fs[i]={"V",me(f[2])}
        elseif f[1]=="F" then fs[i]={"F",f[2],me(f[3])}
        else fs[i]={"I",me(f[2]),me(f[3])} end
      end
      return {"Tbl",fs}
    elseif k=="IfExpr" then
      local cs={} for i,c in ipairs(e[2]) do cs[i]={me(c[1]),me(c[2])} end
      return {"IfExpr",cs,me(e[3])}
    end
    return e
  end
  local function ms(s)
    local k=s[1]
    if k=="LocalVar" then
      local vs={} for i,v in ipairs(s[3]) do vs[i]=me(v) end
      return {"LocalVar",s[2],vs}
    elseif k=="LocalFunc" then return {"LocalFunc",s[2],s[3],s[4],fn(map_blk(s[5],fn))}
    elseif k=="FuncStmt" then return {"FuncStmt",me(s[2]),s[3],s[4],s[5],fn(map_blk(s[6],fn))}
    elseif k=="Assign" then
      local ls,rs={},{}
      for i,l in ipairs(s[2]) do ls[i]=me(l) end
      for i,r in ipairs(s[3]) do rs[i]=me(r) end
      return {"Assign",ls,rs}
    elseif k=="CAssign" then return {"CAssign",s[2],me(s[3]),me(s[4])}
    elseif k=="Do" then return {"Do",fn(map_blk(s[2],fn))}
    elseif k=="While" then return {"While",me(s[2]),fn(map_blk(s[3],fn))}
    elseif k=="Repeat" then return {"Repeat",fn(map_blk(s[2],fn)),me(s[3])}
    elseif k=="If" then
      local cs={} for i,c in ipairs(s[2]) do cs[i]={me(c[1]),fn(map_blk(c[2],fn))} end
      return {"If",cs,s[3] and fn(map_blk(s[3],fn)) or false}
    elseif k=="ForNum" then
      return {"ForNum",s[2],me(s[3]),me(s[4]),s[5] and me(s[5]) or false,fn(map_blk(s[6],fn))}
    elseif k=="ForIn" then
      local es={} for i,e in ipairs(s[3]) do es[i]=me(e) end
      return {"ForIn",s[2],es,fn(map_blk(s[4],fn))}
    elseif k=="Return" then
      local es={} for i,e in ipairs(s[2]) do es[i]=me(e) end
      return {"Return",es}
    elseif k=="CallStmt" then return {"CallStmt",me(s[2])}
    end
    return s
  end
  local ns={}
  for i,s in ipairs(n[2]) do ns[i]=ms(s) end
  return fn({"Block",ns})
end
local function is_va_tbl(e)
  e=unp(e)
  return e[1]=="Tbl" and #e[2]==1 and e[2][1][1]=="V" and unp(e[2][1][2])[1]=="Vararg"
end
local function is_unp_e(e)
  e=unp(e)
  if e[1]=="Var" and e[2]=="unpack" then return true end
  if e[1]=="Bin" and e[2]=="or" and unp(e[3])[1]=="Var" and unp(e[3])[2]=="unpack" then
    local r=unp(e[4])
    if (r[1]=="Field" and unp(r[2])[1]=="Var" and unp(r[2])[2]=="table" and r[3]=="unpack") or (r[1]=="Idx" and unp(r[2])[1]=="Var" and unp(r[2])[2]=="table" and unp(r[3])[1]=="Str" and unp(r[3])[2]=="unpack") then
      return true
    end
  end
  return false
end
local function unwrap_b(b)
  local cur=b
  for _=1,8 do
    local sts=cur[2]
    if #sts==1 and sts[1][1]=="Return" and #sts[1][2]==1 then
      local e=unp(sts[1][2][1])
      if e[1]=="Call" and #e[3]==1 and e[3][1][1]=="Vararg" then
        local fn=unp(e[2])
        if fn[1]=="Func" and #fn[2]==0 and fn[3]==true then
          cur=fn[4]
        else break end
      else break end
    elseif #sts>=2 and #sts<=8 and sts[#sts][1]=="Return" and #sts[#sts][2]==1 then
      local rc=unp(sts[#sts][2][1])
      local fnm=rc[1]=="Call" and #rc[3]==1 and unp(rc[2])[1]=="Var" and unp(rc[2])[2] or nil
      local ua=fnm and unp(rc[3][1]) or nil
      if fnm and ua[1]=="Call" and #ua[3]==1 and unp(ua[2])[1]=="Var" and unp(ua[3][1])[1]=="Var" then
        local hnm,anm=unp(ua[2])[2],unp(ua[3][1])[2]
        local locs,vals={},{}
        local ok=true
        for i=1,#sts-1 do
          local s=sts[i]
          if s[1]=="LocalVar" then
            for j,nm in ipairs(s[2]) do locs[nm]=true vals[nm]=s[3][j] end
          elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" and locs[unp(s[2][1])[2]] then
            vals[unp(s[2][1])[2]]=s[3][1]
          elseif s[1]=="LocalFunc" then
            locs[s[2]]=true vals[s[2]]={"Func",s[3],s[4],s[5]}
          else ok=false break end
        end
        local function res(x)
          local s={}
          while x and unp(x)[1]=="Var" and vals[unp(x)[2]] and not s[unp(x)[2]] do
            s[unp(x)[2]]=true x=vals[unp(x)[2]]
          end
          return x and unp(x)
        end
        local fn=ok and locs[fnm] and res(vals[fnm])
        local un=ok and locs[hnm] and res(vals[hnm])
        local av=ok and locs[anm] and res(vals[anm])
        if fn and fn[1]=="Func" and #fn[2]==0 and fn[3]==true and un and is_unp_e(un) and av and is_va_tbl(av) then
          local used,kh=false,false
          for nm,_ in pairs(locs) do
            if M.has_use(fn[4][2],1,nm) then
              if nm==hnm and not locs["unpack"] and not locs["table"] then kh=true
              else used=true break end
            end
          end
          if not used then
            if kh then
              local nb={{"LocalVar",{hnm},{un}}}
              for _,st in ipairs(fn[4][2]) do nb[#nb+1]=st end
              cur={"Block",nb}
            else cur=fn[4] end
          else break end
        else break end
      else break end
    else break end
  end
  return cur
end
function M.inv_wrap(ast)
  return map_blk(ast,unwrap_b)
end
local function wm_gsub_gv(s)
  if s[1]~="CallStmt" then return nil end
  local mc=unp(s[2])
  if mc[1]~="MCall" or mc[3]~="gsub" or #mc[4]~=2 then return nil end
  local b0,p1,p2=unp(mc[2]),unp(mc[4][1]),unp(mc[4][2])
  if b0[1]~="Str" or b0[2]=="" or p1[1]~="Str" or p1[2]~=".+" or p2[1]~="Func" or #p2[2]~=1 then return nil end
  local fb=p2[4][2]
  if #fb~=1 or fb[1][1]~="Assign" or #fb[1][2]~=1 or #fb[1][3]~=1 then return nil end
  local gv,rv=unp(fb[1][2][1]),unp(fb[1][3][1])
  if gv[1]~="Var" or rv[1]~="Var" or rv[2]~=p2[2][1] then return nil end
  return gv[2],b0[2]
end
local function is_ret0(b)
  local bs=b[2]
  return #bs==1 and bs[1][1]=="Return" and #bs[1][2]==0
end
local function wm_pure(e)
  if type(e)~="table" then return true end
  local k=e[1]
  if k=="Nil" or k=="Bool" or k=="Num" or k=="Str" or k=="Var" or k=="Vararg" or k=="Func" then return true
  elseif k=="Paren" then return wm_pure(e[2])
  elseif k=="Tbl" then
    for _,f in ipairs(e[2]) do
      if f[1]=="V" then if not wm_pure(f[2]) then return false end
      elseif f[1]=="F" then if not wm_pure(f[3]) then return false end
      else if not wm_pure(f[2]) or not wm_pure(f[3]) then return false end end
    end
    return true
  end
  return false
end
local function wm_safe(s,gv)
  local k=s[1]
  if k=="LocalVar" then
    if inl(s[2],gv) then return false end
    for _,v in ipairs(s[3]) do if not wm_pure(v) then return false end end
  elseif k=="LocalFunc" then
    if s[2]==gv then return false end
  else return false end
  return not M.has_use({s},1,gv)
end
local function is_wm_if(s,gv,sv)
  if s[1]~="If" or #s[2]~=1 then return false end
  local c,tb,eb=unp(s[2][1][1]),s[2][1][2],s[3]
  if c[1]~="Bin" then return false end
  local l,r=unp(c[3]),unp(c[4])
  local m1=l[1]=="Var" and l[2]==gv and r[1]=="Str" and (not sv or r[2]==sv)
  local m2=r[1]=="Var" and r[2]==gv and l[1]=="Str" and (not sv or l[2]==sv)
  if not (m1 or m2) then return false end
  if c[2]=="~=" and is_ret0(tb) then return true,eb and eb[2] or {}
  elseif c[2]=="==" and (not eb or is_ret0(eb)) then return true,tb[2] end
  return false
end
local function emit_ub(ns,ub,sts,k)
  local wd=false
  if k<#sts then
    for _,us in ipairs(ub) do
      if us[1]=="LocalVar" then
        for _,nm in ipairs(us[2]) do if M.has_use(sts,k+1,nm) then wd=true break end end
      elseif us[1]=="LocalFunc" then
        if M.has_use(sts,k+1,us[2]) then wd=true end
      end
      if wd then break end
    end
  end
  if wd then ns[#ns+1]={"Do",{"Block",ub}}
  else for _,es in ipairs(ub) do ns[#ns+1]=es end end
end
local function match_wm(s,gv,sv)
  local ok,ub=is_wm_if(s,gv,sv)
  if ok then return ub end
  if s[1]=="Return" and #s[2]==1 then
    local ce=unp(s[2][1])
    local fn=ce[1]=="Call" and #ce[3]==1 and unp(ce[3][1])[1]=="Vararg" and unp(ce[2]) or nil
    if fn and fn[1]=="Func" and #fn[2]==0 and fn[3] then
      local fb,m=fn[4][2],1
      while m<=#fb and wm_safe(fb[m],gv) do m=m+1 end
      if m<=#fb then
        local ok2,ub2=is_wm_if(fb[m],gv,sv)
        if ok2 then
          local nb={}
          for p=1,m-1 do nb[#nb+1]=fb[p] end
          emit_ub(nb,ub2,fb,m)
          for p=m+1,#fb do nb[#nb+1]=fb[p] end
          return {{"Return",{{"Call",{"Func",fn[2],fn[3],{"Block",nb}},ce[3]}}}}
        end
      end
    end
  end
  return nil
end
function M.inv_wm(ast)
  return map_blk(ast,function(b)
    local sts,ns,i=b[2],{},1
    while i<=#sts do
      local gv,sv=i<#sts and wm_gsub_gv(sts[i]) or nil
      if gv then
        local k=i+1
        while k<=#sts and wm_safe(sts[k],gv) do k=k+1 end
        local ub=k<=#sts and match_wm(sts[k],gv,sv) or nil
        if ub then
          if M.has_use(ub,1,gv) or M.has_use(sts,k+1,gv) then ns[#ns+1]=sts[i] end
          for j=i+1,k-1 do ns[#ns+1]=sts[j] end
          emit_ub(ns,ub,sts,k)
          i=k+1
        else
          ns[#ns+1]=sts[i]
          i=i+1
        end
      else
        ns[#ns+1]=sts[i]
        i=i+1
      end
    end
    return {"Block",ns}
  end)
end
local function is_anti_do(s)
  if s[1]~="Do" then return false end
  local h={}
  A.walk(s,function(x)
    if x[1]=="Str" and (x[2]=="Tamper Detected!" or x[2]=="sethook" or x[2]=="getinfo") then h[x[2]]=true
    elseif x[1]=="Field" and (x[3]=="sethook" or x[3]=="getinfo") then h[x[3]]=true end
  end)
  return h["Tamper Detected!"] or (h.sethook and h.getinfo) or false
end
local function has_anti_err(n,ef)
  local ok=false
  A.walk(n,function(x)
    if x[1]=="Str" and x[2]=="Tamper Detected!" then ok=true
    elseif x[1]=="Call" and unp(x[2])[1]=="Var" and ef[unp(x[2])[2]] then ok=true end
  end)
  return ok
end
local function is_anti_st(s,ef)
  local ok=false
  A.walk(s,function(x)
    if x[1]=="Str" and (x[2]=="Tamper Detected!" or x[2]==":(%d*):" or x[2]=="sethook" or x[2]=="getinfo") then ok=true
    elseif x[1]=="Call" and unp(x[2])[1]=="Var" and ef[unp(x[2])[2]] then ok=true end
  end)
  return ok
end
local function live_anti(nm,sts)
  local rb
  local function re(n)
    if type(n)~="table" then return false end
    local k=n[1]
    if type(k)~="string" then
      for _,x in ipairs(n) do if re(x) then return true end end
      return false
    end
    if k=="Var" then return n[2]==nm end
    if k=="Func" then return not inl(n[2],nm) and rb(n[4][2])==true end
    if k=="LocalFunc" then return n[2]~=nm and not inl(n[3],nm) and rb(n[5][2])==true end
    for i=2,#n do if re(n[i]) then return true end end
    return false
  end
  local function rl(l)
    local u=unp(l)
    if u[1]=="Var" then return false
    elseif u[1]=="Idx" then return re(u[2]) or re(u[3])
    elseif u[1]=="Field" then return re(u[2]) end
    return re(u)
  end
  local function rs(s)
    local k=s[1]
    if k=="LocalVar" then
      for _,v in ipairs(s[3]) do if re(v) then return 1 end end
      if inl(s[2],nm) then return 0 end
    elseif k=="LocalFunc" then
      if s[2]==nm then return 0 end
      if not inl(s[3],nm) and rb(s[5][2]) then return 1 end
    elseif k=="FuncStmt" then
      if re(s[2]) then return 1 end
      if not inl(s[4],nm) and not (s[3] and nm=="self") and rb(s[6][2]) then return 1 end
    elseif k=="Assign" then
      for _,r in ipairs(s[3]) do if re(r) then return 1 end end
      for _,l in ipairs(s[2]) do if rl(l) then return 1 end end
      for _,l in ipairs(s[2]) do local u=unp(l) if u[1]=="Var" and u[2]==nm then return 0 end end
    elseif k=="CAssign" then
      if re(s[3]) or re(s[4]) then return 1 end
    elseif k=="Do" then
      local r=rb(s[2][2])
      if r~=nil then return r and 1 or 0 end
    elseif k=="While" then
      if re(s[2]) or rb(s[3][2]) then return 1 end
    elseif k=="Repeat" then
      local sh=false
      for _,st in ipairs(s[2][2]) do
        if st[1]=="LocalVar" and inl(st[2],nm) then sh=true
        elseif st[1]=="LocalFunc" and st[2]==nm then sh=true end
      end
      if rb(s[2][2]) or (not sh and re(s[3])) then return 1 end
    elseif k=="If" then
      for _,br in ipairs(s[2]) do if re(br[1]) or rb(br[2][2]) then return 1 end end
      if s[3] and rb(s[3][2]) then return 1 end
    elseif k=="ForNum" then
      if re(s[3]) or re(s[4]) or (s[5] and re(s[5])) then return 1 end
      if s[2]~=nm and rb(s[6][2]) then return 1 end
    elseif k=="ForIn" then
      for _,e in ipairs(s[3]) do if re(e) then return 1 end end
      if not inl(s[2],nm) and rb(s[4][2]) then return 1 end
    elseif k=="Return" then
      for _,e in ipairs(s[2]) do if re(e) then return 1 end end
    elseif k=="CallStmt" then
      if re(s[2]) then return 1 end
    end
    return 2
  end
  rb=function(bs)
    for _,s in ipairs(bs) do
      local r=rs(s)
      if r==1 then return true elseif r==0 then return false end
    end
    return nil
  end
  return rb(sts)==true
end
local function no_fall(b)
  local bs=b[2]
  if #bs==0 then return false end
  local ls=bs[#bs]
  if ls[1]=="Return" then return true end
  if ls[1]=="While" and unp(ls[2])[1]=="Bool" and unp(ls[2])[2]==true then
    local br=false
    local function sb(n)
      if type(n)~="table" then return end
      if n[1]=="Break" then br=true return end
      if n[1]=="Func" or n[1]=="While" or n[1]=="Repeat" or n[1]=="ForNum" or n[1]=="ForIn" then return end
      for i=1,#n do sb(n[i]) end
    end
    sb(ls[3])
    return not br
  end
  return false
end
function M.inv_anti(ast)
  return map_blk(ast,function(b)
    local sts={}
    for _,s in ipairs(b[2]) do
      if not is_anti_do(s) then sts[#sts+1]=s end
    end
    local ef,pc={},nil
    for i,s in ipairs(sts) do
      local k=s[1]
      if k=="LocalVar" or k=="Assign" or k=="LocalFunc" or k=="FuncStmt" then
        local lh=k=="LocalFunc" and {s[2]} or (k=="FuncStmt" and {s[2]} or s[2])
        local rh=k=="LocalFunc" and {{"Func",s[3],s[4],s[5]}} or (k=="FuncStmt" and {{"Func",s[4],s[5],s[6]}} or s[3])
        if #lh==1 and #rh==1 and unp(rh[1])[1]=="Func" then
          local td=false
          A.walk(rh[1],function(x) if x[1]=="Str" and x[2]=="Tamper Detected!" then td=true end end)
          if td then
            local nm=type(lh[1])=="string" and lh[1] or (unp(lh[1])[1]=="Var" and unp(lh[1])[2] or nil)
            if nm then ef[nm]=true end
          end
        end
        for j=1,math.min(#lh,#rh) do
          local u=unp(rh[j])
          if u[1]=="Var" and ef[u[2]] then
            local nm=type(lh[j])=="string" and lh[j] or (unp(lh[j])[1]=="Var" and unp(lh[j])[2] or nil)
            if nm then ef[nm]=true end
          end
        end
      end
      A.walk(s,function(x) if x[1]=="Str" and x[2]==":(%d*):" then pc=i end end)
    end
    if next(ef) and pc then
      for i=pc+1,#sts do
        local st=sts[i]
        local at_no_else=st[1]=="If" and #st[2]==1 and not st[3] and unp(st[2][1][1])[1]=="Var" and i<#sts and has_anti_err({"Block",{sts[i+1]}},ef) and (sts[i+1][1]=="Return" or i+1==#sts) and no_fall(st[2][1][2])
        if st[1]=="If" and #st[2]==1 and ((st[3] and unp(st[2][1][1])[1]=="Var" and has_anti_err(st[3],ef)) or at_no_else) then
          local tb={}
          for _,x in ipairs(st[2][1][2][2]) do tb[#tb+1]=x end
          if not at_no_else then
            for j=i+1,#sts do tb[#tb+1]=sts[j] end
          end
          local kp,kp_s,tl={},{},{}
          for j,x in ipairs(tb) do tl[j]=x end
          for j=i-1,1,-1 do
            local ps=sts[j]
            if (ps[1]=="LocalVar" or ps[1]=="Assign") and #ps[3]>0 and not is_anti_st(ps,ef) then
              local pvs,ok={},true
              for _,x in ipairs(ps[2]) do
                local nm=type(x)=="string" and x or (unp(x)[1]=="Var" and unp(x)[2] or nil)
                if not nm then ok=false break end
                pvs[#pvs+1]=nm
              end
              if ok then
                local lu=false
                for _,nm in ipairs(pvs) do if live_anti(nm,tl) then lu=true break end end
                if lu then
                  kp[#kp+1]=ps
                  kp_s[j]=true
                  local ntl={ps}
                  for _,x in ipairs(tl) do ntl[#ntl+1]=x end
                  tl=ntl
                end
              end
            elseif ps[1]=="CallStmt" then
              local gvv=wm_gsub_gv(ps)
              if gvv and live_anti(gvv,tl) then
                kp[#kp+1]=ps
                kp_s[j]=true
                local ntl={ps}
                for _,x in ipairs(tl) do ntl[#ntl+1]=x end
                tl=ntl
              end
            end
          end
          local ka={}
          for j=#kp,1,-1 do ka[#ka+1]=kp[j] end
          local uc={}
          for _,x in ipairs(ka) do uc[#uc+1]=x end
          for _,x in ipairs(tb) do uc[#uc+1]=x end
          local ns,dc={},{}
          for j=1,i-1 do
            local ps=sts[j]
            if ps[1]=="LocalVar" and not kp_s[j] then
              local kl={}
              for _,nm in ipairs(ps[2]) do
                if not dc[nm] and M.has_use(uc,1,nm) then dc[nm]=true kl[#kl+1]=nm end
              end
              if #kl>0 then ns[#ns+1]={"LocalVar",kl,{}} end
            end
          end
          for _,x in ipairs(ka) do ns[#ns+1]=x end
          for _,x in ipairs(tb) do ns[#ns+1]=x end
          return {"Block",ns}
        end
      end
    end
    return {"Block",sts}
  end)
end
local function is_split_fn(ps,va,b)
  if #ps~=1 or va then return false end
  local sts=b[2]
  if #sts~=3 then return false end
  if sts[1][1]=="LocalVar" and #sts[1][2]==2 and #sts[1][3]==2 then
    local vc,vk=sts[1][2][1],sts[1][2][2]
    if unp(sts[1][3][1])[1]=="Idx" and unp(sts[1][3][2])[1]=="Str" and unp(sts[1][3][2])[2]=="" and sts[2][1]=="ForNum" and sts[3][1]=="Return" and #sts[3][2]==1 and unp(sts[3][2][1])[1]=="Var" and unp(sts[3][2][1])[2]==vk then
      local fb=sts[2][6][2]
      if #fb==1 and fb[1][1]=="Assign" then
        local bd=unp(fb[1][3][1])
        if bd and bd[1]=="Bin" and bd[2]==".." then
          local idx=unp(bd[4])
          if idx[1]=="Idx" and unp(idx[2])[1]=="Var" and unp(idx[2])[2]==vc then return 1 end
        end
      end
    end
  end
  if sts[1][1]=="LocalVar" and #sts[1][2]==1 and #sts[1][3]==1 then
    local vk=sts[1][2][1]
    if unp(sts[1][3][1])[1]=="Str" and unp(sts[1][3][1])[2]=="" and sts[2][1]=="ForNum" and sts[3][1]=="Return" and #sts[3][2]==1 and unp(sts[3][2][1])[1]=="Var" and unp(sts[3][2][1])[2]==vk then
      local fb=sts[2][6][2]
      if #fb==1 and fb[1][1]=="Assign" then
        local bd=unp(fb[1][3][1])
        if bd and bd[1]=="Bin" and bd[2]==".." and unp(bd[4])[1]=="Idx" and unp(unp(bd[4])[2])[1]=="Var" and unp(unp(bd[4])[2])[2]==ps[1] then
          return 2
        end
      end
    end
  end
  return false
end
local function eval_split_arg(t)
  t=unp(t)
  if t[1]~="Tbl" then return nil end
  local fs=t[2]
  if #fs<1 then return nil end
  local lf=fs[#fs]
  if lf[1]~="V" then return nil end
  local arr=unp(lf[2])
  if arr[1]=="Tbl" then
    local ss={}
    for i,f in ipairs(arr[2]) do
      if f[1]~="V" then return nil end
      local v=unp(f[2])
      if v[1]~="Str" then return nil end
      ss[i]=v[2]
    end
    if #fs-1~=#ss then return nil end
    local out={}
    for i=1,#fs-1 do
      if fs[i][1]~="V" then return nil end
      local ix=unp(fs[i][2])
      if ix[1]~="Num" then return nil end
      local n=ix[2]
      if n<1 or n>#ss or math.floor(n)~=n then return nil end
      out[i]=ss[n]
    end
    return table.concat(out)
  elseif #fs%2==0 then
    local h=#fs/2
    local out={}
    for i=1,h do
      if fs[i][1]~="V" then return nil end
      local ix=unp(fs[i][2])
      if ix[1]~="Num" then return nil end
      local n=ix[2]
      if n<1 or n>h or math.floor(n)~=n then return nil end
      if fs[h+n][1]~="V" then return nil end
      local sv=unp(fs[h+n][2])
      if sv[1]~="Str" then return nil end
      out[i]=sv[2]
    end
    return table.concat(out)
  end
  return nil
end
function M.inv_split(ast)
  local function sp_b(b,decs)
    local d2={} for k,v in pairs(decs) do d2[k]=v end
    local function sp_e(e)
      local k=e[1]
      if k=="Call" and #e[3]==1 then
        local fn=unp(e[2])
        if fn[1]=="Var" and d2[fn[2]] then
          local r=eval_split_arg(e[3][1])
          if r then return {"Str",r} end
        end
        if fn[1]=="Field" and unp(fn[2])[1]=="Var" and unp(fn[2])[2]=="table" and fn[3]=="concat" then
          local t=unp(e[3][1])
          if t[1]=="Tbl" then
            local ss={}
            local ok=true
            for i,f in ipairs(t[2]) do
              if f[1]~="V" or unp(f[2])[1]~="Str" then ok=false break end
              ss[i]=unp(f[2])[2]
            end
            if ok then return {"Str",table.concat(ss)} end
          end
        end
      end
      if k=="Paren" then return {"Paren",sp_e(e[2])}
      elseif k=="Un" then return {"Un",e[2],sp_e(e[3])}
      elseif k=="Bin" then return {"Bin",e[2],sp_e(e[3]),sp_e(e[4])}
      elseif k=="Idx" then return {"Idx",sp_e(e[2]),sp_e(e[3])}
      elseif k=="Field" then return {"Field",sp_e(e[2]),e[3]}
      elseif k=="Call" then
        local as={} for i,a in ipairs(e[3]) do as[i]=sp_e(a) end
        return {"Call",sp_e(e[2]),as}
      elseif k=="MCall" then
        local as={} for i,a in ipairs(e[4]) do as[i]=sp_e(a) end
        return {"MCall",sp_e(e[2]),e[3],as}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(e[2]) do
          if f[1]=="V" then fs[i]={"V",sp_e(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],sp_e(f[3])}
          else fs[i]={"I",sp_e(f[2]),sp_e(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local cs={} for i,c in ipairs(e[2]) do cs[i]={sp_e(c[1]),sp_e(c[2])} end
        return {"IfExpr",cs,sp_e(e[3])}
      elseif k=="Func" then
        local df={} for k2,v in pairs(d2) do df[k2]=v end
        for _,p in ipairs(e[2]) do df[p]=nil end
        return {"Func",e[2],e[3],sp_b(e[4],df)}
      end
      return e
    end
    local ns,rm={},{}
    for _,s in ipairs(b[2]) do
      local k=s[1]
      if k=="LocalVar" and #s[2]==1 and #s[3]==1 then
        local fn=unp(s[3][1])
        if fn[1]=="Func" and is_split_fn(fn[2],fn[3],fn[4]) then
          d2[s[2][1]]=true
          rm[#ns+1]=s[2][1]
          ns[#ns+1]=s
        else
          ns[#ns+1]={"LocalVar",s[2],{sp_e(s[3][1])}}
          d2[s[2][1]]=nil
        end
      elseif k=="LocalFunc" and is_split_fn(s[3],s[4],s[5]) then
        d2[s[2]]=true
        rm[#ns+1]=s[2]
        ns[#ns+1]=s
      elseif k=="LocalFunc" then
        d2[s[2]]=nil
        local df={} for k2,v in pairs(d2) do df[k2]=v end
        for _,p in ipairs(s[3]) do df[p]=nil end
        ns[#ns+1]={"LocalFunc",s[2],s[3],s[4],sp_b(s[5],df)}
      elseif k=="FuncStmt" then
        local df={} for k2,v in pairs(d2) do df[k2]=v end
        for _,p in ipairs(s[4]) do df[p]=nil end
        if s[3] then df.self=nil end
        ns[#ns+1]={"FuncStmt",sp_e(s[2]),s[3],s[4],s[5],sp_b(s[6],df)}
      elseif k=="LocalVar" then
        local vs={} for i,v in ipairs(s[3]) do vs[i]=sp_e(v) end
        ns[#ns+1]={"LocalVar",s[2],vs}
        for _,nm in ipairs(s[2]) do d2[nm]=nil end
      elseif k=="Assign" then
        local ls,rs={},{}
        for i,l in ipairs(s[2]) do ls[i]=sp_e(l) end
        for i,r in ipairs(s[3]) do rs[i]=sp_e(r) end
        ns[#ns+1]={"Assign",ls,rs}
      elseif k=="CAssign" then ns[#ns+1]={"CAssign",s[2],sp_e(s[3]),sp_e(s[4])}
      elseif k=="Do" then ns[#ns+1]={"Do",sp_b(s[2],d2)}
      elseif k=="While" then ns[#ns+1]={"While",sp_e(s[2]),sp_b(s[3],d2)}
      elseif k=="Repeat" then ns[#ns+1]={"Repeat",sp_b(s[2],d2),sp_e(s[3])}
      elseif k=="If" then
        local cs={} for i,c in ipairs(s[2]) do cs[i]={sp_e(c[1]),sp_b(c[2],d2)} end
        ns[#ns+1]={"If",cs,s[3] and sp_b(s[3],d2) or false}
      elseif k=="ForNum" then
        local df={} for k2,v in pairs(d2) do df[k2]=v end df[s[2]]=nil
        ns[#ns+1]={"ForNum",s[2],sp_e(s[3]),sp_e(s[4]),s[5] and sp_e(s[5]) or false,sp_b(s[6],df)}
      elseif k=="ForIn" then
        local es={} for i,e in ipairs(s[3]) do es[i]=sp_e(e) end
        local df={} for k2,v in pairs(d2) do df[k2]=v end
        for _,v in ipairs(s[2]) do df[v]=nil end
        ns[#ns+1]={"ForIn",s[2],es,sp_b(s[4],df)}
      elseif k=="Return" then
        local es={} for i,e in ipairs(s[2]) do es[i]=sp_e(e) end
        ns[#ns+1]={"Return",es}
      elseif k=="CallStmt" then ns[#ns+1]={"CallStmt",sp_e(s[2])}
      else ns[#ns+1]=s end
    end
    local out={}
    for i,s in ipairs(ns) do
      local nm=rm[i]
      if not (nm and not M.has_use(ns,i+1,nm)) then out[#out+1]=s end
    end
    return {"Block",out}
  end
  return sp_b(ast,{})
end
local function parse_mm(e,fld)
  e=unp(e)
  if e[1]~="Func" or #e[2]~=2 or e[3] then return nil end
  local p1,p2=e[2][1],e[2][2]
  local bs=e[4][2]
  if #bs~=1 then return nil end
  local st=bs[1]
  if st[1]=="Assign" and #st[2]==1 and #st[3]==1 then
    local l,r=unp(st[2][1]),unp(st[3][1])
    if r[1]=="Var" and r[2]==p2 then
      if l[1]=="Field" and unp(l[2])[1]=="Var" and unp(l[2])[2]==p1 and l[3]==fld then return "set" end
      if l[1]=="Idx" and unp(l[2])[1]=="Var" and unp(l[2])[2]==p1 and unp(l[3])[1]=="Str" and unp(l[3])[2]==fld then return "set" end
    end
  elseif st[1]=="Return" and #st[2]==1 then
    local r=unp(st[2][1])
    if r[1]=="Field" and unp(r[2])[1]=="Var" and unp(r[2])[2]==p1 and r[3]==fld then return "get" end
    if r[1]=="Idx" and unp(r[2])[1]=="Var" and unp(r[2])[2]==p1 and unp(r[3])[1]=="Str" and unp(r[3])[2]==fld then return "get" end
    if r[1]=="Call" and unp(r[2])[1]=="Var" and unp(r[2])[2]=="rawget" and #r[3]==2 then
      local a1,a2=unp(r[3][1]),unp(r[3][2])
      if a1[1]=="Var" and a1[2]==p1 and a2[1]=="Str" and a2[2]==fld then return "get" end
    end
  end
  return nil
end
local function is_prox_def(e,sm)
  e=unp(e)
  if e[1]~="Call" or #e[3]~=2 then return nil end
  local f=unp(e[2])
  if f[1]~="Var" or (f[2]~="setmetatable" and not sm[f[2]]) then return nil end
  local t1,t2=unp(e[3][1]),unp(e[3][2])
  if t1[1]~="Tbl" or #t1[2]~=1 or t2[1]~="Tbl" or (#t2[2]~=2 and #t2[2]~=3) then return nil end
  local f0=t1[2][1]
  local fld,iv
  if f0[1]=="F" then fld,iv=f0[2],f0[3]
  elseif f0[1]=="I" then
    local kv=unp(f0[2])
    if kv[1]=="Str" or kv[1]=="Num" or kv[1]=="Bool" then fld,iv=kv[2],f0[3] else return nil end
  else return nil end
  local function match_fld(x,fl2)
    if type(fl2)=="string" then
      if x[1]=="Field" and x[3]==fl2 then return true end
      if x[1]=="Idx" and unp(x[3])[1]=="Str" and unp(x[3])[2]==fl2 then return true end
    else
      if x[1]=="Idx" then
        local u=unp(x[3])
        if (u[1]=="Num" or u[1]=="Bool") and u[2]==fl2 then return true end
      end
    end
    return false
  end
  local gop,sop
  for _,mf in ipairs(t2[2]) do
    local mn,mv
    if mf[1]=="F" then mn,mv=mf[2],mf[3]
    elseif mf[1]=="I" and unp(mf[2])[1]=="Str" then mn,mv=unp(mf[2])[2],mf[3]
    else return nil end
    local op=MM[mn]
    if not op then return nil end
    local fn=unp(mv)
    if fn[1]~="Func" or #fn[2]~=2 or fn[3] or #fn[4][2]~=1 then return nil end
    local p1,p2,st=fn[2][1],fn[2][2],fn[4][2][1]
    if st[1]=="Assign" and #st[2]==1 and #st[3]==1 then
      local l,r=unp(st[2][1]),unp(st[3][1])
      if r[1]=="Var" and r[2]==p2 and unp(l[2])[1]=="Var" and unp(l[2])[2]==p1 and match_fld(l,fld) then
        sop=op
      else return nil end
    elseif st[1]=="Return" and #st[2]==1 then
      local r=unp(st[2][1])
      if (r[1]=="Field" or r[1]=="Idx") and unp(r[2])[1]=="Var" and unp(r[2])[2]==p1 and match_fld(r,fld) then
        gop=op
      elseif r[1]=="Call" and unp(r[2])[1]=="Var" and unp(r[2])[2]=="rawget" and #r[3]==2 then
        local a1,a2=unp(r[3][1]),unp(r[3][2])
        if a1[1]=="Var" and a1[2]==p1 and (a2[1]=="Str" or a2[1]=="Num" or a2[1]=="Bool") and a2[2]==fld then
          gop=op
        else return nil end
      else return nil end
    else return nil end
  end
  if gop and sop then return {iv=iv,gop=gop,sop=sop,fld=fld} end
  return nil
end
local function cp_st(st)
  local r={sm={},emp={},prx={}}
  for k,v in pairs(st.sm) do r.sm[k]=v end
  for k,v in pairs(st.emp) do r.emp[k]=v end
  for k,v in pairs(st.prx) do r.prx[k]=v end
  return r
end
local function clr_st(st,nms)
  if type(nms)=="string" then st.sm[nms]=nil st.emp[nms]=nil st.prx[nms]=nil
  else for _,nm in ipairs(nms) do st.sm[nm]=nil st.emp[nm]=nil st.prx[nm]=nil end end
end
function M.inv_prox(ast)
  local function px_b(bl,st)
    local cs=cp_st(st)
    local function px_e(e)
      local k=e[1]
      if k=="Bin" then
        local ou=unp(e[3])
        if ou[1]=="Var" and cs.prx[ou[2]] and e[2]==cs.prx[ou[2]].gop then
          return {"Var",ou[2]}
        end
        return {"Bin",e[2],px_e(e[3]),px_e(e[4])}
      elseif k=="Idx" or k=="Field" then
        local ou=unp(e[2])
        if ou[1]=="Var" and cs.prx[ou[2]] and cs.prx[ou[2]].gop=="IDX" then
          return {"Var",ou[2]}
        end
        if k=="Idx" then return {"Idx",px_e(e[2]),px_e(e[3])} end
        return {"Field",px_e(e[2]),e[3]}
      elseif k=="Paren" then return {"Paren",px_e(e[2])}
      elseif k=="Un" then return {"Un",e[2],px_e(e[3])}
      elseif k=="Call" then
        local as={} for i,a in ipairs(e[3]) do as[i]=px_e(a) end
        return {"Call",px_e(e[2]),as}
      elseif k=="MCall" then
        local as={} for i,a in ipairs(e[4]) do as[i]=px_e(a) end
        return {"MCall",px_e(e[2]),e[3],as}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(e[2]) do
          if f[1]=="V" then fs[i]={"V",px_e(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],px_e(f[3])}
          else fs[i]={"I",px_e(f[2]),px_e(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local css={} for i,c in ipairs(e[2]) do css[i]={px_e(c[1]),px_e(c[2])} end
        return {"IfExpr",css,px_e(e[3])}
      elseif k=="Func" then
        local fcs=cp_st(cs)
        clr_st(fcs,e[2])
        return {"Func",e[2],e[3],px_b(e[4],fcs)}
      end
      return e
    end
    local ns={}
    local rm={}
    for _,s in ipairs(bl[2]) do
      local k=s[1]
      if k=="LocalVar" then
        local vs={}
        local new_px={}
        for idx,v in ipairs(s[3]) do
          local nm=s[2][idx]
          local vu=unp(v)
          if nm and vu[1]=="Var" and vu[2]=="setmetatable" then
            vs[idx]=v
            new_px[nm]={kind="sm"}
          elseif nm and vu[1]=="Func" and #vu[4][2]==0 then
            vs[idx]=v
            new_px[nm]={kind="emp"}
          else
            local info=nm and is_prox_def(v,cs.sm)
            if info then
              vs[idx]=px_e(info.iv)
              local ivu=unp(info.iv)
              local emp=ivu[1]=="Func" and #ivu[4][2]==0 or false
              new_px[nm]={kind="prx",info=info,emp=emp}
            else
              vs[idx]=px_e(v)
            end
          end
        end
        ns[#ns+1]={"LocalVar",s[2],vs}
        clr_st(cs,s[2])
        for nm,act in pairs(new_px) do
          if act.kind=="sm" then cs.sm[nm]=true rm[#ns]=nm
          elseif act.kind=="emp" then cs.emp[nm]=true rm[#ns]=nm
          elseif act.kind=="prx" then cs.prx[nm]=act.info if act.emp then cs.emp[nm]=true end end
        end
      elseif k=="LocalFunc" then
        clr_st(cs,s[2])
        local fcs=cp_st(cs)
        clr_st(fcs,s[3])
        ns[#ns+1]={"LocalFunc",s[2],s[3],s[4],px_b(s[5],fcs)}
      elseif k=="FuncStmt" then
        local fcs=cp_st(cs)
        clr_st(fcs,s[4])
        if s[3] then clr_st(fcs,"self") end
        local tgt=s[2]
        if tgt[1]=="Field" and unp(tgt[2])[1]=="Var" and cs.prx[unp(tgt[2])[2]] and cs.prx[unp(tgt[2])[2]].fld==tgt[3] then
          tgt={"Var",unp(tgt[2])[2]}
        else
          tgt=px_e(tgt)
        end
        ns[#ns+1]={"FuncStmt",tgt,s[3],s[4],s[5],px_b(s[6],fcs)}
      elseif k=="CallStmt" then
        local c=unp(s[2])
        local cf=c[1]=="Call" and unp(px_e(c[2])) or nil
        if cf and #c[3]==1 and cf[1]=="Var" and cs.emp[cf[2]] then
          local a=unp(c[3][1])
          if a[1]=="Bin" and unp(a[3])[1]=="Var" and cs.prx[unp(a[3])[2]] and a[2]==cs.prx[unp(a[3])[2]].sop then
            ns[#ns+1]={"Assign",{{"Var",unp(a[3])[2]}},{px_e(a[4])}}
          elseif a[1]=="Idx" and unp(a[2])[1]=="Var" and cs.prx[unp(a[2])[2]] and cs.prx[unp(a[2])[2]].sop=="IDX" then
            ns[#ns+1]={"Assign",{{"Var",unp(a[2])[2]}},{px_e(a[3])}}
          elseif a[1]=="Field" and unp(a[2])[1]=="Var" and cs.prx[unp(a[2])[2]] and cs.prx[unp(a[2])[2]].sop=="IDX" then
            ns[#ns+1]={"Assign",{{"Var",unp(a[2])[2]}},{{"Str",a[3]}}}
          else
            ns[#ns+1]={"CallStmt",px_e(s[2])}
          end
        else
          ns[#ns+1]={"CallStmt",px_e(s[2])}
        end
      elseif k=="Assign" then
        if #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" then
          local nm=unp(s[2][1])[2]
          local info=is_prox_def(s[3][1],cs.sm)
          if info then
            cs.prx[nm]=info
            local ivu=unp(info.iv)
            if ivu[1]=="Func" and #ivu[4][2]==0 then cs.emp[nm]=true end
            ns[#ns+1]={"Assign",{{"Var",nm}},{px_e(info.iv)}}
          else
            ns[#ns+1]={"Assign",{px_e(s[2][1])},{px_e(s[3][1])}}
          end
        else
          local ls,rs={},{}
          for i,l in ipairs(s[2]) do
            local lu=unp(l)
            if (lu[1]=="Idx" or lu[1]=="Field") and unp(lu[2])[1]=="Var" and cs.prx[unp(lu[2])[2]] then
              local px=cs.prx[unp(lu[2])[2]]
              if px.sop=="IDX" or (lu[1]=="Field" and lu[3]==px.fld) or (lu[1]=="Idx" and unp(lu[3])[1]=="Str" and unp(lu[3])[2]==px.fld) then
                ls[i]={"Var",unp(lu[2])[2]}
              else ls[i]=px_e(l) end
            else ls[i]=px_e(l) end
          end
          for i,r in ipairs(s[3]) do rs[i]=px_e(r) end
          ns[#ns+1]={"Assign",ls,rs}
        end
      elseif k=="CAssign" then ns[#ns+1]={"CAssign",s[2],px_e(s[3]),px_e(s[4])}
      elseif k=="Do" then ns[#ns+1]={"Do",px_b(s[2],cs)}
      elseif k=="While" then ns[#ns+1]={"While",px_e(s[2]),px_b(s[3],cs)}
      elseif k=="Repeat" then
        local nb=px_b(s[2],cs)
        local cs_sv=cs
        cs=cp_st(cs)
        for _,rs in ipairs(nb[2]) do
          if rs[1]=="LocalVar" then clr_st(cs,rs[2])
          elseif rs[1]=="LocalFunc" then clr_st(cs,rs[2]) end
        end
        local nc=px_e(s[3])
        cs=cs_sv
        ns[#ns+1]={"Repeat",nb,nc}
      elseif k=="If" then
        local css={} for i,c in ipairs(s[2]) do css[i]={px_e(c[1]),px_b(c[2],cs)} end
        ns[#ns+1]={"If",css,s[3] and px_b(s[3],cs) or false}
      elseif k=="ForNum" then
        local fcs=cp_st(cs) clr_st(fcs,s[2])
        ns[#ns+1]={"ForNum",s[2],px_e(s[3]),px_e(s[4]),s[5] and px_e(s[5]) or false,px_b(s[6],fcs)}
      elseif k=="ForIn" then
        local es={} for i,e in ipairs(s[3]) do es[i]=px_e(e) end
        local fcs=cp_st(cs) clr_st(fcs,s[2])
        ns[#ns+1]={"ForIn",s[2],es,px_b(s[4],fcs)}
      elseif k=="Return" then
        local es={} for i,e in ipairs(s[2]) do es[i]=px_e(e) end
        ns[#ns+1]={"Return",es}
      else ns[#ns+1]=s end
    end
    local out={}
    for i,s in ipairs(ns) do
      local nm=rm[i]
      if not (nm and #s[2]==1 and not M.has_use(ns,i+1,nm)) then out[#out+1]=s end
    end
    return {"Block",out}
  end
  return px_b(ast,{sm={},emp={},prx={}})
end
local function is_str_pool(s,sev)
  local pv,rh
  if s[1]=="LocalVar" and #s[2]==1 and #s[3]==1 then
    pv,rh=s[2][1],s[3][1]
  elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" then
    pv,rh=unp(s[2][1])[2],s[3][1]
  else
    return nil
  end
  local t=unp(rh)
  if t[1]~="Tbl" or #t[2]==0 then return nil end
  local pvs={}
  for i,f in ipairs(t[2]) do
    if f[1]~="V" then return nil end
    local v=unp(f[2])
    if v[1]=="Str" then
      pvs[i]=v[2]
    elseif v[1]=="Var" and sev and sev[v[2]] then
      pvs[i]=sev[v[2]]
    else
      return nil
    end
  end
  return pv,pvs
end
local function mut_b(sts,i0,nm,ext_ok)
  local function me(e)
    if type(e)~="table" then return false end
    local k=e[1]
    if k=="Call" then
      for _,a in ipairs(e[3]) do
        local u=unp(a)
        if u[1]=="Var" and u[2]==nm then return true end
        if me(a) then return true end
      end
      return me(e[2])
    elseif k=="MCall" then
      for _,a in ipairs(e[4]) do
        local u=unp(a)
        if u[1]=="Var" and u[2]==nm then return true end
        if me(a) then return true end
      end
      return me(e[2])
    elseif k=="Paren" or k=="Un" then return me(e[2]) or (k=="Un" and me(e[3]))
    elseif k=="Bin" or k=="Idx" then return me(e[2]) or me(e[3]) or (k=="Bin" and me(e[4]))
    elseif k=="Field" then return me(e[2])
    elseif k=="Tbl" then
      for _,f in ipairs(e[2]) do
        if f[1]=="V" then if me(f[2]) then return true end
        elseif f[1]=="F" then if me(f[3]) then return true end
        else if me(f[2]) or me(f[3]) then return true end end
      end
    elseif k=="IfExpr" then
      for _,c in ipairs(e[2]) do if me(c[1]) or me(c[2]) then return true end end
      return me(e[3])
    elseif k=="Func" then
      if inl(e[2],nm) then return false end
      return mut_b(e[4][2],1,nm,ext_ok)
    end
    return false
  end
  local function ml(l)
    local u=unp(l)
    if (u[1]=="Var" and u[2]==nm) or (u[1]=="Idx" and unp(u[2])[1]=="Var" and unp(u[2])[2]==nm) or (u[1]=="Field" and unp(u[2])[1]=="Var" and unp(u[2])[2]==nm) then return true end
    return me(u)
  end
  for i=i0,#sts do
    local s=sts[i]
    local k=s[1]
    if k=="LocalVar" then
      for j,v in ipairs(s[3]) do
        local u=unp(v)
        if ext_ok and #s[2]==#s[3] and u[1]=="Var" and u[2]==nm and not mut_b(sts,i+1,s[2][j],true) then
        elseif me(v) then return true end
      end
      if inl(s[2],nm) then return false end
    elseif k=="LocalFunc" then
      if s[2]==nm then return false end
      if not inl(s[3],nm) and mut_b(s[5][2],1,nm,ext_ok) then return true end
    elseif k=="FuncStmt" then
      if ml(s[2]) then return true end
      if not inl(s[4],nm) and not (s[3] and nm=="self") and mut_b(s[6][2],1,nm,ext_ok) then return true end
    elseif k=="Assign" then
      for _,l in ipairs(s[2]) do if ml(l) then return true end end
      for _,r in ipairs(s[3]) do if me(r) then return true end end
    elseif k=="CAssign" then
      if ml(s[3]) or me(s[4]) then return true end
    elseif k=="Do" then
      if mut_b(s[2][2],1,nm,ext_ok) then return true end
    elseif k=="While" then
      if me(s[2]) or mut_b(s[3][2],1,nm,ext_ok) then return true end
    elseif k=="Repeat" then
      if mut_b(s[2][2],1,nm,ext_ok) then return true end
      local sh=false
      for _,st in ipairs(s[2][2]) do
        if st[1]=="LocalVar" and inl(st[2],nm) then sh=true
        elseif st[1]=="LocalFunc" and st[2]==nm then sh=true end
      end
      if not sh and me(s[3]) then return true end
    elseif k=="If" then
      for _,c in ipairs(s[2]) do
        if me(c[1]) or mut_b(c[2][2],1,nm,ext_ok) then return true end
      end
      if s[3] and mut_b(s[3][2],1,nm,ext_ok) then return true end
    elseif k=="ForNum" then
      if me(s[3]) or me(s[4]) or (s[5] and me(s[5])) then return true end
      if s[2]~=nm and mut_b(s[6][2],1,nm,ext_ok) then return true end
    elseif k=="ForIn" then
      for _,e in ipairs(s[3]) do if me(e) then return true end end
      if not inl(s[2],nm) and mut_b(s[4][2],1,nm,ext_ok) then return true end
    elseif k=="Return" then
      for _,e in ipairs(s[2]) do if me(e) then return true end end
    elseif k=="CallStmt" then
      if me(s[2]) then return true end
    end
  end
  return false
end
local function pool_lim(sts,i0,nm)
  for j=i0,#sts do
    local s=sts[j]
    if s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" and unp(s[2][1])[2]==nm then
      if mut_b({{"Return",s[3]}},1,nm,false) then return nil end
      for k=i0,j-1 do
        local sk=sts[k]
        local fc=false
        A.walk(sk,function(x)
          if (x[1]=="Func" or x[1]=="LocalFunc" or x[1]=="FuncStmt") and uv_e(x,nm) then fc=true end
        end)
        if fc then return nil end
      end
      return j-1,true
    elseif mut_b({s},1,nm,true) then
      return nil
    end
  end
  return #sts,false
end
function M.inv_pool(ast)
  local function wr_after(sts,i0,nm)
    for i=i0,#sts do
      local s=sts[i]
      local k=s[1]
      if k=="Assign" then
        for _,l in ipairs(s[2]) do local u=unp(l) if u[1]=="Var" and u[2]==nm then return true end end
      elseif k=="CAssign" then
        local u=unp(s[3]) if u[1]=="Var" and u[2]==nm then return true end
      elseif k=="LocalVar" then
        if inl(s[2],nm) then return false end
      elseif k=="LocalFunc" then
        if s[2]==nm then return false end
        if not inl(s[3],nm) and wr_after(s[5][2],1,nm) then return true end
      elseif k=="FuncStmt" then
        if not s[3] and unp(s[2])[1]=="Var" and unp(s[2])[2]==nm then return true end
        if not inl(s[4],nm) and not (s[3] and nm=="self") and wr_after(s[6][2],1,nm) then return true end
      elseif k=="Do" then
        if wr_after(s[2][2],1,nm) then return true end
      elseif k=="While" then
        if wr_after(s[3][2],1,nm) then return true end
      elseif k=="Repeat" then
        local sh=false
        for _,st in ipairs(s[2][2]) do
          if (st[1]=="LocalVar" and inl(st[2],nm)) or (st[1]=="LocalFunc" and st[2]==nm) then sh=true end
        end
        if not sh and wr_after(s[2][2],1,nm) then return true end
      elseif k=="If" then
        for _,c in ipairs(s[2]) do if wr_after(c[2][2],1,nm) then return true end end
        if s[3] and wr_after(s[3][2],1,nm) then return true end
      elseif k=="ForNum" then
        if s[2]~=nm and wr_after(s[6][2],1,nm) then return true end
      elseif k=="ForIn" then
        if not inl(s[2],nm) and wr_after(s[4][2],1,nm) then return true end
      end
      local fwr=false
      A.walk(s,function(x)
        if fwr then return end
        if x[1]=="Func" and not inl(x[2],nm) and wr_after(x[4][2],1,nm) then fwr=true end
      end)
      if fwr then return true end
    end
    return false
  end
  local function ip_b(b,pl0,sv0)
    local sts={}
    for i,s in ipairs(b[2]) do sts[i]=s end
    local pl={} if pl0 then for k,v in pairs(pl0) do pl[k]=v end end
    local sv={} if sv0 then for k,v in pairs(sv0) do sv[k]=v end end
    local sev={}
    local function cp_pl(t,sh)
      local r={} for k,v in pairs(t) do if not (sh and sh[k]) then r[k]=v end end return r
    end
    local function ip_e(e,p2,v2)
      if type(e)~="table" then return e end
      local k=e[1]
      if k=="Var" and v2 and v2[e[2]] then
        return {"Str",v2[e[2]]}
      elseif k=="Func" then
        local sh={} for _,nm in ipairs(e[2]) do sh[nm]=true end
        return {"Func",e[2],e[3],ip_b(e[4],cp_pl(p2,sh),cp_pl(v2,sh))}
      elseif k=="Paren" then return {"Paren",ip_e(e[2],p2,v2)}
      elseif k=="Un" then return {"Un",e[2],ip_e(e[3],p2,v2)}
      elseif k=="Bin" then return {"Bin",e[2],ip_e(e[3],p2,v2),ip_e(e[4],p2,v2)}
      elseif k=="Idx" then return {"Idx",ip_e(e[2],p2,v2),ip_e(e[3],p2,v2)}
      elseif k=="Field" then return {"Field",ip_e(e[2],p2,v2),e[3]}
      elseif k=="Call" then
        local as={} for j,a in ipairs(e[3]) do as[j]=ip_e(a,p2,v2) end
        return {"Call",ip_e(e[2],p2,v2),as}
      elseif k=="MCall" then
        local as={} for j,a in ipairs(e[4]) do as[j]=ip_e(a,p2,v2) end
        return {"MCall",ip_e(e[2],p2,v2),e[3],as}
      elseif k=="Tbl" then
        local fs={}
        for j,f in ipairs(e[2]) do
          if f[1]=="V" then fs[j]={"V",ip_e(f[2],p2,v2)}
          elseif f[1]=="F" then fs[j]={"F",f[2],ip_e(f[3],p2,v2)}
          else fs[j]={"I",ip_e(f[2],p2,v2),ip_e(f[3],p2,v2)} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local cs={} for j,c in ipairs(e[2]) do cs[j]={ip_e(c[1],p2,v2),ip_e(c[2],p2,v2)} end
        return {"IfExpr",cs,ip_e(e[3],p2,v2)}
      end
      return e
    end
    local i=1
    while i<=#sts do
      local st=sts[i]
      local pv,pvs=is_str_pool(st,sev)
      if pv then
        local lim,ov=pool_lim(sts,i+1,pv)
        if lim then
          local rest={}
          for j=i+1,lim do rest[#rest+1]=sts[j] end
          local nb=S.r_pool({"Block",rest},pv,pvs)
          for j=1,#nb[2] do sts[i+j]=nb[2][j] end
          for j=i+1,lim do
            local sj=sts[j]
            if sj[1]=="LocalVar" and #sj[2]==#sj[3] then
              for l,r in ipairs(sj[3]) do
                local u=unp(r)
                if u[1]=="Var" and u[2]==pv then pl[sj[2][l]]=pvs end
              end
            end
          end
          pl[pv]=pvs
          sv[pv]=nil
          local hc=false
          A.walk(rest,function(x) if x[1]=="Call" or x[1]=="MCall" then hc=true end end)
          if ov and st[1]=="Assign" and not hc and not M.has_use(rest,1,pv) and not uv_e(sts[lim+1][3],pv) then
            table.remove(sts,i)
          elseif not ov and st[1]=="LocalVar" and not M.has_use(sts,i+1,pv) then
            table.remove(sts,i)
          else
            i=i+1
          end
        else
          pl[pv]=nil sv[pv]=nil i=i+1
        end
      elseif st[1]=="LocalVar" and #st[2]==#st[3] then
        local vs={} for j,v in ipairs(st[3]) do vs[j]=ip_e(v,pl,sv) end
        local rm_l=true
        local all_str=#st[2]>=3
        for j,r in ipairs(vs) do
          if unp(r)[1]~="Str" then all_str=false break end
        end
        for j,r in ipairs(vs) do
          local nm=st[2][j]
          local u=unp(r)
          if u[1]=="Var" and pl[u[2]] and not mut_b(sts,i+1,nm,true) then
            local pvs2=pl[u[2]]
            local rest={}
            for m=i+1,#sts do rest[#rest+1]=sts[m] end
            local nb=S.r_pool({"Block",rest},nm,pvs2)
            for m=1,#nb[2] do sts[i+m]=nb[2][m] end
            pl[nm]=pvs2
            sv[nm]=nil
          else
            pl[nm]=nil
            if all_str and not wr_after(sts,i+1,nm) then
              sv[nm]=u[2]
            else
              sv[nm]=nil
            end
          end
          if M.has_use(sts,i+1,nm) then rm_l=false end
          if u[1]=="Str" then sev[nm]=u[2] else sev[nm]=nil end
        end
        if #st[2]==1 and rm_l and unp(vs[1])[1]=="Var" and pl[unp(vs[1])[2]] then
          table.remove(sts,i)
        else
          sts[i]={"LocalVar",st[2],vs}
          i=i+1
        end
      else
        local k=st[1]
        if k=="LocalVar" then
          local vs={} for j,v in ipairs(st[3]) do vs[j]=ip_e(v,pl,sv) end
          for _,nm in ipairs(st[2]) do pl[nm]=nil sv[nm]=nil sev[nm]=nil end
          sts[i]={"LocalVar",st[2],vs}
        elseif k=="Assign" and #st[2]==#st[3] then
          local ls,rs={},{}
          for j,l in ipairs(st[2]) do ls[j]=ip_e(l,pl,sv) end
          local p2={} for q,v in pairs(pl) do p2[q]=v end
          for j,l in ipairs(ls) do local lu=unp(l) if lu[1]=="Var" then p2[lu[2]]=nil end end
          for j,r in ipairs(st[3]) do rs[j]=ip_e(r,p2,sv) end
          sts[i]={"Assign",ls,rs}
          for j,l in ipairs(ls) do
            local lu=unp(l)
            if lu[1]=="Var" then
              pl[lu[2]]=nil sv[lu[2]]=nil
              local ru=unp(rs[j])
              if ru[1]=="Str" then sev[lu[2]]=ru[2] else sev[lu[2]]=nil end
            end
          end
        elseif k=="LocalFunc" then
          pl[st[2]]=nil sv[st[2]]=nil sev[st[2]]=nil
          local sh={[st[2]]=true} for _,p in ipairs(st[3]) do sh[p]=true end
          sts[i]={"LocalFunc",st[2],st[3],st[4],ip_b(st[5],cp_pl(pl,sh),cp_pl(sv,sh))}
        elseif k=="FuncStmt" then
          local sh={} for _,p in ipairs(st[4]) do sh[p]=true end if st[3] then sh.self=true end
          sts[i]={"FuncStmt",ip_e(st[2],pl,sv),st[3],st[4],st[5],ip_b(st[6],cp_pl(pl,sh),cp_pl(sv,sh))}
        elseif k=="Do" then sts[i]={"Do",ip_b(st[2],pl,sv)}
        elseif k=="While" then sts[i]={"While",ip_e(st[2],pl,sv),ip_b(st[3],pl,sv)}
        elseif k=="Repeat" then
          local sh={}
          for _,rs in ipairs(st[2][2]) do
            if rs[1]=="LocalVar" then for _,nm in ipairs(rs[2]) do sh[nm]=true end
            elseif rs[1]=="LocalFunc" then sh[rs[2]]=true end
          end
          sts[i]={"Repeat",ip_b(st[2],pl,sv),ip_e(st[3],cp_pl(pl,sh),cp_pl(sv,sh))}
        elseif k=="If" then
          local cs={} for j,c in ipairs(st[2]) do cs[j]={ip_e(c[1],pl,sv),ip_b(c[2],pl,sv)} end
          sts[i]={"If",cs,st[3] and ip_b(st[3],pl,sv) or false}
        elseif k=="ForNum" then
          sts[i]={"ForNum",st[2],ip_e(st[3],pl,sv),ip_e(st[4],pl,sv),st[5] and ip_e(st[5],pl,sv) or false,ip_b(st[6],cp_pl(pl,{[st[2]]=true}),cp_pl(sv,{[st[2]]=true}))}
        elseif k=="ForIn" then
          local sh={} for _,nm in ipairs(st[2]) do sh[nm]=true end
          local es={} for j,e in ipairs(st[3]) do es[j]=ip_e(e,pl,sv) end
          sts[i]={"ForIn",st[2],es,ip_b(st[4],cp_pl(pl,sh),cp_pl(sv,sh))}
        elseif k=="Return" then
          local es={} for j,e in ipairs(st[2]) do es[j]=ip_e(e,pl,sv) end
          sts[i]={"Return",es}
        elseif k=="CallStmt" then sts[i]={"CallStmt",ip_e(st[2],pl,sv)}
        elseif k=="CAssign" then sts[i]={"CAssign",st[2],ip_e(st[3],pl,sv),ip_e(st[4],pl,sv)} end
        i=i+1
      end
    end
    return {"Block",sts}
  end
  return ip_b(ast,{},{})
end
local function add_s_use(s,lv,sh)
  local function ae(e,s2)
    if type(e)~="table" then return end
    local k=e[1]
    if k=="Var" then if not (s2 and s2[e[2]]) then lv[e[2]]=true end
    elseif k=="Paren" then ae(e[2],s2)
    elseif k=="Un" then ae(e[3],s2)
    elseif k=="Bin" then ae(e[3],s2) ae(e[4],s2)
    elseif k=="Idx" then ae(e[2],s2) ae(e[3],s2)
    elseif k=="Field" then ae(e[2],s2)
    elseif k=="Call" then ae(e[2],s2) for _,a in ipairs(e[3]) do ae(a,s2) end
    elseif k=="MCall" then ae(e[2],s2) for _,a in ipairs(e[4]) do ae(a,s2) end
    elseif k=="Tbl" then
      for _,f in ipairs(e[2]) do
        if f[1]=="V" then ae(f[2],s2)
        elseif f[1]=="F" then ae(f[3],s2)
        else ae(f[2],s2) ae(f[3],s2) end
      end
    elseif k=="IfExpr" then
      for _,c in ipairs(e[2]) do ae(c[1],s2) ae(c[2],s2) end
      ae(e[3],s2)
    elseif k=="Func" then
      local s3={} if s2 then for q,v in pairs(s2) do s3[q]=v end end
      for _,p in ipairs(e[2]) do s3[p]=true end
      for _,st in ipairs(e[4][2]) do add_s_use(st,lv,s3) end
    end
  end
  local function ab(sts,s2)
    local s3={} if s2 then for q,v in pairs(s2) do s3[q]=v end end
    for _,st in ipairs(sts) do
      local k=st[1]
      if k=="LocalVar" then
        for _,v in ipairs(st[3]) do ae(v,s3) end
        for _,nm in ipairs(st[2]) do s3[nm]=true end
      elseif k=="LocalFunc" then
        s3[st[2]]=true
        local s4={} for q,v in pairs(s3) do s4[q]=v end
        for _,p in ipairs(st[3]) do s4[p]=true end
        ab(st[5][2],s4)
      else
        add_s_use(st,lv,s3)
      end
    end
  end
  local k=s[1]
  if k=="LocalVar" then for _,v in ipairs(s[3]) do ae(v,sh) end
  elseif k=="LocalFunc" then
    local s2={} if sh then for q,v in pairs(sh) do s2[q]=v end end
    for _,p in ipairs(s[3]) do s2[p]=true end
    ab(s[5][2],s2)
  elseif k=="FuncStmt" then
    ae(s[2],sh)
    local s2={} if sh then for q,v in pairs(sh) do s2[q]=v end end
    for _,p in ipairs(s[4]) do s2[p]=true end
    if s[3] then s2.self=true end
    ab(s[6][2],s2)
  elseif k=="Assign" then
    for _,l in ipairs(s[2]) do ae(l,sh) end
    for _,r in ipairs(s[3]) do ae(r,sh) end
  elseif k=="CAssign" then ae(s[3],sh) ae(s[4],sh)
  elseif k=="Do" then ab(s[2][2],sh)
  elseif k=="While" then ae(s[2],sh) ab(s[3][2],sh)
  elseif k=="Repeat" then
    local s2={} if sh then for q,v in pairs(sh) do s2[q]=v end end
    ab(s[2][2],s2)
    for _,st in ipairs(s[2][2]) do
      if st[1]=="LocalVar" then for _,nm in ipairs(st[2]) do s2[nm]=true end
      elseif st[1]=="LocalFunc" then s2[st[2]]=true end
    end
    ae(s[3],s2)
  elseif k=="If" then
    for _,c in ipairs(s[2]) do ae(c[1],sh) ab(c[2][2],sh) end
    if s[3] then ab(s[3][2],sh) end
  elseif k=="ForNum" then
    ae(s[3],sh) ae(s[4],sh) if s[5] then ae(s[5],sh) end
    local s2={} if sh then for q,v in pairs(sh) do s2[q]=v end end
    s2[s[2]]=true
    ab(s[6][2],s2)
  elseif k=="ForIn" then
    for _,e in ipairs(s[3]) do ae(e,sh) end
    local s2={} if sh then for q,v in pairs(sh) do s2[q]=v end end
    for _,nm in ipairs(s[2]) do s2[nm]=true end
    ab(s[4][2],s2)
  elseif k=="Return" then
    for _,e in ipairs(s[2]) do ae(e,sh) end
  elseif k=="CallStmt" then ae(s[2],sh)
  end
end
local function dead_loc(ast)
  return map_blk(ast,function(b)
    local sts=b[2]
    local lv,drop={},{}
    for i=#sts,1,-1 do
      local s=sts[i]
      if s[1]=="LocalVar" then
        local all_ok=true
        for j,nm in ipairs(s[2]) do
          if (s[3][j] and not pure_e(s[3][j])) or lv[nm] then all_ok=false break end
        end
        if all_ok then
          for j=#s[2]+1,#s[3] do
            if not pure_e(s[3][j]) then all_ok=false break end
          end
        end
        if all_ok then drop[i]=true end
        for _,nm in ipairs(s[2]) do lv[nm]=nil end
        add_s_use(s,lv,nil)
      elseif s[1]=="LocalFunc" then
        if not lv[s[2]] then drop[i]=true end
        lv[s[2]]=nil
        add_s_use(s,lv,{[s[2]]=true})
      else
        add_s_use(s,lv,nil)
      end
    end
    local out={}
    for i,s in ipairs(sts) do if not drop[i] then out[#out+1]=s end end
    return {"Block",out}
  end)
end
local function inv_loc_tbl(ast)
  local used={}
  A.walk(ast,function(n)
    local k=n[1]
    if k=="Var" or k=="LocalFunc" or k=="ForNum" then used[n[2]]=true
    elseif k=="LocalVar" or k=="ForIn" or k=="Func" then
      for _,nm in ipairs(n[2]) do used[nm]=true end
    elseif k=="FuncStmt" then
      for _,nm in ipairs(n[4]) do used[nm]=true end
    end
  end)
  local nc=0
  local function fresh()
    repeat nc=nc+1 until not used["_l"..nc]
    local nm="_l"..nc
    used[nm]=true
    return nm
  end
  local function has_n(l,nm)
    for _,x in ipairs(l) do if x==nm then return true end end
    return false
  end
  local function chk_b(sts,s0,nm,ks)
    local chk_s
    local function chk_e(e)
      if type(e)~="table" then return true end
      e=unp(e)
      local k=e[1]
      if k=="Idx" then
        local b,ix=unp(e[2]),unp(e[3])
        if b[1]=="Var" and b[2]==nm then
          if ix[1]=="Num" and ix[2]==math.floor(ix[2]) and ix[2]>=0 and ix[2]<1e9 then
            ks[ix[2]]=true
            return true
          end
          return false
        end
        return chk_e(e[2]) and chk_e(e[3])
      elseif k=="Field" then
        local b=unp(e[2])
        if b[1]=="Var" and b[2]==nm then return false end
        return chk_e(e[2])
      elseif k=="MCall" then
        local b=unp(e[2])
        if b[1]=="Var" and b[2]==nm then return false end
        if not chk_e(e[2]) then return false end
        for _,a in ipairs(e[4]) do if not chk_e(a) then return false end end
        return true
      elseif k=="Var" then return e[2]~=nm
      elseif k=="Call" then
        if not chk_e(e[2]) then return false end
        for _,a in ipairs(e[3]) do if not chk_e(a) then return false end end
        return true
      elseif k=="Bin" then return chk_e(e[3]) and chk_e(e[4])
      elseif k=="Un" then return chk_e(e[3])
      elseif k=="Tbl" then
        for _,f in ipairs(e[2]) do
          if f[1]=="V" then if not chk_e(f[2]) then return false end
          elseif f[1]=="F" then if not chk_e(f[3]) then return false end
          else if not chk_e(f[2]) or not chk_e(f[3]) then return false end end
        end
        return true
      elseif k=="IfExpr" then
        for _,c in ipairs(e[2]) do if not chk_e(c[1]) or not chk_e(c[2]) then return false end end
        return chk_e(e[3])
      elseif k=="Func" then
        if has_n(e[2],nm) then return true end
        return chk_b(e[4][2],1,nm,ks)
      end
      return true
    end
    chk_s=function(s)
      local k=s[1]
      if k=="LocalVar" then
        for _,v in ipairs(s[3]) do if not chk_e(v) then return false end end
        return true
      elseif k=="LocalFunc" then
        if s[2]==nm or has_n(s[3],nm) then return true end
        return chk_b(s[5][2],1,nm,ks)
      elseif k=="FuncStmt" then
        if not chk_e(s[2]) then return false end
        if has_n(s[4],nm) or (s[3] and nm=="self") then return true end
        return chk_b(s[6][2],1,nm,ks)
      elseif k=="Assign" then
        for _,l in ipairs(s[2]) do if not chk_e(l) then return false end end
        for _,r in ipairs(s[3]) do if not chk_e(r) then return false end end
        return true
      elseif k=="CAssign" then return chk_e(s[3]) and chk_e(s[4])
      elseif k=="Do" then return chk_b(s[2][2],1,nm,ks)
      elseif k=="While" then return chk_e(s[2]) and chk_b(s[3][2],1,nm,ks)
      elseif k=="Repeat" then
        if not chk_b(s[2][2],1,nm,ks) then return false end
        for _,st in ipairs(s[2][2]) do
          if (st[1]=="LocalVar" and has_n(st[2],nm)) or (st[1]=="LocalFunc" and st[2]==nm) then return true end
        end
        return chk_e(s[3])
      elseif k=="If" then
        for _,c in ipairs(s[2]) do
          if not chk_e(c[1]) or not chk_b(c[2][2],1,nm,ks) then return false end
        end
        return not s[3] or chk_b(s[3][2],1,nm,ks)
      elseif k=="ForNum" then
        if not chk_e(s[3]) or not chk_e(s[4]) or (s[5] and not chk_e(s[5])) then return false end
        if s[2]==nm then return true end
        return chk_b(s[6][2],1,nm,ks)
      elseif k=="ForIn" then
        for _,v in ipairs(s[3]) do if not chk_e(v) then return false end end
        if has_n(s[2],nm) then return true end
        return chk_b(s[4][2],1,nm,ks)
      elseif k=="Return" then
        for _,v in ipairs(s[2]) do if not chk_e(v) then return false end end
        return true
      elseif k=="CallStmt" then return chk_e(s[2])
      end
      return true
    end
    for i=s0,#sts do
      local st=sts[i]
      if not chk_s(st) then return false end
      if (st[1]=="LocalVar" and has_n(st[2],nm)) or (st[1]=="LocalFunc" and st[2]==nm) then break end
    end
    return true
  end
  local function rw_b(sts,s0,nm,km)
    local rw_s
    local function rw_e(e)
      if type(e)~="table" then return e end
      local u=unp(e)
      local k=u[1]
      if k=="Idx" then
        local b,ix=unp(u[2]),unp(u[3])
        if b[1]=="Var" and b[2]==nm and ix[1]=="Num" and km[ix[2]] then return {"Var",km[ix[2]]} end
        return {"Idx",rw_e(u[2]),rw_e(u[3])}
      elseif k=="Field" then return {"Field",rw_e(u[2]),u[3]}
      elseif k=="Call" then
        local args={} for i,a in ipairs(u[3]) do args[i]=rw_e(a) end
        return {"Call",rw_e(u[2]),args}
      elseif k=="MCall" then
        local args={} for i,a in ipairs(u[4]) do args[i]=rw_e(a) end
        return {"MCall",rw_e(u[2]),u[3],args}
      elseif k=="Bin" then return {"Bin",u[2],rw_e(u[3]),rw_e(u[4])}
      elseif k=="Un" then return {"Un",u[2],rw_e(u[3])}
      elseif k=="Tbl" then
        local fs={}
        for i,f in ipairs(u[2]) do
          if f[1]=="V" then fs[i]={"V",rw_e(f[2])}
          elseif f[1]=="F" then fs[i]={"F",f[2],rw_e(f[3])}
          else fs[i]={"I",rw_e(f[2]),rw_e(f[3])} end
        end
        return {"Tbl",fs}
      elseif k=="IfExpr" then
        local cs={} for i,c in ipairs(u[2]) do cs[i]={rw_e(c[1]),rw_e(c[2])} end
        return {"IfExpr",cs,rw_e(u[3])}
      elseif k=="Func" then
        if has_n(u[2],nm) then return e end
        return {"Func",u[2],u[3],{"Block",rw_b(u[4][2],1,nm,km)}}
      end
      return e
    end
    rw_s=function(s)
      local k=s[1]
      if k=="LocalVar" then
        local es={} for i,v in ipairs(s[3]) do es[i]=rw_e(v) end
        return {"LocalVar",s[2],es}
      elseif k=="LocalFunc" then
        if s[2]==nm or has_n(s[3],nm) then return s end
        return {"LocalFunc",s[2],s[3],s[4],{"Block",rw_b(s[5][2],1,nm,km)}}
      elseif k=="FuncStmt" then
        local b2=rw_e(s[2])
        if has_n(s[4],nm) or (s[3] and nm=="self") then return {"FuncStmt",b2,s[3],s[4],s[5],s[6]} end
        return {"FuncStmt",b2,s[3],s[4],s[5],{"Block",rw_b(s[6][2],1,nm,km)}}
      elseif k=="Assign" then
        local ls,rs={},{}
        for i,l in ipairs(s[2]) do ls[i]=rw_e(l) end
        for i,r in ipairs(s[3]) do rs[i]=rw_e(r) end
        return {"Assign",ls,rs}
      elseif k=="CAssign" then return {"CAssign",s[2],rw_e(s[3]),rw_e(s[4])}
      elseif k=="Do" then return {"Do",{"Block",rw_b(s[2][2],1,nm,km)}}
      elseif k=="While" then return {"While",rw_e(s[2]),{"Block",rw_b(s[3][2],1,nm,km)}}
      elseif k=="Repeat" then
        local nb=rw_b(s[2][2],1,nm,km)
        local sh=false
        for _,st in ipairs(s[2][2]) do
          if (st[1]=="LocalVar" and has_n(st[2],nm)) or (st[1]=="LocalFunc" and st[2]==nm) then sh=true break end
        end
        return {"Repeat",{"Block",nb},sh and s[3] or rw_e(s[3])}
      elseif k=="If" then
        local cs={}
        for i,c in ipairs(s[2]) do cs[i]={rw_e(c[1]),{"Block",rw_b(c[2][2],1,nm,km)}} end
        return {"If",cs,s[3] and {"Block",rw_b(s[3][2],1,nm,km)} or false}
      elseif k=="ForNum" then
        local stp=s[5] and rw_e(s[5]) or false
        local nb=s[2]==nm and s[6] or {"Block",rw_b(s[6][2],1,nm,km)}
        return {"ForNum",s[2],rw_e(s[3]),rw_e(s[4]),stp,nb}
      elseif k=="ForIn" then
        local es={} for i,v in ipairs(s[3]) do es[i]=rw_e(v) end
        local nb=has_n(s[2],nm) and s[4] or {"Block",rw_b(s[4][2],1,nm,km)}
        return {"ForIn",s[2],es,nb}
      elseif k=="Return" then
        local es={} for i,v in ipairs(s[2]) do es[i]=rw_e(v) end
        return {"Return",es}
      elseif k=="CallStmt" then return {"CallStmt",rw_e(s[2])}
      end
      return s
    end
    local out={}
    for i=1,s0-1 do out[i]=sts[i] end
    local stop=false
    for i=s0,#sts do
      if stop then out[i]=sts[i]
      else
        local st=sts[i]
        out[i]=rw_s(st)
        if (st[1]=="LocalVar" and has_n(st[2],nm)) or (st[1]=="LocalFunc" and st[2]==nm) then stop=true end
      end
    end
    return out
  end
  return map_blk(ast,function(b)
    local sts=b[2]
    local i=1
    while i<=#sts do
      local st=sts[i]
      if st[1]=="LocalVar" and #st[2]==1 and #st[3]==1 then
        local rhs=unp(st[3][1])
        if rhs[1]=="Tbl" and #rhs[2]==0 then
          local nm=st[2][1]
          local ks={}
          if chk_b(sts,i+1,nm,ks) then
            local kl={} for k,_ in pairs(ks) do kl[#kl+1]=k end
            if #kl>=1 and #kl<=150 then
              table.sort(kl)
              local km,vn={},{}
              for j,k in ipairs(kl) do
                local v=fresh()
                km[k]=v vn[j]=v
              end
              sts=rw_b(sts,i+1,nm,km)
              sts[i]={"LocalVar",vn,{}}
            end
          end
        end
      end
      i=i+1
    end
    return {"Block",sts}
  end)
end
local function is_eu(e)
  e=unp(e)
  if e[1]~="Call" or not is_unp_e(e[2]) or #e[3]<1 then return false end
  local t=unp(e[3][1])
  if t[1]~="Tbl" or #t[2]~=0 then return false end
  if #e[3]==1 then return true end
  local a2=unp(e[3][2])
  if a2[1]~="Num" or a2[2]~=1 then return false end
  if #e[3]==2 then return true end
  if #e[3]==3 then
    local a3=unp(e[3][3])
    if a3[1]=="Nil" or (a3[1]=="Num" and a3[2]==0) then return true end
    if a3[1]=="Field" and a3[3]=="n" then
      local b=unp(a3[2]) return b[1]=="Tbl" and #b[2]==0
    elseif a3[1]=="Idx" and unp(a3[3])[1]=="Str" and unp(a3[3])[2]=="n" then
      local b=unp(a3[2]) return b[1]=="Tbl" and #b[2]==0
    end
  end
  return false
end
local function unp_one(e)
  local u=unp(e)
  if u[1]=="Call" and is_unp_e(u[2]) and #u[3]==1 then
    local t=unp(u[3][1])
    if t[1]=="Tbl" and #t[2]==1 and t[2][1][1]=="V" then
      return e[1]=="Paren" and {"Paren",t[2][1][2]} or t[2][1][2]
    end
  end
  return nil
end
local function clean_unp(ast)
  local tr_b,tr_s,tr_e,tr_l
  tr_e=function(e)
    if type(e)~="table" then return e end
    local k=e[1]
    if k=="Func" then return {"Func",e[2],e[3],tr_b(e[4],true)}
    elseif k=="Paren" then return {"Paren",tr_e(e[2])}
    elseif k=="Un" then return {"Un",e[2],tr_e(e[3])}
    elseif k=="Bin" then return {"Bin",e[2],tr_e(e[3]),tr_e(e[4])}
    elseif k=="Idx" then return {"Idx",tr_e(e[2]),tr_e(e[3])}
    elseif k=="Field" then return {"Field",tr_e(e[2]),e[3]}
    elseif k=="Call" then return {"Call",tr_e(e[2]),tr_l(e[3])}
    elseif k=="MCall" then return {"MCall",tr_e(e[2]),e[3],tr_l(e[4])}
    elseif k=="Tbl" then
      local fs={}
      for i,f in ipairs(e[2]) do
        if f[1]=="V" then
          local r=i==#e[2] and unp_one(f[2]) or nil
          fs[i]={"V",tr_e(r or f[2])}
        elseif f[1]=="F" then fs[i]={"F",f[2],tr_e(f[3])}
        else fs[i]={"I",tr_e(f[2]),tr_e(f[3])} end
      end
      return {"Tbl",fs}
    elseif k=="IfExpr" then
      local cs={} for i,c in ipairs(e[2]) do cs[i]={tr_e(c[1]),tr_e(c[2])} end
      return {"IfExpr",cs,tr_e(e[3])}
    end
    return e
  end
  tr_l=function(es)
    local out={}
    for i,e in ipairs(es) do
      local r=i==#es and unp_one(e) or nil
      out[i]=tr_e(r or e)
    end
    return out
  end
  tr_s=function(s)
    local k=s[1]
    if k=="LocalVar" then return {"LocalVar",s[2],tr_l(s[3])}
    elseif k=="LocalFunc" then return {"LocalFunc",s[2],s[3],s[4],tr_b(s[5],true)}
    elseif k=="FuncStmt" then return {"FuncStmt",tr_e(s[2]),s[3],s[4],s[5],tr_b(s[6],true)}
    elseif k=="Assign" then
      local ls={} for i,l in ipairs(s[2]) do ls[i]=tr_e(l) end
      return {"Assign",ls,tr_l(s[3])}
    elseif k=="CAssign" then return {"CAssign",s[2],tr_e(s[3]),tr_e(s[4])}
    elseif k=="Do" then return {"Do",tr_b(s[2],false)}
    elseif k=="While" then return {"While",tr_e(s[2]),tr_b(s[3],false)}
    elseif k=="Repeat" then return {"Repeat",tr_b(s[2],false),tr_e(s[3])}
    elseif k=="If" then
      local cs={} for i,c in ipairs(s[2]) do cs[i]={tr_e(c[1]),tr_b(c[2],false)} end
      return {"If",cs,s[3] and tr_b(s[3],false) or false}
    elseif k=="ForNum" then
      return {"ForNum",s[2],tr_e(s[3]),tr_e(s[4]),s[5] and tr_e(s[5]) or false,tr_b(s[6],false)}
    elseif k=="ForIn" then return {"ForIn",s[2],tr_l(s[3]),tr_b(s[4],false)}
    elseif k=="Return" then
      if #s[2]==1 and is_eu(s[2][1]) then return {"Return",{}} end
      return {"Return",tr_l(s[2])}
    elseif k=="CallStmt" then return {"CallStmt",tr_e(s[2])}
    end
    return s
  end
  tr_b=function(b,is_fn)
    local ns={}
    for i,s in ipairs(b[2]) do ns[i]=tr_s(s) end
    if is_fn and #ns>0 and ns[#ns][1]=="Return" and #ns[#ns][2]==0 then
      table.remove(ns,#ns)
    end
    return {"Block",ns}
  end
  return tr_b(ast,true)
end
function M.inv_misc(ast,fold,wm)
  ast=norm_env(ast)
  ast=M.inv_wrap(ast)
  ast=M.inv_anti(ast)
  ast=M.inv_wm(ast)
  ast=M.inv_split(ast)
  ast=M.inv_prox(ast)
  ast=inv_loc_tbl(ast)
  ast=M.inv_prox(ast)
  ast=clean_unp(ast)
  if fold then ast=fold(ast) end
  ast=dead_loc(ast)
  return ast
end
M.map_blk=map_blk
return M
