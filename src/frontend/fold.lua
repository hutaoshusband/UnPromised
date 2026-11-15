local A=require("src.frontend.ast")
local M={}
local unp=A.unp
local fl=math.floor
local function lit(x)
  local k=x[1]
  if k=="Nil" then return true,nil
  elseif k=="Bool" or k=="Num" or k=="Str" then return true,x[2] end
  return false,nil
end
local function tru(x)
  local k=x[1]
  if k=="Nil" then return false end
  if k=="Bool" then return x[2] end
  if k=="Num" or k=="Str" or k=="Tbl" or k=="Func" then return true end
  return nil
end
local function mkv(v)
  if v==nil then return {"Nil"} end
  local t=type(v)
  if t=="boolean" then return {"Bool",v}
  elseif t=="number" then
    if v~=v then return nil end
    return {"Num",v}
  elseif t=="string" then return {"Str",v} end
  return nil
end
local function fe(e,xf)
  local k=e[1]
  if k=="Paren" then
    local x=fe(e[2],xf)
    local lk=x[1]
    if lk=="Nil" or lk=="Bool" or lk=="Num" or lk=="Str" then return x end
    local r={"Paren",x}
    return xf and xf(r) or r
  elseif k=="Un" then
    local op,x=e[2],fe(e[3],xf)
    local xu=unp(x)
    local r
    if op=="-" and xu[1]=="Num" then
      local v=-xu[2]
      if v==v then r={"Num",v} end
    elseif op=="not" then
      local tv=tru(xu)
      if tv~=nil then r={"Bool",not tv} end
    elseif op=="#" and xu[1]=="Str" then
      r={"Num",#xu[2]}
    end
    r=r or {"Un",op,x}
    return xf and xf(r) or r
  elseif k=="Bin" then
    local op=e[2]
    local l=fe(e[3],xf)
    local r0=fe(e[4],xf)
    local lu,ru=unp(l),unp(r0)
    local res
    if op=="and" then
      local tl=tru(lu)
      if tl==false then res=l elseif tl==true then res=r0 end
    elseif op=="or" then
      local tl=tru(lu)
      if tl==true then res=l elseif tl==false then res=r0 end
    elseif lu[1]=="Num" and ru[1]=="Num" then
      local a,b=lu[2],ru[2]
      if op=="+" then res=mkv(a+b)
      elseif op=="-" then res=mkv(a-b)
      elseif op=="*" then res=mkv(a*b)
      elseif op=="/" and b~=0 then res=mkv(a/b)
      elseif op=="//" and b~=0 then res=mkv(fl(a/b))
      elseif op=="%" and b~=0 then res=mkv(a%b)
      elseif op=="^" then res=mkv(a^b)
      elseif op=="<" then res={"Bool",a<b}
      elseif op=="<=" then res={"Bool",a<=b}
      elseif op==">" then res={"Bool",a>b}
      elseif op==">=" then res={"Bool",a>=b}
      elseif op=="==" then res={"Bool",a==b}
      elseif op=="~=" then res={"Bool",a~=b}
      elseif op==".." then
        res={"Str",tostring(a)..tostring(b)}
      end
    elseif lu[1]=="Str" and ru[1]=="Str" then
      local a,b=lu[2],ru[2]
      if op==".." then res={"Str",a..b}
      elseif op=="<" then res={"Bool",a<b}
      elseif op=="<=" then res={"Bool",a<=b}
      elseif op==">" then res={"Bool",a>b}
      elseif op==">=" then res={"Bool",a>=b}
      elseif op=="==" then res={"Bool",a==b}
      elseif op=="~=" then res={"Bool",a~=b}
      end
    elseif op==".." and (lu[1]=="Str" or lu[1]=="Num") and (ru[1]=="Str" or ru[1]=="Num") then
      res={"Str",tostring(lu[2])..tostring(ru[2])}
    elseif op=="==" or op=="~=" then
      local ok1,v1=lit(lu)
      local ok2,v2=lit(ru)
      if ok1 and ok2 then
        local eq=(lu[1]==ru[1] and v1==v2)
        res={"Bool",op=="==" and eq or not eq}
      end
    end
    res=res or {"Bin",op,l,r0}
    return xf and xf(res) or res
  elseif k=="Tbl" then
    local fs={}
    for i,f in ipairs(e[2]) do
      if f[1]=="V" then fs[i]={"V",fe(f[2],xf)}
      elseif f[1]=="F" then fs[i]={"F",f[2],fe(f[3],xf)}
      else fs[i]={"I",fe(f[2],xf),fe(f[3],xf)} end
    end
    local r={"Tbl",fs}
    return xf and xf(r) or r
  elseif k=="Idx" then
    local r={"Idx",fe(e[2],xf),fe(e[3],xf)}
    return xf and xf(r) or r
  elseif k=="Field" then
    local r={"Field",fe(e[2],xf),e[3]}
    return xf and xf(r) or r
  elseif k=="Call" then
    local as={}
    for i,a in ipairs(e[3]) do as[i]=fe(a,xf) end
    local r={"Call",fe(e[2],xf),as}
    return xf and xf(r) or r
  elseif k=="MCall" then
    local as={}
    for i,a in ipairs(e[4]) do as[i]=fe(a,xf) end
    local r={"MCall",fe(e[2],xf),e[3],as}
    return xf and xf(r) or r
  elseif k=="Func" then
    local r={"Func",e[2],e[3],M.fold(e[4],xf)}
    return xf and xf(r) or r
  elseif k=="IfExpr" then
    local cs={}
    for i,c in ipairs(e[2]) do cs[i]={fe(c[1],xf),fe(c[2],xf)} end
    local r={"IfExpr",cs,fe(e[3],xf)}
    return xf and xf(r) or r
  end
  return xf and xf(e) or e
end
local function fs(s,xf)
  local k=s[1]
  if k=="LocalVar" then
    local vs={}
    for i,v in ipairs(s[3]) do vs[i]=fe(v,xf) end
    return {"LocalVar",s[2],vs}
  elseif k=="LocalFunc" then
    return {"LocalFunc",s[2],s[3],s[4],M.fold(s[5],xf)}
  elseif k=="FuncStmt" then
    return {"FuncStmt",fe(s[2],xf),s[3],s[4],s[5],M.fold(s[6],xf)}
  elseif k=="Assign" then
    local ls,rs={},{}
    for i,l in ipairs(s[2]) do ls[i]=fe(l,xf) end
    for i,r in ipairs(s[3]) do rs[i]=fe(r,xf) end
    return {"Assign",ls,rs}
  elseif k=="CAssign" then
    return {"CAssign",s[2],fe(s[3],xf),fe(s[4],xf)}
  elseif k=="Do" then
    return {"Do",M.fold(s[2],xf)}
  elseif k=="While" then
    return {"While",fe(s[2],xf),M.fold(s[3],xf)}
  elseif k=="Repeat" then
    return {"Repeat",M.fold(s[2],xf),fe(s[3],xf)}
  elseif k=="If" then
    local cs={}
    for i,c in ipairs(s[2]) do cs[i]={fe(c[1],xf),M.fold(c[2],xf)} end
    local el=s[3] and M.fold(s[3],xf) or false
    return {"If",cs,el}
  elseif k=="ForNum" then
    local st=s[5] and fe(s[5],xf) or false
    return {"ForNum",s[2],fe(s[3],xf),fe(s[4],xf),st,M.fold(s[6],xf)}
  elseif k=="ForIn" then
    local es={}
    for i,e in ipairs(s[3]) do es[i]=fe(e,xf) end
    return {"ForIn",s[2],es,M.fold(s[4],xf)}
  elseif k=="Return" then
    local es={}
    for i,e in ipairs(s[2]) do es[i]=fe(e,xf) end
    return {"Return",es}
  elseif k=="CallStmt" then
    return {"CallStmt",fe(s[2],xf)}
  end
  return s
end
function M.fold(n,xf)
  if n[1]=="Block" then
    local sts={}
    for i,s in ipairs(n[2]) do sts[i]=fs(s,xf) end
    return {"Block",sts}
  end
  return fe(n,xf)
end
return M
