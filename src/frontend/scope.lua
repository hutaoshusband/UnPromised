local A=require("src.frontend.ast")
local M={}
local unp=A.unp
local function ext(sh,nms)
  local r={}
  for k,v in pairs(sh) do r[k]=v end
  if type(nms)=="string" then r[nms]=true
  else for _,x in ipairs(nms) do r[x]=true end end
  return r
end
local rb
local function re(e,pv,pvs,sh)
  local k=e[1]
  if k=="Idx" then
    local t=re(e[2],pv,pvs,sh)
    local ix=re(e[3],pv,pvs,sh)
    if not sh[pv] then
      local tu,ku=unp(t),unp(ix)
      if tu[1]=="Var" and tu[2]==pv and ku[1]=="Num" then
        local n=ku[2]
        if n>=1 and n<=#pvs and math.floor(n)==n then
          return {"Str",pvs[n]}
        end
      end
    end
    return {"Idx",t,ix}
  elseif k=="Field" then return {"Field",re(e[2],pv,pvs,sh),e[3]}
  elseif k=="Paren" then return {"Paren",re(e[2],pv,pvs,sh)}
  elseif k=="Un" then return {"Un",e[2],re(e[3],pv,pvs,sh)}
  elseif k=="Bin" then return {"Bin",e[2],re(e[3],pv,pvs,sh),re(e[4],pv,pvs,sh)}
  elseif k=="Call" then
    local as={}
    for i,a in ipairs(e[3]) do as[i]=re(a,pv,pvs,sh) end
    return {"Call",re(e[2],pv,pvs,sh),as}
  elseif k=="MCall" then
    local as={}
    for i,a in ipairs(e[4]) do as[i]=re(a,pv,pvs,sh) end
    return {"MCall",re(e[2],pv,pvs,sh),e[3],as}
  elseif k=="Tbl" then
    local fs={}
    for i,f in ipairs(e[2]) do
      if f[1]=="V" then fs[i]={"V",re(f[2],pv,pvs,sh)}
      elseif f[1]=="F" then fs[i]={"F",f[2],re(f[3],pv,pvs,sh)}
      else fs[i]={"I",re(f[2],pv,pvs,sh),re(f[3],pv,pvs,sh)} end
    end
    return {"Tbl",fs}
  elseif k=="Func" then
    return {"Func",e[2],e[3],rb(e[4],pv,pvs,ext(sh,e[2]))}
  elseif k=="IfExpr" then
    local cs={}
    for i,c in ipairs(e[2]) do cs[i]={re(c[1],pv,pvs,sh),re(c[2],pv,pvs,sh)} end
    return {"IfExpr",cs,re(e[3],pv,pvs,sh)}
  end
  return e
end
rb=function(blk,pv,pvs,sh)
  local ns={}
  local cs=ext(sh,{})
  for _,s in ipairs(blk[2]) do
    local k=s[1]
    if k=="LocalVar" then
      local vs={}
      for i,v in ipairs(s[3]) do vs[i]=re(v,pv,pvs,cs) end
      ns[#ns+1]={"LocalVar",s[2],vs}
      cs=ext(cs,s[2])
    elseif k=="LocalFunc" then
      cs=ext(cs,s[2])
      ns[#ns+1]={"LocalFunc",s[2],s[3],s[4],rb(s[5],pv,pvs,ext(cs,s[3]))}
    elseif k=="FuncStmt" then
      local sb=ext(cs,s[4])
      if s[3] then sb=ext(sb,"self") end
      ns[#ns+1]={"FuncStmt",re(s[2],pv,pvs,cs),s[3],s[4],s[5],rb(s[6],pv,pvs,sb)}
    elseif k=="Assign" then
      local ls,rs={},{}
      for i,l in ipairs(s[2]) do ls[i]=re(l,pv,pvs,cs) end
      for i,r in ipairs(s[3]) do rs[i]=re(r,pv,pvs,cs) end
      ns[#ns+1]={"Assign",ls,rs}
    elseif k=="CAssign" then
      ns[#ns+1]={"CAssign",s[2],re(s[3],pv,pvs,cs),re(s[4],pv,pvs,cs)}
    elseif k=="Do" then
      ns[#ns+1]={"Do",rb(s[2],pv,pvs,cs)}
    elseif k=="While" then
      ns[#ns+1]={"While",re(s[2],pv,pvs,cs),rb(s[3],pv,pvs,cs)}
    elseif k=="Repeat" then
      local nb,sh2=rb(s[2],pv,pvs,cs)
      ns[#ns+1]={"Repeat",nb,re(s[3],pv,pvs,sh2)}
    elseif k=="If" then
      local css={}
      for i,c in ipairs(s[2]) do css[i]={re(c[1],pv,pvs,cs),rb(c[2],pv,pvs,cs)} end
      local el=s[3] and rb(s[3],pv,pvs,cs) or false
      ns[#ns+1]={"If",css,el}
    elseif k=="ForNum" then
      local st=s[5] and re(s[5],pv,pvs,cs) or false
      ns[#ns+1]={"ForNum",s[2],re(s[3],pv,pvs,cs),re(s[4],pv,pvs,cs),st,rb(s[6],pv,pvs,ext(cs,s[2]))}
    elseif k=="ForIn" then
      local es={}
      for i,e in ipairs(s[3]) do es[i]=re(e,pv,pvs,cs) end
      ns[#ns+1]={"ForIn",s[2],es,rb(s[4],pv,pvs,ext(cs,s[2]))}
    elseif k=="Return" then
      local es={}
      for i,e in ipairs(s[2]) do es[i]=re(e,pv,pvs,cs) end
      ns[#ns+1]={"Return",es}
    elseif k=="CallStmt" then
      ns[#ns+1]={"CallStmt",re(s[2],pv,pvs,cs)}
    else
      ns[#ns+1]=s
    end
  end
  return {"Block",ns},cs
end
function M.r_pool(blk,pv,pvs,sh)
  local nb=rb(blk,pv,pvs,sh or {})
  return nb
end
return M
