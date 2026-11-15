local A=require("src.frontend.ast")
local M={}
local unp=A.unp
local P={
  ["or"]=1,["and"]=2,
  ["<"]=3,[">"]=3,["<="]=3,[">="]=3,["~="]=3,["=="]=3,
  [".."]=4,
  ["+"]=5,["-"]=5,
  ["*"]=6,["/"]=6,["//"]=6,["%"]=6,
  ["^"]=8
}
local RA={[".."]=1,["^"]=1}
local function ep(x)
  local k=x[1]
  if k=="Bin" then return P[x[2]] or 0
  elseif k=="Un" then return 7
  elseif k=="IfExpr" then return 0
  elseif k=="Paren" then return ep(x[2]) end
  return 9
end
local function num(v)
  if v~=v then return "(0/0)" end
  if v==math.huge then return "(1/0)" end
  if v==-math.huge then return "(-1/0)" end
  if v==0 then
    if 1/v<0 then return "-0" end
    return "0"
  end
  if math.floor(v)==v and math.abs(v)<4503599627370496 then
    return string.format("%.0f",v)
  end
  local s=tostring(v)
  if tonumber(s)==v then return s end
  return string.format("%.17g",v)
end
local ES={[7]="\\a",[8]="\\b",[9]="\\t",[10]="\\n",[11]="\\v",[12]="\\f",[13]="\\r",[34]='\\"',[92]="\\\\"}
local function str(s)
  local b={}
  for i=1,#s do
    local c=string.byte(s,i)
    if ES[c] then b[#b+1]=ES[c]
    elseif c>=32 and c<=126 then b[#b+1]=string.char(c)
    else b[#b+1]=string.format("\\%03d",c) end
  end
  return '"'..table.concat(b)..'"'
end
local ub,ue
local function upx(x)
  local k=x[1]
  if k=="Var" then return x[2]
  elseif k=="Field" then return upx(x[2]).."."..x[3]
  elseif k=="Idx" then return upx(x[2]).."["..ue(x[3],false).."]"
  elseif k=="Call" then
    local as={}
    local xs=x[3]
    for i=1,#xs do as[i]=ue(xs[i],i==#xs) end
    return upx(x[2]).."("..table.concat(as,", ")..")"
  elseif k=="MCall" then
    local as={}
    local xs=x[4]
    for i=1,#xs do as[i]=ue(xs[i],i==#xs) end
    return upx(x[2])..":"..x[3].."("..table.concat(as,", ")..")"
  elseif k=="Paren" then
    return "("..ue(x[2],true)..")"
  end
  return "("..ue(x,true)..")"
end
ue=function(e,mr)
  local k=e[1]
  if k=="Nil" then return "nil"
  elseif k=="Bool" then return e[2] and "true" or "false"
  elseif k=="Num" then return num(e[2])
  elseif k=="Str" then return str(e[2])
  elseif k=="Vararg" then return "..."
  elseif k=="Var" or k=="Field" or k=="Idx" or k=="Call" or k=="MCall" then
    return upx(e)
  elseif k=="Paren" then
    local ix=unp(e[2])
    if mr and (ix[1]=="Call" or ix[1]=="MCall" or ix[1]=="Vararg") then
      return "("..ue(ix,true)..")"
    end
    return ue(e[2],mr)
  elseif k=="Tbl" then
    local fs=e[2]
    if #fs==0 then return "{}" end
    local r={}
    for i,f in ipairs(fs) do
      if f[1]=="V" then r[i]=ue(f[2],i==#fs)
      elseif f[1]=="F" then r[i]=f[2].." = "..ue(f[3],false)
      else r[i]="["..ue(f[2],false).."] = "..ue(f[3],false) end
    end
    return "{"..table.concat(r,", ").."}"
  elseif k=="Func" then
    local ps={}
    for i,p in ipairs(e[2]) do ps[i]=p end
    if e[3] then ps[#ps+1]="..." end
    local bs=ub(e[4],"  ")
    if bs=="" then return "function("..table.concat(ps,", ")..") end" end
    return "function("..table.concat(ps,", ")..")\n"..bs.."\nend"
  elseif k=="Un" then
    local op,x=e[2],e[3]
    local sx=ue(x,false)
    if ep(x)<7 then sx="("..sx..")"
    elseif op=="-" and sx:sub(1,1)=="-" then sx="("..sx..")" end
    return (op=="not" and "not " or op)..sx
  elseif k=="Bin" then
    local op,l,r=e[2],e[3],e[4]
    local p=P[op]
    local sl,sr=ue(l,false),ue(r,false)
    local pl,pr=ep(l),ep(r)
    if pl<p or (RA[op] and pl==p) then sl="("..sl..")" end
    if pr<p or (not RA[op] and pr==p) then sr="("..sr..")" end
    return sl.." "..op.." "..sr
  elseif k=="IfExpr" then
    local b={}
    for i,c in ipairs(e[2]) do
      b[#b+1]=(i==1 and "if " or " elseif ")..ue(c[1],false).." then "..ue(c[2],false)
    end
    b[#b+1]=" else "..ue(e[3],false)
    return table.concat(b)
  end
  error("bad expr "..tostring(k))
end
local function us(s,ind)
  local k=s[1]
  if k=="LocalVar" then
    local ns=table.concat(s[2],", ")
    if #s[3]==0 then return ind.."local "..ns end
    local vs={}
    local xs=s[3]
    for i=1,#xs do vs[i]=ue(xs[i],i==#xs) end
    return ind.."local "..ns.." = "..table.concat(vs,", ")
  elseif k=="LocalFunc" then
    local ps={}
    for i,p in ipairs(s[3]) do ps[i]=p end
    if s[4] then ps[#ps+1]="..." end
    local bs=ub(s[5],ind.."  ")
    if bs=="" then return ind.."local function "..s[2].."("..table.concat(ps,", ")..") end" end
    return ind.."local function "..s[2].."("..table.concat(ps,", ")..")\n"..bs.."\n"..ind.."end"
  elseif k=="FuncStmt" then
    local ps={}
    for i,p in ipairs(s[4]) do ps[i]=p end
    if s[5] then ps[#ps+1]="..." end
    local nm=ue(s[2],false)..(s[3] and (":"..s[3]) or "")
    local bs=ub(s[6],ind.."  ")
    if bs=="" then return ind.."function "..nm.."("..table.concat(ps,", ")..") end" end
    return ind.."function "..nm.."("..table.concat(ps,", ")..")\n"..bs.."\n"..ind.."end"
  elseif k=="Assign" then
    local ls,rs={},{}
    for i,l in ipairs(s[2]) do ls[i]=upx(l) end
    local xs=s[3]
    for i=1,#xs do rs[i]=ue(xs[i],i==#xs) end
    local line=table.concat(ls,", ").." = "..table.concat(rs,", ")
    return ind..line
  elseif k=="CAssign" then
    local line=upx(s[3]).." "..s[2].." "..ue(s[4],false)
    return ind..line
  elseif k=="Do" then
    local bs=ub(s[2],ind.."  ")
    if bs=="" then return ind.."do end" end
    return ind.."do\n"..bs.."\n"..ind.."end"
  elseif k=="While" then
    local bs=ub(s[3],ind.."  ")
    local h=ind.."while "..ue(s[2],false).." do"
    if bs=="" then return h.." end" end
    return h.."\n"..bs.."\n"..ind.."end"
  elseif k=="Repeat" then
    local bs=ub(s[2],ind.."  ")
    if bs=="" then return ind.."repeat until "..ue(s[3],false) end
    return ind.."repeat\n"..bs.."\n"..ind.."until "..ue(s[3],false)
  elseif k=="If" then
    local out={}
    for i,c in ipairs(s[2]) do
      local kw=i==1 and "if " or "elseif "
      out[#out+1]=ind..kw..ue(c[1],false).." then"
      local bs=ub(c[2],ind.."  ")
      if bs~="" then out[#out+1]=bs end
    end
    if s[3] then
      out[#out+1]=ind.."else"
      local bs=ub(s[3],ind.."  ")
      if bs~="" then out[#out+1]=bs end
    end
    out[#out+1]=ind.."end"
    return table.concat(out,"\n")
  elseif k=="ForNum" then
    local hd=ind.."for "..s[2].." = "..ue(s[3],false)..", "..ue(s[4],false)
    if s[5] then hd=hd..", "..ue(s[5],false) end
    hd=hd.." do"
    local bs=ub(s[6],ind.."  ")
    if bs=="" then return hd.." end" end
    return hd.."\n"..bs.."\n"..ind.."end"
  elseif k=="ForIn" then
    local es={}
    for i,e in ipairs(s[3]) do es[i]=ue(e,i==#s[3]) end
    local hd=ind.."for "..table.concat(s[2],", ").." in "..table.concat(es,", ").." do"
    local bs=ub(s[4],ind.."  ")
    if bs=="" then return hd.." end" end
    return hd.."\n"..bs.."\n"..ind.."end"
  elseif k=="Return" then
    if #s[2]==0 then return ind.."return" end
    local es={}
    local xs=s[2]
    for i=1,#xs do es[i]=ue(xs[i],i==#xs) end
    return ind.."return "..table.concat(es,", ")
  elseif k=="Break" then return ind.."break"
  elseif k=="Continue" then return ind.."continue"
  elseif k=="CallStmt" then
    return ind..upx(s[2])
  end
  error("bad stmt "..tostring(k))
end
ub=function(b,ind)
  local r={}
  for i,s in ipairs(b[2]) do
    local line=us(s,ind)
    if i>1 and line:sub(#ind+1,#ind+1)=="(" then
      line=ind..";"..line:sub(#ind+1)
    end
    r[i]=line
  end
  return table.concat(r,"\n")
end
function M.expr(e) return ue(e,false) end
function M.stmt(s) return us(s,"") end
function M.emit(b) return ub(b,"") end
return M
