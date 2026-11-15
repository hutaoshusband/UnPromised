local L=require("src.frontend.lex")
local M={}
local BL={["end"]=1,["else"]=1,["elseif"]=1,["until"]=1}
local PREC={
  ["or"]={1,1},["and"]={2,2},
  ["<"]={3,3},[">"]={3,3},["<="]={3,3},[">="]={3,3},["~="]={3,3},["=="]={3,3},
  [".."]={4,3},
  ["+"]={5,5},["-"]={5,5},
  ["*"]={6,6},["/"]={6,6},["//"]={6,6},["%"]={6,6},
  ["^"]={8,7}
}
local CA={["+="]=1,["-="]=1,["*="]=1,["/="]=1,["%="]=1,["^="]=1,["//="]=1,["..="]=1}
local NONC={["="]=1,["("]=1,["["]=1,["."]=1,[":"]=1,["{"]=1}
function M.unp(x)
  while x and x[1]=="Paren" do x=x[2] end
  return x
end
function M.eq(a,b)
  if a==b then return true end
  if type(a)~="table" or type(b)~="table" then return false end
  local na,nb=#a,#b
  if na~=nb then return false end
  for i=1,na do
    if not M.eq(a[i],b[i]) then return false end
  end
  return true
end
function M.cp(x)
  if type(x)~="table" then return x end
  local r={}
  for i=1,#x do r[i]=M.cp(x[i]) end
  return r
end
function M.walk(n,fn)
  if type(n)~="table" then return end
  local k=n[1]
  if type(k)~="string" then
    for i=1,#n do M.walk(n[i],fn) end
    return
  end
  fn(n)
  if k=="Block" then
    for _,s in ipairs(n[2]) do M.walk(s,fn) end
  elseif k=="LocalVar" or k=="Assign" then
    for _,e in ipairs(n[3]) do M.walk(e,fn) end
    if k=="Assign" then
      for _,l in ipairs(n[2]) do M.walk(l,fn) end
    end
  elseif k=="LocalFunc" or k=="Func" then
    local bi=k=="LocalFunc" and 5 or 4
    M.walk(n[bi],fn)
  elseif k=="FuncStmt" then
    M.walk(n[2],fn)
    M.walk(n[6],fn)
  elseif k=="CAssign" then
    M.walk(n[3],fn)
    M.walk(n[4],fn)
  elseif k=="Do" then
    M.walk(n[2],fn)
  elseif k=="While" then
    M.walk(n[2],fn)
    M.walk(n[3],fn)
  elseif k=="Repeat" then
    M.walk(n[2],fn)
    M.walk(n[3],fn)
  elseif k=="If" then
    for _,c in ipairs(n[2]) do
      M.walk(c[1],fn)
      M.walk(c[2],fn)
    end
    if n[3] then M.walk(n[3],fn) end
  elseif k=="IfExpr" then
    for _,c in ipairs(n[2]) do
      M.walk(c[1],fn)
      M.walk(c[2],fn)
    end
    M.walk(n[3],fn)
  elseif k=="ForNum" then
    M.walk(n[3],fn)
    M.walk(n[4],fn)
    if n[5] then M.walk(n[5],fn) end
    M.walk(n[6],fn)
  elseif k=="ForIn" then
    for _,e in ipairs(n[3]) do M.walk(e,fn) end
    M.walk(n[4],fn)
  elseif k=="Return" or k=="Ret" then
    for _,e in ipairs(n[2]) do M.walk(e,fn) end
  elseif k=="CallStmt" or k=="Paren" then
    M.walk(n[2],fn)
  elseif k=="Tbl" then
    for _,f in ipairs(n[2]) do
      if f[1]=="V" then M.walk(f[2],fn)
      elseif f[1]=="F" then M.walk(f[3],fn)
      else M.walk(f[2],fn) M.walk(f[3],fn) end
    end
  elseif k=="Idx" then
    M.walk(n[2],fn) M.walk(n[3],fn)
  elseif k=="Field" then
    M.walk(n[2],fn)
  elseif k=="Call" then
    M.walk(n[2],fn)
    for _,a in ipairs(n[3]) do M.walk(a,fn) end
  elseif k=="MCall" then
    M.walk(n[2],fn)
    for _,a in ipairs(n[4]) do M.walk(a,fn) end
  elseif k=="Bin" then
    M.walk(n[3],fn) M.walk(n[4],fn)
  elseif k=="Un" then
    M.walk(n[3],fn)
  elseif k=="_EXPAND" then
    M.walk(n[2],fn) M.walk(n[4],fn)
    if n[5] then M.walk(n[5],fn) end
  elseif k=="_PACK" or k=="Interp" then
    M.walk(n[2],fn)
    if n[3] then M.walk(n[3],fn) end
  end
end
function M.parse(src)
  local tk=L.lex(src)
  local i=1
  local function cur() return tk[i] end
  local function nxt() return tk[i+1] end
  local function adv() local t=tk[i] i=i+1 return t end
  local function chk(k,v)
    local t=tk[i]
    return t.k==k and (not v or t.v==v)
  end
  local function eat(k,v)
    if not chk(k,v) then
      local t=tk[i]
      error("exp "..(v or k).." got "..t.k..":"..tostring(t.v).." @"..i)
    end
    return adv()
  end
  local pexp,pblk,pfn
  local function pel()
    local r={pexp(0)}
    while chk("SYM",",") do adv() r[#r+1]=pexp(0) end
    return r
  end
  local function pargs()
    if chk("SYM","(") then
      adv()
      local a={}
      if not chk("SYM",")") then a=pel() end
      eat("SYM",")")
      return a
    elseif chk("SYM","{") then
      return {pexp(0)}
    elseif chk("STR") or chk("LSTR") then
      return {{"Str",adv().v}}
    end
    error("bad args")
  end
  local function ptbl()
    eat("SYM","{")
    local fs={}
    while not chk("SYM","}") do
      if chk("SYM","[") then
        adv()
        local k=pexp(0)
        eat("SYM","]")
        eat("SYM","=")
        fs[#fs+1]={"I",k,pexp(0)}
      elseif chk("ID") and nxt().k=="SYM" and nxt().v=="=" then
        local nm=adv().v
        adv()
        fs[#fs+1]={"F",nm,pexp(0)}
      else
        fs[#fs+1]={"V",pexp(0)}
      end
      if chk("SYM",",") or chk("SYM",";") then adv() else break end
    end
    eat("SYM","}")
    return {"Tbl",fs}
  end
  pfn=function()
    eat("SYM","(")
    local ps={}
    local va=false
    if not chk("SYM",")") then
      while true do
        if chk("SYM","...") then
          adv() va=true break
        end
        ps[#ps+1]=eat("ID").v
        if chk("SYM",",") then adv() else break end
      end
    end
    eat("SYM",")")
    local b=pblk()
    eat("KW","end")
    return ps,va,b
  end
  local function ppfx()
    local e
    if chk("ID") then
      e={"Var",adv().v}
    elseif chk("SYM","(") then
      adv()
      e={"Paren",pexp(0)}
      eat("SYM",")")
    else
      local t=cur()
      error("bad pfx "..t.k..":"..tostring(t.v).." @"..i)
    end
    while true do
      if chk("SYM",".") then
        adv()
        e={"Field",e,eat("ID").v}
      elseif chk("SYM","[") then
        adv()
        e={"Idx",e,pexp(0)}
        eat("SYM","]")
      elseif chk("SYM",":") then
        adv()
        local m=eat("ID").v
        e={"MCall",e,m,pargs()}
      elseif chk("SYM","(") or chk("SYM","{") or chk("STR") or chk("LSTR") then
        e={"Call",e,pargs()}
      else
        break
      end
    end
    return e
  end
  local function psimp()
    local t=cur()
    if t.k=="NUM" then adv() return {"Num",t.v}
    elseif t.k=="STR" or t.k=="LSTR" then adv() return {"Str",t.v}
    elseif t.k=="KW" then
      if t.v=="nil" then adv() return {"Nil"}
      elseif t.v=="true" then adv() return {"Bool",true}
      elseif t.v=="false" then adv() return {"Bool",false}
      elseif t.v=="function" then
        adv()
        local ps,va,b=pfn()
        return {"Func",ps,va,b}
      elseif t.v=="if" then
        adv()
        local cs={}
        local c=pexp(0)
        eat("KW","then")
        cs[#cs+1]={c,pexp(0)}
        while chk("KW","elseif") do
          adv()
          local c2=pexp(0)
          eat("KW","then")
          cs[#cs+1]={c2,pexp(0)}
        end
        eat("KW","else")
        local el=pexp(0)
        return {"IfExpr",cs,el}
      end
    elseif t.k=="SYM" then
      if t.v=="..." then adv() return {"Vararg"}
      elseif t.v=="{" then return ptbl() end
    end
    return ppfx()
  end
  pexp=function(mp)
    local l
    if (chk("KW","not") or chk("SYM","-") or chk("SYM","#")) then
      local op=adv().v
      l={"Un",op,pexp(7)}
    else
      l=psimp()
    end
    while true do
      local t=cur()
      local p=PREC[t.v]
      if not p or (t.k~="SYM" and t.k~="KW") or p[1]<mp then break end
      local op=adv().v
      local r=pexp(p[2]+1)
      l={"Bin",op,l,r}
    end
    return l
  end
  local function pstmt()
    local t=cur()
    if t.k=="KW" then
      if t.v=="local" then
        adv()
        if chk("KW","function") then
          adv()
          local nm=eat("ID").v
          local ps,va,b=pfn()
          return {"LocalFunc",nm,ps,va,b}
        end
        local nms={eat("ID").v}
        while chk("SYM",",") do adv() nms[#nms+1]=eat("ID").v end
        local vs={}
        if chk("SYM","=") then adv() vs=pel() end
        return {"LocalVar",nms,vs}
      elseif t.v=="function" then
        adv()
        local e={"Var",eat("ID").v}
        while chk("SYM",".") do adv() e={"Field",e,eat("ID").v} end
        local mth=false
        if chk("SYM",":") then adv() mth=eat("ID").v end
        local ps,va,b=pfn()
        return {"FuncStmt",e,mth,ps,va,b}
      elseif t.v=="do" then
        adv()
        local b=pblk()
        eat("KW","end")
        return {"Do",b}
      elseif t.v=="while" then
        adv()
        local c=pexp(0)
        eat("KW","do")
        local b=pblk()
        eat("KW","end")
        return {"While",c,b}
      elseif t.v=="repeat" then
        adv()
        local b=pblk()
        eat("KW","until")
        local c=pexp(0)
        return {"Repeat",b,c}
      elseif t.v=="if" then
        adv()
        local cs={}
        local c=pexp(0)
        eat("KW","then")
        cs[#cs+1]={c,pblk()}
        while chk("KW","elseif") do
          adv()
          local c2=pexp(0)
          eat("KW","then")
          cs[#cs+1]={c2,pblk()}
        end
        local el=false
        if chk("KW","else") then adv() el=pblk() end
        eat("KW","end")
        return {"If",cs,el}
      elseif t.v=="for" then
        adv()
        local nm=eat("ID").v
        if chk("SYM","=") then
          adv()
          local a=pexp(0)
          eat("SYM",",")
          local b=pexp(0)
          local s=false
          if chk("SYM",",") then adv() s=pexp(0) end
          eat("KW","do")
          local blk=pblk()
          eat("KW","end")
          return {"ForNum",nm,a,b,s,blk}
        else
          local vs={nm}
          while chk("SYM",",") do adv() vs[#vs+1]=eat("ID").v end
          eat("KW","in")
          local es=pel()
          eat("KW","do")
          local blk=pblk()
          eat("KW","end")
          return {"ForIn",vs,es,blk}
        end
      elseif t.v=="return" then
        adv()
        local es={}
        local nt=cur()
        if not (nt.k=="EOF" or (nt.k=="SYM" and nt.v==";") or (nt.k=="KW" and BL[nt.v])) then
          es=pel()
        end
        return {"Return",es}
      elseif t.v=="break" then
        adv()
        return {"Break"}
      end
    elseif t.k=="ID" and t.v=="continue" then
      local nx=nxt()
      local isc=true
      if nx.k=="STR" or nx.k=="LSTR" then isc=false
      elseif nx.k=="SYM" and (NONC[nx.v] or CA[nx.v] or nx.v==",") then isc=false end
      if isc then adv() return {"Continue"} end
    end
    local e=ppfx()
    if e[1]=="Call" or e[1]=="MCall" then return {"CallStmt",e} end
    if chk("SYM") and CA[cur().v] then
      local op=adv().v
      return {"CAssign",op,e,pexp(0)}
    end
    local ls={e}
    while chk("SYM",",") do adv() ls[#ls+1]=ppfx() end
    eat("SYM","=")
    local rs=pel()
    return {"Assign",ls,rs}
  end
  pblk=function()
    local sts={}
    while true do
      while chk("SYM",";") do adv() end
      local t=cur()
      if t.k=="EOF" or (t.k=="KW" and BL[t.v]) then break end
      sts[#sts+1]=pstmt()
      while chk("SYM",";") do adv() end
    end
    return {"Block",sts}
  end
  local b=pblk()
  eat("EOF")
  return b
end
return M
