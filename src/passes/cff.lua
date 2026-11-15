local A=require("src.frontend.ast")
local M={}
local unp=A.unp
local function lnum(e)
  e=unp(e)
  if e[1]=="Num" then return e[2] end
  if e[1]=="Un" and e[2]=="-" and unp(e[3])[1]=="Num" then return -unp(e[3])[2] end
  return nil
end
function M.eval_cond(c,pv,val)
  c=unp(c)
  if c[1]=="Un" and c[2]=="not" then
    local r=M.eval_cond(c[3],pv,val)
    if r==nil then return nil end
    return not r
  end
  if c[1]~="Bin" then return nil end
  local op,l,r=c[2],unp(c[3]),unp(c[4])
  local a,b
  if l[1]=="Var" and l[2]==pv then a=val b=lnum(r)
  elseif r[1]=="Var" and r[2]==pv then a=lnum(l) b=val end
  if not (a and b) then return nil end
  if op=="<" then return a<b
  elseif op=="<=" then return a<=b
  elseif op==">" then return a>b
  elseif op==">=" then return a>=b
  elseif op=="==" then return a==b
  elseif op=="~=" then return a~=b end
  return nil
end
local function is_disp_if(st,pv)
  if st[1]~="If" or #st[2]<1 then return false end
  for _,br in ipairs(st[2]) do
    if M.eval_cond(br[1],pv,0)==nil then return false end
  end
  return true
end
function M.ext_disp(blk,pv)
  local ls={}
  local function walk_b(b)
    if #b[2]==1 and is_disp_if(b[2][1],pv) then
      local ifs=b[2][1]
      for _,br in ipairs(ifs[2]) do walk_b(br[2]) end
      if ifs[3] then walk_b(ifs[3]) end
    else
      ls[#ls+1]=b
    end
  end
  walk_b(blk)
  local function route(id)
    local b=blk
    while #b[2]==1 and is_disp_if(b[2][1],pv) do
      local ifs=b[2][1]
      local taken=false
      for _,br in ipairs(ifs[2]) do
        if M.eval_cond(br[1],pv,id) then
          b=br[2]
          taken=true
          break
        end
      end
      if not taken then
        if ifs[3] then b=ifs[3] else return nil end
      end
    end
    return b
  end
  return ls,route
end
local function while_pv(cond)
  cond=unp(cond)
  if cond[1]=="Var" then return cond[2] end
  if cond[1]=="Bin" and (cond[2]=="~=" or cond[2]=="<" or cond[2]==">" or cond[2]=="<=" or cond[2]==">=") then
    local l,r=unp(cond[3]),unp(cond[4])
    if l[1]=="Var" and lnum(r) then return l[2] end
    if r[1]=="Var" and lnum(l) then return r[2] end
  end
  return nil
end
function M.find_cff(ast)
  local out={}
  A.walk(ast,function(n)
    if n[1]=="While" then
      local pv=while_pv(n[2])
      if pv and #n[3][2]==1 and is_disp_if(n[3][2][1],pv) then
        local ls,rt=M.ext_disp(n[3],pv)
        if #ls>=2 then
          out[#out+1]={pv=pv,w=n,ls=ls,route=rt}
        end
      end
    end
  end)
  return out
end
M.lnum=lnum
return M
