local A=require("src.frontend.ast")
local F=require("src.frontend.fold")
local E=require("src.backend.emit")
local MS=require("src.passes.misc")
local CA=require("src.passes.ca")
local CF=require("src.passes.cff_cfg")
local EN=require("src.passes.enc")
local VL=require("src.passes.vm_lift")
local M={}
function M.deobf_node(ast)
  local a=ast
  for _=1,6 do
    local p=a
    a=F.fold(a)
    a=MS.inv_misc(a,F.fold,false)
    a=MS.inv_pool(a)
    a=CA.inv_ca(a)
    a=CF.inv_cff(a,F.fold)
    a=EN.inv_enc(a)
    a=MS.inv_pool(a)
    a=VL.inv_vm(a,true)
    a=MS.inv_misc(F.fold(a),F.fold,false)
    a=VL._sugar_expr(a)
    if A.eq(a,p) then break end
  end
  a=MS.inv_misc(F.fold(a),F.fold,true)
  return F.fold(VL._sugar_expr(a))
end
function M.deobf_ast(src)
  return M.deobf_node(A.parse(src))
end
function M.deobf(src)
  return E.emit(M.deobf_ast(src))
end
return M
