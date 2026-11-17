local A=require("src.frontend.ast")
local VM=require("src.passes.vm")
local VCS=require("src.passes.vm_cs")
local OPS=require("src.ir.ops")
local unp,eq=A.unp,A.eq
local BIN,UN=OPS.BIN,OPS.UN
local NZ do local z=0 NZ=-z end
local M={}
local KW={
  ["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,["false"]=1,
  ["for"]=1,["function"]=1,["if"]=1,["in"]=1,["local"]=1,["nil"]=1,["not"]=1,["or"]=1,
  ["repeat"]=1,["return"]=1,["then"]=1,["true"]=1,["until"]=1,["while"]=1
}
local function is_id(s)
  return type(s)=="string" and s:match("^[A-Za-z_][A-Za-z0-9_]*$")~=nil and not KW[s]
end
local function is_ec(e)
  local k=e[1]
  return k=="Call" or k=="MCall" or k=="Vararg"
end
local function t1(xs)
  if #xs>0 and is_ec(xs[#xs]) then
    local out={}
    for i=1,#xs-1 do out[i]=xs[i] end
    out[#xs]={"Paren",xs[#xs]}
    return out
  end
  return xs
end
local function w1(e)
  return is_ec(e) and {"Paren",e} or e
end
local function ng(e,rv)
  local u=unp(e)
  local k=u[1]
  if k=="Tbl" or k=="Func" or k=="Call" or k=="MCall" or k=="Vararg" then return true end
  if k=="Var" then
    for _,v in pairs(rv) do if v==u[2] then return true end end
  end
  return false
end
local function tbl_can(es,kx)
  local k0=kx[1]
  if k0~="Num" and k0~="Str" and k0~="Bool" then return false end
  local an=0
  for _,f in ipairs(es) do if f[1]=="V" then an=an+1 end end
  if k0=="Num" then
    local kv=kx[2]
    if kv==kv and math.floor(kv)==kv and kv>=1 and kv<=an then return false end
  end
  for _,f in ipairs(es) do
    if f[1]=="I" then
      local fk=f[2]
      if (fk[1]~="Num" and fk[1]~="Str" and fk[1]~="Bool") or eq(fk,kx) then return false end
    elseif f[1]=="F" then
      if eq({"Str",f[2]},kx) then return false end
    end
  end
  return true
end
local function const_ast(v)
  if v==nil then return {"Nil"} end
  local tp=type(v)
  if tp=="boolean" then return {"Bool",v} end
  if tp=="number" then return {"Num",v} end
  if tp=="string" then return {"Str",v} end
  error("const:"..tp)
end
local function has_side(e)
  if type(e)~="table" then return false end
  local k=e[1]
  if type(k)~="string" then
    for i=1,#e do if has_side(e[i]) then return true end end
    return false
  end
  if k=="Call" or k=="MCall" or k=="Func" or k=="Tbl" then return true end
  for i=2,#e do if has_side(e[i]) then return true end end
  return false
end
local function has_call(e)
  if type(e)~="table" then return false end
  local k=e[1]
  if type(k)~="string" then
    for i=1,#e do if has_call(e[i]) then return true end end
    return false
  end
  if k=="Call" or k=="MCall" then return true end
  for i=2,#e do if has_call(e[i]) then return true end end
  return false
end
local function reads_mem(e,mv)
  if type(e)~="table" then return false end
  local k=e[1]
  if type(k)~="string" then
    for i=1,#e do if reads_mem(e[i],mv) then return true end end
    return false
  end
  if k=="Call" or k=="MCall" or k=="GVar" or k=="Idx" or k=="Field" then return true end
  if k=="Var" and mv[e[2]] then return true end
  for i=2,#e do if reads_mem(e[i],mv) then return true end end
  return false
end
local function vars_e(e)
  local s={}
  local function f(x)
    if type(x)~="table" then return end
    local k=x[1]
    if type(k)~="string" then
      for i=1,#x do f(x[i]) end
      return
    end
    if k=="Var" then s[x[2]]=true
    elseif k~="Func" then
      for i=2,#x do f(x[i]) end
    end
  end
  f(e)
  return s
end
local function all_vars(n)
  local s={}
  A.walk(n,function(x) if x[1]=="Var" then s[x[2]]=true end end)
  return s
end
local function sub_e(e,nm,val)
  if type(e)~="table" then return e end
  local k=e[1]
  if type(k)~="string" then
    local r={} for i=1,#e do r[i]=sub_e(e[i],nm,val) end return r
  end
  if k=="Var" and e[2]==nm then return val end
  if k=="Func" then return e end
  if k=="Call" then
    local nf=sub_e(e[2],nm,val)
    local na=sub_e(e[3],nm,val)
    if #e[3]>0 and e[3][#e[3]][1]=="Var" and e[3][#e[3]][2]==nm then
      na[#na]=w1(na[#na])
    end
    return {"Call",nf,na}
  end
  if k=="MCall" then
    local no=sub_e(e[2],nm,val)
    local na=sub_e(e[4],nm,val)
    if #e[4]>0 and e[4][#e[4]][1]=="Var" and e[4][#e[4]][2]==nm then
      na[#na]=w1(na[#na])
    end
    return {"MCall",no,e[3],na}
  end
  if k=="Tbl" then
    local nf={}
    for ix,f in ipairs(e[2]) do
      if f[1]=="I" then
        nf[ix]={"I",sub_e(f[2],nm,val),sub_e(f[3],nm,val)}
      elseif f[1]=="F" then
        nf[ix]={"F",f[2],sub_e(f[3],nm,val)}
      else
        local v2=sub_e(f[2],nm,val)
        if ix==#e[2] and f[2][1]=="Var" and f[2][2]==nm then v2=w1(v2) end
        nf[ix]={"V",v2}
      end
    end
    return {"Tbl",nf}
  end
  local r={k} for i=2,#e do r[i]=sub_e(e[i],nm,val) end return r
end
local function is_pure_lit(e)
  e=unp(e)
  local k=e[1]
  return k=="Num" or k=="Str" or k=="Bool" or k=="Nil"
end
local function stmt_writes_var(st,vs)
  local k=st[1]
  if k=="Assign" then
    for _,l in ipairs(st[2]) do
      local u=unp(l)
      if u[1]=="Var" and vs[u[2]] then return true end
    end
    return false
  elseif k=="LocalVar" then
    for _,n in ipairs(st[2]) do if vs[n] then return true end end
    return false
  elseif k=="LocalFunc" then
    return vs[st[2]]==true
  elseif k=="If" then
    for _,br in ipairs(st[2]) do
      for _,s in ipairs(br[2][2]) do if stmt_writes_var(s,vs) then return true end end
    end
    if st[3] then
      for _,s in ipairs(st[3][2]) do if stmt_writes_var(s,vs) then return true end end
    end
  elseif k=="While" then
    for _,s in ipairs(st[3][2]) do if stmt_writes_var(s,vs) then return true end end
  elseif k=="Repeat" or k=="Do" then
    for _,s in ipairs(st[2][2]) do if stmt_writes_var(s,vs) then return true end end
  elseif k=="ForNum" then
    if vs[st[2]] then return true end
    for _,s in ipairs(st[6][2]) do if stmt_writes_var(s,vs) then return true end end
  elseif k=="ForIn" then
    for _,n in ipairs(st[2]) do if vs[n] then return true end end
    for _,s in ipairs(st[4][2]) do if stmt_writes_var(s,vs) then return true end end
  end
  return false
end
local function stmt_mutates_mem(st)
  local k=st[1]
  if k=="CallStmt" then return true end
  if k=="Assign" then
    for _,l in ipairs(st[2]) do
      local u=unp(l)
      if u[1]=="Idx" or u[1]=="Field" then return true end
    end
    return has_call(st[2]) or has_call(st[3])
  elseif k=="LocalVar" then
    return has_call(st[3])
  elseif k=="If" then
    for _,br in ipairs(st[2]) do
      if has_call(br[1]) then return true end
      for _,s in ipairs(br[2][2]) do if stmt_mutates_mem(s) then return true end end
    end
    if st[3] then
      for _,s in ipairs(st[3][2]) do if stmt_mutates_mem(s) then return true end end
    end
  elseif k=="While" then
    if has_call(st[2]) then return true end
    for _,s in ipairs(st[3][2]) do if stmt_mutates_mem(s) then return true end end
  elseif k=="Repeat" then
    if has_call(st[3]) then return true end
    for _,s in ipairs(st[2][2]) do if stmt_mutates_mem(s) then return true end end
  elseif k=="Do" then
    for _,s in ipairs(st[2][2]) do if stmt_mutates_mem(s) then return true end end
  elseif k=="ForNum" then
    if has_call(st[3]) or has_call(st[4]) or (st[5] and has_call(st[5])) then return true end
    for _,s in ipairs(st[6][2]) do if stmt_mutates_mem(s) then return true end end
  elseif k=="ForIn" then
    if has_call(st[3]) then return true end
    for _,s in ipairs(st[4][2]) do if stmt_mutates_mem(s) then return true end end
  end
  return false
end
local function pre_safe(pre,val,mv)
  if is_pure_lit(val) then return true end
  if has_call(val) then
    for _,x in ipairs(pre) do if has_call(x) or reads_mem(x,mv) then return false end end
    return true
  end
  if reads_mem(val,mv) or val[1]=="Tbl" then
    for _,x in ipairs(pre) do if has_call(x) then return false end end
    return true
  end
  return true
end
local function eval_prefix(n,nm)
  local pre,hit,multi={},false,false
  local function g(x)
    if type(x)~="table" then return end
    local k=x[1]
    if type(k)~="string" then
      for i=1,#x do g(x[i]) end
      return
    end
    if hit then
      if k=="Var" and x[2]==nm then multi=true return end
      if k=="Func" then return end
      if k=="Tbl" then
        for _,f in ipairs(x[2]) do
          if f[1]=="V" then g(f[2]) else g(f[2]) g(f[3]) end
        end
        return
      end
      for i=2,#x do g(x[i]) end
      return
    end
    if k=="Var" then
      if x[2]==nm then hit=true else pre[#pre+1]=x end
      return
    end
    if k=="GVar" or k=="Func" or k=="Num" or k=="Str" or k=="Bool" or k=="Nil" or k=="Vararg" then
      pre[#pre+1]=x return
    end
    if k=="Call" then g(x[2]) g(x[3]) return end
    if k=="MCall" then g(x[2]) g(x[4]) return end
    if k=="Tbl" then
      for _,f in ipairs(x[2]) do
        if f[1]=="I" then g(f[2]) g(f[3])
        elseif f[1]=="F" then g(f[3])
        else g(f[2]) end
      end
      return
    end
    if k=="Bin" and (x[2]=="and" or x[2]=="or") then
      g(x[3]) if not hit then g(x[4]) end return
    end
    for i=2,#x do g(x[i]) end
  end
  g(n)
  return pre,hit,multi
end
local function cnt_uses(n,nm)
  local c=0
  A.walk(n,function(x) if x[1]=="Var" and x[2]==nm then c=c+1 end end)
  return c
end
local function inline_stmt(st,nm,val,mv)
  local k=st[1]
  if k=="Assign" then
    local c1,c2=cnt_uses(st[2],nm),cnt_uses(st[3],nm)
    local lhs_ex={}
    for _,l in ipairs(st[2]) do
      local ul=unp(l)
      if ul[1]=="Idx" then lhs_ex[#lhs_ex+1]=ul[2] lhs_ex[#lhs_ex+1]=ul[3]
      elseif ul[1]=="Field" then lhs_ex[#lhs_ex+1]=ul[2] end
    end
    if c1==0 and c2==1 then
      local pre_in={}
      for _,x in ipairs(lhs_ex) do pre_in[#pre_in+1]=x end
      pre_in[#pre_in+1]=st[3]
      local pre,hit,multi=eval_prefix(pre_in,nm)
      if not hit or multi or not pre_safe(pre,val,mv) then return nil end
      local nr=sub_e(st[3],nm,val)
      local rs=st[3]
      if #rs>0 and rs[#rs][1]=="Var" and rs[#rs][2]==nm and #st[2]>#rs then
        nr[#nr]=w1(nr[#nr])
      end
      return {"Assign",st[2],nr}
    end
    if c1==1 and c2==0 then
      for _,l in ipairs(st[2]) do
        local ul=unp(l)
        if ul[1]=="Var" and ul[2]==nm then return nil end
      end
      local pre,hit,multi=eval_prefix(lhs_ex,nm)
      if not hit or multi or cnt_uses(lhs_ex,nm)~=1 or not pre_safe(pre,val,mv) then return nil end
      local function ok_b(bk)
        return bk=="Var" or bk=="GVar" or bk=="Idx" or bk=="Field" or bk=="Call" or bk=="MCall" or bk=="Paren"
      end
      local nls={}
      for i,l in ipairs(st[2]) do
        local ul=unp(l)
        if ul[1]=="Idx" then
          local b2=sub_e(ul[2],nm,val)
          if ul[2][1]=="Var" and ul[2][2]==nm and not ok_b(unp(b2)[1]) then b2={"Paren",b2} end
          nls[i]={"Idx",b2,sub_e(ul[3],nm,val)}
        elseif ul[1]=="Field" then
          local b2=sub_e(ul[2],nm,val)
          if ul[2][1]=="Var" and ul[2][2]==nm and not ok_b(unp(b2)[1]) then b2={"Paren",b2} end
          nls[i]={"Field",b2,ul[3]}
        else
          nls[i]=l
        end
      end
      return {"Assign",nls,st[3]}
    end
    return nil
  elseif k=="LocalVar" then
    if #st[3]==0 then return nil end
    local pre,hit,multi=eval_prefix(st[3],nm)
    if not hit or multi or cnt_uses(st[3],nm)~=1 or not pre_safe(pre,val,mv) then return nil end
    local nr=sub_e(st[3],nm,val)
    local rs=st[3]
    if #rs>0 and rs[#rs][1]=="Var" and rs[#rs][2]==nm and #st[2]>#rs then
      nr[#nr]=w1(nr[#nr])
    end
    return {"LocalVar",st[2],nr}
  elseif k=="CallStmt" then
    local pre,hit,multi=eval_prefix(st[2],nm)
    if not hit or multi or cnt_uses(st[2],nm)~=1 or not pre_safe(pre,val,mv) then return nil end
    return {"CallStmt",sub_e(st[2],nm,val)}
  elseif k=="Return" then
    local pre,hit,multi=eval_prefix(st[2],nm)
    if not hit or multi or cnt_uses(st[2],nm)~=1 or not pre_safe(pre,val,mv) then return nil end
    local nr=sub_e(st[2],nm,val)
    local es=st[2]
    if #es>0 and es[#es][1]=="Var" and es[#es][2]==nm then nr[#nr]=w1(nr[#nr]) end
    return {"Return",nr}
  elseif k=="If" then
    local c0=st[2][1][1]
    local pre,hit,multi=eval_prefix(c0,nm)
    if not hit or multi or cnt_uses(c0,nm)~=1 or not pre_safe(pre,val,mv) then return nil end
    local tail_cs={{st[2][1][2]}}
    for i=2,#st[2] do tail_cs[#tail_cs+1]=st[2][i] end
    if cnt_uses(tail_cs,nm)>0 or (st[3] and cnt_uses(st[3],nm)>0) then return nil end
    local ncs={{sub_e(c0,nm,val),st[2][1][2]}}
    for i=2,#st[2] do ncs[i]=st[2][i] end
    return {"If",ncs,st[3]}
  elseif k=="While" then
    local pre,hit,multi=eval_prefix(st[2],nm)
    if not hit or multi or cnt_uses(st[2],nm)~=1 or cnt_uses(st[3],nm)>0 or not pre_safe(pre,val,mv) then return nil end
    return {"While",sub_e(st[2],nm,val),st[3]}
  elseif k=="ForNum" then
    local hdr=st[5] and {st[3],st[4],st[5]} or {st[3],st[4]}
    local pre,hit,multi=eval_prefix(hdr,nm)
    if not hit or multi or cnt_uses(hdr,nm)~=1 or cnt_uses(st[6],nm)>0 or not pre_safe(pre,val,mv) then return nil end
    return {"ForNum",st[2],sub_e(st[3],nm,val),sub_e(st[4],nm,val),st[5] and sub_e(st[5],nm,val) or false,st[6]}
  elseif k=="ForIn" then
    local pre,hit,multi=eval_prefix(st[3],nm)
    if not hit or multi or cnt_uses(st[3],nm)~=1 or cnt_uses(st[4],nm)>0 or not pre_safe(pre,val,mv) then return nil end
    return {"ForIn",st[2],sub_e(st[3],nm,val),st[4]}
  elseif k=="_EXPAND" then
    local ex_l={}
    for i,e in ipairs(st[4]) do ex_l[i]=e end
    if st[5] then ex_l[#ex_l+1]=st[5] end
    local pre,hit,multi=eval_prefix(ex_l,nm)
    if not hit or multi or cnt_uses(st[2],nm)>0 or cnt_uses(ex_l,nm)~=1 or not pre_safe(pre,val,mv) then return nil end
    local nes={}
    for i,e in ipairs(st[4]) do nes[i]=sub_e(e,nm,val) end
    if not st[5] and #st[4]>0 and st[4][#st[4]][1]=="Var" and st[4][#st[4]][2]==nm then
      nes[#nes]=w1(nes[#nes])
    end
    local ntl=st[5] and sub_e(st[5],nm,val) or false
    return {"_EXPAND",st[2],st[3],nes,ntl}
  end
  return nil
end
local function can_m_fold(st,nm,val,mv)
  local pre,hp=eval_prefix(st,nm)
  if not hp or not pre_safe(pre,val,mv) then return false end
  local hit,bad=false,false
  A.walk(st,function(x)
    if x[1]=="Call" and #x[3]>=1 and x[3][1][1]=="Var" and x[3][1][2]==nm then
      local fn=unp(x[2])
      if fn[1]=="Idx" and fn[2][1]=="Var" and fn[2][2]==nm and fn[3][1]=="Str" and is_id(fn[3][2]) then
        local tail={} for i=2,#x[3] do tail[i-1]=x[3][i] end
        if cnt_uses(tail,nm)==0 then hit=true return end
      end
      bad=true
    end
  end)
  return hit and not bad and cnt_uses(st,nm)==2
end
local function m_fold(st,nm,val)
  local function f(x)
    if type(x)~="table" then return x end
    local k=x[1]
    if type(k)~="string" then
      local r={} for i=1,#x do r[i]=f(x[i]) end return r
    end
    if k=="Call" and #x[3]>=1 and x[3][1][1]=="Var" and x[3][1][2]==nm then
      local fn=unp(x[2])
      if fn[1]=="Idx" and fn[2][1]=="Var" and fn[2][2]==nm and fn[3][1]=="Str" and is_id(fn[3][2]) then
        local na={} for i=2,#x[3] do na[i-1]=f(x[3][i]) end
        return {"MCall",val,fn[3][2],na}
      end
    end
    local r={k} for i=2,#x do r[i]=f(x[i]) end return r
  end
  return f(st)
end
function M._sugar_expr(n,kgv)
  if type(n)~="table" then return n end
  local k=n[1]
  if type(k)~="string" then
    local r={} for i=1,#n do r[i]=M._sugar_expr(n[i],kgv) end return r
  end
  if k=="GVar" then return kgv and n or {"Var",n[2]} end
  if k=="Idx" then
    local b,ix=M._sugar_expr(n[2],kgv),M._sugar_expr(n[3],kgv)
    local bk=b[1]
    if ix[1]=="Str" and is_id(ix[2]) and (bk=="Var" or bk=="GVar" or bk=="Field" or bk=="Idx" or bk=="MCall" or bk=="Call" or bk=="Paren") then
      return {"Field",b,ix[2]}
    end
    return {"Idx",b,ix}
  end
  if k=="Call" then
    local b,args=M._sugar_expr(n[2],kgv),M._sugar_expr(n[3],kgv)
    if b[1]=="Field" and (b[2][1]=="Var" or b[2][1]=="GVar") and #args>0 and eq(args[1],b[2]) then
      local na={} for i=2,#args do na[i-1]=args[i] end
      return {"MCall",b[2],b[3],na}
    end
    return {"Call",b,args}
  end
  if k=="Tbl" then
    local nf={}
    for i,f in ipairs(n[2]) do
      if f[1]=="I" then nf[i]={"I",M._sugar_expr(f[2],kgv),M._sugar_expr(f[3],kgv)}
      elseif f[1]=="F" then nf[i]={"F",f[2],M._sugar_expr(f[3],kgv)}
      else nf[i]={"V",M._sugar_expr(f[2],kgv)} end
    end
    return {"Tbl",nf}
  end
  local r={k} for i=2,#n do r[i]=M._sugar_expr(n[i],kgv) end return r
end
local function fold_seq(sts,ts,mv,tail_e,kgv)
  local out={}
  for _,st in ipairs(sts) do
    local k=st[1]
    if k=="If" then
      local ncs={}
      for _,br in ipairs(st[2]) do ncs[#ncs+1]={br[1],{"Block",fold_seq(br[2][2],ts,mv,nil,kgv)}} end
      local eb=st[3] and {"Block",fold_seq(st[3][2],ts,mv,nil,kgv)} or false
      while eb and #eb[2]==1 and eb[2][1][1]=="If" do
        local ni=eb[2][1]
        for _,br in ipairs(ni[2]) do ncs[#ncs+1]=br end
        eb=ni[3]
      end
      st={"If",ncs,eb}
    elseif k=="While" then
      st={"While",st[2],{"Block",fold_seq(st[3][2],ts,mv,nil,kgv)}}
    elseif k=="Repeat" then
      st={"Repeat",{"Block",fold_seq(st[2][2],ts,mv,st[3],kgv)},st[3]}
    elseif k=="ForNum" then
      st={"ForNum",st[2],st[3],st[4],st[5],{"Block",fold_seq(st[6][2],ts,mv,nil,kgv)}}
    elseif k=="ForIn" then
      st={"ForIn",st[2],st[3],{"Block",fold_seq(st[4][2],ts,mv,nil,kgv)}}
    elseif k=="Do" then
      st={"Do",{"Block",fold_seq(st[2][2],ts,mv,nil,kgv)}}
    end
    out[#out+1]=st
  end
  local function dead_clrs(sts2,from_i,nm)
    if tail_e and cnt_uses(tail_e,nm)>0 then return nil end
    local ixs={}
    for ix=from_i,#sts2 do
      local s=sts2[ix]
      if cnt_uses(s,nm)>0 then
        if s[1]=="Assign" and #s[2]==1 and #s[3]==1 and s[2][1][1]=="Var" and s[2][1][2]==nm and s[3][1][1]=="Nil" then
          ixs[#ixs+1]=ix
        else return nil end
      end
    end
    return ixs
  end
  local function cap_before(sts2,upto,nm)
    local fl=false
    for i=1,upto do
      A.walk(sts2[i],function(n)
        if fl then return end
        if n[1]=="Func" then
          for _,p in ipairs(n[2]) do if p==nm then return end end
          if cnt_uses(n[4],nm)>0 then fl=true end
        end
      end)
      if fl then return true end
    end
    return false
  end
  sts=out
  if #sts>0 and sts[#sts][1]=="Return" then
    local drop,k={},#sts-1
    while k>=1 and sts[k][1]=="Assign" and #sts[k][2]==1 and sts[k][2][1][1]=="Var" and #sts[k][3]==1 and sts[k][3][1][1]=="Nil" do
      local nmk=sts[k][2][1][2]
      if ts[nmk] and cnt_uses(sts[#sts],nmk)==0 and not cap_before(sts,k-1,nmk) then
        drop[k]=true k=k-1
      else break end
    end
    if next(drop) then
      local ns={}
      for idx,s in ipairs(sts) do if not drop[idx] then ns[#ns+1]=s end end
      sts=ns
    end
  end
  local ch=true
  while ch do
    ch=false
    local i=1
    while i<#sts do
      local s0,s1=sts[i],sts[i+1]
      local did=false
      if i+2<=#sts and s0[1]=="LocalVar" and #s0[2]==1 and #s0[3]==1 and ts[s0[2][1]]
        and s1[1]=="Assign" and #s1[2]==1 and #s1[3]==1 and s1[2][1][1]=="Var"
        and s1[3][1][1]=="Var" and s1[3][1][2]==s0[2][1] and sts[i+2][1]=="If" then
        local nm,rv=s0[2][1],s1[2][1][2]
        local s2=sts[i+2]
        local cd=unp(s2[2][1][1])
        local is_v=cd[1]=="Var" and cd[2]==nm
        local is_nv=cd[1]=="Un" and cd[2]=="not" and cd[3][1]=="Var" and cd[3][2]==nm
        if nm~=rv and (is_v or is_nv) then
          local rest_i={{s2[2][1][2]}}
          for bi=2,#s2[2] do rest_i[#rest_i+1]=s2[2][bi] end
          if cnt_uses(rest_i,nm)==0 and (not s2[3] or cnt_uses(s2[3],nm)==0) then
            local clrs=dead_clrs(sts,i+3,nm)
            if clrs then
              for ci=#clrs,1,-1 do table.remove(sts,clrs[ci]) end
              local ncd=is_v and {"Var",rv} or {"Un","not",{"Var",rv}}
              local ncs={{ncd,s2[2][1][2]}}
              for bi=2,#s2[2] do ncs[bi]=s2[2][bi] end
              sts[i]={"Assign",{{"Var",rv}},s0[3]}
              sts[i+1]={"If",ncs,s2[3]}
              table.remove(sts,i+2)
              ch=true did=true
            end
          end
        end
      end
      if not did and (s0[1]=="LocalVar" or s0[1]=="Assign") and #s0[2]==1 and #s0[3]==1
        and s1[1]=="If" and #s1[2]==1 and not s1[3] and #s1[2][1][2][2]==1
        and s1[2][1][2][2][1][1]=="Assign" and #s1[2][1][2][2][1][3]==1 then
        local nm
        if s0[1]=="LocalVar" then nm=s0[2][1]
        else local u=unp(s0[2][1]) if u[1]=="Var" then nm=u[2] end end
        local as1=s1[2][1][2][2][1]
        if nm and #as1[2]==1 and as1[2][1][1]=="Var" and as1[2][1][2]==nm and not vars_e(as1[3][1])[nm] then
          local cd=unp(s1[2][1][1])
          if cd[1]=="Var" and cd[2]==nm then
            sts[i]={s0[1],s0[2],{{"Bin","and",s0[3][1],as1[3][1]}}}
            table.remove(sts,i+1) ch=true did=true
          elseif cd[1]=="Un" and cd[2]=="not" and cd[3][1]=="Var" and cd[3][2]==nm then
            sts[i]={s0[1],s0[2],{{"Bin","or",s0[3][1],as1[3][1]}}}
            table.remove(sts,i+1) ch=true did=true
          end
        end
      end
      if not did and s0[1]=="LocalVar" and #s0[2]==1 and #s0[3]==1 and ts[s0[2][1]]
        and s0[3][1][1]=="Tbl" and s1[1]=="Assign" and #s1[2]==1 and #s1[3]==1 then
        local lh=unp(s1[2][1])
        local tnm=s0[2][1]
        if lh[1]=="Idx" and unp(lh[2])[1]=="Var" and unp(lh[2])[2]==tnm
          and not vars_e(lh[3])[tnm] and not vars_e(s1[3][1])[tnm] then
          local ce=s0[3][1][2]
          local cur_e={} for idx,x in ipairs(ce) do cur_e[idx]=x end
          local has_tl=#cur_e>0 and cur_e[#cur_e][1]=="V" and is_ec(unp(cur_e[#cur_e][2]))
          if not has_tl then
            local kx=unp(lh[3])
            local vx=s1[3][1]
            if tbl_can(cur_e,kx) then
              local arr_n=0 for _,f in ipairs(cur_e) do if f[1]=="V" then arr_n=arr_n+1 end end
              if kx[1]=="Num" and kx[2]==arr_n+1 then
                local vx2=is_ec(unp(vx)) and {"Paren",vx} or vx
                cur_e[#cur_e+1]={"V",vx2}
              else
                cur_e[#cur_e+1]={"I",kx,vx}
              end
              sts[i]={"LocalVar",s0[2],{{"Tbl",cur_e}}}
              table.remove(sts,i+1) ch=true did=true
            end
          end
        end
      end
      if not did and s0[1]=="LocalVar" and #s0[2]==1 and #s0[3]==1 and ts[s0[2][1]]
        and s0[3][1][1]=="Tbl" and s1[1]=="_EXPAND" then
        local tnm=s0[2][1]
        local u1=unp(s1[2])
        if u1[1]=="Var" and u1[2]==tnm and not vars_e(s1[4])[tnm] and (not s1[5] or not vars_e(s1[5])[tnm]) then
          local ce=s0[3][1][2]
          local cur_e={} for idx,x in ipairs(ce) do cur_e[idx]=x end
          local arr_n=0 for _,f in ipairs(cur_e) do if f[1]=="V" then arr_n=arr_n+1 end end
          local has_tl=#cur_e>0 and cur_e[#cur_e][1]=="V" and is_ec(unp(cur_e[#cur_e][2]))
          local ok_exp=not has_tl and arr_n==s1[3]-1
          if ok_exp then
            for ie=0,#s1[4]-1 do
              if not tbl_can(cur_e,{"Num",s1[3]+ie}) then ok_exp=false break end
            end
          end
          if ok_exp and s1[5] then
            for _,f in ipairs(cur_e) do
              if f[1]=="F" then ok_exp=false break
              elseif f[1]=="I" and (f[2][1]~="Num" or f[2][2]>=s1[3]) then ok_exp=false break end
            end
          end
          if ok_exp then
            local es,tl=s1[4],s1[5]
            for ie,e in ipairs(es) do
              local np=not tl and ie==#es and is_ec(unp(e))
              cur_e[#cur_e+1]={"V",np and {"Paren",e} or e}
            end
            if tl then cur_e[#cur_e+1]={"V",tl} end
            sts[i]={"LocalVar",s0[2],{{"Tbl",cur_e}}}
            table.remove(sts,i+1) ch=true did=true
          end
        end
      end
      if not did and s0[1]=="LocalVar" and #s0[2]==1 and #s0[3]==1 and ts[s0[2][1]] then
        local nm,val=s0[2][1],s0[3][1]
        local clrs=dead_clrs(sts,i+2,nm)
        if clrs then
          local ns=inline_stmt(s1,nm,val,mv)
          if ns then
            for ci=#clrs,1,-1 do table.remove(sts,clrs[ci]) end
            sts[i]=ns
            table.remove(sts,i+1)
            ch=true did=true
          end
        end
      end
      if not did then i=i+1 end
    end
    local j=1
    while j<=#sts and not ch do
      local s0=sts[j]
      if s0[1]=="LocalVar" and #s0[2]==1 and #s0[3]==1 and ts[s0[2][1]] then
        local nm,val=s0[2][1],s0[3][1]
        local vs=vars_e(val)
        local u_idx
        for k=j+1,#sts do if cnt_uses(sts[k],nm)>0 then u_idx=k break end end
        local clrs=u_idx and dead_clrs(sts,u_idx+1,nm) or nil
        if clrs then
          local ok=true
          local vm,vc=reads_mem(val,mv),has_call(val)
          for k=j+1,u_idx-1 do
            local mid=sts[k]
            if stmt_writes_var(mid,vs) or ((vc or vm) and stmt_mutates_mem(mid)) then
              ok=false break
            end
          end
          if ok then
            local ns=inline_stmt(sts[u_idx],nm,val,mv)
            if ns then
              for ci=#clrs,1,-1 do table.remove(sts,clrs[ci]) end
              sts[u_idx]=ns
              table.remove(sts,j)
              ch=true break
            end
            if cnt_uses(sts[u_idx],nm)==2 and can_m_fold(sts[u_idx],nm,val,mv) then
              for ci=#clrs,1,-1 do table.remove(sts,clrs[ci]) end
              sts[u_idx]=m_fold(sts[u_idx],nm,val)
              table.remove(sts,j)
              ch=true break
            end
          end
        end
      end
      j=j+1
    end
  end
  local out2={}
  for _,st in ipairs(sts) do
    if st[1]=="_EXPAND" then
      local tbl_e,bi,es,tl=st[2],st[3],st[4],st[5]
      for ie,e in ipairs(es) do
        local e2=is_ec(unp(e)) and {"Paren",e} or e
        out2[#out2+1]={"Assign",{{"Idx",tbl_e,{"Num",bi+ie-1}}},{e2}}
      end
      if tl then
        local off=bi+#es-1
        local sel={"Var","select"}
        local n_s={"LocalVar",{"_xn"},{{"Call",sel,{{"Str","#"},{"Vararg"}}}}}
        local lp={"ForNum","_xk",{"Num",1},{"Var","_xn"},false,{"Block",{
          {"Assign",{{"Idx",tbl_e,{"Bin","+",{"Num",off},{"Var","_xk"}}}},{{"Call",sel,{{"Var","_xk"},{"Vararg"}}}}}
        }}}
        out2[#out2+1]={"CallStmt",{"Call",{"Func",{},true,{"Block",{n_s,lp}}},{tl}}}
      end
    else
      out2[#out2+1]=st
    end
  end
  local res={}
  for i,s in ipairs(out2) do res[i]=M._sugar_expr(s,kgv) end
  return res
end
local function any_var_after(sts,from_i,nm)
  for i=from_i,#sts do if cnt_uses(sts[i],nm)>0 then return true end end
  return false
end
local function collect_takes(cd,pc,ep,res_r)
  local j=pc+1
  local takes,skipped={},{}
  while j<ep do
    local ins=cd[j]
    local op2=ins[1]
    if op2=="TAKE" and ins[3]==res_r then
      takes[#takes+1]={j,ins[2],ins[4]}
      j=j+1
    elseif op2=="CLEAR" or op2=="CLEARS" or op2=="NIL" then
      local regs=op2=="CLEARS" and ins[2] or {ins[2]}
      local hit=false
      for _,r in ipairs(regs) do if r==res_r then hit=true break end end
      if hit then break end
      skipped[#skipped+1]=j
      j=j+1
    else
      break
    end
  end
  if #takes==0 then return {},pc+1,{} end
  local last_t=takes[#takes][1]
  while #skipped>0 and skipped[#skipped]>last_t do skipped[#skipped]=nil end
  return takes,last_t+1,skipped
end
function M.lift_proto(pr,up_vars,is_root,st,kgv)
  if not st then st={v=0,p=0} end
  st.p=st.p+1
  local pid=st.p
  local cd,consts,chs=pr.code,pr.constants,pr.children
  local g_names={}
  for _,ins in ipairs(cd) do
    if ins[1]=="GLOBAL" or ins[1]=="SETGLOBAL" then
      local cidx=ins[1]=="GLOBAL" and ins[3] or ins[2]
      local v=consts[cidx]
      if type(v)=="string" and is_id(v) then g_names[v]=true end
    end
  end
  local function nv(pfx)
    while true do
      st.v=st.v+1
      local cand=pfx..st.v
      if not g_names[cand] then return cand end
    end
  end
  local loops=OPS.find_loops(cd)
  local p_names,cell_prm={},{}
  for idx,p in ipairs(pr.params) do
    local r,cap=p[1],p[2]
    local nm=pid==1 and ("_a"..idx) or ("_p"..pid.."_"..idx)
    while g_names[nm] do nm="_"..nm end
    p_names[r]=nm
    if cap then cell_prm[r]=true end
  end
  local lin,lout,_,def_web,use_web,web_info=OPS.build_webs(pr,loops)
  local cell_webs={}
  for wid,wi in pairs(web_info) do
    if wi[2][0] and cell_prm[wi[1]] then cell_webs[wid]=true end
  end
  for pc,ins in ipairs(cd) do
    local op,a,b=ins[1],ins[2],ins[3]
    if op=="CELL" then
      local w=def_web[pc][a] if w then cell_webs[w]=true end
    elseif op=="SETCELL" then
      local w=use_web[pc][a] if w then cell_webs[w]=true end
    elseif op=="GETCELL" then
      local w=use_web[pc][b] if w then cell_webs[w]=true end
    elseif op=="CLOSURE" then
      for _,cp in ipairs(chs[b].captures) do
        if cp[1]==0 then
          local w=use_web[pc][cp[2]] if w then cell_webs[w]=true end
        end
      end
    end
  end
  local cell_vars,web_var,dec_top,dec_top_s={},{},{},{}
  local wids={} for wid in pairs(web_info) do wids[#wids+1]=wid end
  table.sort(wids)
  for _,wid in ipairs(wids) do
    local wi=web_info[wid]
    local r,ds,cr=wi[1],wi[2],wi[3]
    if cell_webs[wid] then
      cell_vars[wid]=(ds[0] and p_names[r]) and p_names[r] or nv("_c")
    elseif ds[0] and p_names[r] then
      web_var[wid]=p_names[r]
    elseif cr then
      local nm=nv("_r")
      web_var[wid]=nm
      dec_top[#dec_top+1]=nm dec_top_s[nm]=true
    end
  end
  local function rm_top(lv)
    if dec_top_s[lv] then
      dec_top_s[lv]=nil
      for i,v in ipairs(dec_top) do if v==lv then table.remove(dec_top,i) break end end
    end
  end
  local declared_webs={}
  for w,wi in pairs(web_info) do if cell_webs[w] and wi[2][0] then declared_webs[w]=true end end
  local function bind_loop_web(w,pfx)
    if not w then return nv(pfx) end
    if cell_webs[w] then declared_webs[w]=true return cell_vars[w] end
    if web_var[w] then local lv=web_var[w] rm_top(lv) return lv end
    local lv=nv(pfx) web_var[w]=lv return lv
  end
  local for_info={}
  local lpcs={} for lpc in pairs(loops) do lpcs[#lpcs+1]=lpc end table.sort(lpcs)
  for _,lpc in ipairs(lpcs) do
    if loops[lpc][1]=="ForNum" then
      local c1=cd[lpc][2]
      local c1_w=def_web[lpc][c1]
      if c1_w and web_var[c1_w] then rm_top(web_var[c1_w]) end
      local lr,lvar
      if lpc+3<=#cd and (cd[lpc+3][1]=="MOVE" or cd[lpc+3][1]=="CELL") and cd[lpc+3][3]==c1 then
        lr=cd[lpc+3][2]
        local lw=def_web[lpc+3][lr]
        lvar=bind_loop_web(lw,"_i")
      else
        lvar=bind_loop_web(c1_w,"_i")
      end
      for_info[lpc]={lr,lvar}
    end
  end
  local function gvar(nm)
    if type(nm)=="string" and is_id(nm) then return {"GVar",nm} end
    return {"Idx",{"Call",{"GVar","getfenv"},{}},const_ast(nm)}
  end
  local tmp_set={}
  local function lift_range(sp,ep,loop_ctx,skip_pc,env_out,rvar)
    local stmts,env={},{}
    local rv={} if rvar then for k,v in pairs(rvar) do rv[k]=v end end
    local cur_pc=sp
    local function flush_cb() env={} end
    local function rd(r,at_pc)
      if r==0 then return {"Nil"} end
      if env[r] then return env[r] end
      local w=use_web[at_pc or cur_pc][r]
      if w and web_var[w] then return {"Var",web_var[w]} end
      return {"Nil"}
    end
    local function emit_tmp(val)
      local t=nv("_t")
      tmp_set[t]=true
      stmts[#stmts+1]={"LocalVar",{t},{val}}
      return {"Var",t}
    end
    local function wr(r,val,allow_expr,at_pc)
      local w=def_web[at_pc or cur_pc][r]
      local g=ng(val,rv)
      if w and web_var[w] then
        stmts[#stmts+1]={"Assign",{{"Var",web_var[w]}},{val}}
        env[r]=nil
        rv[r]=g and web_var[w] or nil
      else
        if allow_expr and is_pure_lit(val) then
          env[r]=val rv[r]=nil
        elseif val[1]=="Var" and tmp_set[val[2]] and allow_expr then
          env[r]=val rv[r]=g and val[2] or nil
        else
          local te=emit_tmp(val)
          env[r]=te rv[r]=g and te[2] or nil
        end
      end
    end
    local function emit_takes(takes,src_e,allow_single_trunc)
      local mx,tmap=0,{}
      for _,tk in ipairs(takes) do
        if tk[3]>mx then mx=tk[3] end
        tmap[tk[3]]={tk[1],tk[2]}
      end
      if #takes==1 and takes[1][3]==1 and allow_single_trunc then
        wr(takes[1][2],{"Paren",src_e},false,takes[1][1])
        return
      end
      local lh,t_tmps={},{}
      local all_t=true
      for ix=1,mx do
        local tm=tmap[ix]
        if tm then
          local tpc,rg=tm[1],tm[2]
          local w=def_web[tpc][rg]
          if w and web_var[w] then
            lh[ix]={"Var",web_var[w]} env[rg]=nil all_t=false
          else
            local tn=nv("_t") tmp_set[tn]=true t_tmps[rg]=tn lh[ix]={"Var",tn}
          end
        else
          local tn=nv("_t") tmp_set[tn]=true lh[ix]={"Var",tn}
        end
      end
      if all_t then
        local nms={} for ix=1,mx do nms[ix]=lh[ix][2] end
        stmts[#stmts+1]={"LocalVar",nms,{src_e}}
      else
        stmts[#stmts+1]={"Assign",lh,{src_e}}
      end
      for ix=1,mx do
        if tmap[ix] then rv[tmap[ix][2]]=lh[ix][2] end
      end
      for rg,tn in pairs(t_tmps) do env[rg]={"Var",tn} end
    end
    local pc=sp
    while pc<ep do
      cur_pc=pc
      if loop_ctx then
        if pc==loop_ctx[2] then stmts[#stmts+1]={"Continue"} break end
        if pc==loop_ctx[1] then stmts[#stmts+1]={"Break"} break end
      end
      local lp=pc~=skip_pc and loops[pc] or nil
      if lp and lp[1]=="ForNum" then
        local ep2,ap2=lp[2],lp[3]
        local i0=cd[pc]
        local e1,e2,e3=rd(i0[2],pc),rd(i0[3],pc),rd(i0[4],pc)
        flush_cb()
        local lr,lvar=for_info[pc][1],for_info[pc][2]
        local bs=lr and pc+4 or pc+3
        local bsts=lift_range(bs,ap2,{ep2,ap2},nil,nil,rv)
        local stp=(e3[1]=="Num" and e3[2]==1) and false or e3
        stmts[#stmts+1]={"ForNum",lvar,e1,e2,stp,{"Block",bsts}}
        pc=ep2
      elseif lp and lp[1]=="ForIn" then
        local ep2,cp2=lp[2],lp[3]
        local c2=cd[pc]
        local rit,rst,rct=c2[3],c2[4][1],c2[4][2]
        local its={rd(rit,pc),rd(rst,pc),rd(rct,pc)}
        local w1v=use_web[pc][rit] and web_var[use_web[pc][rit]]
        local w2v=use_web[pc][rst] and web_var[use_web[pc][rst]]
        if #stmts>=1 and stmts[#stmts][1]=="Assign" and #stmts[#stmts][2]>=2 and #stmts[#stmts][3]==1 then
          local ls=stmts[#stmts][2]
          local u1,u2=unp(ls[1]),unp(ls[2])
          if u1[1]=="Var" and u2[1]=="Var" and u1[2]==w1v and u2[2]==w2v then
            its={stmts[#stmts][3][1]}
            stmts[#stmts]=nil
          end
        end
        if #its==3 and its[3][1]=="Nil" then its={its[1],its[2]} end
        if #its==2 and its[2][1]=="Nil" then its={its[1]} end
        flush_cb()
        local res_r=c2[2]
        local j=pc+5
        if j<ep2 and cd[j][1]=="MOVE" and cd[j][2]==rct then j=j+1 end
        local lvars={}
        while j<ep2-1 and cd[j][1]=="TAKE" and cd[j][3]==res_r do
          local tv=cd[j][2]
          local tpc=j
          j=j+1
          if j<ep2 and (cd[j][1]=="MOVE" or cd[j][1]=="CELL") and cd[j][3]==tv then
            local lrg=cd[j][2]
            lvars[#lvars+1]=bind_loop_web(def_web[j][lrg],"_k")
            j=j+1
          else
            lvars[#lvars+1]=bind_loop_web(def_web[tpc][tv],"_k")
          end
        end
        if #lvars==0 then lvars={nv("_k")} end
        while j<ep2-1 and (cd[j][1]=="CLEAR" or cd[j][1]=="CLEARS") do j=j+1 end
        local bsts=lift_range(j,ep2-1,{ep2,cp2},nil,nil,rv)
        stmts[#stmts+1]={"ForIn",lvars,its,{"Block",bsts}}
        pc=ep2
      elseif lp and lp[1]=="While" then
        local ep2,hp2,jc=lp[2],lp[3],lp[4]
        flush_cb()
        local c_env={}
        local c_sts=lift_range(hp2,jc,nil,pc,c_env,rv)
        local cr=cd[jc][2]
        local cwn=use_web[jc][cr] and web_var[use_web[jc][cr]]
        local cv
        if cwn then cv={"Var",cwn}
        elseif c_env[cr] then
          cv=c_env[cr]
          if cv[1]=="Var" and #c_sts>0 and c_sts[#c_sts][1]=="LocalVar" and #c_sts[#c_sts][2]==1
            and c_sts[#c_sts][2][1]==cv[2] and #c_sts[#c_sts][3]==1 and not any_var_after(c_sts,#c_sts,cv[2]) then
            local lc=table.remove(c_sts) cv=lc[3][1]
          end
        elseif #c_sts>0 and c_sts[#c_sts][1]=="LocalVar" and #c_sts[#c_sts][3]==1 then
          cv=table.remove(c_sts)[3][1]
        else cv={"Nil"} end
        local bsts=lift_range(jc+1,ep2-1,{ep2,hp2},nil,nil,rv)
        if #c_sts==0 then
          stmts[#stmts+1]={"While",cv,{"Block",bsts}}
        else
          local nb={}
          for _,s in ipairs(c_sts) do nb[#nb+1]=s end
          nb[#nb+1]={"If",{{{"Un","not",cv},{"Block",{{"Break"}}}}},false}
          for _,s in ipairs(bsts) do nb[#nb+1]=s end
          stmts[#stmts+1]={"While",{"Bool",true},{"Block",nb}}
        end
        pc=ep2
      elseif lp and lp[1]=="Repeat" then
        local ep2,jt=lp[2],lp[3]
        flush_cb()
        local r_env={}
        local ists=lift_range(pc,jt,{ep2,jt},pc,r_env,rv)
        local cr=cd[jt][2]
        local cwn=use_web[jt][cr] and web_var[use_web[jt][cr]]
        local cv=cwn and {"Var",cwn} or (r_env[cr] or {"Nil"})
        if cwn and #ists>0 and ists[#ists][1]=="Assign" and #ists[#ists][2]==1
          and ists[#ists][2][1][1]=="Var" and ists[#ists][2][1][2]==cwn and #ists[#ists][3]==1 then
          local used_p=false
          for k=1,#ists-1 do if cnt_uses(ists[k],cwn)>0 then used_p=true break end end
          if not used_p then cv=table.remove(ists)[3][1] end
        elseif not cwn and cv[1]=="Var" and #ists>0 and ists[#ists][1]=="LocalVar" and #ists[#ists][2]==1
          and ists[#ists][2][1]==cv[2] and #ists[#ists][3]==1 then
          local used_p=false
          for k=1,#ists-1 do if cnt_uses(ists[k],cv[2])>0 then used_p=true break end end
          if not used_p then cv=table.remove(ists)[3][1] end
        end
        stmts[#stmts+1]={"Repeat",{"Block",ists},cv}
        pc=ep2
      else
        local ins=cd[pc]
        local op,a,b,c,d=ins[1],ins[2],ins[3],ins[4],ins[5]
        if op=="JMP" then
          flush_cb()
          if loop_ctx and a==loop_ctx[1] then stmts[#stmts+1]={"Break"}
          elseif loop_ctx and a==loop_ctx[2] then stmts[#stmts+1]={"Continue"} end
          break
        elseif op=="JFALSE" or op=="JTRUE" then
          local tgt=b
          local cond=rd(a)
          if op=="JFALSE" then cond={"Un","not",cond} end
          env[a]=nil
          flush_cb()
          if loop_ctx and tgt==loop_ctx[1] then
            stmts[#stmts+1]={"If",{{cond,{"Block",{{"Break"}}}}},false} pc=pc+1
          elseif loop_ctx and tgt==loop_ctx[2] then
            stmts[#stmts+1]={"If",{{cond,{"Block",{{"Continue"}}}}},false} pc=pc+1
          elseif tgt==ep then
            local inv_c=(cond[1]=="Un" and cond[2]=="not") and cond[3] or {"Un","not",cond}
            local tb=lift_range(pc+1,ep,loop_ctx,nil,nil,rv)
            stmts[#stmts+1]={"If",{{inv_c,{"Block",tb}}},false}
            break
          elseif pc+1<tgt and tgt<=ep then
            local inv_c=(cond[1]=="Un" and cond[2]=="not") and cond[3] or {"Un","not",cond}
            local pre_ins=cd[tgt-1]
            if pre_ins[1]=="JMP" and tgt<pre_ins[2] and pre_ins[2]<=ep then
              local jp=pre_ins[2]
              local tb=lift_range(pc+1,tgt-1,loop_ctx,nil,nil,rv)
              local eb=lift_range(tgt,jp,loop_ctx,nil,nil,rv)
              local cs={{inv_c,{"Block",tb}}}
              local eb_blk=#eb>0 and {"Block",eb} or false
              if #eb==1 and eb[1][1]=="If" then
                for _,br in ipairs(eb[1][2]) do cs[#cs+1]=br end
                eb_blk=eb[1][3]
              end
              stmts[#stmts+1]={"If",cs,eb_blk}
              pc=jp
            else
              local tb=lift_range(pc+1,tgt,loop_ctx,nil,nil,rv)
              stmts[#stmts+1]={"If",{{inv_c,{"Block",tb}}},false}
              pc=tgt
            end
          else
            pc=pc+1
          end
        elseif op=="CLEAR" or op=="CLEARS" or op=="NIL" then
          local regs_c=op=="CLEARS" and a or {a}
          local lva={}
          for rk in pairs(lout[pc]) do
            if rv[rk] then lva[rv[rk]]=true end
            if env[rk] then for v in pairs(vars_e(env[rk])) do lva[v]=true end end
          end
          local cv_s={} for _,v in pairs(cell_vars) do cv_s[v]=true end
          local dn={}
          for _,rg in ipairs(regs_c) do
            if lout[pc][rg] then
              wr(rg,{"Nil"},true)
            else
              local vn=rv[rg] rv[rg]=nil env[rg]=nil
              if (op=="CLEAR" or op=="CLEARS") and vn and not lva[vn] and not dn[vn] and not cv_s[vn] then
                stmts[#stmts+1]={"Assign",{{"Var",vn}},{{"Nil"}}}
                dn[vn]=true
              end
            end
          end
          pc=pc+1
        elseif op=="LOAD" then
          wr(a,const_ast(consts[b]),true) pc=pc+1
        elseif op=="MOVE" then
          if a~=b then
            local rb=rd(b)
            if rb[1]=="_PACK" then
              if not (def_web[pc][a] and web_var[def_web[pc][a]]) then
                env[a]=rb
              else
                local esp={} for idx,x in ipairs(rb[2]) do esp[idx]=x end
                local tlp=rb[3]
                if not tlp and #esp>0 and is_ec(unp(esp[#esp])) then esp[#esp]={"Paren",esp[#esp]} end
                local lfs={} for idx,e in ipairs(esp) do lfs[idx]={"V",e} end
                if tlp then lfs[#lfs+1]={"V",tlp} end
                wr(a,{"Tbl",lfs},false)
              end
            else
              wr(a,rb,rb[1]=="Var" and tmp_set[rb[2]]==true)
            end
          end
          pc=pc+1
        elseif op=="CELL" then
          local w=def_web[pc][a]
          local vn=cell_vars[w]
          if not declared_webs[w] then
            declared_webs[w]=true
            stmts[#stmts+1]={"LocalVar",{vn},{rd(b)}}
          else
            stmts[#stmts+1]={"Assign",{{"Var",vn}},{rd(b)}}
          end
          pc=pc+1
        elseif op=="GETCELL" then
          local w=use_web[pc][b]
          wr(a,(w and cell_vars[w]) and {"Var",cell_vars[w]} or {"Nil"},false)
          pc=pc+1
        elseif op=="SETCELL" then
          local w=use_web[pc][a]
          if w and cell_vars[w] then
            stmts[#stmts+1]={"Assign",{{"Var",cell_vars[w]}},{rd(b)}}
          end
          pc=pc+1
        elseif op=="GETUP" then
          wr(a,{"Var",up_vars[b]},false) pc=pc+1
        elseif op=="SETUP" then
          stmts[#stmts+1]={"Assign",{{"Var",up_vars[a]}},{rd(b)}} pc=pc+1
        elseif op=="GLOBAL" then
          wr(a,gvar(consts[b]),false) pc=pc+1
        elseif op=="SETGLOBAL" then
          stmts[#stmts+1]={"Assign",{gvar(consts[a])},{rd(b)}} pc=pc+1
        elseif op=="TABLE" then
          wr(a,{"Tbl",{}},false) pc=pc+1
        elseif op=="GETTABLE" then
          wr(a,{"Idx",rd(b),rd(c)},false) pc=pc+1
        elseif op=="SETTABLE" then
          stmts[#stmts+1]={"Assign",{{"Idx",rd(a),rd(b)}},{rd(c)}} pc=pc+1
        elseif BIN[op] then
          wr(a,{"Bin",BIN[op],rd(b),rd(c)},false) pc=pc+1
        elseif UN[op] then
          local rb=rd(b)
          if op=="NEG" and rb[1]=="Num" and rb[2]==0 then
            wr(a,{"Num",1/rb[2]>0 and NZ or 0},true)
          else
            wr(a,{"Un",UN[op],rb},false)
          end
          pc=pc+1
        elseif op=="CLOSURE" then
          local ch=chs[b]
          local cups={}
          for idx,cp in ipairs(ch.captures) do
            if cp[1]==0 then
              local w=use_web[pc][cp[2]]
              cups[idx]=(w and cell_vars[w]) or "_nil"
            else
              cups[idx]=up_vars[cp[2]]
            end
          end
          wr(a,M.lift_proto(ch,cups,false,st,kgv),false)
          pc=pc+1
        elseif op=="VARARG" then
          local takes,j,skipped=collect_takes(cd,pc,ep,a)
          if #takes>0 then
            for _,spc in ipairs(skipped) do
              local is=cd[spc]
              local regs=is[1]=="CLEARS" and is[2] or {is[2]}
              for _,rg in ipairs(regs) do
                if lout[spc][rg] then wr(rg,{"Nil"},true,spc) else env[rg]=nil end
              end
            end
            emit_takes(takes,{"Vararg"},true)
            pc=j
          else
            env[a]={"_PACK",{},{"Vararg"}} pc=pc+1
          end
        elseif op=="ARGS" then
          local es={}
          for idx,r in ipairs(b or {}) do es[idx]=rd(r) end
          local tl=(c and c~=0) and rd(c) or false
          while type(tl)=="table" and tl[1]=="_PACK" do
            for _,x in ipairs(tl[2]) do es[#es+1]=x end
            tl=tl[3]
          end
          env[a]={"_PACK",es,tl}
          pc=pc+1
        elseif op=="EXPAND" then
          local tbl_e=rd(a)
          local pk=rd(c)
          local es,tl
          if pk[1]=="_PACK" then
            es={} for idx,x in ipairs(pk[2]) do es[idx]=x end
            tl=pk[3]
          else
            es={pk} tl=false
          end
          stmts[#stmts+1]={"_EXPAND",tbl_e,b,es,tl}
          pc=pc+1
        elseif op=="TAKE" then
          local src_pk=rd(b)
          if type(src_pk)=="table" and src_pk[1]=="_PACK" then
            local esp,tlp=src_pk[2],src_pk[3]
            local vt
            if c>=1 and c<=#esp then vt=esp[c]
            elseif tlp and c==#esp+1 then vt=is_ec(tlp) and {"Paren",tlp} or tlp
            else
              local es2={} for idx,x in ipairs(esp) do es2[idx]=x end
              if not tlp and #es2>0 and is_ec(unp(es2[#es2])) then es2[#es2]={"Paren",es2[#es2]} end
              local lfs={} for idx,e in ipairs(es2) do lfs[idx]={"V",e} end
              if tlp then lfs[#lfs+1]={"V",tlp} end
              vt={"Idx",{"Tbl",lfs},{"Num",c}}
            end
            wr(a,vt,false)
          else
            wr(a,{"Idx",src_pk,{"Num",c}},false)
          end
          pc=pc+1
        elseif op=="CALL0" or op=="CALL1" or op=="CALL2" or op=="CALL3" or op=="CALL" then
          local fn_e=rd(b)
          local args={}
          if op=="CALL" then
            local pk=rd(c)
            if pk[1]=="_PACK" then
              for idx,x in ipairs(pk[2]) do args[idx]=x end
              if pk[3] then args[#args+1]=pk[3]
              elseif #args>0 and is_ec(unp(args[#args])) then args[#args]={"Paren",args[#args]} end
            else
              args={pk}
            end
          else
            local xs={} for idx,r in ipairs(c or {}) do xs[idx]=rd(r) end
            args=t1(xs)
          end
          local cal={"Call",fn_e,args}
          if d==0 then
            stmts[#stmts+1]={"CallStmt",cal} pc=pc+1
          elseif d==1 then
            wr(a,cal,false) pc=pc+1
          else
            local takes,j,skipped=collect_takes(cd,pc,ep,a)
            if #takes>0 then
              for _,spc in ipairs(skipped) do
                local is=cd[spc]
                local regs=is[1]=="CLEARS" and is[2] or {is[2]}
                for _,rg in ipairs(regs) do
                  if lout[spc][rg] then wr(rg,{"Nil"},true,spc) else env[rg]=nil end
                end
              end
              emit_takes(takes,cal,false)
              pc=j
            else
              env[a]=cal pc=pc+1
            end
          end
        elseif op=="TAILCALL0" or op=="TAILCALL1" or op=="TAILCALL2" or op=="TAILCALL3" or op=="TAILCALL" then
          local fn_e=rd(a)
          local args={}
          if op=="TAILCALL" then
            local pk=rd(b)
            if pk[1]=="_PACK" then
              for idx,x in ipairs(pk[2]) do args[idx]=x end
              if pk[3] then args[#args+1]=pk[3]
              elseif #args>0 and is_ec(unp(args[#args])) then args[#args]={"Paren",args[#args]} end
            else
              args={pk}
            end
          else
            local xs={} for idx,r in ipairs(b or {}) do xs[idx]=rd(r) end
            args=t1(xs)
          end
          flush_cb()
          stmts[#stmts+1]={"Return",{{"Call",fn_e,args}}}
          break
        elseif op=="RETURN0" then
          flush_cb() stmts[#stmts+1]={"Return",{}} break
        elseif op=="RETURN1" or op=="RETURN2" or op=="RETURN3" then
          local rs={rd(a)}
          if b then rs[2]=rd(b) end
          if c then rs[3]=rd(c) end
          flush_cb()
          local rs2={}
          for idx,e in ipairs(rs) do
            if idx==#rs and is_ec(e) then rs2[idx]={"Paren",e} else rs2[idx]=e end
          end
          stmts[#stmts+1]={"Return",rs2}
          break
        elseif op=="RETURN" then
          local pk=rd(a)
          flush_cb()
          if pk[1]=="_PACK" then
            local es,tl=pk[2],pk[3]
            local aes={}
            for i,e in ipairs(es) do
              if not tl and i==#es and is_ec(e) then aes[i]={"Paren",e} else aes[i]=e end
            end
            if tl then aes[#aes+1]=tl end
            stmts[#stmts+1]={"Return",aes}
          else
            stmts[#stmts+1]={"Return",{pk}}
          end
          break
        else
          error("vm_op:"..tostring(op))
        end
      end
    end
    if env_out then for k,v in pairs(env) do env_out[k]=v end end
    return stmts
  end
  local body=lift_range(1,#cd+1,nil)
  if #body>0 and body[#body][1]=="Return" and #body[#body][2]==0 then table.remove(body) end
  local mv={}
  for _,v in pairs(cell_vars) do mv[v]=true end
  for _,v in ipairs(up_vars or {}) do mv[v]=true end
  body=fold_seq(body,tmp_set,mv,nil,kgv)
  local uv=all_vars({"Block",body})
  local ut={}
  for _,v in ipairs(dec_top) do if uv[v] then ut[#ut+1]=v end end
  if #ut>0 then table.insert(body,1,{"LocalVar",ut,{}}) end
  local ps={}
  for i,p in ipairs(pr.params) do ps[i]=p_names[p[1]] end
  local va=not not pr.vararg
  if is_root then return {"Block",body} end
  return {"Func",ps,va,{"Block",body}}
end
local function is_wm_set(s)
  if s[1]=="Assign" and #s[2]==1 and #s[3]==1 then
    local l,r=unp(s[2][1]),unp(s[3][1])
    return l[1]=="Var" and l[2]:find("PROMETHEUS",1,true)~=nil and r[1]=="Str"
  end
  if s[1]=="CallStmt" then
    local mc=unp(s[2])
    if mc[1]=="MCall" and mc[3]=="gsub" and #mc[4]==2 then
      local b0,p1,p2=unp(mc[2]),unp(mc[4][1]),unp(mc[4][2])
      return b0[1]=="Str" and p1[1]=="Str" and p1[2]==".+" and p2[1]=="Func" and #p2[2]==1
    end
  end
  return false
end
local function vm_here(b)
  local hit=false
  local function g(x)
    if hit or type(x)~="table" then return end
    local k=x[1]
    if k=="Block" then
      local ok,inf=pcall(VM.ext_vm,x)
      if ok and inf then hit=true return end
    end
    for i=1,#x do g(x[i]) end
  end
  for _,s in ipairs(b[2]) do g(s) if hit then return false end end
  return true
end
function M.inv_vm(ast,kgv)
  local function lft(b)
    local ok,info=pcall(VM.ext_vm,b)
    local ld
    if ok and info then
      if not vm_here(b) then return nil end
      ld=M.lift_proto(info.proto,{},true,nil,kgv)
    else
      ld=VCS.lift_cs(b)
    end
    if not ld then return nil end
    local wm={}
    for _,st in ipairs(b[2]) do if is_wm_set(st) then wm[#wm+1]=st end end
    if #wm>0 then
      local out={}
      for _,s in ipairs(wm) do out[#out+1]=s end
      for _,s in ipairs(ld[2]) do out[#out+1]=s end
      return {"Block",out}
    end
    return ld
  end
  local function rec(n)
    if type(n)~="table" then return n end
    local k=n[1]
    if type(k)~="string" then
      local r={} for i=1,#n do r[i]=rec(n[i]) end return r
    end
    if k=="Func" then
      local lb=lft(n[4])
      if lb then return {"Func",n[2],n[3],lb} end
      return {"Func",n[2],n[3],rec(n[4])}
    end
    local r={k} for i=2,#n do r[i]=rec(n[i]) end return r
  end
  return lft(ast) or rec(ast)
end
return M
