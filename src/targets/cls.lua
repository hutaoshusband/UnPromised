local A=require("src.frontend.ast")
local F=require("src.frontend.fold")
local S=require("src.frontend.scope")
local CA=require("src.passes.ca")
local CF=require("src.passes.cff")
local EN=require("src.passes.enc")
local M={}
local unp=A.unp
local function has_reb(n)
  local h=false
  A.walk(n,function(x)
    if h then return end
    if x[1]=="LocalFunc" or x[1]=="Func" then
      local ps,va,bd
      if x[1]=="LocalFunc" then ps,va,bd=x[3],x[4],x[5] else ps,va,bd=x[2],x[3],x[4] end
      if #ps==3 and not va then
        local rt=bd[2][#bd[2]]
        if rt and rt[1]=="Return" and #rt[2]==1 then
          local rx=unp(rt[2][1])
          if rx[1]=="Idx" and unp(rx[3])[1]=="Var" and unp(rx[3])[2]==ps[3] then h=true end
        end
      end
    end
  end)
  return h
end
local function has_vmw(n)
  local h=false
  A.walk(n,function(x)
    if h then return end
    if x[1]=="While" and unp(x[2])[1]=="Bool" and unp(x[2])[2]==true then
      local c=0
      A.walk(x[3],function(y) if y[1]=="If" then c=c+1 end end)
      if c>=40 then h=true end
    end
  end)
  return h
end
local function has_wm(b)
  for _,s in ipairs(b) do
    if s[1]=="CallStmt" and unp(s[2])[1]=="MCall" and unp(s[2])[3]=="gsub" then return true end
  end
  return false
end
local function has_anti(n)
  local h=false
  A.walk(n,function(x)
    if h then return end
    if x[1]=="Str" and (x[2]=="Tamper Detected!" or x[2]=="sethook") then h=true
    elseif x[1]=="Field" and (x[3]=="sethook" or x[3]=="getupvalue") then h=true end
  end)
  return h
end
local function has_prox(n)
  local h=false
  A.walk(n,function(x)
    if h then return end
    if x[1]=="Call" and #x[3]==2 and unp(x[3][1])[1]=="Tbl" and unp(x[3][2])[1]=="Tbl" and #unp(x[3][2])[2]==2 then
      local e0,e1=unp(x[3][2])[2][1],unp(x[3][2])[2][2]
      if e0[1]=="F" and e1[1]=="F" and unp(e0[3])[1]=="Func" and unp(e1[3])[1]=="Func" then
        local f0,f1=unp(e0[3]),unp(e1[3])
        if #f0[2]==2 and #f1[2]==2 and #f0[4][2]==1 and #f1[4][2]==1 then
          local k0,k1=f0[4][2][1][1],f1[4][2][1][1]
          if (k0=="Assign" and k1=="Return") or (k0=="Return" and k1=="Assign") then h=true end
        end
      end
    end
  end)
  return h
end
local function has_split(n)
  local h=false
  A.walk(n,function(x)
    if h then return end
    if x[1]=="Func" and #x[2]==1 and not x[3] and #x[4][2]>0 and x[4][2][#x[4][2]][1]=="Return" then
      for _,st in ipairs(x[4][2]) do
        if st[1]=="ForNum" and st[4][1]=="Bin" and st[4][2]=="/" and unp(st[4][3])[1]=="Un" and unp(st[4][3])[2]=="#" and unp(unp(st[4][3])[3])[1]=="Var" and unp(unp(st[4][3])[3])[2]==x[2][1] then
          h=true
        end
      end
    end
  end)
  return h
end
local function cnt_half(n)
  local c=0
  A.walk(n,function(x)
    if x[1]=="Num" and x[2]%1~=0 then c=c+1 end
  end)
  return c
end
local function cff_info(n)
  local ds=CF.find_cff(n)
  if #ds==0 then return nil end
  local best=ds[1]
  for i=2,#ds do if #ds[i].ls>#best.ls then best=ds[i] end end
  local h=cnt_half(n)
  local an
  A.walk(n,function(x)
    if an then return end
    if x[1]=="Return" and #x[2]==1 and unp(x[2][1])[1]=="Call" then
      local c=unp(x[2][1])
      local fn=unp(c[2])
      if fn[1]=="Func" and not fn[3] and #fn[2]>=15 and #CF.find_cff(fn[4])>0 then
        an=#c[3]
      end
    end
  end)
  local fl=(an==7 or (an~=11 and h==0)) and "wearedevs" or "prom_v03"
  local m45,m8=false,false
  for _,blk in ipairs(best.ls) do
    local p1,p2=EN.ext_lcg(blk)
    local f45,f257=EN.ext_lcg_blk(blk[2])
    if (p1 and p2) or f45 then m45=true end
    if EN.ext_k8(blk) or f257 or EN.ext_k8_blk(blk[2]) then m8=true end
  end
  return {flavor=fl,args=an,leaves=#best.ls,half=h,enc=m45 and m8,pv=best.pv,ls=best.ls}
end
local function try_pool(sts)
  for i,st in ipairs(sts) do
    if st[1]=="LocalVar" and #st[2]==1 and #st[3]==1 and unp(st[3][1])[1]=="Tbl" then
      local fs=unp(st[3][1])[2]
      local ok=#fs>0
      local pvs={}
      for j,f in ipairs(fs) do
        if f[1]~="V" or unp(f[2])[1]~="Str" then ok=false break end
        pvs[j]=unp(f[2])[2]
      end
      if ok and i<#sts then
        local has_r=sts[#sts][1]=="Return"
        if not has_r then
          for j=i+1,#sts do if sts[j][1]=="Do" then has_r=true break end end
        end
        if has_r then
          local rest={}
          for j=i+1,#sts do rest[#rest+1]=sts[j] end
          local ns={}
          for j=1,i do ns[j]=sts[j] end
          for _,x in ipairs(S.r_pool({"Block",rest},st[2][1],pvs)[2]) do ns[#ns+1]=x end
          return true,{"Block",ns}
        end
      end
    end
  end
  return false,{"Block",sts}
end
function M.detect_layers(ast)
  ast=F.fold(ast)
  local wm=has_wm(ast[2])
  local cur=ast
  local wn=0
  while cur[1]=="Block" and #cur[2]>0 and cur[2][#cur[2]][1]=="Return" and #cur[2][#cur[2]][2]==1 do
    local c0=unp(cur[2][#cur[2]][2][1])
    local fn=c0[1]=="Call" and unp(c0[2]) or nil
    if fn and fn[1]=="Func" and #fn[2]==0 and fn[3] and #c0[3]==1 and unp(c0[3][1])[1]=="Vararg" then
      wn=wn+1
      if has_wm(fn[4][2]) then wm=true end
      cur=fn[4]
    else break end
  end
  local h=CA.find_hdr(cur[2])
  local ca
  local bst=cur[2]
  if h then
    local dc=h.dec
    local em="none"
    if dc then
      if dc.t64 and dc.t85 then em="mixed" elseif dc.t64 then em="base64" elseif dc.t85 then em="base85" end
    end
    ca={flat=false,enc=em,rot=h.rot~=nil}
    bst={}
    for k=1,h.i0-1 do bst[#bst+1]=cur[2][k] end
    for k=h.i1,#cur[2] do bst[#bst+1]=cur[2][k] end
  end
  local pool,cur2=try_pool(bst)
  local ci=cff_info(cur2)
  local reb=has_reb(cur2)
  local vmw=has_vmw(cur2)
  local anti=has_anti(cur2)
  if ci and not ca then
    local t64,t85,hip=false,false,false
    for _,blk in ipairs(ci.ls) do
      for _,st in ipairs(blk[2]) do
        if st[1]=="Assign" then
          if #st[3]==1 and unp(st[3][1])[1]=="Str" and unp(st[3][1])[2]=="ipairs" then hip=true end
          for _,r in ipairs(st[3]) do
            local u=unp(r)
            if u[1]=="Tbl" then
              if #u[2]==64 then t64=true elseif #u[2]==85 then t85=true end
            end
          end
        end
      end
    end
    if t64 or t85 then
      ca={flat=true,enc=(t64 and t85) and "mixed" or (t64 and "base64" or "base85"),rot=hip}
    end
  end
  local enc_do=false
  A.walk(cur2,function(x)
    if enc_do then return end
    if x[1]=="Do" then
      local m45,_,m8=EN.ext_lcg(x)
      if m45 and m8 then enc_do=true end
    end
  end)
  local enc=(ci and ci.enc) and "cff" or (enc_do and "native" or nil)
  local vm
  if ci and vmw then vm="native_proxy"
  elseif vmw then vm="native"
  elseif reb and ci then
    local cr=false
    for _,blk in ipairs(ci.ls) do if has_reb(blk) then cr=true break end end
    vm=cr and "fallback_cff" or "flattened"
  end
  local sp,px=has_split(cur2),has_prox(cur2)
  local kind
  if vm=="native_proxy" then kind="PROM_V03_MEDIUM"
  elseif vm=="flattened" then kind="PROM_V03_STRONG"
  elseif vm=="fallback_cff" then kind="PROM_V03_STRONG_FALLBACK"
  elseif ci and ci.flavor=="wearedevs" then kind="WEAREDEVS"
  elseif vm=="native" then kind="PROM_V03_VMIFY"
  elseif ci and ca and not ca.flat and wn>=1 then kind="PROM_V03_WEAK"
  elseif ci then kind="PROM_V03_CFF"
  elseif ca or enc or px or sp or wm or anti or wn>0 then kind="PROM_V03_CUSTOM"
  else kind="PROM_V03_MINIFY" end
  local co
  if ci then co={flavor=ci.flavor,args=ci.args,leaves=ci.leaves,half=ci.half,enc=ci.enc} end
  return {kind=kind,wrap=wn,pool=pool,ca=ca,cff=co,vm=vm,enc=enc,split=sp,prox=px,wm=wm,anti=anti}
end
function M.cls_ast(ast,sts)
  sts=sts or ast[2]
  local k=M.detect_layers(ast).kind
  if k=="PROM_V03_MEDIUM" or k=="PROM_V03_STRONG" or k=="WEAREDEVS" then return k end
  if #sts==2 and sts[1][1]=="LocalVar" and #sts[1][3]>0 and unp(sts[1][3][1])[1]=="Tbl" then return "PROM_V03_MEDIUM" end
  if cnt_half(ast)>0 then return "PROM_V03_STRONG" end
  return "WEAREDEVS"
end
return M
