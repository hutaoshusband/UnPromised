local A=require("src.frontend.ast")
local F=require("src.frontend.fold")
local M={}
local unp,cp=A.unp,A.cp
local fl,sb,sc=math.floor,string.byte,string.char
local M45=35184372088832
local function lnum(e)
  e=unp(e)
  if e[1]=="Num" then return e[2] end
  if e[1]=="Un" and e[2]=="-" and unp(e[3])[1]=="Num" then return -unp(e[3])[2] end
  return nil
end
local function mul45(a,b)
  local a0=a%32768
  local a1=fl(a/32768)%32768
  local a2=fl(a/1073741824)
  local b0=b%32768
  local b1=fl(b/32768)%32768
  local b2=fl(b/1073741824)
  local p0=a0*b0
  local p1=(a0*b1+a1*b0)%1073741824
  local p2=(a0*b2+a1*b1+a2*b0)%32768
  return (p0+p1*32768+p2*1073741824)%M45
end
function M.dec_str(c,seed,m45,a45,m8,k8)
  local s45=seed%M45
  local s8=seed%255+2
  local bf={}
  local pv=k8
  local out={}
  for i=1,#c do
    if #bf==0 then
      s45=(mul45(s45,m45)+a45)%M45
      local st=0
      repeat s8=(s8*m8)%257 st=st+1 if st>300 then break end until s8~=1
      local r=s8%32
      local j=13-(s8-r)/32
      local l=(fl(s45/(2^j))%4294967296)/(2^r)
      local v=fl((l%1)*4294967296)+fl(l)
      local lo=v%65536
      local hi=(v-lo)/65536
      bf={lo%256,(lo-lo%256)/256,hi%256,(hi-hi%256)/256}
    end
    local b=table.remove(bf)
    pv=(sb(c,i)+b+pv)%256
    out[i]=sc(pv)
  end
  return table.concat(out)
end
local function ext_lcg(n)
  local m45,a45,m8
  A.walk(n,function(x)
    if x[1]=="Bin" and x[2]=="%" then
      local modv=lnum(x[4])
      if modv==M45 then
        local inn=unp(x[3])
        if inn[1]=="Bin" and inn[2]=="+" then
          local p1,p2=unp(inn[3]),unp(inn[4])
          local mulp,addv
          local n1,n2=lnum(p1),lnum(p2)
          if p1[1]=="Bin" and p1[2]=="*" and n2 then mulp,addv=p1,n2
          elseif p2[1]=="Bin" and p2[2]=="*" and n1 then mulp,addv=p2,n1 end
          if mulp and addv then
            local mv=lnum(unp(mulp[3])) or lnum(unp(mulp[4]))
            if mv then m45,a45=mv,addv end
          end
        end
      elseif modv==257 then
        local inn=unp(x[3])
        if inn[1]=="Bin" and inn[2]=="*" then
          local mv=lnum(unp(inn[3])) or lnum(unp(inn[4]))
          if mv then m8=mv end
        end
      end
    end
  end)
  return m45,a45,m8
end
local function has_256_byte(n,kv)
  local sb_ok,st_ok,m_ok=false,false,false
  local v256={}
  A.walk(n,function(x)
    if (x[1]=="Field" and x[3]=="byte") or (x[1]=="Idx" and unp(x[3])[1]=="Str" and unp(x[3])[2]=="byte") then
      sb_ok=true
      if unp(x[2])[1]=="Var" and unp(x[2])[2]=="string" then st_ok=true end
    elseif x[1]=="Var" and x[2]=="string" then
      st_ok=true
    end
    if kv=="" then
      if x[1]=="Bin" and x[2]=="%" and lnum(x[4])==256 then m_ok=true end
    elseif (x[1]=="LocalVar" or x[1]=="Assign") and #x[2]==#x[3] then
      for i=1,#x[2] do
        local lh=x[1]=="LocalVar" and x[2][i] or (unp(x[2][i])[1]=="Var" and unp(x[2][i])[2] or nil)
        if lh then
          local r=unp(x[3][i])
          if r[1]=="Bin" and r[2]=="%" and lnum(r[4])==256 then
            v256[lh]=true
            if lh==kv then m_ok=true end
          elseif r[1]=="Var" and v256[r[2]] then
            v256[lh]=true
            if lh==kv then m_ok=true end
          end
        end
      end
    end
  end)
  return sb_ok and st_ok and m_ok
end
local function ext_k8(n)
  local k8
  A.walk(n,function(b)
    if b[1]=="Block" then
      local sts=b[2]
      for i=1,#sts-1 do
        local s1,s2=sts[i],sts[i+1]
        if s2[1]=="ForNum" or s2[1]=="While" then
          local nm,val
          if s1[1]=="LocalVar" and #s1[2]==1 and #s1[3]==1 then nm,val=s1[2][1],lnum(s1[3][1])
          elseif s1[1]=="Assign" and #s1[2]==1 and #s1[3]==1 and unp(s1[2][1])[1]=="Var" then
            nm,val=unp(s1[2][1])[2],lnum(s1[3][1])
          end
          local lb=s2[1]=="ForNum" and s2[6] or s2[3]
          if nm and val and val>=0 and val<=255 and math.floor(val)==val then
            if has_256_byte(lb,nm) then k8=val end
          end
        end
        local bps=s1[1]=="LocalVar" and #s1[2]==#s1[3] and s1[2] or nil
        local brs=bps and s1[3] or nil
        if not bps and s1[1]=="Assign" and #s1[2]==#s1[3] then
          bps,brs={},{}
          for j=1,#s1[2] do
            if unp(s1[2][j])[1]=="Var" then bps[#bps+1]=unp(s1[2][j])[2] brs[#brs+1]=s1[3][j] end
          end
        end
        if bps then
          for j=1,#bps do
            if brs[j] then
              local val=lnum(brs[j])
              if val and val>=0 and val<=255 and math.floor(val)==val then
                for k=i+1,math.min(#sts,i+8) do
                  local sk=sts[k]
                  if (sk[1]=="ForNum" or sk[1]=="While") and has_256_byte(sk[1]=="ForNum" and sk[6] or sk[3],bps[j]) then
                    k8=val
                  end
                end
              end
            end
          end
        end
      end
    end
  end)
  return k8
end
local function smt_tbl(rhs,ev)
  rhs=unp(rhs)
  if rhs[1]~="Call" or unp(rhs[2])[1]~="Var" or unp(rhs[2])[2]~="setmetatable" or #rhs[3]~=2 then return nil end
  local t1,t2=unp(rhs[3][1]),unp(rhs[3][2])
  if t1[1]~="Tbl" or #t1[2]~=0 or t2[1]~="Tbl" then return nil end
  for _,f in ipairs(t2[2]) do
    if f[1]=="F" and f[2]=="__index" then
      local v=unp(f[3])
      return v[1]=="Var" and v[2] or true
    elseif f[1]=="I" then
      local kx=unp(f[2])
      if (kx[1]=="Str" and kx[2]=="__index") or (ev and kx[1]=="Var" and ev[kx[2]] and ev[kx[2]][1]=="Str" and ev[kx[2]][2]=="__index") then
        local v=unp(f[3])
        return v[1]=="Var" and v[2] or true
      end
    end
  end
  return nil
end
local function is_smt(rhs,ev) return smt_tbl(rhs,ev)~=nil end
local function ext_dec_fn(fn)
  if fn[1]~="Func" or #fn[2]<2 or fn[3] then return nil end
  if ext_lcg(fn[4]) then return nil end
  return ext_k8(fn[4])
end
local function bind_pairs(s)
  local ps={}
  if s[1]=="LocalVar" then
    if #s[2]==#s[3] then
      for i=1,#s[2] do ps[#ps+1]={s[2][i],s[3][i]} end
    elseif #s[3]==0 then
      for _,nm in ipairs(s[2]) do ps[#ps+1]={nm,{"Nil"}} end
    end
  elseif s[1]=="Assign" and #s[2]==#s[3] then
    for i=1,#s[2] do
      local l=unp(s[2][i])
      if l[1]=="Var" then ps[#ps+1]={l[2],s[3][i]} end
    end
  elseif s[1]=="LocalFunc" then
    ps[1]={s[2],{"Func",s[3],s[4],s[5]}}
  elseif s[1]=="FuncStmt" and not s[3] and unp(s[2])[1]=="Var" then
    ps[1]={unp(s[2])[2],{"Func",s[4],s[5],s[6]}}
  end
  return ps
end
local function ext_tf(n)
  local tn,fn
  A.walk(n,function(x)
    for _,pr in ipairs(bind_pairs(x)) do
      local nm,rhs=pr[1],unp(pr[2])
      if is_smt(rhs) then tn=nm
      elseif rhs[1]=="Func" and #rhs[2]==2 and ext_dec_fn(rhs) then fn=nm end
    end
  end)
  if tn and not fn then
    A.walk(n,function(x)
      for _,pr in ipairs(bind_pairs(x)) do
        local nm,rhs=pr[1],unp(pr[2])
        if rhs[1]=="Func" and #rhs[2]==2 then fn=nm end
      end
    end)
  end
  return tn,fn
end
local function vars_rd(n)
  local s={}
  local function f(x,bnd)
    if type(x)~="table" then return end
    local k=x[1]
    if type(k)~="string" then
      for i=1,#x do f(x[i],bnd) end
      return
    end
    if k=="Var" then
      if not bnd[x[2]] then s[x[2]]=true end
    elseif k=="Block" then
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,st in ipairs(x[2]) do
        if st[1]=="LocalVar" then
          f(st[3],b2)
          for _,nm in ipairs(st[2]) do b2[nm]=true end
        elseif st[1]=="LocalFunc" then
          b2[st[2]]=true
          f(st[5],b2)
        else
          f(st,b2)
        end
      end
    elseif k=="Func" then
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,p in ipairs(x[2]) do b2[p]=true end
      f(x[4],b2)
    elseif k=="ForNum" then
      f(x[3],bnd) f(x[4],bnd) if x[5] then f(x[5],bnd) end
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      b2[x[2]]=true
      f(x[6],b2)
    elseif k=="ForIn" then
      f(x[3],bnd)
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,nm in ipairs(x[2]) do b2[nm]=true end
      f(x[4],b2)
    elseif k=="Repeat" then
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,st in ipairs(x[2][2]) do
        if st[1]=="LocalVar" then
          f(st[3],b2)
          for _,nm in ipairs(st[2]) do b2[nm]=true end
        elseif st[1]=="LocalFunc" then
          b2[st[2]]=true
          f(st[5],b2)
        else
          f(st,b2)
        end
      end
      f(x[3],b2)
    elseif k=="Assign" then
      for _,l in ipairs(x[2]) do if unp(l)[1]~="Var" then f(l,bnd) end end
      f(x[3],bnd)
    elseif k=="CAssign" then
      if unp(x[3])[1]~="Var" then f(x[3],bnd) end
      f(x[4],bnd)
    else
      for i=2,#x do f(x[i],bnd) end
    end
  end
  f(n,{})
  return s
end
local function wr_in(n)
  local s={}
  local function f(x,bnd)
    if type(x)~="table" then return end
    local k=x[1]
    if type(k)~="string" then
      for i=1,#x do f(x[i],bnd) end
      return
    end
    if k=="Assign" then
      for _,l in ipairs(x[2]) do
        local u=unp(l)
        if u[1]=="Var" then if not bnd[u[2]] then s[u[2]]=true end
        else f(l,bnd) end
      end
      f(x[3],bnd)
    elseif k=="CAssign" then
      local u=unp(x[3])
      if u[1]=="Var" then if not bnd[u[2]] then s[u[2]]=true end
      else f(x[3],bnd) end
      f(x[4],bnd)
    elseif k=="Block" then
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,st in ipairs(x[2]) do
        if st[1]=="LocalVar" then
          f(st[3],b2)
          for _,nm in ipairs(st[2]) do b2[nm]=true end
        elseif st[1]=="LocalFunc" then
          b2[st[2]]=true
          f(st[5],b2)
        else
          f(st,b2)
        end
      end
    elseif k=="LocalVar" then
      f(x[3],bnd)
    elseif k=="LocalFunc" then
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      b2[x[2]]=true f(x[5],b2)
    elseif k=="FuncStmt" then
      if not x[3] and unp(x[2])[1]=="Var" and not bnd[unp(x[2])[2]] then s[unp(x[2])[2]]=true end
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,p in ipairs(x[4]) do b2[p]=true end
      f(x[6],b2)
    elseif k=="ForNum" then
      f(x[3],bnd) f(x[4],bnd) if x[5] then f(x[5],bnd) end
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      b2[x[2]]=true f(x[6],b2)
    elseif k=="ForIn" then
      f(x[3],bnd)
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,nm in ipairs(x[2]) do b2[nm]=true end
      f(x[4],b2)
    elseif k=="Func" then
      local b2={} for u,v in pairs(bnd) do b2[u]=v end
      for _,p in ipairs(x[2]) do b2[p]=true end
      f(x[4],b2)
    else
      for i=2,#x do f(x[i],bnd) end
    end
  end
  f(n,{})
  return s
end
local function is_sbox_s(st)
  local k=st[1]
  if k=="ForNum" or k=="While" or k=="Repeat" then return true end
  if k=="LocalVar" or k=="Assign" then
    local ps=bind_pairs(st)
    if #ps==0 then return false end
    for _,pr in ipairs(ps) do
      local r=unp(pr[2])
      if r[1]=="Tbl" and #r[2]==0 then
      elseif r[1]=="Num" or r[1]=="Nil" or r[1]=="Bool" or r[1]=="Str" then
      elseif r[1]=="Field" and unp(r[2])[1]=="Var" and (unp(r[2])[2]=="math" or unp(r[2])[2]=="table" or unp(r[2])[2]=="string") then
      elseif r[1]=="Idx" and unp(r[2])[1]=="Var" and (unp(r[2])[2]=="math" or unp(r[2])[2]=="table" or unp(r[2])[2]=="string") then
      elseif r[1]=="Var" then
      else return false end
    end
    return true
  end
  return false
end
local function sub_v(e,env)
  if type(e)~="table" then return e end
  if e[1]=="Var" and env[e[2]] then return cp(env[e[2]]) end
  if e[1]=="Func" or e[1]=="LocalFunc" then return e end
  if type(e[1])~="string" then
    local r={} for i=1,#e do r[i]=sub_v(e[i],env) end return r
  end
  local r={e[1]} for i=2,#e do r[i]=sub_v(e[i],env) end return r
end
local function ref_after(nm,sts,i0)
  for i=i0,#sts do
    local s=sts[i]
    if vars_rd(s)[nm] or wr_in(s)[nm] then return true end
    if s[1]=="LocalVar" then
      for _,ln in ipairs(s[2]) do if ln==nm then return false end end
    elseif s[1]=="LocalFunc" and s[2]==nm then
      return false
    end
  end
  return false
end
local function dead_after(nm,sts,i0)
  for i=i0,#sts do
    local s=sts[i]
    if vars_rd(s)[nm] then return false end
    if s[1]=="LocalVar" then
      for _,ln in ipairs(s[2]) do if ln==nm then return true end end
    elseif s[1]=="LocalFunc" and s[2]==nm then
      return true
    elseif s[1]=="Assign" and #s[2]==1 and #s[3]==1 and unp(s[2][1])[1]=="Var" and unp(s[2][1])[2]==nm then
      return true
    end
    if s[1]=="If" or s[1]=="While" or s[1]=="Repeat" or s[1]=="ForNum" or s[1]=="ForIn" or s[1]=="Do" then
      if wr_in(s)[nm] then return false end
    end
  end
  return true
end
local function cp_m(t)
  local r={} for k,v in pairs(t) do r[k]=v end return r
end
local function inv_enc_blk(blk,sp0,ta0,env0,cr0)
  local sts=blk[2]
  local sp,ta,env,cr=cp_m(sp0),cp_m(ta0),cp_m(env0),cp_m(cr0)
  local rm,dvs,rm_r,setups={},{},{},{}
  for i,st in ipairs(sts) do
    if st[1]=="Do" then
      local m45,a45,m8=ext_lcg(st)
      if m45 and m8 then
        local fnm,tnm,k8
        for _,sub in ipairs(st[2][2]) do
          for _,pr in ipairs(bind_pairs(sub)) do
            local nm,rhs=pr[1],unp(pr[2])
            if is_smt(rhs) then tnm=nm
            elseif rhs[1]=="Func" then
              local k=ext_dec_fn(rhs)
              if k then fnm,k8=nm,k end
            end
          end
        end
        if fnm and k8 then
          setups[i]={fnm,tnm,m45,a45,m8,k8}
          rm[i]=true dvs[fnm]=true
          if tnm then dvs[tnm]=true end
        end
      end
    end
  end
  local pi,m45,a45,m8,di,ti,fnm,tnm,k8,pnm
  local function add_setup(hi,sfn,stnm,sm45,sa45,sm8,sk8,need,shi)
    setups[hi]={sfn,stnm,sm45,sa45,sm8,sk8}
    for j=(shi or hi),1,-1 do
      if j==pi or j==di or j==ti then
        rm[j]=true
        for _,pr in ipairs(bind_pairs(sts[j])) do dvs[pr[1]]=true end
      else
        local sj=sts[j]
        if j>pi then
          local ps=bind_pairs(sj)
          if #ps>0 then
            local all_n=true
            for _,pr in ipairs(ps) do if not need[pr[1]] then all_n=false break end end
            if all_n and is_sbox_s(sj) then
              rm[j]=true
              for _,pr in ipairs(ps) do
                dvs[pr[1]]=true
                for v,_ in pairs(vars_rd(pr[2])) do need[v]=true end
              end
            end
          end
        else
          if rm[j] or ext_lcg(sj) then break end
          if is_sbox_s(sj) then
            local rd,wr=vars_rd(sj),wr_in(sj)
            local hit=false
            for v,_ in pairs(need) do if rd[v] or wr[v] then hit=true break end end
            if hit then
              rm[j]=true
              for v,_ in pairs(wr) do dvs[v]=true end
              for v,_ in pairs(rd) do need[v]=true end
            elseif sj[1]=="LocalVar" and #sj[3]>0 then
              local ps=bind_pairs(sj)
              if #ps>0 then
                local all_n=true
                for _,pr in ipairs(ps) do if not need[pr[1]] then all_n=false break end end
                if all_n then
                  for _,pr in ipairs(ps) do
                    dvs[pr[1]]=true
                    for v,_ in pairs(vars_rd(pr[2])) do need[v]=true end
                  end
                end
              end
            end
          else
            local ps=bind_pairs(sj)
            local fn_b=#ps>0
            for _,pr in ipairs(ps) do if unp(pr[2])[1]~="Func" then fn_b=false break end end
            local wr,rd=wr_in(sj),vars_rd(sj)
            local bad=false
            for v,_ in pairs(need) do if wr[v] or (not fn_b and rd[v]) then bad=true break end end
            if bad then break end
          end
        end
      end
    end
    for v,_ in pairs(need) do rm_r[v]=true end
  end
  local senv={}
  for i,st in ipairs(sts) do
    if not rm[i] then
      for _,pr in ipairs(bind_pairs(st)) do
        local nm,rhs=pr[1],unp(pr[2])
        if rhs[1]=="Func" then
          local l45,la45,lm8=ext_lcg(rhs)
          if l45 and lm8 then
            pi,pnm,m45,a45,m8,di,ti,fnm,tnm,k8=i,nm,l45,la45,lm8,nil,nil,nil,nil,nil
            dvs[nm]=true
            break
          end
          if pi and not di then
            local k=ext_dec_fn(rhs)
            if k then di,fnm,k8=i,nm,k dvs[nm]=true break end
          end
        end
        if pi and is_smt(rhs,senv) then
          ti,tnm=i,nm dvs[nm]=true
        end
      end
      if st[1]=="LocalVar" or st[1]=="Assign" then
        for _,pr in ipairs(bind_pairs(st)) do
          local u=unp(pr[2])
          if u[1]=="Str" then senv[pr[1]]=u else senv[pr[1]]=nil end
        end
      else
        for v,_ in pairs(wr_in(st)) do senv[v]=nil end
      end
      if pi and di and ti and i>=ti then
        local hi=math.max(pi,di,ti)
        local need={[pnm]=true,[fnm]=true,[tnm]=true}
        for _,idx in ipairs({pi,di,ti}) do
          for v,_ in pairs(vars_rd(sts[idx])) do need[v]=true end
        end
        add_setup(hi,fnm,tnm,m45,a45,m8,k8,need)
        pi,di,ti,fnm,tnm,k8,pnm=nil,nil,nil,nil,nil,nil,nil
      elseif pi and not (di and ti) and i>pi then
        local af,ak,itnm,sb1
        A.walk(st,function(x)
          if ak and itnm then return end
          if x[1]=="Idx" then
            local b1,ca=unp(x[2]),unp(x[3])
            local srv=(not ti) and smt_tbl(b1,senv) or nil
            local tok=(ti and b1[1]=="Var" and b1[2]==tnm and tnm) or (srv and (type(srv)=="string" and ("__IDX_"..srv) or "__INLINE_SMT"))
            if tok and ca[1]=="Call" and #ca[3]>=2 then
              local fn=unp(ca[2])
              if di and fn[1]=="Var" and fn[2]==fnm then
                af,ak,itnm,sb1=sts[di],k8,tok,b1
              elseif not di and fn[1]=="Func" then
                local k=ext_dec_fn(fn)
                if k then af,ak,itnm,sb1=fn,k,tok,b1 end
              end
            end
          end
        end)
        if not ak and ti and not di and i>ti then
          A.walk(st,function(x)
            if ak then return end
            if x[1]=="Func" then
              local k=ext_dec_fn(x)
              if k then af,ak,itnm=x,k,tnm end
            end
          end)
        end
        if ak and itnm then
          local hi=math.max(pi,di or 0,ti or 0)
          local shi=math.max(hi,i-1)
          local sfn=di and fnm or ("__ANON_"..itnm)
          local need={[pnm]=true}
          if di then need[fnm]=true end
          if ti then need[tnm]=true end
          for v,_ in pairs(vars_rd(sts[pi])) do need[v]=true end
          if di then for v,_ in pairs(vars_rd(sts[di])) do need[v]=true end end
          if ti then for v,_ in pairs(vars_rd(sts[ti])) do need[v]=true end end
          if sb1 then for v,_ in pairs(vars_rd(sb1)) do need[v]=true end end
          for v,_ in pairs(vars_rd(af)) do need[v]=true end
          add_setup(hi,sfn,itnm,m45,a45,m8,ak,need,shi)
          pi,di,ti,fnm,tnm,k8,pnm=nil,nil,nil,nil,nil,nil,nil
        end
      end
    end
  end
  if pi and not di and not ti then
    local pal={[pnm]=true}
    local ev2={}
    local jcs,srv
    for j=pi+1,#sts do
      local sj=sts[j]
      if sj[1]=="LocalVar" or sj[1]=="Assign" then
        for _,pr in ipairs(bind_pairs(sj)) do
          local u=unp(pr[2])
          if u[1]=="Var" and pal[u[2]] then pal[pr[1]]=true dvs[pr[1]]=true end
          if u[1]=="Str" then ev2[pr[1]]=u else ev2[pr[1]]=nil end
        end
      elseif sj[1]=="CallStmt" then
        local t=smt_tbl(sj[2],ev2)
        if t then jcs,srv=j,t break end
      end
    end
    if jcs then
      local need={[pnm]=true}
      for v,_ in pairs(pal) do need[v]=true end
      for v,_ in pairs(vars_rd(sts[pi])) do need[v]=true end
      for v,_ in pairs(vars_rd(sts[jcs])) do need[v]=true end
      if type(srv)=="string" then need[srv]=true end
      local ok_d=true
      for j=jcs+1,#sts do
        local rd=vars_rd(sts[j])
        for v,_ in pairs(pal) do if rd[v] then ok_d=false break end end
        if type(srv)=="string" and rd[srv] then ok_d=false end
        if not ok_d then break end
      end
      if ok_d then
        for k=pi-1,math.max(1,pi-12),-1 do
          local sk=sts[k]
          if sk[1]=="While" or sk[1]=="ForNum" then
            local imp=false
            A.walk(sk,function(x) if x[1]=="Func" or x[1]=="MCall" or x[1]=="Vararg" then imp=true end end)
            if not imp then
              A.walk(sk,function(x)
                if x[1]=="Assign" then
                  for ix,l in ipairs(x[2]) do
                    local u=unp(l)
                    if u[1]=="Idx" and unp(u[2])[1]=="Var" and x[3][ix] then
                      local cm,hm=unp(u[2])[2],false
                      A.walk(x[3][ix],function(y) if y[1]=="Bin" and y[2]=="-" and lnum(y[4])==1 then hm=true end end)
                      if hm then
                        local ru=false
                        for m=pi+1,#sts do if vars_rd(sts[m])[cm] then ru=true break end end
                        if not ru then need[cm]=true end
                      end
                    end
                  end
                end
              end)
            end
          end
        end
        rm[jcs]=true
        add_setup(pi,"__DEAD_"..pi,nil,m45,a45,m8,0,need,jcs-1)
      end
    end
  end
  local wsuf={}
  wsuf[#sts+1]={}
  for i=#sts,1,-1 do
    local s2=cp_m(wsuf[i+1])
    for v,_ in pairs(wr_in(sts[i])) do s2[v]=true end
    wsuf[i]=s2
  end
  local fwd_sp={}
  local function find_decl(v,lim)
    for j=lim-1,1,-1 do
      local sj=sts[j]
      if sj[1]=="LocalVar" then
        for _,nm in ipairs(sj[2]) do if nm==v then return j end end
      elseif sj[1]=="LocalFunc" and sj[2]==v then return j end
    end
    return 1
  end
  for hi,s in pairs(setups) do
    local fnm,tnm=s[1],s[2]
    local dec_i=find_decl(fnm,hi)
    local info={tnm,s[3],s[4],s[5],s[6]}
    fwd_sp[#fwd_sp+1]={dec_i,hi,fnm,info}
    local fal,tal={[fnm]=true},tnm and {[tnm]=true} or {}
    for k=hi+1,math.min(#sts,hi+16) do
      local ps=bind_pairs(sts[k])
      if #ps==0 then break end
      for _,pr in ipairs(ps) do
        local nm,rhs=pr[1],unp(pr[2])
        if rhs[1]=="Var" and fal[rhs[2]] then
          fal[nm]=true
          fwd_sp[#fwd_sp+1]={find_decl(nm,k),k,nm,info}
        elseif rhs[1]=="Var" and tnm and tal[rhs[2]] then
          tal[nm]=true
        end
      end
    end
  end
  local cur_i=0
  local function tf_e(e,sp2,ta2,e2,cr2)
    if type(e)~="table" then return e end
    local k=e[1]
    if k=="Block" then return inv_enc_blk(e,sp2,ta2,e2,cr2) end
    if k=="Func" then
      local s2,t2,en2,c2=cp_m(sp2),cp_m(ta2),cp_m(e2),cp_m(cr2)
      for _,fs in ipairs(fwd_sp) do
        if cur_i>=fs[1] and cur_i<fs[2] and not s2[fs[3]] then
          s2[fs[3]]=fs[4]
        end
      end
      local sh={} for _,p in ipairs(e[2]) do sh[p]=true end
      for u,fv in pairs(s2) do if sh[u] or (fv[1] and sh[fv[1]]) then s2[u]=nil end end
      for u,v in pairs(ta2) do if sh[u] or sh[v] then t2[u]=nil end end
      for u,v in pairs(cr2) do if sh[u] or sh[v[1]] then c2[u]=nil end end
      for u,_ in pairs(e2) do if sh[u] then en2[u]=nil end end
      local ws=wr_in(e[4])
      for u,_ in pairs(ws) do en2[u]=nil s2[u]=nil t2[u]=nil c2[u]=nil end
      return {"Func",e[2],e[3],inv_enc_blk(e[4],s2,t2,en2,c2)}
    elseif k=="ForNum" then
      local v=e[2]
      local s2,t2,en2,c2=cp_m(sp2),cp_m(ta2),cp_m(e2),cp_m(cr2)
      en2[v]=nil
      for u,fv in pairs(sp2) do if u==v or fv[1]==v then s2[u]=nil end end
      for u,tv in pairs(ta2) do if u==v or tv==v then t2[u]=nil end end
      for u,cv in pairs(cr2) do if u==v or cv[1]==v then c2[u]=nil end end
      return {"ForNum",v,tf_e(e[3],sp2,ta2,e2,cr2),tf_e(e[4],sp2,ta2,e2,cr2),e[5] and tf_e(e[5],sp2,ta2,e2,cr2) or false,inv_enc_blk(e[6],s2,t2,en2,c2)}
    elseif k=="ForIn" then
      local vs={} for _,v in ipairs(e[2]) do vs[v]=true end
      local s2,t2,en2,c2=cp_m(sp2),cp_m(ta2),cp_m(e2),cp_m(cr2)
      for u,_ in pairs(vs) do en2[u]=nil end
      for u,fv in pairs(sp2) do if vs[u] or (fv[1] and vs[fv[1]]) then s2[u]=nil end end
      for u,tv in pairs(ta2) do if vs[u] or vs[tv] then t2[u]=nil end end
      for u,cv in pairs(cr2) do if vs[u] or vs[cv[1]] then c2[u]=nil end end
      local es={} for i,x in ipairs(e[3]) do es[i]=tf_e(x,sp2,ta2,e2,cr2) end
      return {"ForIn",e[2],es,inv_enc_blk(e[4],s2,t2,en2,c2)}
    elseif k=="Idx" then
      local b1,ca=unp(e[2]),unp(e[3])
      local to
      if b1[1]=="Var" then
        to=ta2[b1[2]] or b1[2]
      else
        local srv=smt_tbl(b1,e2)
        if srv then to=type(srv)=="string" and ("__IDX_"..srv) or "__INLINE_SMT" end
      end
      if to and ca[1]=="Var" and cr2[ca[2]] then
        if cr2[ca[2]][1]==to then return {"Str",cr2[ca[2]][2]} end
      end
      if to and ca[1]=="Call" and #ca[3]>=2 then
        local fn=unp(ca[2])
        local tnm,m4,a4,m8v,k8v
        if fn[1]=="Var" and sp2[fn[2]] then
          local fv=sp2[fn[2]]
          if fv[1]==to then tnm,m4,a4,m8v,k8v=fv[1],fv[2],fv[3],fv[4],fv[5] end
        elseif fn[1]=="Func" then
          local ik=ext_dec_fn(fn)
          if ik then
            for _,fv in pairs(sp2) do
              if fv[1]==to then tnm,m4,a4,m8v,k8v=fv[1],fv[2],fv[3],fv[4],ik break end
            end
          end
        end
        if m4 then
          local a0=F.fold(sub_v(tf_e(ca[3][1],sp2,ta2,e2,cr2),e2))
          local a1=F.fold(sub_v(tf_e(ca[3][2],sp2,ta2,e2,cr2),e2))
          local cs,sn=unp(a0),lnum(a1)
          if cs[1]=="Str" and sn and math.floor(sn)==sn then
            return {"Str",M.dec_str(cs[2],sn,m4,a4,m8v,k8v)}
          end
        end
      end
      return {"Idx",tf_e(e[2],sp2,ta2,e2,cr2),tf_e(e[3],sp2,ta2,e2,cr2)}
    elseif k=="Call" then
      local fn=unp(e[2])
      if fn[1]=="Var" and sp2[fn[2]] and #e[3]==2 then
        local fv=sp2[fn[2]]
        if not fv[1] then
          local a0=F.fold(sub_v(tf_e(e[3][1],sp2,ta2,e2,cr2),e2))
          local a1=F.fold(sub_v(tf_e(e[3][2],sp2,ta2,e2,cr2),e2))
          local cs,sn=unp(a0),lnum(a1)
          if cs[1]=="Str" and sn and math.floor(sn)==sn then
            return {"Str",M.dec_str(cs[2],sn,fv[2],fv[3],fv[4],fv[5])}
          end
        end
      end
      local as={} for i,a in ipairs(e[3]) do as[i]=tf_e(a,sp2,ta2,e2,cr2) end
      return {"Call",tf_e(e[2],sp2,ta2,e2,cr2),as}
    elseif type(k)~="string" then
      local r={} for i=1,#e do r[i]=tf_e(e[i],sp2,ta2,e2,cr2) end return r
    end
    local r={k} for i=2,#e do r[i]=tf_e(e[i],sp2,ta2,e2,cr2) end return r
  end
  local out={}
  for i,st in ipairs(sts) do
    cur_i=i
    if setups[i] then
      local s=setups[i]
      sp[s[1]]={s[2],s[3],s[4],s[5],s[6]}
    end
    if rm[i] then
      if st[1]=="LocalVar" and #st[2]>0 then
        for _,nm in ipairs(st[2]) do rm_r[nm]=true end
        out[#out+1]={"LocalVar",st[2],{}}
      end
    else
      local k=st[1]
      local st2
      if k=="While" or k=="Repeat" or k=="ForNum" or k=="ForIn" then
        local ws=wr_in(st)
        for v,_ in pairs(ws) do env[v]=nil sp[v]=nil ta[v]=nil cr[v]=nil end
        st2=tf_e(st,sp,ta,env,cr)
        for v,_ in pairs(ws) do env[v]=nil sp[v]=nil ta[v]=nil cr[v]=nil end
      elseif k=="If" or k=="Do" then
        local ws=wr_in(st)
        if k=="If" then
          local cs={}
          for j,c2 in ipairs(st[2]) do cs[j]={tf_e(c2[1],sp,ta,env,cr),inv_enc_blk(c2[2],sp,ta,env,cr)} end
          st2={"If",cs,st[3] and inv_enc_blk(st[3],sp,ta,env,cr) or false}
        else
          st2={"Do",inv_enc_blk(st[2],sp,ta,env,cr)}
        end
        for v,_ in pairs(ws) do env[v]=nil sp[v]=nil ta[v]=nil cr[v]=nil end
      elseif k=="CAssign" then
        local u=unp(st[3])
        local lh=u[1]=="Var" and st[3] or tf_e(st[3],sp,ta,env,cr)
        st2={"CAssign",st[2],lh,tf_e(st[4],sp,ta,env,cr)}
        if u[1]=="Var" then env[u[2]]=nil sp[u[2]]=nil ta[u[2]]=nil cr[u[2]]=nil end
      elseif k=="LocalVar" or k=="Assign" then
        local rh2={}
        for _,r in ipairs(st[3]) do
          if r[1]=="Func" then
            local ws=cp_m(wsuf[i+1])
            for u,_ in pairs(wr_in(r)) do ws[u]=true end
            local e_fn={} for kv,vv in pairs(env) do if not ws[kv] then e_fn[kv]=vv end end
            rh2[#rh2+1]=tf_e(r,sp,ta,e_fn,cr)
          else
            rh2[#rh2+1]=tf_e(r,sp,ta,env,cr)
          end
        end
        local lh2={}
        for j,l in ipairs(st[2]) do
          if type(l)=="string" or unp(l)[1]=="Var" then lh2[j]=l else lh2[j]=tf_e(l,sp,ta,env,cr) end
        end
        st2={k,lh2,rh2}
        local tor={} for _,fv in pairs(sp) do if fv[1] then tor[fv[1]]=true end end
        if #lh2==#rh2 then
          for j=1,#lh2 do
            local nm=type(lh2[j])=="string" and lh2[j] or (unp(lh2[j])[1]=="Var" and unp(lh2[j])[2] or nil)
            if nm then
              local ur=unp(rh2[j])
              local ssp=ur[1]=="Var" and sp[ur[2]] or nil
              local sta=(ur[1]=="Var" and (ta[ur[2]] or (tor[ur[2]] and ur[2]))) or nil
              local scr
              if ur[1]=="Call" and unp(ur[2])[1]=="Var" and sp[unp(ur[2])[2]] and #ur[3]==2 then
                local fv=sp[unp(ur[2])[2]]
                if fv[1] then
                  local a0=F.fold(sub_v(ur[3][1],env))
                  local a1=F.fold(sub_v(ur[3][2],env))
                  local cs,sn=unp(a0),lnum(a1)
                  if cs[1]=="Str" and sn and math.floor(sn)==sn then
                    scr={fv[1],M.dec_str(cs[2],sn,fv[2],fv[3],fv[4],fv[5])}
                  end
                end
              end
              sp[nm]=nil ta[nm]=nil cr[nm]=nil
              if ssp then
                sp[nm]=ssp dvs[nm]=true env[nm]=nil
              elseif sta then
                ta[nm]=sta dvs[nm]=true env[nm]=nil
              elseif scr then
                cr[nm]=scr dvs[nm]=true env[nm]=nil
              else
                local ru0=unp(rh2[j])
                local rk0=ru0[1]
                if rk0=="Str" or rk0=="Num" or rk0=="Bool" or rk0=="Nil" then
                  env[nm]=ru0
                elseif rk0=="Un" or rk0=="Bin" or rk0=="Var" then
                  local rf=unp(F.fold(rh2[j]))
                  if rf[1]=="Str" or rf[1]=="Num" or rf[1]=="Bool" or rf[1]=="Nil" then
                    env[nm]=rf
                  else
                    env[nm]=nil
                  end
                else
                  env[nm]=nil
                end
              end
            end
          end
        else
          for _,l in ipairs(lh2) do
            local nm=type(l)=="string" and l or (unp(l)[1]=="Var" and unp(l)[2] or nil)
            if nm then env[nm]=nil sp[nm]=nil ta[nm]=nil cr[nm]=nil end
          end
        end
      elseif k=="LocalFunc" or k=="FuncStmt" then
        local r=k=="LocalFunc" and {"Func",st[3],st[4],st[5]} or {"Func",st[4],st[5],st[6]}
        local ws=cp_m(wsuf[i+1])
        for u,_ in pairs(wr_in(r)) do ws[u]=true end
        local e_fn={} for kv,vv in pairs(env) do if not ws[kv] then e_fn[kv]=vv end end
        local r2=tf_e(r,sp,ta,e_fn,cr)
        if k=="LocalFunc" then
          st2={"LocalFunc",st[2],r2[2],r2[3],r2[4]}
          local nm=st[2] env[nm]=nil sp[nm]=nil ta[nm]=nil cr[nm]=nil
        else
          st2={"FuncStmt",st[2],st[3],r2[2],r2[3],r2[4]}
          if not st[3] and unp(st[2])[1]=="Var" then
            local nm=unp(st[2])[2] env[nm]=nil sp[nm]=nil ta[nm]=nil cr[nm]=nil
          end
        end
      else
        st2=tf_e(st,sp,ta,env,cr)
      end
      out[#out+1]=st2
    end
  end
  for v,_ in pairs(dvs) do rm_r[v]=true end
  if next(rm_r) then
    local ch=true
    while ch do
      ch=false
      local kp={}
      for idx,st in ipairs(out) do
        local keep=true
        if st[1]=="LocalVar" and #st[3]==0 then
          local nl={}
          for _,nm in ipairs(st[2]) do
            if not rm_r[nm] or ref_after(nm,out,idx+1) then nl[#nl+1]=nm else ch=true end
          end
          if #nl==0 then keep=false
          elseif #nl~=#st[2] then kp[#kp+1]={"LocalVar",nl,{}} keep=false end
        else
          local ps=bind_pairs(st)
          if #ps>0 then
            local all_d=true
            for _,pr in ipairs(ps) do
              if not (dvs[pr[1]] and dead_after(pr[1],out,idx+1)) then all_d=false break end
            end
            if all_d then
              ch=true keep=false
              if st[1]=="LocalVar" then
                local nl={}
                for _,nm in ipairs(st[2]) do
                  if ref_after(nm,out,idx+1) then nl[#nl+1]=nm end
                end
                if #nl>0 then kp[#kp+1]={"LocalVar",nl,{}} end
              end
            end
          end
        end
        if keep then kp[#kp+1]=st end
      end
      out=kp
    end
  end
  return {"Block",out}
end
local function ext_lcg_blk(sts)
  local env={}
  local f45,f257
  for _,st in ipairs(sts) do
    if st[1]=="Assign" then
      local rvs={}
      for k,r in ipairs(st[3]) do
        r=unp(r)
        if r[1]=="Num" then rvs[k]={"C",r[2]}
        elseif r[1]=="Var" then rvs[k]=env[r[2]] or {"V",r[2]}
        elseif r[1]=="Bin" and (r[2]=="*" or r[2]=="+" or r[2]=="%") and unp(r[3])[1]=="Var" and unp(r[4])[1]=="Var" then
          local lv=env[unp(r[3])[2]] or {"V",unp(r[3])[2]}
          local rv=env[unp(r[4])[2]] or {"V",unp(r[4])[2]}
          local nd={r[2],lv,rv}
          rvs[k]=nd
          if r[2]=="%" and rv[1]=="C" and rv[2]==M45 and lv[1]=="+" then
            local a,b=lv[2],lv[3]
            if b[1]=="*" and a[1]=="C" then a,b=b,a end
            if a[1]=="*" and b[1]=="C" then
              local mu=a[2][1]=="C" and a[2][2] or (a[3][1]=="C" and a[3][2] or nil)
              if mu then f45={mu,b[2]} end
            end
          elseif r[2]=="%" and rv[1]=="C" and rv[2]==257 and lv[1]=="*" then
            local mu=lv[2][1]=="C" and lv[2][2] or (lv[3][1]=="C" and lv[3][2] or nil)
            if mu then f257=mu end
          end
        end
      end
      for ix,l in ipairs(st[2]) do
        l=unp(l)
        if l[1]=="Var" then env[l[2]]=rvs[ix] end
      end
    end
  end
  return f45,f257
end
local function ext_k8_blk(sts)
  local h45,h255=false,false
  for _,st in ipairs(sts) do
    if st[1]=="Assign" then
      for _,r in ipairs(st[3]) do
        local u=unp(r)
        if u[1]=="Num" then
          if u[2]==M45 then h45=true elseif u[2]==255 then h255=true end
        end
      end
    end
  end
  if not (h45 and h255) then return nil end
  local sl=false
  for _,st in ipairs(sts) do
    if st[1]=="Assign" then
      for _,r in ipairs(st[3]) do
        if unp(r)[1]=="Un" and unp(r)[2]=="#" then sl=true end
      end
      if sl then
        for _,r in ipairs(st[3]) do
          local u=unp(r)
          if u[1]=="Num" and u[2]%1==0 and u[2]>=3 and u[2]<256 and u[2]~=255 then return u[2] end
        end
      end
    end
  end
  for _,st in ipairs(sts) do
    if st[1]=="Assign" then
      for _,r in ipairs(st[3]) do
        local u=unp(r)
        if u[1]=="Num" and u[2]%1==0 and u[2]>=0 and u[2]<256 and u[2]~=0 and u[2]~=1 and u[2]~=2 and u[2]~=255 then return u[2] end
      end
    end
  end
  return nil
end
function M.inv_enc(ast)
  return F.fold(inv_enc_blk(ast,{},{},{},{}))
end
M.ext_lcg=ext_lcg
M.ext_lcg_blk=ext_lcg_blk
M.ext_k8=ext_k8
M.ext_k8_blk=ext_k8_blk
M.ext_tf=ext_tf
return M
