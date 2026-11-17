local A=require("src.frontend.ast")
local CFF=require("src.passes.cff")
local unp=A.unp
local M={}
local function is_int(v)
  return type(v)=="number" and v==v and v~=math.huge and v~=-math.huge and math.floor(v)==v
end
local function lit(n)
  n=unp(n)
  local k=n[1]
  if k=="Num" or k=="Str" or k=="Bool" then return true,n[2] end
  if k=="Nil" then return true,nil end
  if k=="Un" and n[2]=="-" then
    local ok,v=lit(n[3])
    if ok and type(v)=="number" then return true,-v end
  elseif k=="Bin" then
    local o1,l=lit(n[3])
    local o2,r=lit(n[4])
    if o1 and o2 and type(l)=="number" and type(r)=="number" then
      local op=n[2]
      if op=="+" then return true,l+r
      elseif op=="-" then return true,l-r
      elseif op=="*" then return true,l*r
      elseif op=="/" then return true,l/r
      elseif op=="%" then return true,l%r
      elseif op=="^" then return true,l^r
      end
    end
  end
  return false,nil
end
local function is_sh_tbl(t)
  t=unp(t)
  if t[1]~="Tbl" or #t[2]==0 then return false end
  for _,sh in ipairs(t[2]) do
    if sh[1]~="V" then return false end
    local st=unp(sh[2])
    if st[1]~="Tbl" then return false end
    for _,rc in ipairs(st[2]) do
      if rc[1]~="V" then return false end
      local rt=unp(rc[2])
      if rt[1]~="Tbl" or #rt[2]<3 or #rt[2]>4 then return false end
      for _,x in ipairs(rt[2]) do if x[1]~="V" then return false end end
      local ok1,k1=lit(rt[2][1][2])
      local ok2,k2=lit(rt[2][2][2])
      local ok3=lit(rt[2][3][2])
      local ok4=true
      if #rt[2]==4 then ok4=lit(rt[2][4][2]) end
      if not (ok1 and ok2 and ok3 and ok4 and is_int(k1) and is_int(k2)) then return false end
    end
  end
  return true
end
local function find_rb_calls(ast)
  local out={}
  A.walk(ast,function(n)
    if n[1]=="Call" and #n[3]==3 then
      local a1,a2=unp(n[3][2]),unp(n[3][3])
      if a1[1]=="Num" and a2[1]=="Num" and is_int(a1[2]) and is_int(a2[2]) then
        if a1[2]>=1 and a2[2]>=1 and a2[2]<=a1[2] and is_sh_tbl(n[3][1]) then
          out[#out+1]={n,unp(n[3][1]),a1[2],a2[2]}
        end
      end
    end
  end)
  return out
end
function M.dec_shards(st_tbl,cnt,rt)
  local ts={}
  for i=1,cnt do ts[i]={} end
  for _,sh in ipairs(st_tbl[2]) do
    local st=unp(sh[2])
    for _,rc in ipairs(st[2]) do
      local fs=unp(rc[2])[2]
      local _,tid=lit(fs[1][2])
      local _,key=lit(fs[2][2])
      local _,val=lit(fs[3][2])
      if #fs==4 then
        local ok4,v4=lit(fs[4][2])
        if ok4 and v4 then val=ts[val] end
      end
      ts[tid][key]=val
    end
  end
  return ts[rt]
end
local function var_nm(n)
  n=unp(n)
  return n[1]=="Var" and n[2] or nil
end
local FLIP={["=="]="==",["<="]=">=",[">="]="<=",["<"]=">",[">"]="<"}
local function is_op_cmp(c,ov)
  c=unp(c)
  if c[1]~="Bin" or not FLIP[c[2]] then return nil end
  local l,r=unp(c[3]),unp(c[4])
  if var_nm(l)==ov and r[1]=="Num" and is_int(r[2]) then return {c[2],r[2]} end
  if var_nm(r)==ov and l[1]=="Num" and is_int(l[2]) then return {FLIP[c[2]],l[2]} end
  return nil
end
local function collect_leaves(st,ov)
  local out={}
  local function g(s)
    if s[1]~="If" then return end
    for _,br in ipairs(s[2]) do
      local mc=is_op_cmp(br[1],ov)
      if not mc then return end
      if mc[1]=="==" then
        out[mc[2]]=br[2][2]
      else
        for _,cs in ipairs(br[2][2]) do g(cs) end
      end
    end
    if s[3] then
      for _,cs in ipairs(s[3][2]) do g(cs) end
    end
  end
  g(st)
  return out
end
local function eval_role(e,env)
  e=unp(e)
  local k=e[1]
  if k=="Var" then return env[e[2]] end
  if k=="Num" and e[2]==1 then return {"Num1"} end
  if k=="Field" then
    local b=eval_role(e[2],env)
    if b and b[1]=="P" then return {"PF",e[3]} end
  end
  if k=="Idx" then
    local b=eval_role(e[2],env)
    local ix=unp(e[3])
    if b and b[1]=="P" and ix[1]=="Num" and is_int(ix[2]) then return {"PF",ix[2]} end
    if b and b[1]=="PF" then
      local ir=eval_role(ix,env)
      if ir and ir[1]=="PC" then return {"I_fetch",b[2]} end
    end
    if b and b[1]=="I" and ix[1]=="Num" and is_int(ix[2]) then
      if ix[2]==1 then return {"OP"} end
      if ix[2]>=2 and ix[2]<=5 then return {"S",ix[2]} end
    end
  end
  return nil
end
local function find_loop_info(ast)
  local res={}
  A.walk(ast,function(fn)
    local ps,body
    if fn[1]=="Func" then ps,body=fn[2],fn[4]
    elseif fn[1]=="LocalFunc" then ps,body=fn[3],fn[5]
    elseif fn[1]=="FuncStmt" then ps,body=fn[4],fn[6]
    else return end
    if #ps~=5 then return end
    local pP,pU,pEnv,pR,pV=ps[1],ps[2],ps[3],ps[4],ps[5]
    local env={[pP]={"P"},[pU]={"U"},[pEnv]={"Env"},[pR]={"R"},[pV]={"V"}}
    local sts=body[2]
    local wi
    for i,s in ipairs(sts) do
      if s[1]=="While" and unp(s[2])[1]=="Bool" and unp(s[2])[2]==true then wi=i break end
    end
    if not wi then return end
    local function is_pc_inc(r,nm)
      r=unp(r)
      return r[1]=="Bin" and r[2]=="+" and var_nm(r[3])==nm
        and env[nm] and env[nm][1]=="PC" and unp(r[4])[1]=="Num" and unp(r[4])[2]==1
    end
    local function step(s)
      if s[1]=="LocalVar" and #s[3]>0 then
        local vs={}
        for i,r in ipairs(s[3]) do vs[i]=eval_role(r,env) end
        for i,nm in ipairs(s[2]) do
          if vs[i] then env[nm]=vs[i] else env[nm]=nil end
        end
      elseif s[1]=="Assign" then
        local all_v=true
        for _,l in ipairs(s[2]) do if unp(l)[1]~="Var" then all_v=false break end end
        if all_v then
          local vs={}
          for i,r in ipairs(s[3]) do vs[i]=eval_role(r,env) end
          for i,l in ipairs(s[2]) do
            local nm=unp(l)[2]
            if vs[i] then env[nm]=vs[i]
            elseif s[3][i] and is_pc_inc(s[3][i],nm) then env[nm]={"PC"}
            else env[nm]=nil end
          end
        end
      end
    end
    for i=1,wi-1 do step(sts[i]) end
    local wsts=sts[wi][3][2]
    local di
    for i,s in ipairs(wsts) do if s[1]=="If" then di=i break end end
    if not di then return end
    for i=1,di-1 do
      local s=wsts[i]
      if s[1]=="LocalVar" or s[1]=="Assign" then
        if #s[2]==1 and #s[3]==1 then
          local rh=unp(s[3][1])
          if rh[1]=="Idx" then
            local er=eval_role(rh[2],env)
            if er and er[1]=="PF" then
              local pv=var_nm(rh[3])
              if pv then env[pv]={"PC"} end
            end
          end
        end
        local vs={}
        for j,r in ipairs(s[3]) do vs[j]=eval_role(r,env) end
        if s[1]=="LocalVar" then
          for j,nm in ipairs(s[2]) do
            local v=vs[j]
            if v and v[1]=="I_fetch" then
              env.__k_code=v[2] env[nm]={"I"}
            elseif v then env[nm]=v
            else env[nm]=nil end
          end
        else
          for j,l in ipairs(s[2]) do
            if unp(l)[1]=="Var" then
              local nm=unp(l)[2]
              local v=vs[j]
              if v and v[1]=="I_fetch" then
                env.__k_code=v[2] env[nm]={"I"}
              elseif v then env[nm]=v
              elseif s[3][j] and is_pc_inc(s[3][j],nm) then env[nm]={"PC"}
              else env[nm]=nil end
            end
          end
        end
      end
    end
    local op_v
    for k,v in pairs(env) do
      if type(k)=="string" and k~="__k_code" and v[1]=="OP" then op_v=k break end
    end
    if not op_v then return end
    local leaves=collect_leaves(wsts[di],op_v)
    local cnt=0
    for _ in pairs(leaves) do cnt=cnt+1 end
    if cnt>=45 then res[#res+1]={fn,env,leaves} end
  end)
  return res
end
local BOPS={
  ["+"]="ADD",["-"]="SUB",["*"]="MUL",["/"]="DIV",["%"]="MOD",["^"]="POW",[".."]="CONCAT",
  ["<"]="LT",["<="]="LE",[">"]="GT",[">="]="GE",["=="]="EQ",["~="]="NE"
}
local UOPS={["not"]="NOT",["-"]="NEG",["#"]="LEN"}
local function is_leaf_lit(n)
  n=unp(n)
  local k=n[1]
  if k=="Num" or k=="Str" or k=="Bool" or k=="Nil" then return true end
  return k=="Un" and n[2]=="-" and unp(n[3])[1]=="Num"
end
local function sub_leaf_c(n,ce)
  if type(n)~="table" then return n end
  local k=n[1]
  if type(k)~="string" then
    local r={} for i=1,#n do r[i]=sub_leaf_c(n[i],ce) end return r
  end
  if k=="Var" then return ce[n[2]] or n end
  if k=="Assign" then
    local nl={}
    for i,l in ipairs(n[2]) do
      local ul=unp(l)
      nl[i]=ul[1]=="Var" and ul or sub_leaf_c(l,ce)
    end
    local nr=sub_leaf_c(n[3],ce)
    for _,l in ipairs(n[2]) do
      local ul=unp(l)
      if ul[1]=="Var" then ce[ul[2]]=nil end
    end
    return {"Assign",nl,nr}
  end
  if k=="ForNum" then
    local s2,e2=sub_leaf_c(n[3],ce),sub_leaf_c(n[4],ce)
    local sp2=n[5] and sub_leaf_c(n[5],ce) or false
    local ce2={} for kv,v in pairs(ce) do if kv~=n[2] then ce2[kv]=v end end
    return {"ForNum",n[2],s2,e2,sp2,sub_leaf_c(n[6],ce2)}
  end
  if k=="Block" then
    local ce2={} for kv,v in pairs(ce) do ce2[kv]=v end
    local out={} for i,st in ipairs(n[2]) do out[i]=sub_leaf_c(st,ce2) end
    return {"Block",out}
  end
  if k=="Func" then
    local ps={} for _,p in ipairs(n[2]) do ps[p]=true end
    local ce2={} for kv,v in pairs(ce) do if not ps[kv] then ce2[kv]=v end end
    return {"Func",n[2],n[3],sub_leaf_c(n[4],ce2)}
  end
  if k=="LocalFunc" then
    local ps={[n[2]]=true} for _,p in ipairs(n[3]) do ps[p]=true end
    local ce2={} for kv,v in pairs(ce) do if not ps[kv] then ce2[kv]=v end end
    return {"LocalFunc",n[2],n[3],n[4],sub_leaf_c(n[5],ce2)}
  end
  if k=="FuncStmt" then
    local ps={} for _,p in ipairs(n[4]) do ps[p]=true end
    local ce2={} for kv,v in pairs(ce) do if not ps[kv] then ce2[kv]=v end end
    return {"FuncStmt",sub_leaf_c(n[2],ce),n[3],n[4],n[5],sub_leaf_c(n[6],ce2)}
  end
  local r={k} for i=2,#n do r[i]=sub_leaf_c(n[i],ce) end return r
end
local function norm_leaf(sts,env)
  local ce,out={},{}
  for _,st in ipairs(sts) do
    local done=false
    if st[1]=="Assign" and #st[2]==1 and #st[3]==1 then
      local lh=unp(st[2][1])
      if lh[1]=="Var" and (not env[lh[2]] or env[lh[2]][1]=="S") then
        local rh=sub_leaf_c(st[3][1],ce)
        if is_leaf_lit(rh) then ce[lh[2]]=unp(rh) done=true end
      end
    end
    if not done then
      out[#out+1]=sub_leaf_c(st,ce)
      if st[1]~="Assign" and st[1]~="LocalVar" then ce={} end
    end
  end
  return out
end
local function classify_leaf(sts,env,nrm)
  local function rl(e)
    e=unp(e)
    return e[1]=="Var" and env[e[2]] or nil
  end
  local function slot(e)
    local r=rl(e)
    return (r and r[1]=="S") and r[2] or nil
  end
  local function is_r_idx(e)
    e=unp(e)
    local b=e[1]=="Idx" and rl(e[2]) or nil
    if b and b[1]=="R" then return slot(e[3]) end
    return nil
  end
  local function is_r_1(e)
    e=unp(e)
    if e[1]=="Idx" then
      local ix=unp(e[3])
      if ix[1]=="Num" and ix[2]==1 then return is_r_idx(e[2]) end
    end
    return nil
  end
  local function is_u_1(e)
    e=unp(e)
    if e[1]=="Idx" then
      local ix=unp(e[3])
      if ix[1]=="Num" and ix[2]==1 then
        local u=unp(e[2])
        local ub=u[1]=="Idx" and rl(u[2]) or nil
        if ub and ub[1]=="U" then return slot(u[3]) end
      end
    end
    return nil
  end
  local function is_k_idx(e)
    e=unp(e)
    if e[1]=="Idx" then
      local r=rl(e[2])
      local s=slot(e[3])
      if r and r[1]=="PF" and s then return {r[2],s} end
    end
    return nil
  end
  local function is_env_k(e)
    e=unp(e)
    local b=e[1]=="Idx" and rl(e[2]) or nil
    if b and b[1]=="Env" then return is_k_idx(e[3]) end
    return nil
  end
  local function is_take(e)
    e=unp(e)
    if e[1]=="Idx" then
      local b=is_r_idx(e[2])
      local c=slot(e[3])
      if b and c then return {b,c} end
    end
    return nil
  end
  local function is_r_r(e)
    e=unp(e)
    if e[1]=="Idx" then
      local b=is_r_idx(e[2])
      local c=is_r_idx(e[3])
      if b and c then return {b,c} end
    end
    return nil
  end
  local function idx_fk(e)
    e=unp(e)
    if e[1]=="Idx" then return e[2],e[3] end
    if e[1]=="Field" then return e[2],{"Str",e[3]} end
    return nil,nil
  end
  local function is_ck(k)
    return (is_int(k) and k<0) or k=="n"
  end
  local function has_unpack(c)
    local hit
    A.walk(c,function(x)
      if x[1]=="Call" and #x[3]==3 then
        local a2=unp(x[3][2])
        if a2[1]=="Num" and a2[2]==1 then
          local _,kx=idx_fk(x[3][3])
          if kx then
            local ok,kv=lit(kx)
            if ok and is_ck(kv) then hit=kv end
          end
        end
      end
    end)
    return hit
  end
  local function unpack_var(c)
    local hit
    A.walk(c,function(x)
      if x[1]=="Call" and #x[3]==3 then
        local a2=unp(x[3][2])
        if a2[1]=="Num" and a2[2]==1 then
          local b,kx=idx_fk(x[3][3])
          if b and kx then
            local ok,kv=lit(kx)
            if ok and is_ck(kv) then hit=var_nm(b) end
          end
        end
      end
    end)
    return hit
  end
  local function reg_binds()
    local mp={}
    for i=1,#sts-1 do
      local s=sts[i]
      if (s[1]=="Assign" or s[1]=="LocalVar") and #s[2]==#s[3] then
        for j=1,#s[2] do
          local l=s[2][j]
          local nm=type(l)=="string" and l or var_nm(l)
          local ri=is_r_idx(s[3][j])
          if nm and ri then mp[nm]=ri end
        end
      end
    end
    return mp
  end
  local function call_arity(c)
    for _,a in ipairs(c[3]) do
      local ua=unp(a)
      local b=ua[1]=="Idx" and rl(ua[2]) or nil
      if b and b[1]=="R" then
        local ix=unp(ua[3])
        if ix[1]=="Idx" then
          local sc=slot(ix[2])
          if sc then return sc,#c[3] end
        end
      end
    end
    if #c[3]==0 then return nil,0 end
    return nil,nil
  end
  local function asg1(s)
    if s[1]=="Assign" and #s[2]==1 and #s[3]==1 then return var_nm(s[2][1]),s[3][1] end
    if s[1]=="LocalVar" and #s[2]==1 and #s[3]==1 then return s[2][1],s[3][1] end
    return nil
  end
  local function clears_a(st,bfn)
    if st[1]~="ForNum" or #st[6][2]~=1 or st[6][2][1][1]~="Assign" then return nil end
    local lh=unp(st[6][2][1][2][1])
    local b=lh[1]=="Idx" and rl(lh[2]) or nil
    if b and b[1]=="R" then return bfn(unp(st[4])) end
    return nil
  end
  local function tv_eq(t,k,v)
    return t[1]==k and t[2]==v
  end
  local function fn_try(ns)
    return classify_leaf(ns,env,true)
  end
  if #sts==1 then
    local st=sts[1]
    local k=st[1]
    if k=="Return" then
      local es=st[2]
      if #es==0 then return "RETURN0",{} end
      local rs={}
      local ok=true
      for i,e in ipairs(es) do
        rs[i]=is_r_idx(e)
        if not rs[i] then ok=false break end
      end
      if ok and (#rs>=1 and #rs<=3) then
        local lbl={"a","b","c"}
        local info={}
        for i,r in ipairs(rs) do info[lbl[i]]=r end
        return "RETURN"..#rs,info
      end
    end
    if k=="Assign" and #st[2]==1 and #st[3]==1 then
      local lh,rh=unp(st[2][1]),unp(st[3][1])
      local lhr=rl(lh)
      if lhr and lhr[1]=="PC" and slot(rh) then return "JMP",{a=slot(rh)} end
      local ra=is_r_idx(lh)
      if ra then
        if rh[1]=="Nil" then return "NIL_OR_CLEAR",{a=ra} end
        if rh[1]=="Tbl" and #rh[2]==0 then return "TABLE",{a=ra} end
        if rh[1]=="Tbl" and #rh[2]==1 and rh[2][1][1]=="V" then
          local rb=is_r_idx(rh[2][1][2])
          if rb then return "CELL",{a=ra,b=rb} end
        end
        local rhr=rl(rh)
        if rhr and rhr[1]=="V" then return "VARARG",{a=ra} end
        local rb=is_r_idx(rh)
        if rb then return "MOVE",{a=ra,b=rb} end
        local kr=is_k_idx(rh)
        if kr then return "LOAD",{a=ra,b=kr[2],k_const=kr[1]} end
        local rb1=is_r_1(rh)
        if rb1 then return "GETCELL",{a=ra,b=rb1} end
        local ub1=is_u_1(rh)
        if ub1 then return "GETUP",{a=ra,b=ub1} end
        local ek=is_env_k(rh)
        if ek then return "GLOBAL",{a=ra,b=ek[2],k_const=ek[1]} end
        local tk=is_take(rh)
        if tk then return "TAKE",{a=ra,b=tk[1],c=tk[2]} end
        local rr=is_r_r(rh)
        if rr then return "GETTABLE",{a=ra,b=rr[1],c=rr[2]} end
        if rh[1]=="Bin" and BOPS[rh[2]] then
          local rb2,rc2=is_r_idx(rh[3]),is_r_idx(rh[4])
          if rb2 and rc2 then return BOPS[rh[2]],{a=ra,b=rb2,c=rc2} end
        end
        if rh[1]=="Un" and UOPS[rh[2]] then
          local rb2=is_r_idx(rh[3])
          if rb2 then return UOPS[rh[2]],{a=ra,b=rb2} end
        end
      end
      local ra1=is_r_1(lh)
      if ra1 then
        local rb=is_r_idx(rh)
        if rb then return "SETCELL",{a=ra1,b=rb} end
      end
      local ua1=is_u_1(lh)
      if ua1 then
        local rb=is_r_idx(rh)
        if rb then return "SETUP",{a=ua1,b=rb} end
      end
      local ek=is_env_k(lh)
      if ek then
        local rb=is_r_idx(rh)
        if rb then return "SETGLOBAL",{a=ek[2],b=rb,k_const=ek[1]} end
      end
      local rr=is_r_r(lh)
      if rr then
        local rc=is_r_idx(rh)
        if rc then return "SETTABLE",{a=rr[1],b=rr[2],c=rc} end
      end
    end
    if k=="ForNum" then
      local sa=clears_a(st,function(bf) return (bf[1]=="Un" and bf[2]=="#") and slot(bf[3]) or nil end)
      if sa then return "CLEARS",{a=sa} end
    end
    if k=="If" then
      local cs,eb=st[2],st[3]
      local c=unp(cs[1][1])
      local tb=cs[1][2]
      if c[1]=="Bin" and c[2]=="~=" and #cs==2 and eb then
        local sd1,sd2=is_r_idx(c[3]),is_r_idx(c[4])
        if sd1 and sd1==sd2 and #tb[2]==1 and tb[2][1][1]=="Assign" then
          local sa=is_r_idx(tb[2][1][2][1])
          local tv=unp(tb[2][1][3][1])
          if tv_eq(tv,"Bool",false) and sa then
            local e0=cs[2][2][2][1]
            if e0 and e0[1]=="Assign" then
              local cmp_le=unp(e0[3][1])
              if cmp_le[1]=="Bin" and cmp_le[2]=="<=" then
                local sb,sc=is_r_idx(cmp_le[3]),is_r_idx(cmp_le[4])
                if sb and sc then return "FORCHECK",{a=sa,b=sb,c=sc,d=sd1} end
              end
            end
          end
        end
      end
    end
  end
  if #sts==2 then
    local s0,s1=sts[1],sts[2]
    local a0,v0=asg1(s0)
    if a0 and s1[1]=="ForNum" then
      local rh0=unp(v0)
      if rh0[1]=="Un" and rh0[2]=="#" then
        local sa=clears_a(s1,function(bf) return (bf[1]=="Var" and bf[2]==a0) and slot(rh0[3]) or nil end)
        if sa then return "CLEARS",{a=sa} end
      end
    end
    if a0 and s1[1]=="Assign" and #s1[2]==1 and #s1[3]==1 then
      local rb=is_r_idx(v0)
      local ra=is_r_idx(s1[2][1])
      local rh1=unp(s1[3][1])
      if rb and ra and rh1[1]=="Tbl" and #rh1[2]==1 and rh1[2][1][1]=="V" and var_nm(rh1[2][1][2])==a0 then
        return "CELL",{a=ra,b=rb}
      end
    end
    if a0 and s1[1]=="Return" and #s1[2]==1 then
      local ra=is_r_idx(v0)
      local rc=unp(s1[2][1])
      if ra and rc[1]=="Call" then
        local ck=has_unpack(rc)
        if ck then return "RETURN",{a=ra,ck=ck} end
      end
    end
  end
  if #sts==3 and sts[2][1]=="Assign" and sts[3][1]=="If" then
    local s0,s1,s2=sts[1],sts[2],sts[3]
    local vx,v0=asg1(s0)
    local sa=vx and is_r_idx(v0) or nil
    if vx and sa and #s1[2]==1 and #s1[3]==1 and is_r_idx(s1[2][1])==sa and unp(s1[3][1])[1]=="Nil" then
      local tb=s2[2][1][2][2]
      if #s2[2]==1 and not s2[3] and #tb==1 and tb[1][1]=="Assign" then
        local pcr=rl(tb[1][2][1])
        local sb=slot(tb[1][3][1])
        if pcr and pcr[1]=="PC" and sb then
          local cd=unp(s2[2][1][1])
          if cd[1]=="Un" and cd[2]=="not" and unp(cd[3])[1]=="Var" and unp(cd[3])[2]==vx then
            return "JFALSE",{a=sa,b=sb}
          end
          if cd[1]=="Var" and cd[2]==vx then return "JTRUE",{a=sa,b=sb} end
        end
      end
    end
  end
  if #sts==9 then
    local rs,ok={},true
    for i=0,2 do
      local s0,s1,s2=sts[3*i+1],sts[3*i+2],sts[3*i+3]
      local a0,v0=asg1(s0)
      if not a0 or s1[1]~="If" or s2[1]~="Assign" then ok=false break end
      local cd=unp(s1[2][1][1])
      if cd[1]~="Bin" or cd[2]~="==" or unp(cd[4])[1]~="Nil" then ok=false break end
      local ra=#s2[2]==1 and is_r_idx(s2[2][1]) or nil
      local ua0=unp(v0)
      local rb=(ua0[1]=="Call" and #ua0[3]==1) and is_r_idx(ua0[3][1]) or nil
      if not ra or ra~=rb or var_nm(s2[3][1])~=var_nm(cd[3]) then ok=false break end
      rs[#rs+1]=ra
    end
    if ok and #rs==3 then return "FORPREP",{a=rs[1],b=rs[2],c=rs[3]} end
  end
  local a0,v0=asg1(sts[1])
  if a0 then
    local r0=unp(v0)
    if r0[1]=="Tbl" and #r0[2]==1 and (r0[2][1][1]=="I" or r0[2][1][1]=="F") then
      local f0=r0[2][1]
      local okk,k0,okv,vv0
      if f0[1]=="F" then okk,k0=true,f0[2] okv,vv0=lit(f0[3])
      else okk,k0=lit(f0[2]) okv,vv0=lit(f0[3]) end
      if okk and okv and is_ck(k0) and vv0==0 and sts[#sts][1]=="Assign" then
        local sa=is_r_idx(sts[#sts][2][1])
        local ip_s,sc_s
        A.walk({"Block",sts},function(x)
          if x[1]=="Call" and #x[3]==1 and slot(x[3][1]) then ip_s=slot(x[3][1]) end
        end)
        for _,s in ipairs(sts) do
          if s[1]=="If" then
            local cd=unp(s[2][1][1])
            if cd[1]=="Bin" and cd[2]=="~=" and slot(cd[3]) and tv_eq(unp(cd[4]),"Num",0) then
              sc_s=slot(cd[3])
            end
          end
        end
        if sa and ip_s and sc_s then return "ARGS",{a=sa,b=ip_s,c=sc_s,ck=k0} end
      end
    end
    local r0b,r0k=idx_fk(r0)
    if r0b and r0k then
      local b0b,b0k=idx_fk(r0b)
      if b0b and b0k then
        local pb=rl(b0b)
        local okc,k_ch=lit(b0k)
        if pb and pb[1]=="P" and okc and k_ch then
          local sb=slot(r0k)
          local k_cap
          A.walk({"Block",sts},function(x)
            if x[1]=="Un" and x[2]=="#" then
              local _,kx=idx_fk(x[3])
              if kx then
                local okp,kp=lit(kx)
                if okp and kp then k_cap=kp end
              end
            end
          end)
          local sa=sts[#sts][1]=="Assign" and is_r_idx(sts[#sts][2][1]) or nil
          if sa and sb and k_cap then return "CLOSURE",{a=sa,b=sb,k_ch=k_ch,k_cap=k_cap} end
        end
      end
    end
    local has_fn=false
    for _,s in ipairs(sts) do if s[1]=="ForNum" then has_fn=true break end end
    if has_fn then
      local rc=is_r_idx(v0)
      local ck
      if rc then
        for i=2,#sts do
          local s=sts[i]
          local an,av=asg1(s)
          if an then
            local ib,kx=idx_fk(av)
            if ib and kx and var_nm(ib)==a0 then
              local okk,kv=lit(kx)
              if okk and is_ck(kv) then ck=kv end
            end
          elseif s[1]=="ForNum" then
            if not ck then
              local ib,kx=idx_fk(s[4])
              if ib and kx and var_nm(ib)==a0 then
                local okk,kv=lit(kx)
                if okk and is_ck(kv) then ck=kv end
              end
            end
            if ck then
              local info={c=rc,ck=ck}
              A.walk(s[6],function(x)
                if x[1]=="Assign" and #x[2]==1 then
                  local lh=unp(x[2][1])
                  if lh[1]=="Idx" and is_r_idx(lh[2]) then
                    info.a=is_r_idx(lh[2])
                    local ix=unp(lh[3])
                    if ix[1]=="Bin" and ix[2]=="-" and unp(ix[3])[1]=="Bin" then
                      local sbv=slot(unp(ix[3])[3])
                      if sbv then info.b=sbv end
                    end
                  end
                end
              end)
              if info.a and info.b then return "EXPAND",info end
            end
          end
        end
      end
    end
  end
  if sts[#sts][1]=="If" and #sts[#sts][2]>=2 then
    local ist=sts[#sts]
    local eb=ist[3]
    local cal
    if eb and #eb[2]>=1 then
      local e1=eb[2][1]
      if e1[1]=="CallStmt" then cal=unp(e1[2])
      elseif e1[1]=="Assign" and #e1[2]==1 and #e1[3]==1 and unp(e1[3][1])[1]=="Call" then cal=unp(e1[3][1]) end
    end
    local mp=reg_binds()
    local fn_nm=(cal and cal[1]=="Call") and var_nm(cal[2]) or nil
    local sb=(fn_nm and mp[fn_nm]) or (a0 and is_r_idx(v0) or nil)
    if not sb then
      if not nrm then
        local ns=norm_leaf(sts,env)
        if not A.eq(ns,sts) then return fn_try(ns) end
      end
      return nil,{}
    end
    local sd,sa
    for i=2,#ist[2] do
      local ec,eb2=unp(ist[2][i][1]),ist[2][i][2]
      if ec[1]=="Bin" and ec[2]=="==" and slot(ec[3]) then
        sd=slot(ec[3])
        if #eb2[2]>=1 and eb2[2][1][1]=="Assign" then
          sa=is_r_idx(eb2[2][1][2][1])
        end
      end
    end
    if sd and sa and cal then
      local ck=has_unpack(cal)
      if ck then
        local uv=unpack_var(cal)
        local sc=uv and mp[uv] or nil
        if not sc then
          for i=1,#sts-1 do
            local s=sts[i]
            if s[1]=="Assign" and #s[2]==2 and #s[3]==2 then
              sc=is_r_idx(s[3][2])
            elseif i>1 then
              local an,av=asg1(s)
              local r2=an and is_r_idx(av) or nil
              if r2 then sc=r2 end
            end
          end
        end
        if sc then return "CALL",{a=sa,b=sb,c=sc,d=sd,ck=ck} end
      end
      local sc,ar=call_arity(cal)
      if ar then
        local info={a=sa,b=sb,d=sd}
        if sc then info.c=sc end
        return "CALL"..ar,info
      end
    end
  end
  local tc_tb,tc_eb
  local sl=sts[#sts]
  if sl[1]=="If" and #sl[2]==1 and sl[3] then
    tc_tb,tc_eb=sl[2][1][2][2],sl[3][2]
  elseif #sts>=2 and sts[#sts-1][1]=="If" and #sts[#sts-1][2]==1 and not sts[#sts-1][3] and sl[1]=="Return" then
    tc_tb,tc_eb=sts[#sts-1][2][1][2][2],{sl}
  end
  if tc_tb and #tc_tb==1 and tc_tb[1][1]=="Return" and #tc_tb[1][2]>=1 then
    local er=rl(tc_tb[1][2][1])
    if er and er[1]=="Env" and #tc_eb==1 and tc_eb[1][1]=="Return" and #tc_eb[1][2]==1 then
      local cal=unp(tc_eb[1][2][1])
      if cal[1]=="Call" then
        local mp=reg_binds()
        local fn_nm=var_nm(cal[2])
        local sa=(fn_nm and mp[fn_nm]) or (a0 and is_r_idx(v0) or nil)
        if not sa then
          if not nrm then
            local ns=norm_leaf(sts,env)
            if not A.eq(ns,sts) then return fn_try(ns) end
          end
          return nil,{}
        end
        local ck=has_unpack(cal)
        if ck then
          local uv=unpack_var(cal)
          local sb=uv and mp[uv] or nil
          if not sb then
            for i=1,#sts-1 do
              local s=sts[i]
              if s[1]=="Assign" and #s[2]==2 and #s[3]==2 then
                sb=is_r_idx(s[3][2])
              elseif i>1 then
                local an,av=asg1(s)
                local r2=an and is_r_idx(av) or nil
                if r2 then sb=r2 end
              end
            end
          end
          if sb then return "TAILCALL",{a=sa,b=sb,ck=ck} end
        end
        local sb,ar=call_arity(cal)
        if ar then
          local info={a=sa}
          if sb then info.b=sb end
          return "TAILCALL"..ar,info
        end
      end
    end
  end
  if not nrm then
    local ns=norm_leaf(sts,env)
    if not A.eq(ns,sts) then return fn_try(ns) end
  end
  return nil,{}
end
local function dict_arr(d)
  if not d then return {},0 end
  local mx=0
  for k in pairs(d) do if is_int(k) and k>mx then mx=k end end
  local out={}
  for i=1,mx do out[i]=d[i] end
  return out,mx
end
function M.dec_proto(rp,fs,ops,opx)
  local code={}
  local cds,cdn=dict_arr(rp[fs.code])
  for i=1,cdn do
    local ins=cds[i]
    local op=ops[ins[1]]
    local a,b,c,d=ins[opx[1]],ins[opx[2]],ins[opx[3]],ins[opx[4]]
    if type(a)=="table" then a=dict_arr(a) end
    if type(b)=="table" then b=dict_arr(b) end
    if type(c)=="table" then c=dict_arr(c) end
    code[i]={op,a,b,c,d}
  end
  local consts,cn=dict_arr(rp[fs.constants])
  local caps={}
  local cp_raw,cpn=dict_arr(rp[fs.captures])
  for i=1,cpn do local t=dict_arr(cp_raw[i]) caps[i]={t[1],t[2]} end
  local prms={}
  local pr_raw,prn=dict_arr(rp[fs.params])
  for i=1,prn do local t=dict_arr(pr_raw[i]) prms[i]={t[1],not not t[2]} end
  local chs={}
  local ch_raw,chn=dict_arr(rp[fs.children])
  for i=1,chn do chs[i]=M.dec_proto(ch_raw[i],fs,ops,opx) end
  return {
    code=code,constants=consts,consts_n=cn,
    captures=caps,params=prms,vararg=not not rp[fs.vararg],
    maxRegister=rp[fs.maxRegister],children=chs
  }
end
local function lit_tbl(t)
  t=unp(t)
  local o,v=lit(t)
  if o then return true,v end
  if t[1]~="Tbl" then return false,nil end
  local res,ai={},1
  for _,f in ipairs(t[2]) do
    if f[1]=="V" then
      local ok,fv=lit_tbl(f[2])
      if not ok then return false,nil end
      res[ai]=fv ai=ai+1
    elseif f[1]=="F" then
      local ok,fv=lit_tbl(f[3])
      if not ok then return false,nil end
      res[f[2]]=fv
    else
      local ok1,fk=lit(f[2])
      local ok2,fv=lit_tbl(f[3])
      if not ok1 or not ok2 or fk==nil then return false,nil end
      res[fk]=fv
    end
  end
  return true,res
end
local function find_dir_vm(ast)
  local out
  A.walk(ast,function(n)
    if out then return end
    if n[1]=="Call" and #n[3]>=1 then
      for _,arg in ipairs(n[3]) do
        local u=unp(arg)
        if u[1]=="Tbl" and #u[2]>=1 and u[2][1][1]=="V" then
          local p0=unp(u[2][1][2])
          if p0[1]=="Tbl" and #p0[2]>=5 then
            local ok,tv=lit_tbl(u)
            if ok and type(tv)=="table" and type(tv[1])=="table" then
              out={n,tv}
              return
            end
          end
        end
      end
    end
  end)
  return out
end
function M.ext_vm(ast)
  local loops=find_loop_info(ast)
  if #loops==0 then return nil end
  local loop_fn,env,leaves=loops[1][1],loops[1][2],loops[1][3]
  local rbs=find_rb_calls(ast)
  local rb_call,root_tbl
  if #rbs>0 then
    local rb=rbs[#rbs]
    rb_call=rb[1]
    root_tbl=M.dec_shards(rb[2],rb[3],rb[4])
  else
    local dv=find_dir_vm(ast)
    if not dv then return nil end
    rb_call,root_tbl=dv[1],dv[2]
  end
  local root_p=root_tbl[1]
  local ops,clear_nil,slots={}, {}, {a={},b={},c={},d={}}
  local meta={code=env.__k_code}
  for op_id,bsts in pairs(leaves) do
    local nm,info=classify_leaf(bsts,env)
    if not nm then error("unclassified vm op:"..tostring(op_id)) end
    if nm=="NIL_OR_CLEAR" then
      clear_nil[#clear_nil+1]=op_id
      if info.a then slots.a[info.a]=true end
    else
      ops[op_id]=nm
      for _,ak in ipairs({"a","b","c","d"}) do
        if info[ak] then slots[ak][info[ak]]=true end
      end
      if info.k_const then meta.constants=info.k_const end
      if info.k_ch then meta.children=info.k_ch end
      if info.k_cap then meta.captures=info.k_cap end
      if info.ck then meta.countKey=info.ck end
    end
  end
  if #clear_nil~=2 then error("clear_nil count:"..#clear_nil) end
  ops[clear_nil[1]]="CLEAR"
  ops[clear_nil[2]]="NIL"
  local opx={}
  for i,ak in ipairs({"a","b","c","d"}) do
    local v,c=nil,0
    for k in pairs(slots[ak]) do v=k c=c+1 end
    if c~=1 then error("slot "..ak.." cnt="..c) end
    opx[i]=v
  end
  local used={[meta.code]=true,[meta.constants]=true,[meta.children]=true,[meta.captures]=true}
  local rem={}
  for k in pairs(root_p) do if not used[k] then rem[#rem+1]=k end end
  if #rem~=3 then error("rem keys:"..#rem) end
  for _,k in ipairs(rem) do
    local v=root_p[k]
    if type(v)=="boolean" then meta.vararg=k
    elseif is_int(v) then meta.maxRegister=k
    elseif type(v)=="table" then meta.params=k
    else error("proto key type:"..type(v)) end
  end
  local fs={
    code=meta.code,constants=meta.constants,captures=meta.captures,
    params=meta.params,vararg=meta.vararg,maxRegister=meta.maxRegister,
    children=meta.children
  }
  return {
    rb_call=rb_call,loop_fn=loop_fn,root_tbl=root_tbl,
    opcodes=ops,operands=opx,fields=fs,countKey=meta.countKey,
    proto=M.dec_proto(root_p,fs,ops,opx)
  }
end
function M.ext_med_vm(n)
  local sh_szs,op_ifs,w_n,fs={},0,0,0
  A.walk(n,function(x)
    local ps,body
    if x[1]=="Func" then ps,body=x[2],x[4]
    elseif x[1]=="LocalFunc" then ps,body=x[3],x[5]
    elseif x[1]=="FuncStmt" then ps,body=x[4],x[6]
    end
    if ps and #ps==3 then
      fs=fs+1
      local ws={}
      A.walk(x,function(m)
        if m[1]=="While" and m[2][1]=="Bool" and m[2][2]==true then ws[#ws+1]=m end
      end)
      if #ws>0 then
        w_n=w_n+#ws
        A.walk(ws[1],function(m) if m[1]=="If" then op_ifs=op_ifs+1 end end)
      elseif #body[2]>=1 and body[2][1][1]=="LocalVar" and #body[2][1][3]>0 and body[2][1][3][1][1]=="Tbl" then
        local tb=body[2][1][3][1][2]
        local ok=#tb>0
        for _,f in ipairs(tb) do
          if f[1]~="V" or f[2][1]~="Tbl" then ok=false break end
        end
        if ok then for _,f in ipairs(tb) do sh_szs[#sh_szs+1]=#f[2][2] end end
      end
    end
  end)
  local ssum=0 for _,v in ipairs(sh_szs) do ssum=ssum+v end
  return {factories=fs,shards_n=#sh_szs,shard_sizes=sh_szs,shard_sum=ssum,vm_while=w_n,opcode_ifs=op_ifs}
end
function M.ext_str_vm(rr)
  local rc={}
  A.walk(rr[5],function(n)
    if n[1]=="Call" and #n[3]==3 and n[3][1][1]=="Tbl" and n[3][2][1]=="Num" and n[3][3][1]=="Num" then
      rc[#rc+1]=n
    end
  end)
  local sh_tbl=rc[1][3][1][2]
  local sh_szs={}
  for _,f in ipairs(sh_tbl) do
    if f[1]=="V" and f[2][1]=="Tbl" then sh_szs[#sh_szs+1]=#f[2][2] end
  end
  local pc,rt=rc[1][3][2][2],rc[1][3][3][2]
  local ssum=0 for _,v in ipairs(sh_szs) do ssum=ssum+v end
  local d2={}
  A.walk(rr[5],function(m)
    if m[1]=="While" and m[2][1]=="Var" and #m[3][2]==1 and m[3][2][1][1]=="If" and m[3][2][1][2][1][1][1]=="Bin" then
      d2[#d2+1]=CFF.ext_disp(m,m[2][2])
    end
  end)
  local leaves=0
  if d2[1] then for _ in pairs(d2[1]) do leaves=leaves+1 end end
  return {shards_n=#sh_tbl,shard_sizes=sh_szs,shard_sum=ssum,protos=pc,root=rt,rt_leaves=leaves}
end
return M
