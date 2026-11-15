local M={}
local sb,sc,sf=string.byte,string.char,string.format
local tn,fl=tonumber,math.floor
local KW={
  ["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,
  ["false"]=1,["for"]=1,["function"]=1,["if"]=1,["in"]=1,["local"]=1,
  ["nil"]=1,["not"]=1,["or"]=1,["repeat"]=1,["return"]=1,["then"]=1,
  ["true"]=1,["until"]=1,["while"]=1
}
local ESC={a="\7",b="\8",f="\12",n="\10",r="\13",t="\9",v="\11",["\\"]="\\",['"']='"',["'"]="'"}
local function u8(cp)
  if cp<128 then return sc(cp) end
  if cp<2048 then return sc(192+fl(cp/64),128+cp%64) end
  if cp<65536 then return sc(224+fl(cp/4096),128+fl(cp/64)%64,128+cp%64) end
  return sc(240+fl(cp/262144),128+fl(cp/4096)%64,128+fl(cp/64)%64,128+cp%64)
end
local function lb(s,i)
  if sb(s,i)~=91 then return nil end
  local j=i+1
  while sb(s,j)==61 do j=j+1 end
  if sb(s,j)~=91 then return nil end
  return j-i-1,j+1
end
local function ls(s,eq,j)
  local n=#s
  if sb(s,j)==13 and sb(s,j+1)==10 then j=j+2
  elseif sb(s,j)==10 or sb(s,j)==13 then j=j+1 end
  local cl="]"..string.rep("=",eq).."]"
  local k,e=s:find(cl,j,true)
  if not k then error("unclosed long str") end
  local v=s:sub(j,k-1):gsub("\r\n","\n"):gsub("\r","\n")
  return v,e+1
end
local function pnum(s,i)
  local n=#s
  local b0,b1=sb(s,i),sb(s,i+1)
  if b0==48 and (b1==98 or b1==66) then
    local j=i+2
    local v,ok=0,false
    while j<=n do
      local c=sb(s,j)
      if c==48 or c==49 then v=v*2+(c-48); ok=true elseif c~=95 then break end
      j=j+1
    end
    return ok and v or nil,j
  elseif b0==48 and (b1==120 or b1==88) then
    local j=i+2
    local ip,fp,ep={},{},{}
    local hx=function(c) return (c>=48 and c<=57) or (c>=65 and c<=70) or (c>=97 and c<=102) end
    while j<=n do
      local c=sb(s,j)
      if hx(c) then ip[#ip+1]=sc(c) elseif c~=95 then break end
      j=j+1
    end
    local hf=false
    if sb(s,j)==46 then
      hf=true
      j=j+1
      while j<=n do
        local c=sb(s,j)
        if hx(c) then fp[#fp+1]=sc(c) elseif c~=95 then break end
        j=j+1
      end
    end
    local ex=0
    if sb(s,j)==112 or sb(s,j)==80 then
      hf=true
      j=j+1
      local sg=1
      if sb(s,j)==43 then j=j+1 elseif sb(s,j)==45 then sg=-1 j=j+1 end
      while j<=n do
        local c=sb(s,j)
        if c>=48 and c<=57 then ep[#ep+1]=sc(c) elseif c~=95 then break end
        j=j+1
      end
      ex=sg*(tn(table.concat(ep)) or 0)
    end
    local v=0
    for k=1,#ip do v=v*16+tn(ip[k],16) end
    if not hf then return (#ip>0) and v or nil,j end
    if #fp>0 then
      local fv=0
      for k=1,#fp do fv=fv*16+tn(fp[k],16) end
      v=v+fv/(16^#fp)
    end
    return v*(2^ex),j
  end
  local j=i
  local bf={}
  local dg=function(c) return c and c>=48 and c<=57 end
  while j<=n do
    local c=sb(s,j)
    if dg(c) then bf[#bf+1]=sc(c) elseif c~=95 then break end
    j=j+1
  end
  if sb(s,j)==46 then
    bf[#bf+1]="."
    j=j+1
    while j<=n do
      local c=sb(s,j)
      if dg(c) then bf[#bf+1]=sc(c) elseif c~=95 then break end
      j=j+1
    end
  end
  if sb(s,j)==101 or sb(s,j)==69 then
    bf[#bf+1]="e"
    j=j+1
    if sb(s,j)==43 or sb(s,j)==45 then bf[#bf+1]=sc(sb(s,j)) j=j+1 end
    while j<=n do
      local c=sb(s,j)
      if dg(c) then bf[#bf+1]=sc(c) elseif c~=95 then break end
      j=j+1
    end
  end
  return tn(table.concat(bf)),j
end
local function pstr(s,i)
  local q=sb(s,i)
  local j,n=i+1,#s
  local bf={}
  while j<=n do
    local c=sb(s,j)
    if c==q then return table.concat(bf),j+1 end
    if c==92 then
      j=j+1
      local e=sb(s,j)
      if e==13 then
        j=j+1
        if sb(s,j)==10 then j=j+1 end
        bf[#bf+1]="\n"
      elseif e==10 then
        j=j+1
        if sb(s,j)==13 then j=j+1 end
        bf[#bf+1]="\n"
      elseif e==122 then
        j=j+1
        while j<=n do
          local w=sb(s,j)
          if w==32 or w==9 or w==10 or w==13 or w==11 or w==12 then j=j+1 else break end
        end
      elseif e==120 then
        bf[#bf+1]=sc(tn(s:sub(j+1,j+2),16))
        j=j+3
      elseif e==117 and sb(s,j+1)==123 then
        local k=s:find("}",j+2,true)
        bf[#bf+1]=u8(tn(s:sub(j+2,k-1),16))
        j=k+1
      elseif e and e>=48 and e<=57 then
        local k=j
        while k<=n and k<j+3 do
          local d=sb(s,k)
          if d>=48 and d<=57 then k=k+1 else break end
        end
        bf[#bf+1]=sc(tn(s:sub(j,k-1))%256)
        j=k
      else
        local ch=sc(e)
        bf[#bf+1]=ESC[ch] or ch
        j=j+1
      end
    else
      bf[#bf+1]=sc(c)
      j=j+1
    end
  end
  error("unclosed str")
end
function M.lex(s)
  local tk={}
  local i,n=1,#s
  if s:sub(1,3)=="\239\187\191" then i=4 end
  if s:sub(i,i+1)=="#!" then
    local p=s:find("\n",i,true)
    i=p and p+1 or n+1
  end
  while i<=n do
    local c=sb(s,i)
    if c==32 or c==9 or c==10 or c==13 or c==11 or c==12 then
      i=i+1
    elseif c==45 and sb(s,i+1)==45 then
      local eq,nj=lb(s,i+2)
      if eq then
        local _,nx=ls(s,eq,nj)
        i=nx
      else
        local p=s:find("\n",i+2,true)
        i=p and p+1 or n+1
      end
    elseif c==91 and (sb(s,i+1)==91 or sb(s,i+1)==61) then
      local eq,nj=lb(s,i)
      if eq then
        local v,nx=ls(s,eq,nj)
        tk[#tk+1]={k="LSTR",v=v}
        i=nx
      else
        tk[#tk+1]={k="SYM",v="["}
        i=i+1
      end
    elseif c==34 or c==39 then
      local v,nx=pstr(s,i)
      tk[#tk+1]={k="STR",v=v}
      i=nx
    elseif (c>=48 and c<=57) or (c==46 and sb(s,i+1) and sb(s,i+1)>=48 and sb(s,i+1)<=57) then
      local v,nx=pnum(s,i)
      tk[#tk+1]={k="NUM",v=v}
      i=nx
    elseif (c>=65 and c<=90) or (c>=97 and c<=122) or c==95 then
      local j=i+1
      while j<=n do
        local d=sb(s,j)
        if (d>=65 and d<=90) or (d>=97 and d<=122) or (d>=48 and d<=57) or d==95 then j=j+1 else break end
      end
      local w=s:sub(i,j-1)
      tk[#tk+1]={k=KW[w] and "KW" or "ID",v=w}
      i=j
    else
      local s3=s:sub(i,i+2)
      if s3=="..." or s3=="..=" or s3=="//=" then
        tk[#tk+1]={k="SYM",v=s3}
        i=i+3
      else
        local s2=s:sub(i,i+1)
        if s2==".." or s2=="==" or s2=="~=" or s2=="<=" or s2==">=" or s2=="::"
          or s2=="+=" or s2=="-=" or s2=="*=" or s2=="/=" or s2=="%=" or s2=="^=" or s2=="//" or s2=="->" then
          tk[#tk+1]={k="SYM",v=s2}
          i=i+2
        else
          tk[#tk+1]={k="SYM",v=sc(c)}
          i=i+1
        end
      end
    end
  end
  tk[#tk+1]={k="EOF",v=""}
  return tk
end
return M
