local M={}
function M.succs(b)
  local t=b.term
  if not t then return {} end
  if t[1]=="Jmp" then return {t[2]}
  elseif t[1]=="Branch" then
    if t[3]==t[4] then return {t[3]} end
    return {t[3],t[4]}
  end
  return {}
end
function M.preds(bs)
  local p={}
  for id,_ in pairs(bs) do p[id]={} end
  for id,b in pairs(bs) do
    for _,s in ipairs(M.succs(b)) do
      if p[s] then p[s][#p[s]+1]=id end
    end
  end
  return p
end
function M.rpo(bs,ent)
  local vis,po={},{}
  local function dfs(u)
    vis[u]=true
    local b=bs[u]
    if b then
      for _,v in ipairs(M.succs(b)) do
        if not vis[v] and bs[v] then dfs(v) end
      end
    end
    po[#po+1]=u
  end
  if bs[ent] then dfs(ent) end
  local ord={}
  for i=#po,1,-1 do ord[#ord+1]=po[i] end
  return ord,vis
end
function M.prune(bs,ent)
  local _,vis=M.rpo(bs,ent)
  local nb={}
  for id,b in pairs(bs) do
    if vis[id] then nb[id]=b end
  end
  return nb
end
local function inter(idom,pos,b1,b2)
  local f1,f2=b1,b2
  while f1~=f2 do
    if not f1 or not f2 or not pos[f1] or not pos[f2] then return nil end
    while pos[f1]>pos[f2] do f1=idom[f1] if not f1 or not pos[f1] then return nil end end
    while pos[f2]>pos[f1] do f2=idom[f2] if not f2 or not pos[f2] then return nil end end
  end
  return f1
end
function M.doms(bs,ent)
  local ord=M.rpo(bs,ent)
  local pos={}
  for i,id in ipairs(ord) do pos[id]=i end
  local pr=M.preds(bs)
  local idom={[ent]=ent}
  local chg=true
  while chg do
    chg=false
    for i=2,#ord do
      local b=ord[i]
      local ni
      for _,p in ipairs(pr[b]) do
        if idom[p] then
          ni=ni and inter(idom,pos,p,ni) or p
        end
      end
      if ni and idom[b]~=ni then idom[b]=ni chg=true end
    end
  end
  return idom,ord,pos,pr
end
function M.dominates(idom,ent,a,b)
  local cur=b
  local seen=0
  while cur and cur~=a do
    if cur==ent or cur==idom[cur] then return false end
    cur=idom[cur]
    seen=seen+1
    if seen>10000 then return false end
  end
  return cur==a
end
function M.pdoms(bs)
  local EX="__EXIT__"
  local rbs={[EX]={term={"Exit"}}}
  local pr=M.preds(bs)
  for id,b in pairs(bs) do
    local ss=M.succs(b)
    if #ss==0 then
      rbs[id]={term={"Exit"}}
    end
  end
  local rp={}
  for id,_ in pairs(bs) do rp[id]={} end
  rp[EX]={}
  for id,b in pairs(bs) do
    local ss=M.succs(b)
    if #ss==0 then
      rp[EX][#rp[EX]+1]=id
    else
      for _,s in ipairs(ss) do
        if bs[s] then rp[s][#rp[s]+1]=id end
      end
    end
  end
  local vis,po={},{}
  local function rdfs(u)
    vis[u]=true
    local ls=(u==EX) and rp[EX] or pr[u]
    if ls then
      for _,v in ipairs(ls) do
        if not vis[v] then rdfs(v) end
      end
    end
    po[#po+1]=u
  end
  rdfs(EX)
  local ord={}
  for i=#po,1,-1 do ord[#ord+1]=po[i] end
  local pos={}
  for i,id in ipairs(ord) do pos[id]=i end
  local ip={[EX]=EX}
  local chg=true
  while chg do
    chg=false
    for i=2,#ord do
      local b=ord[i]
      local ss=M.succs(bs[b])
      local ns=#ss==0 and {EX} or ss
      local ni
      for _,s in ipairs(ns) do
        if ip[s] then
          ni=ni and inter(ip,pos,s,ni) or s
        end
      end
      if ni and ip[b]~=ni then ip[b]=ni chg=true end
    end
  end
  return ip
end
function M.nat_loops(bs,ent)
  local idom,ord,_,pr=M.doms(bs,ent)
  local lps={}
  for _,u in ipairs(ord) do
    local b=bs[u]
    for _,h in ipairs(M.succs(b)) do
      if M.dominates(idom,ent,h,u) then
        if not lps[h] then lps[h]={hdr=h,body={[h]=true},latches={}} end
        local lp=lps[h]
        lp.latches[#lp.latches+1]=u
        if not lp.body[u] then
          local st={u}
          lp.body[u]=true
          while #st>0 do
            local x=table.remove(st)
            for _,p in ipairs(pr[x]) do
              if not lp.body[p] and bs[p] then
                lp.body[p]=true
                st[#st+1]=p
              end
            end
          end
        end
      end
    end
  end
  return lps,idom
end
return M
