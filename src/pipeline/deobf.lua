local A=require("src.frontend.ast")
local F=require("src.frontend.fold")
local E=require("src.backend.emit")
local MS=require("src.passes.misc")
local CA=require("src.passes.ca")
local CF=require("src.passes.cff_cfg")
local EN=require("src.passes.enc")
local VL=require("src.passes.vm_lift")
local M={}
local bk,bh,bc,bg
local function bc_f()
  if bh then pcall(bh.close,bh); bh=nil end
end
local function bu()
  if type(io)~="table" or type(io.popen)~="function" then return "" end
  local ok,f=pcall(io.popen,"uname -s 2>/dev/null","r")
  if not ok or not f then return "" end
  local ok2,s=pcall(f.read,f,"*l")
  pcall(f.close,f)
  return ok2 and type(s)=="string" and s or ""
end
local function bi()
  if bk then return end
  bk=true
  if type(os)~="table" then return end
  local sep=type(package)=="table" and type(package.config)=="string" and package.config:sub(1,1) or "/"
  if sep=="\\" then
    if type(io)=="table" and type(io.popen)=="function" then
      local ok,h=pcall(io.popen,"powershell -NoProfile -NonInteractive -Command - >nul 2>&1","w")
      if ok and h then
        bh=h
        if type(newproxy)=="function" then
          bg=newproxy(true)
          getmetatable(bg).__gc=bc_f
        elseif type(setmetatable)=="function" then
          bg=setmetatable({},{__gc=bc_f})
        end
        return
      end
    end
    if type(os.execute)=="function" then
      bc='powershell -NoProfile -NonInteractive -Command "try{[console]::beep(800,50)}catch{}" >nul 2>&1'
    end
    return
  end
  if type(os.execute)~="function" then return end
  local u=bu()
  if u=="Darwin" then
    bc='osascript -e "beep" >/dev/null 2>&1 || afplay /System/Library/Sounds/Ping.aiff >/dev/null 2>&1 || { printf "\\a" >/dev/tty; } 2>/dev/null || true'
  else
    local l=""
    if type(io)=="table" and type(io.popen)=="function" then
      local ok,f=pcall(io.popen,"if command -v paplay >/dev/null 2>&1 && [ -f /usr/share/sounds/freedesktop/stereo/bell.oga ]; then echo pa; elif command -v canberra-gtk-play >/dev/null 2>&1; then echo cb; elif command -v beep >/dev/null 2>&1; then echo bp; fi 2>/dev/null","r")
      if ok and f then
        local ok2,s=pcall(f.read,f,"*l")
        pcall(f.close,f)
        if ok2 and type(s)=="string" then l=s end
      end
    end
    if l=="pa" then
      bc='paplay /usr/share/sounds/freedesktop/stereo/bell.oga >/dev/null 2>&1 || { printf "\\a" >/dev/tty; } 2>/dev/null || true'
    elseif l=="cb" then
      bc='canberra-gtk-play -i bell >/dev/null 2>&1 || { printf "\\a" >/dev/tty; } 2>/dev/null || true'
    elseif l=="bp" then
      bc='beep -f 800 -l 50 >/dev/null 2>&1 || { printf "\\a" >/dev/tty; } 2>/dev/null || true'
    else
      bc='{ printf "\\a" >/dev/tty; } 2>/dev/null || true'
    end
  end
end
function M.beep()
  bi()
  if bh then
    local o1,r1=pcall(bh.write,bh,"try{[console]::beep(800,50)}catch{}\n")
    local o2,r2=o1 and r1 and pcall(bh.flush,bh)
    if o1 and r1 and o2 and r2 then return end
    bc_f()
  end
  if bc and type(os)=="table" and type(os.execute)=="function" then
    pcall(os.execute,bc)
  end
end
local function ps(fn,...)
  local r=fn(...)
  M.beep()
  return r
end
function M.deobf_node(ast)
  local a=ast
  for _=1,6 do
    local p=a
    a=ps(F.fold,a)
    a=ps(MS.inv_misc,a,F.fold,false)
    a=ps(MS.inv_pool,a)
    a=ps(CA.inv_ca,a)
    a=ps(CF.inv_cff,a,F.fold)
    a=ps(EN.inv_enc,a)
    a=ps(MS.inv_pool,a)
    a=ps(VL.inv_vm,a,true)
    a=ps(F.fold,a)
    a=ps(MS.inv_misc,a,F.fold,false)
    a=ps(VL._sugar_expr,a)
    if A.eq(a,p) then break end
  end
  a=ps(F.fold,a)
  a=ps(MS.inv_misc,a,F.fold,true)
  a=ps(VL._sugar_expr,a)
  return ps(F.fold,a)
end
function M.deobf_ast(src)
  return M.deobf_node(A.parse(src))
end
function M.deobf(src)
  return E.emit(M.deobf_ast(src))
end
return M
