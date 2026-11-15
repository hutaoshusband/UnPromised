local D=require("src.pipeline.deobf")
local C=require("src.targets.cls")
local A=require("src.frontend.ast")
local ip,op,inf
for i=1,#arg do
  if arg[i]=="--info" then inf=true
  elseif not ip then ip=arg[i]
  elseif not op then op=arg[i] end
end
local f=(ip and ip~="-") and assert(io.open(ip,"rb")) or io.stdin
local s=f:read("*a")
if ip and ip~="-" then f:close() end
local ast=A.parse(s)
if inf then
  local ly=C.detect_layers(ast)
  io.stderr:write(string.format("kind=%s wrap=%d pool=%s cff=%s vm=%s enc=%s\n",ly.kind,ly.wrap,tostring(ly.pool),ly.cff and tostring(ly.cff.leaves) or "nil",tostring(ly.vm),tostring(ly.enc)))
end
local out=D.deobf(s)
if op then
  local g=assert(io.open(op,"wb"))
  g:write(out)
  g:close()
else
  io.write(out,"\n")
end
