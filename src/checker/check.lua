package.path="?.lua;tests/?.lua;"..package.path
local A=require("src.frontend.ast")
local D=require("src.pipeline.deobf")
local C=require("src.targets.cls")
local P=require("tests.generators.prom")
local function rd(p)
  local f=assert(io.open(p,"rb"),"open:"..p)
  local s=f:read("*a")
  f:close()
  return s
end
local ok_n,ng_n=0,0
local function chk(nm,fn)
  local ok,er=pcall(fn)
  if ok then
    ok_n=ok_n+1
    io.write("PASS ",nm,"\n")
  else
    ng_n=ng_n+1
    io.write("FAIL ",nm,": ",tostring(er),"\n")
  end
  io.flush()
end
local function eq51(a,b,n0)
  local o1,e1=P.cap(a)
  assert(o1,"src:"..tostring(e1))
  local o2,e2=P.cap(b)
  assert(o2,"dec:"..tostring(e2))
  if n0~=false then assert(e1==e2,"mismatch:\n"..tostring(e1).."\n~=\n"..tostring(e2)) end
end
local nl_src=rd("tests/not/source/non_roblox/lua.lua")
chk("clean:non_roblox/lua",function() eq51(nl_src,D.deobf(nl_src)) end)
for _,sp in ipairs({"non_roblox/luau.luau","roblox/lua.lua","roblox/luau.luau"}) do
  chk("clean:"..sp,function() A.parse(D.deobf(rd("tests/not/source/"..sp))) end)
end
for _,sp in ipairs({"non_roblox/prometheus/medium/lua.lua","non_roblox/prometheus/strong/lua.lua","non_roblox/wearedevs/lua.lua"}) do
  chk("curated:"..sp,function()
    local ob=rd("tests/not/obfuscated/"..sp)
    C.detect_layers(A.parse(ob))
    local out=D.deobf(ob)
    A.parse(out)
    eq51(nl_src,out)
  end)
end
local creq={
  {"non_roblox/prometheus/medium/luau.luau",{"standalone-luau",":ready","* 2","luau-complete","\\000\\255"}},
  {"non_roblox/prometheus/strong/luau.luau",{"standalone-luau",":ready","* 2","luau-complete","\\000\\255"}},
  {"non_roblox/wearedevs/luau.luau",{"standalone-luau",":ready","K += t * 2","\\000\\255"}},
  {"roblox/prometheus/medium/lua.lua",{"Players","ReplicatedStorage","FixtureRemote","RobloxLuaFixture",".Name",":GetService(","\\000\\255"}},
  {"roblox/prometheus/strong/lua.lua",{"Players","ReplicatedStorage","FixtureRemote","RobloxLuaFixture",".Name",":GetService(","\\000\\255"}},
  {"roblox/wearedevs/lua.lua",{"Players","ReplicatedStorage","FixtureRemote","RobloxLuaFixture",".Name",":GetService(",":FireServer(\"hello-player\"","\\000\\255"}},
  {"roblox/prometheus/medium/luau.luau",{"LuauFixtureRemote","RobloxLuauFixture","8",".Name",":GetService(","roblox-luau-complete","\\000\\255"}},
  {"roblox/prometheus/strong/luau.luau",{"LuauFixtureRemote","RobloxLuauFixture","8",".Name",":GetService(","roblox-luau-complete","\\000\\255"}},
  {"roblox/wearedevs/luau.luau",{"LuauFixtureRemote","RobloxLuauFixture","q *= 4",".Name",":GetService(","roblox-luau-complete","\\000\\255"}},
}
local ccls={
  {"non_roblox/prometheus/medium/lua.lua","PROM_V03_MEDIUM"},
  {"non_roblox/prometheus/strong/lua.lua","PROM_V03_STRONG"},
  {"non_roblox/wearedevs/lua.lua","WEAREDEVS"},
  {"roblox/prometheus/medium/lua.lua","PROM_V03_MEDIUM"},
  {"roblox/prometheus/strong/lua.lua","PROM_V03_STRONG"},
  {"roblox/wearedevs/lua.lua","WEAREDEVS"},
}
for _,ic in ipairs(ccls) do
  chk("cls:curated:"..ic[1],function()
    local ast=A.parse(rd("tests/not/obfuscated/"..ic[1]))
    assert(C.detect_layers(ast).kind==ic[2])
    assert(C.cls_ast(ast)==ic[2])
  end)
end
for _,it in ipairs(creq) do
  chk("curated:"..it[1],function()
    local ob=rd("tests/not/obfuscated/"..it[1])
    C.detect_layers(A.parse(ob))
    local out=D.deobf(ob)
    A.parse(out)
    for _,q in ipairs(it[2]) do assert(out:find(q,1,true),"missing:"..q) end
  end)
end
if arg[1]~="--curated" then
  local prs={"Minify","Weak","Cff","Vmify","Medium","Strong"}
  local nms={}
  for k in pairs(P.cases51) do nms[#nms+1]=k end
  table.sort(nms)
  for _,pr in ipairs(prs) do
    for _,nm in ipairs(nms) do
      chk("51:"..nm.."["..pr.."]",function()
        local src=P.cases51[nm](1)
        local ob=P.obf(src,pr,"Lua51",1,true)
        local out=D.deobf(ob)
        eq51(src,out)
      end)
    end
  end
  local sts={
    {"EncryptStrings",{}},
    {"ConstantArray",{}},
    {"ConstantArray",{Encoding="base64",Rotate=true,LocalWrapperCount=3,StringsOnly=false}},
    {"ConstantArray",{Encoding="base85",Rotate=true,LocalWrapperCount=3,StringsOnly=false}},
    {"ConstantArray",{Encoding="mixed",Rotate=true,LocalWrapperCount=3,StringsOnly=false}},
    {"ProxifyLocals",{}},
    {"ProxifyLocals",{LiteralType="string"}},
    {"SplitStrings",{}},
    {"NumbersToExpressions",{}},
    {"NumbersToExpressions",{Threshold=1}},
    {"WrapInFunction",{}},
    {"WrapInFunction",{Iterations=2}},
    {"AddVararg",{}},
    {"WatermarkCheck",{Content="WeAreDevs"}},
    {"AntiTamper",{}},
    {"AntiTamper",{UseDebug=true}},
  }
  for idx,st in ipairs(sts) do
    chk("step:"..st[1].."#"..idx,function()
      local src=P.cases51["synth_upval"](1)
      local ob=P.obfStep(src,st[1],st[2],"Lua51",1)
      local out=D.deobf(ob)
      eq51(src,out)
    end)
  end
  for _,ct in ipairs({"strcat","table","custom"}) do
    for _,md in ipairs({"local","global","inline"}) do
      chk("split:"..ct..":"..md,function()
        local src=P.cases51["strings"](1)
        local ob=P.obfStep(src,"SplitStrings",{Threshold=1,ConcatenationType=ct,Mode=md},"Lua51",1)
        eq51(src,D.deobf(ob))
      end)
    end
  end
  local ek={Minify="PROM_V03_MINIFY",Weak="PROM_V03_WEAK",Cff="PROM_V03_CFF",Vmify="PROM_V03_VMIFY",Medium="PROM_V03_MEDIUM",Strong="PROM_V03_STRONG"}
  for _,pr in ipairs(prs) do
    chk("cls:preset:"..pr,function()
      local ob=P.obf("local a=1 if a==1 then print(1) else print(2) end",pr,"Lua51",1,true)
      assert(C.detect_layers(A.parse(ob)).kind==ek[pr])
    end)
  end
  for _,pr in ipairs({"Weak","Medium","Strong"}) do
    chk("at:"..pr,function()
      local src=P.cases51["synth_upval"](2)
      local ob=P.obf(src,pr,"Lua51",2,false)
      eq51(src,D.deobf(ob))
    end)
  end
  local pm=require("src.prometheus")
  local pz=require("src.presets")
  local function obf_m(src,steps)
    return pm.Pipeline:fromConfig({LuaVersion="Lua51",VarNamePrefix="",NameGenerator="MangledShuffled",PrettyPrint=false,Seed=1,Steps=steps}):apply(src,"c")
  end
  local wms="local x=42 print(x) return x+1"
  for _,ex in ipairs({"Cff","Vmify","Medium","Strong"}) do
    chk("wmc:"..ex,function()
      local st={{Name="WatermarkCheck",Settings={Content="WeAreDevs"}}}
      if ex=="Cff" or ex=="Vmify" then st[2]={Name=ex,Settings={}}
      else for _,s in ipairs(pz[ex].Steps) do st[#st+1]=s end end
      local out=D.deobf(obf_m(wms,st))
      assert(not out:find("WeAreDevs",1,true),"wm_left")
      eq51(wms,out)
    end)
  end
  local cbs={
    {"anti_dbg_cff",{{Name="AntiTamper",Settings={UseDebug=true}},{Name="Cff",Settings={}}}},
    {"anti_dbg_vm",{{Name="AntiTamper",Settings={UseDebug=true}},{Name="Vmify",Settings={}}}},
    {"vm_enc_cff",{{Name="Vmify",Settings={}},{Name="EncryptStrings",Settings={}},{Name="Cff",Settings={}}}},
    {"enc_vm",{{Name="EncryptStrings",Settings={}},{Name="Vmify",Settings={}}}},
    {"ca_rot_vm",{{Name="ConstantArray",Settings={Threshold=1,Rotate=true,Encoding="mixed"}},{Name="Vmify",Settings={}}}},
  }
  for _,cb in ipairs(cbs) do
    chk("combo:"..cb[1],function()
      local src=P.cases51["synth_upval"](3)
      eq51(src,D.deobf(obf_m(src,cb[2])))
    end)
  end
  local unms={}
  for k in pairs(P.casesU) do unms[#unms+1]=k end
  table.sort(unms)
  for _,pr in ipairs(prs) do
    for _,nm in ipairs(unms) do
      chk("U:"..nm.."["..pr.."]",function()
        local src=P.casesU[nm](1)
        local ob=P.obf(src,pr,"LuaU",1,true)
        local out=D.deobf(ob)
        assert(P.parseOk(out,"LuaU"),"parseU failed")
      end)
    end
  end
end
io.write(string.format("SUMMARY: pass=%d fail=%d total=%d\n",ok_n,ng_n,ok_n+ng_n))
if ng_n>0 then os.exit(1) end
