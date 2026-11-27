local rp = "re/prometheus"
_G.arg = _G.arg or {}
package.path = rp .. "/?.lua;" .. rp .. "/src/?.lua;" .. package.path
local P = require("src.prometheus")
local Pr = require("src.presets")
local Par = require("prometheus.parser")
P.Logger.logLevel = P.Logger.LogLevel.Error

local function rd(p)
	local f = assert(io.open(p, "rb"))
	local s = f:read("*a")
	f:close()
	return s
end

local function wr(p, s)
	local f = assert(io.open(p, "wb"))
	f:write(s)
	f:close()
end

local function cp(t)
	if type(t) ~= "table" then return t end
	local r = {}
	for k, v in pairs(t) do r[k] = cp(v) end
	return r
end

local function mkRng(sd)
	local x = sd % 2147483647
	if x <= 0 then x = x + 2147483646 end
	return function(a, b)
		x = (x * 48271) % 2147483647
		if not a then return x / 2147483647 end
		if not b then return 1 + (x % a) end
		return a + (x % (b - a + 1))
	end
end

local function genExpr(sd)
	local r = mkRng(sd)
	local o = {
		"local a,b,c=" .. r(-50, 50) .. "," .. r(1, 20) .. "," .. r(-10, 10),
		"local s='" .. string.char(64 + r(1, 26), 96 + r(1, 26), 48 + r(0, 9)) .. "'",
		"local t={x=a+b*c,y=(a-c)%b,z=a..s..b}",
		"local u=(t.x>0 and t.y or -t.y)+(#s*3)",
		"print('se',a,b,c,s,t.x,t.y,t.z,u)",
		"return u",
	}
	return table.concat(o, "\n")
end

local function genCfg(sd)
	local r = mkRng(sd + 17)
	local l = r(4, 9)
	local o = {
		"local acc=0",
		"for i=1," .. l .. " do",
		"  if i%2==0 then acc=acc+i*3 elseif i%3==0 then acc=acc-i else acc=acc+1 end",
		"end",
		"local j=0",
		"while j<" .. r(3, 7) .. " do j=j+1; if j==2 then acc=acc+5 else acc=acc+j end end",
		"local k=0",
		"repeat k=k+1; local d=k*2; acc=acc+d until k>=" .. r(2, 5),
		"print('sc',acc,j,k)",
		"return acc",
	}
	return table.concat(o, "\n")
end

local function genUpv(sd)
	local r = mkRng(sd + 53)
	local o = {
		"local fs={}",
		"for i=1," .. r(4, 8) .. " do",
		"  local v=i*" .. r(2, 5),
		"  fs[i]=function(d) v=v+d; return v end",
		"end",
		"local res={}",
		"for i=1,#fs do res[i]=fs[i](i) end",
		"for i=1,#fs do res[#fs+i]=fs[i](10) end",
		"print('su',table.concat(res,','))",
		"return res[#res]",
	}
	return table.concat(o, "\n")
end

local tc51 = {
	closures = function()
		return [[
local arr={}
for i=1,20 do local x=(x or 1)+i arr[i]=function() return x end end
for _,f in ipairs(arr) do print(f()) end]]
	end,
	loops = function()
		return [[
local s=0
for i=1,50 do s=s+i end
for i=50,1,-2 do s=s-i end
local w=0 for i=0,10,0.5 do w=w+1 end
local t={10,20,30} for _,v in ipairs(t) do s=s+v end
local m={a=1,b=2,c=3} for _,v in pairs(m) do s=s+v end
print(s,w)]]
	end,
	multi_ret = function()
		return [[
local function mv() return 42,"hi",true,nil end
local a,b,c,d=mv()
local function pv(...) return ... end
local x,y,z=pv(10,nil,30)
local t={mv()}
print(a,b,c,tostring(d),x,tostring(y),z,select('#',pv(1,nil,3)),t[1],t[2])]]
	end,
	numbers = function()
		return [[
local p=-1.00000000000001
local h=1111111111111111
local l=1111111111111110
local inf=10e500
local nan=10e500-10e400
print(p==tonumber("-1.00000000000001"),h-l,inf==math.huge,nan~=nan)]]
	end,
	strings = function()
		return [[
local p="lorem ipsum dolor sit amet ipsum lorem"
local c={}
for w in p:gmatch("%w+") do c[w]=(c[w] or 0)+1 end
for _,w in ipairs({"lorem","ipsum","dolor","sit","amet"}) do print(w,c[w]) end]]
	end,
	signed_zero = function()
		return [[
local function z1() return -0 end
local function z2() return -0.0 end
local function z3() return 0*-1 end
local function z4() return 0 end
print(1/z1()==-math.huge,1/z2()==-math.huge,1/z3()==-math.huge,1/z4()==math.huge)]]
	end,
	for_coerce = function()
		return [[
local f,l,st="1","5","1"
local c=0
for i=f,l,st do assert(type(i)=="number") c=c+1 end
local d=0
for i="10","1","-2" do d=d+i end
print(c,d,type(f),f)]]
	end,
	parens = function()
		return [[
local n=0
local function pr() n=n+1 return 1,2 end
local a,b=(pr())
local t={(pr())}
print(n,a,tostring(b),t[1],tostring(t[2]),select("#",(pr())))]]
	end,
	ambig_call = function()
		return [[
local c=1
;(function() c=c+1 print("ac",c) end)()]]
	end,
	repeat_scope = function()
		return [[
local i=0 local res=0
repeat local a=i local b=a*2 res=a+b i=i+1 until b>=8
print(i,res,_G.a==nil)]]
	end,
	src_non_roblox_lua = function()
		return rd("tests/not/source/non_roblox/lua.lua")
	end,
	single_str = function()
		return 'print("this is a test")'
	end,
	no_str = function()
		return "print(88*88)"
	end,
	single_ret = function()
		return 'local x=10 local function add(a,b) return a+b end print("sum",add(x,32))'
	end,
	closure_at = function()
		return 'local f=function() return "real" end print(tostring(f):find("function")~=nil,f())'
	end,
	synth_expr = genExpr,
	synth_cfg = genCfg,
	synth_upval = genUpv,
}

local tcU = {
	src_non_roblox_luau = function()
		return rd("tests/not/source/non_roblox/luau.luau")
	end,
	src_roblox_luau = function()
		return rd("tests/not/source/roblox/luau.luau")
	end,
	luau_compound = function()
		return [[
local x=10 x+=5 x-=3 x*=2 x/=4 x%=5 x^=2
local s="a" s..="b"
return x,s]]
	end,
	luau_ifelse = function()
		return [[
local x=3
local y=if x<0 then -1 elseif x==3 then 30 else 99
return y]]
	end,
	luau_continue = function()
		return [[
local s=0
for i=1,10 do if i%2==0 then continue end s=s+i end
return s]]
	end,
}

local function obf(code, preset, ver, sd, noAt)
	local bp = assert(Pr[preset], "bad preset: " .. tostring(preset))
	local cfg = cp(bp)
	cfg.LuaVersion = ver
	cfg.Seed = sd
	if noAt then
		local st = {}
		for _, s in ipairs(cfg.Steps) do
			if s.Name ~= "AntiTamper" then st[#st + 1] = s end
		end
		cfg.Steps = st
	end
	local pl = P.Pipeline:fromConfig(cfg)
	return pl:apply(code, "dyn")
end

local function obfStep(code, name, sets, ver, sd)
	local pl = P.Pipeline:fromConfig({
		LuaVersion = ver,
		VarNamePrefix = "",
		NameGenerator = "MangledShuffled",
		PrettyPrint = false,
		Seed = sd,
		Steps = {{Name = name, Settings = sets or {}}},
	})
	return pl:apply(code, "dyn")
end

local function cap(code)
	local out = {}
	local env = {}
	for k, v in pairs(_G) do env[k] = v end
	env._G = env
	env.print = function(...)
		local r = {}
		for i = 1, select("#", ...) do r[i] = tostring(select(i, ...)) end
		out[#out + 1] = table.concat(r, "\t")
	end
	local fn, err = loadstring(code, "=dyn")
	if not fn then return false, "load:" .. tostring(err) end
	setfenv(fn, env)
	local res = {pcall(fn)}
	if not res[1] then return false, "run:" .. tostring(res[2]) end
	local rs = {}
	for i = 2, #res do rs[#rs + 1] = tostring(res[i]) end
	return true, table.concat(out, "\n") .. "|ret:" .. table.concat(rs, ",")
end

local function parseOk(code, ver)
	local ok, err = pcall(function()
		Par:new({LuaVersion = ver}):parse(code)
	end)
	return ok, err
end

local function withVer(ref, fn)
	if not ref or ref == "HEAD" or ref == "master" then return true, fn(P, Pr) end
	local tag = ref:gsub("[^%w_.-]", "_")
	local wt = "re/wt_" .. tag
	local f = io.open(wt .. "/src/prometheus.lua", "rb")
	if not f then
		if os.execute("git -C " .. rp .. " rev-parse --verify " .. ref .. " >nul 2>&1") ~= 0 then
			return false, "missing_ref:" .. ref
		end
		if os.execute("git -C " .. rp .. " worktree add --detach ../wt_" .. tag .. " " .. ref .. " >nul 2>&1") ~= 0 then
			return false, "worktree_fail:" .. ref
		end
	else
		f:close()
	end
	local sv = {}
	for k, v in pairs(package.loaded) do
		if k:match("^src%.prometheus") or k:match("^src%.presets") or k:match("^prometheus") or k == "logger" then
			sv[k] = v
			package.loaded[k] = nil
		end
	end
	local op = package.path
	package.path = wt .. "/?.lua;" .. wt .. "/src/?.lua;" .. op
	local ok, res = pcall(function()
		local pv = require("src.prometheus")
		local zv = require("src.presets")
		pv.Logger.logLevel = pv.Logger.LogLevel.Error
		return fn(pv, zv)
	end)
	package.path = op
	for k in pairs(package.loaded) do
		if k:match("^src%.prometheus") or k:match("^src%.presets") or k:match("^prometheus") or k == "logger" then
			package.loaded[k] = nil
		end
	end
	for k, v in pairs(sv) do package.loaded[k] = v end
	return ok, res
end

local function obfVer(ref, code, preset, ver, sd, noAt)
	return withVer(ref, function(pv, zv)
		local bp = assert(zv[preset], "bad preset: " .. tostring(preset))
		local cfg = cp(bp)
		cfg.LuaVersion = ver
		cfg.Seed = sd
		if noAt then
			local st = {}
			for _, s in ipairs(cfg.Steps) do
				if s.Name ~= "AntiTamper" then st[#st + 1] = s end
			end
			cfg.Steps = st
		end
		return pv.Pipeline:fromConfig(cfg):apply(code, "dyn")
	end)
end

local function hasVer(ref)
	if not ref or ref == "HEAD" or ref == "master" then return true end
	local f = io.open("re/wt_" .. ref:gsub("[^%w_.-]", "_") .. "/src/prometheus.lua", "rb")
	if f then f:close() return true end
	return os.execute("git -C " .. rp .. " rev-parse --verify " .. ref .. " >nul 2>&1") == 0
end

local M = {
	cases51 = tc51,
	casesU = tcU,
	obf = obf,
	obfStep = obfStep,
	obfVer = obfVer,
	hasVer = hasVer,
	cap = cap,
	parseOk = parseOk,
}

local function runSuite(sd, outDir, useAt, vb, ps)
	if io.stdout and io.stdout.setvbuf then io.stdout:setvbuf("no") end
	local pass, fail = 0, 0
	ps = ps or {"Minify", "Weak", "Cff", "Vmify", "Medium", "Strong"}
	local cl = {}
	for k in pairs(tc51) do cl[#cl + 1] = k end
	table.sort(cl)
	for ci, cn in ipairs(cl) do
		local src = tc51[cn](sd + ci * 101)
		local ok0, ex0 = cap(src)
		assert(ok0, "plain fail " .. cn .. ": " .. tostring(ex0))
		for pi, pn in ipairs(ps) do
			local t0 = os.clock()
			local code = obf(src, pn, "Lua51", sd + ci * 31 + pi, not useAt)
			if outDir then wr(outDir .. "/" .. cn .. "_" .. pn .. ".lua", code) end
			local pok, perr = parseOk(code, "Lua51")
			local ok1, ex1 = cap(code)
			if vb then print(string.format("5.1 %s [%s] %.2fs pok=%s ok=%s", cn, pn, os.clock() - t0, tostring(pok), tostring(ok1 and ex1 == ex0))) end
			if pok and ok1 and ex1 == ex0 then
				pass = pass + 1
			else
				fail = fail + 1
				print(string.format("FAIL 5.1 %s [%s] parse=%s ok=%s\n  exp=%q\n  got=%q",
					cn, pn, tostring(pok), tostring(ok1), tostring(ex0), tostring(ex1 or perr)))
			end
		end
	end
	local st = {
		{"ConstantArray", {StringsOnly = true, Threshold = 1, Encoding = "mixed"}},
		{"EncryptStrings", {}},
		{"NumbersToExpressions", {}},
		{"SplitStrings", {Threshold = 1}},
		{"ProxifyLocals", {}},
		{"WrapInFunction", {}},
		{"AddVararg", {}},
	}
	local base = tc51.synth_cfg(sd + 777)
	local okb, exb = cap(base)
	assert(okb, exb)
	for si, sp in ipairs(st) do
		local t0 = os.clock()
		local code = obfStep(base, sp[1], sp[2], "Lua51", sd + 900 + si)
		local pok = parseOk(code, "Lua51")
		local ok1, ex1 = cap(code)
		if vb then print(string.format("STEP %s %.2fs pok=%s ok=%s", sp[1], os.clock() - t0, tostring(pok), tostring(ok1 and ex1 == exb))) end
		if pok and ok1 and ex1 == exb then
			pass = pass + 1
		else
			fail = fail + 1
			print(string.format("FAIL STEP %s parse=%s ok=%s got=%q", sp[1], tostring(pok), tostring(ok1), tostring(ex1)))
		end
	end
	local ul = {}
	for k in pairs(tcU) do ul[#ul + 1] = k end
	table.sort(ul)
	for ci, cn in ipairs(ul) do
		local src = tcU[cn](sd + ci * 131)
		for pi, pn in ipairs(ps) do
			local t0 = os.clock()
			local code = obf(src, pn, "LuaU", sd + ci * 19 + pi, not useAt)
			if outDir then wr(outDir .. "/" .. cn .. "_" .. pn .. ".luau", code) end
			local pok, perr = parseOk(code, "LuaU")
			if vb then print(string.format("LuaU %s [%s] %.2fs pok=%s", cn, pn, os.clock() - t0, tostring(pok))) end
			if pok then
				pass = pass + 1
			else
				fail = fail + 1
				print(string.format("FAIL LuaU %s [%s] parse=%s", cn, pn, tostring(perr)))
			end
		end
	end
	print(string.format("SUMMARY pass=%d fail=%d", pass, fail))
	return fail == 0
end

local isCli = true
if ... ~= nil and package.loaded[(...)] ~= nil then isCli = false end
if isCli then
	local sd, outDir, useAt, vb, ps = 20261112, nil, false, false, nil
	local i = 1
	while arg and i <= #arg do
		local a = arg[i]
		if a == "--seed" and arg[i + 1] then sd = tonumber(arg[i + 1]); i = i + 2
		elseif a == "--out" and arg[i + 1] then outDir = arg[i + 1]; i = i + 2
		elseif a == "--antitamper" then useAt = true; i = i + 1
		elseif a == "--verbose" then vb = true; i = i + 1
		elseif a == "--preset" and arg[i + 1] then ps = {arg[i + 1]}; i = i + 2
		else i = i + 1 end
	end
	assert(sd, "invalid seed")
	local ok = runSuite(sd, outDir, useAt, vb, ps)
	os.exit(ok and 0 or 1)
end

return M
