# contributing

Contributions to UnPromised are welcome as long as they follow the project's engineering rules, static-analysis constraints, and repository hygiene.

## core engineering rules

- **no comments in code**: write self-contained, direct Lua without inline or block comments. if your code does not explain itself, it is not good enough.
- **expert-level code density**: readability for beginners is not a goal. write for engineers deeply fluent in Lua 5.1/Luau internals, compilers, CFG/SSA, and deobfuscation.
- **strictly static & adaptive**: never execute untrusted target code during classification or deobfuscation, and never require CLI flags or manual preset hints. Every change must work automatically across Prometheus (`Minify`, `Weak`, `Cff`, `Vmify`, `Medium`, `Strong`, custom step combinations), WeAreDevs, Lua 5.1, and Luau.

## documentation & repository cleanliness

- **no tracked test files**: do not generate and commit piles of obfuscated fixture files into the repo. Keep the repository clean; use code-driven generators and programmatic checks instead.

## development workflow

1. **prove gaps with tests first**: before implementing a fix or new pass feature, reproduce the exact failure mode or missing capability using programmatic test cases (e.g. via Prometheus presets/custom pipelines or curated edge cases).
2. **fix the root pass cleanly**: put parser/folder changes in `src/frontend/`, deobfuscation passes in `src/passes/`, classification in `src/targets/cls.lua`, and orchestration in `src/pipeline/deobf.lua` without duplicating logic across passes.
3. **verify before finishing**: run both curated checks and the full automated suite with Lua 5.1 after your final edit:
   ```sh
   lua src/checker/check.lua --curated
   lua src/checker/check.lua
   ```
   Verify CLI detection (`lua src/cli.lua --info <file>`), confirm zero comments exist in modified Lua files, and check `git status` to ensure no extra `.md` files, temporary scripts, or tracked fixtures remain.
