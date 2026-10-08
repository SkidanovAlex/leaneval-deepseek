# FT (odd order) port to lean-eval v4.35 — PORT-NOTES

Target: Lean v4.35.0-rc3 / Mathlib 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22 / lean-eval 0e093293afbe96be91504ae6e44947876d3fc84e
(lean-eval main checked 2026-10-04: still v4.35.0-rc3 @ 0e09329).

## Source choice
- Chosen: ~/ftport/odd-order (yawara/odd-order main @ 7a412ea, 2026-09-27, Lean v4.34.1, Mathlib d13f23b7).
  Reason: one toolchain step from v4.35 (the July submission extraction is on v4.32.0-rc1 / Mathlib 360da6f,
  three steps back) and it is the maintained tree. The submission's theorem-only pruning bought only -0.7% peak RSS and
  +5% wall, so it is not worth re-deriving; its packaging idea (re-root modules as Submission.OddOrder.*, keep the
  logical namespace OddOrder) is reused.
- Submission measurements (v4.32, 588 modules, self-hosted box): build 716 s / max-RSS 6.99 GB; lean4export 50 s /
  7.40 GiB / 1.03 GB export; comparator + kernel replay 238 s / 7.40 GiB. Nanoda not measured there.

## FT closure
- Import closure of OddOrder.FeitThompson (local modules): 712 files / 474,717 lines (list: ~/ftport/ft_closure.txt,
  script ~/ftport/closure.py). Breakdown: BG 172, Peterfalvi 308, GroupTheory 152, Isaacs 64, Mathlib 6, Algebra 4, FT* 6.
- NO file under OddOrder/Peterfalvi/Appendices/ (Suzuki, Suzuki2Groups, FeitSibley*, NearField*, RankOne*,
  SemilinearField, ExceptionalNearField) and no GroupTheory.BrauerSuzuki*/RankOneBNPair is in the closure.
  Sibley-named files that ARE in it are Peterfalvi §8/§9/§12 coherence chapters (S08_Sibley*, S09_FrobeniusSibley,
  S12_TypeVSibley, S08_CoherenceCorePart2/SibleyBounds) — part of the FT proof itself.

## Workspace
- ~/ftport/ft435: staged by `LEANEVAL_ROOT=~/src/curric/lean-eval-v435 lbeval.py stage feit_thompson --dest ~/ftport/ft435`
  (.lake/packages -> shared ~/src/curric/lean-eval-v435/.lake/packages; Mathlib prebuilt).
- Sources: Submission/OddOrder/** = the closure, imports re-rooted OddOrder.X -> Submission.OddOrder.X
  (~/ftport/extract.py). Namespace OddOrder unchanged. Submission.lean: `Submission.feit_thompson := OddOrder.feitThompson _h`.
- v4.35 option block (marked `-- ftport:v435-opts-begin/end`) inserted after imports of every file; ~/ftport/port_loop.sh
  builds in rounds and strips the block from any file that fails with it (list in logs/stripped.txt).
  ~/ftport/addopts.py re-adds it.

## Rounds / fixes
- R1 (55 s): 4 failures. CyclicSubgroupUnique: "No goals" -> fixed by stripping options.
  ChermakDelgado, BG.Ch2_Uniqueness.Setup: Mathlib API change, `IsSimpleGroup.eq_bot_or_eq_top_of_normal` now takes
  `[H.Normal]` instance-implicitly -> ~/ftport/fix_simple.py rewrites every `R.eq_bot_or_eq_top_of_normal`
  (R : IsSimpleGroup) to `@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ R` (44 files; not IsChiefFactor's own field).
  CyclotomicGaloisAction: `AlgEquiv.coe_ringEquiv` -> `AlgEquiv.coe_toRingEquiv`; L247 `rw [h1, h2, h3]` -> `rw [h1, h2]; exact h3`.
- R3-R4: Isaacs.Ch01_Sylow.Basic etc: `Subgroup.Normal.eq_bot_or_eq_top` is now `(H) [H.Normal]` ->
  ~/ftport/fix_normal.py rewrites `hN.eq_bot_or_eq_top` / `Subgroup.Normal.eq_bot_or_eq_top h` to
  `@Subgroup.Normal.eq_bot_or_eq_top _ _ _ _ h` (10 files). CyclicSubgroupUnique L55 `exact` -> `try exact` (congr 1 closes it now).
- R5: `Subgroup.card_dvd_of_surjective` now has `f` implicit: drop the `_` (S08_CoherenceCorePart1, WielandtAssembly),
  `(f := ...)` in Isaacs Ch03 Theorem315.
- R7: AppC_LemmaC3_ConjugateLine L678 `simp [map_mul, hline_neg_one]` leaves `a = a` -> `... <;> first | rfl | (congr 1)` (keeps options).
- R9: S10_MinimalSimpleStructure: `ULift.ext _ _ h` -> `ULift.ext h` (3 sites).
- Loop improvement: a failing file is stripped of the option block only if its errors look option-induced
  (No goals / timeout / heartbeats / recursion / failed to synthesize) OR it compiles cleanly without the block
  (~/ftport/try_noopts.sh); otherwise it is left for a manual fix.
- R16 (2026-10-04 19:00Z): BUILD OK. 16 rounds, ~22 min wall on 16 cores. Option block stripped from 11 files
  (logs/stripped.txt), kept in the other 700.
- `lake build Solution Submission Challenge` OK; axioms of feit_thompson, Submission.feit_thompson,
  OddOrder.feitThompson = [propext, Classical.choice, Quot.sound].
- Snapshot: git --git-dir=~/ftport/ft435.git --work-tree=~/ftport/ft435, commit 4efa642 (local only).

## 16 GB acceptance
- ~/ftport/accept.sh: rm -rf .lake/build; lake build; lake test (v435 comparator/lean4export/nanoda on PATH), inside
  `systemd-run --user --unit=ftport-acceptN -p MemoryMax=16G -p MemorySwapMax=0 -p AllowedCPUs=0-3 taskset -c 0-3`.
  Samples (cgroup anon/file every 3 s + per-process RSS > 200 MB) in logs/<tag>/samples.txt, phases in phases.txt.
- accept1 (2026-10-04 19:08-19:28Z, 4 CPUs, MemoryMax=16G, no swap) PASSED; no memory fixes were needed:
  - clean `lake build` (Mathlib cached; all 712 FT modules + Challenge/Solution/Submission): rc=0, wall 15m49s,
    cgroup memory.peak 6.01 GB (includes page cache), max cgroup anon 4.03 GB; largest single lean RSS 7.56 GB
    (RSS counts the shared Mathlib mmap).
  - `lake test` (comparator d03acab + lean4export 076e8e5 + nanoda 68d5ca9, v4.35 builds): rc=0, wall 4m32s, cgroup
    memory.peak 7.60 GB; per-process max RSS: lean4export 8.8 GB, comparator 3.7 GB, nanoda_bin 1.2 GB.
    Verdict lines: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution",
    "Your solution is okay!" (permitted_axioms = propext, Quot.sound, Classical.choice).
  - K (kernel CPU) is small: export + nanoda + full single-thread replay fit in the 4.5 min test phase. Expected grader
    wall ~16 min build + ~5 min test, far below the 6 h cap. The FT closure alone fits 16 GB with ~2x headroom
    (the earlier exit-143 reports concerned whole-repo builds).

## Rebuild on another box (exact steps)
1. Toolchain: `elan toolchain install leanprover/lean4:v4.35.0-rc3` (lean-toolchain pins it).
2. Unpack: `mkdir ft435 && tar xzf ftport-final.tgz -C ft435 && cd ft435` (tarball root = workspace root).
3. Dependencies: lake-manifest.json pins mathlib 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22, lean-pool
   e9d53e9cbcff8dfd0cc816ba94db7a26b082929f, TauCeti/batteries/aesop/... at lean-eval 0e093293's revs. Either
   a) share a prebuilt tree: `mkdir -p .lake && ln -s <lean-eval-v435>/.lake/packages .lake/packages`
      (this is what `LEANEVAL_ROOT=~/src/curric/lean-eval-v435 lbeval.py stage` does; that tree has Mathlib built at
      5e0c4e5 and lean-pool built), or
   b) fresh: `lake exe cache get` (lake first clones the manifest packages, then downloads Mathlib oleans for 5e0c4e5);
      `lake build` then builds lean-pool itself (small).
   `lakefile.toml` is lean-eval's generated one (allowNonModules = true; requires lean-pool + mathlib). Do not change it.
4. Build, capped: `taskset -c 0-3 systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 lake build`
   (~16 min on 4 cores, ~6 GB). Axiom check: a scratch file with `import Solution` and `#print axioms feit_thompson`
   run via `lake env lean`.
5. Grader check: put lean4export / comparator / nanoda_bin / landrun (lean-eval 0e093293 tool pins) on PATH and run
   `lake test` under the same cap (~4.5 min, ~7.6 GB). ftport-tools/accept.sh does steps 4-5 with memory sampling.

## Using the FT library downstream (bender_suzuki, gorenstein_walter)
- Copy `Submission/OddOrder/**` (and LICENSE-odd-order) into the downstream workspace; module names are
  `Submission.OddOrder.*`, logical namespace `OddOrder`. Then `import Submission.OddOrder.FeitThompson` and use
  `OddOrder.feitThompson {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) : Group.IsSolvable G`.
  Every other module keeps its name: `Submission.OddOrder.{BG,Peterfalvi,Isaacs,GroupTheory,Algebra,Mathlib}.*`,
  `Submission.OddOrder.FeitThompsonSetup`, etc. (list: ftport-tools/ft_closure.txt, prefix `Submission.`).
- Files keep their own respectTransparency option block (between `-- ftport:v435-opts-begin/end`).

## License / attribution
- yawara/odd-order is Apache-2.0 (LICENSE; no NOTICE file). Copyright (c) 2026 Yawara Ishida
  (A.I.System Research, Inc.). CITATION.cff asks to cite "odd-order: The Feit-Thompson Odd Order Theorem in Lean 4",
  https://github.com/yawara/odd-order, with the commit hash used: 7a412eae81e9510a684fd8c180cf1fbd47b8d00d.
- Apache-2.0 section 4 obligations, met in this tree: the license ships as LICENSE-odd-order; every file keeps its
  original copyright header; modifications are stated here (imports re-rooted OddOrder.* -> Submission.OddOrder.*,
  v4.35 option block inserted, and the API fixes listed under "Rounds / fixes"; made by the ftport port, 2026-10-04).
  Any downstream submission that includes these files must keep LICENSE-odd-order and this attribution.

## Tarball
- ~/ftport/ftport-final.tgz (+ .md5): the workspace root without .lake/.lbe*/verify.sh, i.e. Challenge/Solution/
  Submission(.lean + Submission/), WorkspaceTest.lean, config.json, holes.json, lakefile.toml, lake-manifest.json,
  lean-toolchain, README.md, LICENSE-odd-order, PORT-NOTES.md, ftport-tools/ (the scripts used for the port).
