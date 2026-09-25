import Mathlib
import Submission.Work.HilbertTowerCM.Defs
import Submission.Work.HilbertTowerCM.Tower
import Submission.Work.HilbertTowerCM.Reduction
import Submission.Work.HilbertTowerCM.cmWall_of_benchmark

/-!
# `Work.HilbertTowerCM.Main` -- the CM endgame over `Kc = ℚ(√-30030)`

This is the consumer-facing module of the area: it assembles

* the levels that the arithmetic input `Work.ClassFieldTower.InfiniteProTwoExtension Kc`
  (infinitude of the maximal unramified pro-`2` extension of `Kc`) supplies
  (`Work.HilbertTowerCM.exists_level_finrank_ge`: levels of unbounded `ℚ`-degree, unramified, of
  root discriminant `rootDiscr Kc`), with
* the three walls (`RealPartWall`, `CMLevelWall`, `HalfRealLevelWall`) and their reductions to
  `Work.CMRealSubfield.CMWall` and to the benchmark (`Work.HilbertTowerCM.Reduction`).

## The exact remaining obligation

The arithmetic input gives *levels*; what the CM endgame consumes is that those levels have a
**large real part** (or are **CM**).  In formulas, over `Kc`:

* `RealPartWall Kc` -- levels `L` with `[L⁺ : ℚ] ≥ N` (`L⁺ = NumberField.maximalRealSubfield L`);
  this is the weakest sufficient input, and `benchmark_of_realPartWall` turns it into the
  benchmark with the constant `rootDiscr Kc = √120120`;
* `CMLevelWall Kc` -- levels that are CM; these give `Work.CMRealSubfield.CMWall`
  (`cmWall_of_cmLevelWall`);
* `HalfRealLevelWall Kc` -- levels with `2 * [L⁺ : ℚ] ≥ [L : ℚ]` (true for CM levels).

`Work.HilbertTowerCM.Obstruction` records what we know about the passage from the arithmetic
input to those walls: the complex conjugation acts on the levels through the group
`Gal(L/Kc)`, and the maximal real subfield is the fixed field of the closed subgroup generated
by the conjugations.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Work.HilbertTowerCM

/-! ## 1. The unconditional content of the arithmetic input -/

/-- **The arithmetic input, unpacked.**  `InfiniteProTwoExtension Kc` gives unramified levels of
arbitrarily large `ℚ`-degree, each of root discriminant `rootDiscr Kc`.

This is everything that the infinitude statement supplies: it is a statement about the *degrees*
of the levels, not about their real parts. -/
theorem exists_level_finrank_ge_Kc (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (N : ℕ) : ∃ L : UnramifiedLevel ClassFieldTower.Kc, N ≤ Module.finrank ℚ L.L :=
  exists_level_finrank_ge h N

/-- The levels are totally complex (the base `Kc` is), so they are never totally real and the
CM condition `[L : L⁺] = 2` is a genuine extra requirement. -/
theorem level_isTotallyComplex_Kc (L : UnramifiedLevel ClassFieldTower.Kc) :
    IsTotallyComplex L.L :=
  L.isTotallyComplex

/-! ## 2. The three conditional endgames over `Kc` -/

/-- **The CM endgame over `Kc`.**  If, for every `N`, the unramified tower over `Kc` contains a
level which is **CM** of degree `≥ N`, then `Work.CMRealSubfield.CMWall` holds -- with the
constant `rootDiscr Kc`, no constant lost.  Combined with
`Work.CMRealSubfield.benchmark_of_cmWall` this is the route to the benchmark. -/
theorem cmWall_of_infiniteProTwoExtension_Kc_of_cmLevels
    (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (hcm : CMLevelWall ClassFieldTower.Kc) : CMRealSubfield.CMWall :=
  cmWall_of_cmLevelWall hcm

/-- The same, straight to the benchmark. -/
theorem benchmark_of_infiniteProTwoExtension_Kc_of_cmLevels
    (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (hcm : CMLevelWall ClassFieldTower.Kc) : CMRealSubfield.Benchmark :=
  benchmark_of_cmLevelWall hcm

/-- **The real-part endgame over `Kc`.**  If, for every `N`, the unramified tower over `Kc`
contains a level whose maximal real subfield has degree `≥ N`, then the benchmark holds with the
constant `rootDiscr Kc`.  No CM hypothesis is used: the witnesses are the (totally real) maximal
real subfields of the levels. -/
theorem benchmark_of_infiniteProTwoExtension_Kc_of_realPart
    (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (hreal : RealPartWall ClassFieldTower.Kc) : CMRealSubfield.Benchmark :=
  benchmark_of_realPartWall hreal

/-- The real-part endgame in root-discriminant form. -/
theorem rootDiscrBenchmark_of_infiniteProTwoExtension_Kc_of_realPart
    (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (hreal : RealPartWall ClassFieldTower.Kc) : CMRealSubfield.RootDiscrBenchmark :=
  rootDiscrBenchmark_of_realPartWall hreal

/-- **The half-real endgame over `Kc`** (the structurally weakest form, through
`Work.CMRealSubfield.benchmark_of_halfRealSubfieldWall`). -/
theorem benchmark_of_infiniteProTwoExtension_Kc_of_halfReal
    (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (hhalf : HalfRealLevelWall ClassFieldTower.Kc) : CMRealSubfield.Benchmark :=
  benchmark_of_halfRealLevelWall hhalf

/-- The CM-level wall is a half-real wall, so the CM endgame also produces the structurally
weakest hypothesis. -/
theorem halfRealLevelWall_of_infiniteProTwoExtension_Kc_of_cmLevels
    (h : ClassFieldTower.InfiniteProTwoExtension ClassFieldTower.Kc)
    (hcm : CMLevelWall ClassFieldTower.Kc) : HalfRealLevelWall ClassFieldTower.Kc :=
  halfRealLevelWall_of_cmLevelWall hcm

/-! ## 2'. `CMWall` is *equivalent* to the benchmark

`Work.CMRealSubfield.benchmark_of_cmWall` gives `CMWall → Benchmark`.  The converse is
`Work.HilbertTowerCM.cmWall_of_benchmark`: from a totally real family `K` of unbounded degree with
`|disc K| ≤ C ^ [K : ℚ]`, the fields `K(i)` are CM (quadratic over a totally real field, totally
complex) with `rootDiscr K(i) ≤ 2 * rootDiscr K`.  So the CM-witness formulation loses nothing — and,
conversely, **the "CM bridge" is not a structural weakening of the target**: any proof of it is a
proof of the benchmark (given `InfiniteProTwoExtension Kc`).  This is the precise sense in which
`Submission.NumberField.CMLevelsOfTower` is arithmetic, not structural.
-/

/-- **`CMWall` and the benchmark are equivalent.** -/
theorem cmWall_iff_benchmark : CMRealSubfield.CMWall ↔ CMRealSubfield.Benchmark :=
  ⟨CMRealSubfield.benchmark_of_cmWall, cmWall_of_benchmark⟩

/-! ## 3. The route in the vocabulary of the whole workspace -/

/-- The CM endgame also produces the bare weak wall `Submission.NumberField.BoundedRdTowerWall`
(the levels themselves, without any real-part or CM hypothesis, have constant root discriminant;
this is `Work.ClassFieldTower.boundedRdTowerWall_of_shafarevichKoch_witness`). -/
theorem boundedDiscrTowerWall_of_realPartWall_Kc
    (h : RealPartWall ClassFieldTower.Kc) :
    Submission.NumberField.BoundedDiscrTowerWall :=
  Submission.NumberField.boundedDiscrTowerWall_of_boundedRdTowerWall (by
    obtain ⟨C, hC, hfam⟩ := rootDiscrBenchmark_of_realPartWall h
    exact ⟨C, hC, fun N => by
      obtain ⟨d, hd, K, hF, hNF, -, hfin, hrd⟩ := hfam N
      exact ⟨d, hd, K, hF, hNF, hfin, hrd⟩⟩)

end Work.HilbertTowerCM
