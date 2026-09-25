import Mathlib
import Submission.Work.HilbertTowerCM.Defs
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le
import Submission.Helpers

/-!
# `Work.HilbertTowerCM.Reduction` -- the walls imply the benchmark

This module assembles the three walls of `Work.HilbertTowerCM.Defs` with the reduction of
`Submission.Work.CMRealSubfield`, in the *sharp* constant `C = rootDiscr F` supplied by the
unramified tower over `F`.

* `benchmark_of_realPartWall` : `RealPartWall F → Benchmark`.  The witnesses are the **maximal
  real subfields** `L⁺` of the levels: they are totally real, have `[L⁺ : ℚ] ≥ N` by hypothesis,
  and `rootDiscr L⁺ ≤ rootDiscr L = rootDiscr F`.  No CM hypothesis is needed.
* `benchmark_of_halfRealLevelWall` : `HalfRealLevelWall F → Benchmark` (through
  `Work.CMRealSubfield.benchmark_of_halfRealSubfieldWall`).
* `cmWall_of_cmLevelWall`/`benchmark_of_cmLevelWall` : `CMLevelWall F → CMWall → Benchmark`.
* `cmWall_of_halfRealLevelWall` : the half-real form is equivalent to the CM form.

Everything here is a *reduction*: the arithmetic obligation of the endgame is to produce levels
satisfying one of the walls (see `Work.HilbertTowerCM.Tower` for the levels that an infinite
unramified pro-`2` extension supplies).
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Work.HilbertTowerCM

/-! ## 1. The real-part wall -/

/-- **The real-part wall implies the benchmark, with the constant `rootDiscr F`.**

For a level `L` with `[L⁺ : ℚ] ≥ N`, the witness for the benchmark is `L⁺`
(`NumberField.maximalRealSubfield L`): it is totally real, of degree `≥ N`, and
`rootDiscr L⁺ ≤ rootDiscr L = rootDiscr F`. -/
theorem benchmark_of_realPartWall {F : Type*} [Field F] [NumberField F] (h : RealPartWall F) :
    CMRealSubfield.Benchmark := by
  refine ⟨rootDiscr F, lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F),
    fun N => ?_⟩
  obtain ⟨L, hN⟩ := h N
  refine ⟨Module.finrank ℚ (UnramifiedLevel.realPart L), hN,
    UnramifiedLevel.realPart L, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
  exact Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl
    (UnramifiedLevel.realPart_rootDiscr_le L)

/-- `RootDiscrBenchmark` form of `benchmark_of_realPartWall`. -/
theorem rootDiscrBenchmark_of_realPartWall {F : Type*} [Field F] [NumberField F]
    (h : RealPartWall F) : CMRealSubfield.RootDiscrBenchmark := by
  refine ⟨rootDiscr F, lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F),
    fun N => ?_⟩
  obtain ⟨L, hN⟩ := h N
  refine ⟨Module.finrank ℚ (UnramifiedLevel.realPart L), hN,
    UnramifiedLevel.realPart L, inferInstance, inferInstance, inferInstance, rfl,
    UnramifiedLevel.realPart_rootDiscr_le L⟩

/-! ## 2. The CM-level wall -/

/-- **The CM-level wall gives `Work.CMRealSubfield.CMWall`**, with the constant `rootDiscr F`:
a CM level of degree `≥ N` has `rootDiscr = rootDiscr F`, so no constant is lost. -/
theorem cmWall_of_cmLevelWall {F : Type*} [Field F] [NumberField F] (h : CMLevelWall F) :
    CMRealSubfield.CMWall := by
  refine ⟨rootDiscr F, lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F),
    fun N => ?_⟩
  obtain ⟨L, hCM, hN⟩ := h N
  exact ⟨L.L, inferInstance, inferInstance, hCM, hN,
    Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl (le_of_eq L.rootDiscr_eq)⟩

/-- The CM-level wall implies the benchmark (via `Work.CMRealSubfield.benchmark_of_cmWall`). -/
theorem benchmark_of_cmLevelWall {F : Type*} [Field F] [NumberField F] (h : CMLevelWall F) :
    CMRealSubfield.Benchmark :=
  CMRealSubfield.benchmark_of_cmWall (cmWall_of_cmLevelWall h)

/-! ## 3. The half-real wall -/

/-- **The half-real level wall gives the half-degree-real-subfield wall** of
`Work.CMRealSubfield`: the levels themselves are the witnesses, with the constant `rootDiscr F`
and the half-degree hypothesis on the maximal real subfield. -/
theorem halfRealSubfieldWall_of_halfRealLevelWall {F : Type*} [Field F] [NumberField F]
    (h : HalfRealLevelWall F) : CMRealSubfield.HalfRealSubfieldWall := by
  refine ⟨rootDiscr F, lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F),
    fun N => ?_⟩
  obtain ⟨L, hN, hhalf⟩ := h N
  exact ⟨L.L, inferInstance, inferInstance, hN,
    Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl (le_of_eq L.rootDiscr_eq),
    hhalf⟩

/-- **The half-real level wall implies the benchmark** (`Work.CMRealSubfield`), with the constant
`rootDiscr F`. -/
theorem benchmark_of_halfRealLevelWall {F : Type*} [Field F] [NumberField F]
    (h : HalfRealLevelWall F) : CMRealSubfield.Benchmark :=
  CMRealSubfield.benchmark_of_halfRealSubfieldWall (halfRealSubfieldWall_of_halfRealLevelWall h)

/-! ## 4. Relation between the walls -/

/-- **CM levels have unbounded real parts**: a CM level `L` of degree `≥ 2N` has
`[L⁺ : ℚ] = [L : ℚ]/2 ≥ N` (`[L : L⁺] = 2` for a CM field).  So `CMLevelWall` is the strongest of
the three walls, and it also feeds the CM-free reduction `benchmark_of_realPartWall`. -/
theorem realPartWall_of_cmLevelWall {F : Type*} [Field F] [NumberField F] (h : CMLevelWall F) :
    RealPartWall F := by
  intro N
  obtain ⟨L, hCM, hdeg⟩ := h (2 * N)
  refine ⟨L, ?_⟩
  haveI := hCM
  have h2 : Module.finrank ℚ L.L = 2 * Module.finrank ℚ (UnramifiedLevel.realPart L) :=
    CMRealSubfield.RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield L.L
  show N ≤ Module.finrank ℚ (UnramifiedLevel.realPart L)
  omega

/-- The CM-level wall is the strongest of the three: a CM level is half-real.  The converse does
**not** hold: `HalfRealLevelWall` only asks for `2 * [L⁺ : ℚ] ≥ [L : ℚ]`, which is strictly
weaker than the CM condition `[L : L⁺] = 2`; see
`Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank`. -/
theorem halfRealLevelWall_of_cmLevelWall' {F : Type*} [Field F] [NumberField F]
    (h : CMLevelWall F) : HalfRealLevelWall F := halfRealLevelWall_of_cmLevelWall h

/-- **A level is CM iff it is totally complex with real part of exactly half the degree** (the
criterion `of_forall_isConj` of `Work.CMRealSubfield.CMBasic` supplies the CM-ness of a level once
a single involution is exhibited as the complex conjugation at every complex place). -/
theorem cmLevelWall_of_halfRealLevelWall_of_totallyComplex {F : Type*} [Field F] [NumberField F]
    [IsTotallyComplex F]
    (h : HalfRealLevelWall F)
    (hhex : ∀ N : ℕ, ∃ L : UnramifiedLevel F, 2 * Module.finrank ℚ (UnramifiedLevel.realPart L)
      = Module.finrank ℚ L.L ∧ N ≤ Module.finrank ℚ L.L) : CMLevelWall F := by
  intro N
  obtain ⟨L, hhalf, hN⟩ := hhex N
  haveI : IsTotallyComplex L.L := L.isTotallyComplex
  exact ⟨L, (isCMField_iff_realPart_half L).mpr ⟨inferInstance, hhalf.symm⟩, hN⟩

end Work.HilbertTowerCM
