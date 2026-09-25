import Mathlib
import Submission.Work.HilbertTowerCM.Defs
import Submission.Work.HilbertTowerCM.Reduction
import Submission.Work.HilbertTowerCM.cmWall_of_benchmark
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces
import Submission.Work.CMRealSubfield.RealSubfield.finrank_maximalRealSubfield_eq_finrank_of_isTotallyReal

/-!
# `Work.HilbertTowerCM.TotallyRealBase` -- why the `RealPartWall` is the right wall

The CM endgame of `Work.HilbertTowerCM` consumes the `RealPartWall`: levels whose maximal real
subfield has unbounded degree.  This module records the situation in which that wall is *automatic*,
namely the route that is actually on the proof path of this workspace: a **totally real base**
(`NumberField.IsTotallyReal F`) whose levels are unramified also at the infinite places.  There the
levels are themselves totally real
(`Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces`), so a level is
its own maximal real subfield,

  `[L⁺ : ℚ] = [L : ℚ]`,

and a family of levels of unbounded degree gives `RealPartWall F` — hence the benchmark, by the
CM-free reduction `Work.HilbertTowerCM.benchmark_of_realPartWall`.

This is the structural reason why the tame tower over a totally real base
(`Submission.NumberField.MartinetTameWall`) needs no CM input at all, while the unramified tower
over the imaginary quadratic field `Kc` — whose levels are totally complex — does.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Work.HilbertTowerCM

/-- **A level is its own real part if the base is totally real and the level is unramified at the
infinite places.** -/
theorem realPart_finrank_eq_finrank_of_totallyReal {F : Type*} [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] (L : UnramifiedLevel F)
    (hunr : IsUnramifiedAtInfinitePlaces F L.L) :
    UnramifiedLevel.realPart_finrank L = Module.finrank ℚ L.L := by
  haveI : IsTotallyReal L.L :=
    Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces F L.L
  exact Work.CMRealSubfield.RealSubfield.finrank_maximalRealSubfield_eq_finrank_of_isTotallyReal L.L

/-- **The `RealPartWall` from a totally real base.**  If `F` is totally real and has unramified
(in the sense of `differentIdeal = ⊤`) levels of unbounded degree which are in addition unramified
at the infinite places, then `RealPartWall F` holds, hence the benchmark with constant
`rootDiscr F` (`Work.HilbertTowerCM.benchmark_of_realPartWall`). -/
theorem realPartWall_of_totallyReal_base {F : Type*} [Field F] [NumberField F]
    [NumberField.IsTotallyReal F]
    (h : ∀ N : ℕ, ∃ L : UnramifiedLevel F,
      IsUnramifiedAtInfinitePlaces F L.L ∧ N ≤ Module.finrank ℚ L.L) :
    RealPartWall F := by
  intro N
  obtain ⟨L, hunr, hdeg⟩ := h N
  refine ⟨L, ?_⟩
  rw [show UnramifiedLevel.realPart_finrank L = Module.finrank ℚ L.L from
    realPart_finrank_eq_finrank_of_totallyReal L hunr]
  exact hdeg

/-- The same, straight to the benchmark. -/
theorem benchmark_of_totallyReal_base {F : Type*} [Field F] [NumberField F]
    [NumberField.IsTotallyReal F]
    (h : ∀ N : ℕ, ∃ L : UnramifiedLevel F,
      IsUnramifiedAtInfinitePlaces F L.L ∧ N ≤ Module.finrank ℚ L.L) :
    CMRealSubfield.Benchmark :=
  benchmark_of_realPartWall (realPartWall_of_totallyReal_base h)

/-- **A genuine source of CM levels of unbounded degree.**  A totally real base with levels of
unbounded degree unramified at the infinite places gives the benchmark by the CM-free
`benchmark_of_totallyReal_base`, hence `Work.CMRealSubfield.CMWall` by `cmWall_of_benchmark`
(the fields `K(i)`).  This is the way to *discharge* the CM-witness endgame: the CM input has to
come from a totally real (tame) tower, not from the levels of `Kc_∅`. -/
theorem cmWall_of_totallyReal_base {F : Type*} [Field F] [NumberField F]
    [NumberField.IsTotallyReal F]
    (h : ∀ N : ℕ, ∃ L : UnramifiedLevel F,
      IsUnramifiedAtInfinitePlaces F L.L ∧ N ≤ Module.finrank ℚ L.L) :
    CMRealSubfield.CMWall :=
  cmWall_of_benchmark (benchmark_of_totallyReal_base h)

end Work.HilbertTowerCM
