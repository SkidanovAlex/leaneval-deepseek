import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxOrthDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.eFunMemLp` — the slab indicators are bounded and `L²`

The normalised slab indicator `eFun ℓ N k = V^{-1/2}·1_{eSlice ℓ N k}` is a constant
multiple of the indicator of the measurable set `eSlice ℓ N k`, whose volume is the
finite number `ℓ³/N` (`volume_eSlice`).  Hence it is bounded a.e. (`MemLp · ⊤`) and
square integrable (`MemLp · 2`), with the same proof for both exponents.
-/

noncomputable section

open MeasureTheory Set

namespace Work.BoseBoxFock

/-- The (unnormalised) indicator of a slab is `MemLp` for **every** exponent: it is the
indicator of a measurable set of finite volume. -/
private lemma memLp_eSlice_indicator {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 0 < N)
    (k : Fin N) (p : ENNReal) :
    MemLp ((eSlice ℓ N k).indicator (fun _ => (1 : ℂ))) p
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  classical
  have hν : volume (eSlice ℓ N k) ≠ ⊤ := by
    rw [volume_eSlice hℓ hN k]
    exact ENNReal.ofReal_ne_top
  exact memLp_indicator_const p (measurableSet_eSlice ℓ N k) (1 : ℂ) (Or.inr hν)

theorem eFunMemLp (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N) (k : Fin N) :
    MeasureTheory.MemLp (Work.BoseBoxFock.eFun ℓ N k) ⊤ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) ∧
    MeasureTheory.MemLp (Work.BoseBoxFock.eFun ℓ N k) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  exact ⟨(memLp_eSlice_indicator hℓ hN k ⊤).const_mul _,
    (memLp_eSlice_indicator hℓ hN k 2).const_mul _⟩

end Work.BoseBoxFock
