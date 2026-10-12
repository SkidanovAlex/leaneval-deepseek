import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxOrthDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integralStarEFunMul` — integration against a slab indicator

The normalised slab indicator `eFun ℓ N k` is real valued (its values are the real number
`V^{-1/2}` on the slab `eSlice ℓ N k` and `0` elsewhere), so `star (eFun ℓ N k x) = eFun ℓ N k x`
(`star_eFun`).  Consequently, for any `v`,

`star (eFun ℓ N k x) * v x = (eSlice ℓ N k).indicator (fun y => (V^{-1/2} : ℂ) * v y) x`

pointwise.  The right-hand side is an indicator function, so its integrability is exactly
integrability of `v` on the (finite-measure) slab, and its integral is the constant `V^{-1/2}`
times the integral of `v` over the slab.
-/

noncomputable section

open MeasureTheory Set

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock

theorem integralStarEFunMul (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N) (k : Fin N)
    (v : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (starRingEnd ℂ) (Work.BoseBoxFock.eFun ℓ N k x) * v x) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) ∧
    (∫ x, (starRingEnd ℂ) (Work.BoseBoxFock.eFun ℓ N k x) * v x) = ((Work.BoseBoxFock.slScale ℓ N : ℝ) : ℂ) * ∫ x in Work.BoseBoxFock.eSlice ℓ N k, v x := by
  classical
  have hmeas : MeasurableSet (eSlice ℓ N k) := measurableSet_eSlice ℓ N k
  have hfin : (volume : Measure ℝ³) (eSlice ℓ N k) ≠ ⊤ := by
    rw [volume_eSlice hℓ hN k]; exact ENNReal.ofReal_ne_top
  have hfinI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (eSlice ℓ N k)) :=
    isFiniteMeasure_restrict.2 hfin
  -- `v` is integrable on the finite-measure slab
  have hv_slice : IntegrableOn (fun x => ((slScale ℓ N : ℝ) : ℂ) * v x) (eSlice ℓ N k) volume :=
    ((hv.restrict (eSlice ℓ N k)).integrable (by norm_num)).const_mul _
  have hA : Integrable ((eSlice ℓ N k).indicator (fun y => ((slScale ℓ N : ℝ) : ℂ) * v y)) volume :=
    (integrable_indicator_iff hmeas).2 hv_slice
  -- pointwise identification with the slab indicator
  have hpt : ∀ x, (starRingEnd ℂ) (eFun ℓ N k x) * v x
      = (eSlice ℓ N k).indicator (fun y => ((slScale ℓ N : ℝ) : ℂ) * v y) x := by
    intro x
    rw [star_eFun]
    by_cases hx : x ∈ eSlice ℓ N k
    · rw [eFun_of_mem hx, Set.indicator_of_mem hx]
    · rw [eFun_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  refine ⟨?_, ?_⟩
  · exact hA.congr (Filter.Eventually.of_forall (fun x => (hpt x).symm))
  · rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_indicator hmeas, MeasureTheory.integral_const_mul]

end Work.BoseBoxFock
