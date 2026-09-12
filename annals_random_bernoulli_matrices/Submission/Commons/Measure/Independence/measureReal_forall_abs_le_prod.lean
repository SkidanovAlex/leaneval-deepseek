import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.BigOperators

namespace Commons.Measure.Independence

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Independence + small-ball bounds give a product bound for the probability that all the
coordinates `ξ i` are simultaneously small. -/
theorem measureReal_forall_abs_le_prod {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Fin m → Ω → ℝ} (hξ : iIndepFun ξ P)
    {η τ : Fin m → ℝ} (hτ : ∀ i, 0 ≤ τ i)
    (hsmall : ∀ i : Fin m, P.real {x | |ξ i x| ≤ η i} ≤ τ i) :
    P.real {x | ∀ i : Fin m, |ξ i x| ≤ η i} ≤ ∏ i, τ i := by
  classical
  let A : Fin m → Set Ω := fun i => {x | |ξ i x| ≤ η i}
  have hA_meas : ∀ i : Fin m,
      MeasurableSet[(inferInstance : MeasurableSpace ℝ).comap (ξ i)] (A i) := by
    intro i
    dsimp [A]
    rw [show {x | |ξ i x| ≤ η i} = (ξ i) ⁻¹' (Set.Icc (-η i) (η i)) by
      ext x
      simp [abs_le]]
    exact (MeasurableSpace.measurableSet_comap
      (m := (inferInstance : MeasurableSpace ℝ))
      (s := (ξ i) ⁻¹' (Set.Icc (-η i) (η i)))).2
        ⟨Set.Icc (-η i) (η i), measurableSet_Icc, rfl⟩
  have hset : {x | ∀ i : Fin m, |ξ i x| ≤ η i} = ⋂ i, A i := by
    ext x
    simp [A]
  have hprod : P (⋂ i, A i) = ∏ i, P (A i) :=
    hξ.meas_iInter (fun i => hA_meas i)
  calc
    P.real {x | ∀ i : Fin m, |ξ i x| ≤ η i} = P.real (⋂ i, A i) := by rw [hset]
    _ = (P (⋂ i, A i)).toReal := rfl
    _ = (∏ i, P (A i)).toReal := by rw [hprod]
    _ = ∏ i, (P (A i)).toReal := by rw [ENNReal.toReal_prod]
    _ ≤ ∏ i, τ i := by
      refine Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => ?_)
      exact hsmall i

end Commons.Measure.Independence
