import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseDict

theorem cIPn_boxAnnOf_eq_prodInt {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (w : Fin m → ℝ)
    (Θ : Work.BoseDict.Xn (d + 1) → ℂ) (Θ' : Work.BoseDict.Xn d → ℂ)
    (hInt : MeasureTheory.Integrable (fun p : Work.BoseDict.Sp × Work.BoseDict.Xn d =>
      Work.BoseDict.etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2)) :
    Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e w d Θ) Θ'
      = (Real.sqrt ((d : ℝ) + 1) : ℂ) * ∫ p : Work.BoseDict.Sp × Work.BoseDict.Xn d,
          Work.BoseDict.etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2 := by
  classical
  -- Pointwise: the conjugation of the box annihilation, with the complex conjugation moved
  -- onto `Θ` (unconditional `integral_conj`, `√(d+1)` is a real number).
  have hstep : ∀ y : Xn d,
      (starRingEnd ℂ) (boxAnnOf e w d Θ y) * Θ' y
        = (Real.sqrt ((d : ℝ) + 1) : ℂ)
            * ((∫ z : Sp, etaOf e w z * (starRingEnd ℂ) (Θ (Fin.cons z y))) * Θ' y) := by
    intro y
    simp only [boxAnnOf]
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    simp only [map_mul, Complex.conj_conj]
    rw [mul_assoc]
  simp only [cIPn]
  calc ∫ y : Xn d, (starRingEnd ℂ) (boxAnnOf e w d Θ y) * Θ' y
      = ∫ y : Xn d, (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ((∫ z : Sp, etaOf e w z * (starRingEnd ℂ) (Θ (Fin.cons z y))) * Θ' y) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ∫ y : Xn d, (∫ z : Sp, etaOf e w z * (starRingEnd ℂ) (Θ (Fin.cons z y))) * Θ' y :=
        MeasureTheory.integral_const_mul _ _
    _ = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ∫ y : Xn d, ∫ z : Sp, etaOf e w z * (starRingEnd ℂ) (Θ (Fin.cons z y)) * Θ' y := by
        congr 1
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y =>
          (MeasureTheory.integral_mul_const (Θ' y)
            (fun z : Sp => etaOf e w z * (starRingEnd ℂ) (Θ (Fin.cons z y)))).symm)
    _ = (Real.sqrt ((d : ℝ) + 1) : ℂ)
          * ∫ p : Sp × Xn d,
              etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2 := by
        congr 1
        exact (MeasureTheory.integral_prod_symm (fun p : Sp × Xn d =>
          etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2) hInt).symm

end Work.BoseDict
