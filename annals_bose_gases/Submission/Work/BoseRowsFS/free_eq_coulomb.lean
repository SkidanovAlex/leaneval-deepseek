import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.Rb5Lin.chat_sq_div_integral_eq_coulomb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open MeasureTheory

/-- **Fubini for the pair (Coulomb) integrand.**  If the pair function
`(x,y) ↦ W x * W y / ‖x - y‖` is integrable on the product `ℝ³ × ℝ³`, then its product-measure
Bochner integral is the iterated one.  (The Lebesgue measure on `EuclideanSpace ℝ (Fin 3) ×
EuclideanSpace ℝ (Fin 3)` is the product measure by the `MeasureSpace` instance, so
`MeasureTheory.integral_prod` applies directly.) -/
lemma coulomb_integral_prod_eq_iterated {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcd : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W p.1 * W p.2 / ‖p.1 - p.2‖)) :
    (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), W p.1 * W p.2 / ‖p.1 - p.2‖)
      = ∫ x, ∫ y, W x * W y / ‖x - y‖ :=
  MeasureTheory.integral_prod _ hcd

theorem free_eq_coulomb {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hcd : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W p.1 * W p.2 / ‖p.1 - p.2‖)) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p, Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2))
      = (1 / (8 * Real.pi)) * (∫ x, ∫ y, W x * W y / ‖x - y‖) := by
  -- the Fourier–Coulomb identity, with the position-space double integral as an iterated `∫⁻`
  rw [Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal hW hW0 hWe]
  congr 1
  -- `.toReal` of the iterated `∫⁻` is the product Bochner integral (a.e. nonnegativity of `W`)
  rw [← Work.BoseFixR.Rb5Lin.integral_coulomb_eq_toReal_lintegral hW hW0]
  -- and that product integral is the iterated one (Fubini, using the hypothesis `hcd`)
  exact coulomb_integral_prod_eq_iterated hcd

end Work.BoseRowsFS
