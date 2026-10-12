import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

open MeasureTheory

/-- The Fourier kernel `exp(I⟪p,x⟫)` appearing in `integral_mul_invFT`. -/
noncomputable def invFTKernel (p x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ p x : ℂ))

lemma norm_invFTKernel (p x : EuclideanSpace ℝ (Fin 3)) : ‖invFTKernel p x‖ = 1 := by
  rw [invFTKernel, Complex.norm_exp]
  simp

lemma continuous_invFTKernel_swap :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      invFTKernel z.2 z.1 := by
  simp only [invFTKernel]
  fun_prop

/-- The multiplication formula for the inverse Fourier transform: for `F c : L¹(ℝ³, ℂ)` the
double pairing `∫_x F x (∫_p c p e^{I⟪p,x⟫})` may be swapped into
`∫_p (∫_x F x e^{I⟪p,x⟫}) c p`, by Fubini applied to the jointly integrable
`(x,p) ↦ F x c p e^{I⟪p,x⟫}` (the kernel has modulus one and `⟪p,x⟫` is symmetric). -/
theorem integral_mul_invFT {F c : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hF : MeasureTheory.Integrable F) (hc : MeasureTheory.Integrable c) :
    (∫ x : EuclideanSpace ℝ (Fin 3), F x * (∫ p : EuclideanSpace ℝ (Fin 3),
        c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), F x * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) * c p := by
  classical
  show (∫ x : EuclideanSpace ℝ (Fin 3), F x * (∫ p : EuclideanSpace ℝ (Fin 3),
        c p * invFTKernel p x))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), F x * invFTKernel p x) * c p
  -- joint integrability of `(x,p) ↦ F x * c p * exp(I⟪p,x⟫)` on the product measure
  have hbase : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => F z.1 * c z.2)
      (volume.prod volume) := hF.mul_prod hc
  have hjoint : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        F z.1 * c z.2 * invFTKernel z.2 z.1)
      (volume.prod volume) :=
    hbase.mul_bdd continuous_invFTKernel_swap.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => le_of_eq (norm_invFTKernel z.2 z.1))
  have hL : (∫ x : EuclideanSpace ℝ (Fin 3),
        F x * (∫ p : EuclideanSpace ℝ (Fin 3), c p * invFTKernel p x))
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          ∫ p : EuclideanSpace ℝ (Fin 3), F x * c p * invFTKernel p x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hR : (∫ p : EuclideanSpace ℝ (Fin 3),
        (∫ x : EuclideanSpace ℝ (Fin 3), F x * invFTKernel p x) * c p)
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          ∫ x : EuclideanSpace ℝ (Fin 3), F x * c p * invFTKernel p x := by
    apply integral_congr_ae
    filter_upwards with p
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hL, hR]
  exact integral_integral_swap hjoint

end Work.BoseBoxFock.LatSym
