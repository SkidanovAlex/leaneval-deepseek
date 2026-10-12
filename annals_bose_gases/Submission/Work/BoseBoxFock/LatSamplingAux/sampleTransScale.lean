import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.LatVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSamplingAux

open MeasureTheory

/-- Change of variables for the affine map `x ↦ z + ℓ • x` with `ℓ > 0` against Lebesgue measure
on `ℝ³`: the dilation contributes the Jacobian factor `(ℓ³)⁻¹`, the translation contributes
nothing (Lebesgue measure is translation invariant). -/
theorem integral_comp_add_smul {ℓ : ℝ} (hℓ : 0 < ℓ) (g : EuclideanSpace ℝ (Fin 3) → ℂ)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), g (z + ℓ • x))
      = (ℓ ^ 3 : ℂ)⁻¹ * ∫ y : EuclideanSpace ℝ (Fin 3), g y := by
  have h1 := Measure.integral_comp_smul_of_nonneg (μ := volume)
    (f := fun y : EuclideanSpace ℝ (Fin 3) => g (z + y)) ℓ (hR := hℓ.le)
  have h2 : (∫ x : EuclideanSpace ℝ (Fin 3), g (z + x)) = ∫ x, g x :=
    integral_add_left_eq_self g z
  rw [h1, h2, finrank_euclideanSpace, Fintype.card_fin]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem sampleTransScale {ℓ : ℝ} (hℓ : 0 < ℓ) (F : EuclideanSpace ℝ (Fin 3) → ℂ)
    (z : EuclideanSpace ℝ (Fin 3)) (m : Fin 3 → ℤ) :
    (∫ x : EuclideanSpace ℝ (Fin 3),
        F (z + ℓ • x) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m)))))
      = (ℓ ^ 3 : ℂ)⁻¹ *
        ((∫ y : EuclideanSpace ℝ (Fin 3),
            Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) y : ℂ))) * F y)
          * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ))) := by
  set k : EuclideanSpace ℝ (Fin 3) := (2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m with hk
  -- the exponent identity `e^{-2πi⟪x,l⟫} = e^{i⟪k,z⟫} · e^{-i⟪z+ℓx,k⟫}`
  have hex : ∀ x : EuclideanSpace ℝ (Fin 3),
      -(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m) : ℂ))
        = Complex.I * (inner ℝ k z : ℂ) + -(Complex.I * (inner ℝ (z + ℓ • x) k : ℂ)) := by
    intro x
    have hreal : inner ℝ (z + ℓ • x) k - inner ℝ k z
        = 2 * Real.pi * inner ℝ x (Work.BoseBoxFock.latVec m) := by
      rw [hk]
      simp only [inner_add_left, real_inner_smul_left, inner_smul_right]
      rw [real_inner_comm (Work.BoseBoxFock.latVec m) z]
      field_simp
      ring
    have h' : (inner ℝ (z + ℓ • x) k : ℂ)
        = (inner ℝ k z : ℂ) + 2 * (Real.pi : ℂ) * (inner ℝ x (Work.BoseBoxFock.latVec m) : ℂ) := by
      have : (inner ℝ (z + ℓ • x) k : ℂ) - inner ℝ k z
          = 2 * (Real.pi : ℂ) * inner ℝ x (Work.BoseBoxFock.latVec m) := by
        exact_mod_cast hreal
      linear_combination this
    rw [h']; ring
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      F (z + ℓ • x) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m))))
        = Complex.exp (Complex.I * (inner ℝ k z : ℂ)) *
          (F (z + ℓ • x) * Complex.exp (-(Complex.I * (inner ℝ (z + ℓ • x) k : ℂ)))) := by
    intro x
    rw [hex x, Complex.exp_add]
    ring
  -- symmetry of the real inner product in the Fourier factor
  have hsym : (∫ y, F y * Complex.exp (-(Complex.I * (inner ℝ y k : ℂ))))
      = ∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * F y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [real_inner_comm k y]
    ring
  calc (∫ x, F (z + ℓ • x) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (Work.BoseBoxFock.latVec m)))))
      = ∫ x, Complex.exp (Complex.I * (inner ℝ k z : ℂ)) *
            (F (z + ℓ • x) * Complex.exp (-(Complex.I * (inner ℝ (z + ℓ • x) k : ℂ)))) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = Complex.exp (Complex.I * (inner ℝ k z : ℂ)) *
          ∫ x, F (z + ℓ • x) * Complex.exp (-(Complex.I * (inner ℝ (z + ℓ • x) k : ℂ))) :=
          integral_const_mul _ _
    _ = Complex.exp (Complex.I * (inner ℝ k z : ℂ)) *
          ((ℓ ^ 3 : ℂ)⁻¹ * ∫ y, F y * Complex.exp (-(Complex.I * (inner ℝ y k : ℂ)))) := by
          rw [integral_comp_add_smul hℓ (fun y => F y * Complex.exp (-(Complex.I * (inner ℝ y k : ℂ)))) z]
    _ = (ℓ ^ 3 : ℂ)⁻¹ *
          ((∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * F y) *
            Complex.exp (Complex.I * (inner ℝ k z : ℂ))) := by
          rw [hsym]; ring

end Work.BoseBoxFock.LatSamplingAux
