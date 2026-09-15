import Submission.FUP.Dbar
import Submission.Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg

open MeasureTheory

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The weighted integration by parts for `∂̄` and the formal adjoint

For a weight `ψ : ℂᵈ → ℂ` and smooth compactly supported `F, G : ℂᵈ → ℂ`,

  `∫ (∂̄_j F) · G · e^{-ψ} = - ∫ F · (∂̄_j G) · e^{-ψ} + ∫ F · G · (∂̄_j ψ) · e^{-ψ}`.

Iterating this over `j` gives the identity expressing that
`ϑ_ψ u = -∑_j (∂_j u_j - u_j ∂_j ψ)` is the formal adjoint of `∂̄` with respect to the weighted
inner product `⟨f, u⟩_ψ = ∫ ∑_j f (z) conj (u z j) e^{-ψ z}`:

  `∫ (∑_j (∂̄_j g) conj (u_j)) e^{-ψ} = ∫ g conj (ϑ_ψ u) e^{-ψ}`.
-/

namespace Submission.FUP

/-- **Weighted integration by parts for `∂̄_j`.** -/
theorem integral_dbar_mul_weighted_eq_neg {F G ψ : ℂᵈ → ℂ} (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G) (hψ : ContDiff ℝ 1 ψ) (hsF : HasCompactSupport F)
    (hsG : HasCompactSupport G) (j : Fin d) :
    (∫ z, partialZbar j F z * G z * Complex.exp (-(ψ z)))
      = - (∫ z, F z * partialZbar j G z * Complex.exp (-(ψ z)))
        + (∫ z, F z * G z * partialZbar j ψ z * Complex.exp (-(ψ z))) := by
  have hexp : Continuous (fun z : ℂᵈ => Complex.exp (-(ψ z))) :=
    Complex.continuous_exp.comp hψ.continuous.neg
  have hFd1 : Continuous (fun z : ℂᵈ => fderiv ℝ F z (Pi.single j (1 : ℂ))) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hFd2 : Continuous (fun z : ℂᵈ => fderiv ℝ F z (Pi.single j Complex.I)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hGd1 : Continuous (fun z : ℂᵈ => fderiv ℝ G z (Pi.single j (1 : ℂ))) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hGd2 : Continuous (fun z : ℂᵈ => fderiv ℝ G z (Pi.single j Complex.I)) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψd1 : Continuous (fun z : ℂᵈ => fderiv ℝ ψ z (Pi.single j (1 : ℂ))) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψd2 : Continuous (fun z : ℂᵈ => fderiv ℝ ψ z (Pi.single j Complex.I)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hA1 : Integrable (fun z : ℂᵈ =>
      fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z))) :=
    ((hFd1.mul hG.continuous).mul hexp).integrable_of_hasCompactSupport
      ((hsG.mul_left (f := fun z => fderiv ℝ F z (Pi.single j (1 : ℂ)))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have hA2 : Integrable (fun z : ℂᵈ =>
      fderiv ℝ F z (Pi.single j Complex.I) * G z * Complex.exp (-(ψ z))) :=
    ((hFd2.mul hG.continuous).mul hexp).integrable_of_hasCompactSupport
      ((hsG.mul_left (f := fun z => fderiv ℝ F z (Pi.single j Complex.I))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have hB1 : Integrable (fun z : ℂᵈ =>
      F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) :=
    ((hF.continuous.mul hGd1).mul hexp).integrable_of_hasCompactSupport
      ((hsF.mul_right (f' := fun z => fderiv ℝ G z (Pi.single j (1 : ℂ)))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have hB2 : Integrable (fun z : ℂᵈ =>
      F z * fderiv ℝ G z (Pi.single j Complex.I) * Complex.exp (-(ψ z))) :=
    ((hF.continuous.mul hGd2).mul hexp).integrable_of_hasCompactSupport
      ((hsF.mul_right (f' := fun z => fderiv ℝ G z (Pi.single j Complex.I))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have hC1 : Integrable (fun z : ℂᵈ =>
      F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) :=
    (((hF.continuous.mul hG.continuous).mul hψd1).mul hexp).integrable_of_hasCompactSupport
      (((hsF.mul_right (f' := G)).mul_right
        (f' := fun z => fderiv ℝ ψ z (Pi.single j (1 : ℂ)))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have hC2 : Integrable (fun z : ℂᵈ =>
      F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I) * Complex.exp (-(ψ z))) :=
    (((hF.continuous.mul hG.continuous).mul hψd2).mul hexp).integrable_of_hasCompactSupport
      (((hsF.mul_right (f' := G)).mul_right
        (f' := fun z => fderiv ℝ ψ z (Pi.single j Complex.I))).mul_right
        (f' := fun z => Complex.exp (-(ψ z))))
  have h1 := Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg (F := F) (G := G)
    (φ := ψ) hF hG hψ hsF hsG (Pi.single j (1 : ℂ))
  have h2 := Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg (F := F) (G := G)
    (φ := ψ) hF hG hψ hsF hsG (Pi.single j Complex.I)
  have hpt : ∀ z : ℂᵈ, partialZbar j F z * G z * Complex.exp (-(ψ z))
      = ((fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z)))
          + Complex.I * (fderiv ℝ F z (Pi.single j Complex.I) * G z
            * Complex.exp (-(ψ z)))) / 2 := by
    intro z; rw [partialZbar]; ring
  have hpt2 : ∀ z : ℂᵈ, F z * partialZbar j G z * Complex.exp (-(ψ z))
      = ((F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z)))
          + Complex.I * (F z * fderiv ℝ G z (Pi.single j Complex.I)
            * Complex.exp (-(ψ z)))) / 2 := by
    intro z; rw [partialZbar]; ring
  have hpt3 : ∀ z : ℂᵈ, F z * G z * partialZbar j ψ z * Complex.exp (-(ψ z))
      = ((F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z)))
          + Complex.I * (F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
            * Complex.exp (-(ψ z)))) / 2 := by
    intro z; rw [partialZbar]; ring
  have key1 : (∫ z, ((fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z)))
        + Complex.I * (fderiv ℝ F z (Pi.single j Complex.I) * G z
          * Complex.exp (-(ψ z)))) / 2)
      = (∫ z, fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z))) / 2
        + Complex.I * ((∫ z, fderiv ℝ F z (Pi.single j Complex.I) * G z
          * Complex.exp (-(ψ z))) / 2) := by
    rw [integral_div, integral_add hA1 (hA2.const_mul Complex.I), integral_const_mul]
    ring
  have key2 : (∫ z, F z * partialZbar j G z * Complex.exp (-(ψ z)))
      = (∫ z, F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) / 2
        + Complex.I * ((∫ z, F z * fderiv ℝ G z (Pi.single j Complex.I)
          * Complex.exp (-(ψ z))) / 2) := by
    rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpt2),
      integral_div, integral_add hB1 (hB2.const_mul Complex.I), integral_const_mul]
    ring
  have key3 : (∫ z, F z * G z * partialZbar j ψ z * Complex.exp (-(ψ z)))
      = (∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) / 2
        + Complex.I * ((∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
          * Complex.exp (-(ψ z))) / 2) := by
    rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpt3),
      integral_div, integral_add hC1 (hC2.const_mul Complex.I), integral_const_mul]
    ring
  calc (∫ z, partialZbar j F z * G z * Complex.exp (-(ψ z)))
      = ∫ z, ((fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z)))
          + Complex.I * (fderiv ℝ F z (Pi.single j Complex.I) * G z
            * Complex.exp (-(ψ z)))) / 2 :=
        integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpt)
    _ = (∫ z, fderiv ℝ F z (Pi.single j (1 : ℂ)) * G z * Complex.exp (-(ψ z))) / 2
        + Complex.I * ((∫ z, fderiv ℝ F z (Pi.single j Complex.I) * G z
          * Complex.exp (-(ψ z))) / 2) := key1
    _ = (-(∫ z, F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z)))
          + ∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ))
            * Complex.exp (-(ψ z))) / 2
        + Complex.I * ((-(∫ z, F z * fderiv ℝ G z (Pi.single j Complex.I)
              * Complex.exp (-(ψ z)))
          + ∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
            * Complex.exp (-(ψ z))) / 2) := by
        rw [h1, h2]
    _ = - ((∫ z, F z * fderiv ℝ G z (Pi.single j (1 : ℂ)) * Complex.exp (-(ψ z))) / 2
            + Complex.I * ((∫ z, F z * fderiv ℝ G z (Pi.single j Complex.I)
              * Complex.exp (-(ψ z))) / 2))
        + ((∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j (1 : ℂ))
              * Complex.exp (-(ψ z))) / 2
            + Complex.I * ((∫ z, F z * G z * fderiv ℝ ψ z (Pi.single j Complex.I)
              * Complex.exp (-(ψ z))) / 2)) := by
        ring
    _ = - (∫ z, F z * partialZbar j G z * Complex.exp (-(ψ z)))
        + (∫ z, F z * G z * partialZbar j ψ z * Complex.exp (-(ψ z))) := by
        rw [← key2, ← key3]


end Submission.FUP
