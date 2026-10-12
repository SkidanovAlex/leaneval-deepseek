import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Submission.ChiWitness
import Submission.ConvChiBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

theorem chiScale_iteratedFDeriv_le (G : ℕ → ℝ)
    (hG : ∀ k (x : EuclideanSpace ℝ (Fin 3)),
      ‖iteratedFDeriv ℝ k Submission.BoseGases.chi x‖ ≤ G k)
    (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (∀ k (y : EuclideanSpace ℝ (Fin 3)),
        ‖iteratedFDeriv ℝ k (Submission.BoseGases.chiScale ℓ) y‖ ≤ (ℓ⁻¹) ^ k * G k) ∧
    (∀ k (z y : EuclideanSpace ℝ (Fin 3)),
        ‖iteratedFDeriv ℝ k (fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale ℓ (y + z)) y‖ ≤ (ℓ⁻¹) ^ k * G k) := by
  -- `chiScale ℓ = chi ∘ L` with `L = ℓ⁻¹ • 1` the linear map `x ↦ ℓ⁻¹ • x`.
  set L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := (ℓ⁻¹) • 1 with hLdef
  have hLx : ∀ x : EuclideanSpace ℝ (Fin 3), L x = (ℓ⁻¹) • x := by
    intro x
    rw [hLdef]
    simp
  -- operator norm of the scaling map
  have hLn : ‖L‖ ≤ ℓ⁻¹ := by
    rw [hLdef, norm_smul, norm_one, mul_one]
    exact le_of_eq (by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)])
  have hcomp : Submission.BoseGases.chiScale ℓ = Submission.BoseGases.chi ∘ L := by
    funext x
    simp only [Function.comp_apply, Submission.BoseGases.chiScale, hLx]
  -- `G k` is nonnegative, being an upper bound for a norm
  have hGnn : ∀ k, 0 ≤ G k := fun k =>
    (norm_nonneg (iteratedFDeriv ℝ k Submission.BoseGases.chi
      (0 : EuclideanSpace ℝ (Fin 3)))).trans (hG k 0)
  have h1 : ∀ k (y : EuclideanSpace ℝ (Fin 3)),
      ‖iteratedFDeriv ℝ k (Submission.BoseGases.chiScale ℓ) y‖ ≤ (ℓ⁻¹) ^ k * G k := by
    intro k y
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right L
      Submission.BoseGases.chi_contDiff y (WithTop.coe_le_coe.mpr le_top)]
    calc ‖(iteratedFDeriv ℝ k Submission.BoseGases.chi (L y)).compContinuousLinearMap
            (fun _ => L)‖
        ≤ ‖iteratedFDeriv ℝ k Submission.BoseGases.chi (L y)‖ * ∏ _ : Fin k, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ k Submission.BoseGases.chi (L y)‖ * ‖L‖ ^ k := by simp
      _ ≤ G k * (ℓ⁻¹) ^ k :=
          mul_le_mul (hG k (L y)) (pow_le_pow_left₀ (norm_nonneg L) hLn k)
            (by positivity) (hGnn k)
      _ = (ℓ⁻¹) ^ k * G k := mul_comm _ _
  refine ⟨h1, ?_⟩
  -- the shifted function: the iterated derivative is just shifted in the argument
  intro k z y
  rw [iteratedFDeriv_comp_add_right k z y]
  exact h1 k (y + z)

end Work.BoseFixB3.CS.Pieces
