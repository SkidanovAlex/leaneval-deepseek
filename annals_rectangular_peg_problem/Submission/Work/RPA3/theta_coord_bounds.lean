import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.contDiff_thetaP

/-!
# Boundedness of the coordinates of the tubular map `θ` on a compact strip

For `τ` in the compact interval `[-1,2]`, `|x| ≤ X`, `t ∈ [0,2π]` and `‖ξ‖ ≤ R` the tubular
parametrisation
`θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ(τ)(x,t) + ξ₂ ∂_tℓ(τ)(x,t))`
is bounded: the family term is a continuous image of a compact set, and the two slice
derivatives `∂_xℓ`, `∂_tℓ` are `C⁷` (`contDiff_sliceDerivX`, `contDiff_sliceDerivT`), hence
bounded on the same compact set; `J` is an isometry (`norm_J`) and `|ξ_i| ≤ ‖ξ‖ ≤ R`.

Both coordinate bounds of `theta_coord_bounds` follow from the single norm bound
`‖θ(τ,x,t,ξ)‖ ≤ M`, since `|w.1.1| ≤ ‖w‖` and `|w.1.2| ≤ ‖w‖` for `w : PS`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- `J(q,p) = (p,-q)` preserves the (max) norm. -/
lemma norm_J (v : PS) : ‖J v‖ = ‖v‖ := by
  have h : J v = (v.2, -v.1) := rfl
  rw [h, Prod.norm_def, Prod.norm_def, norm_neg]
  exact (max_comm _ _).symm

/-- The first coordinate of a point of the phase space is bounded by its norm. -/
lemma abs_fst_fst_le_norm (w : PS) : |w.1.1| ≤ ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

/-- The second coordinate of a point of the phase space is bounded by its norm. -/
lemma abs_fst_snd_le_norm (w : PS) : |w.1.2| ≤ ‖w‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The first coordinate of `ξ : ℝ × ℝ` is bounded by `‖ξ‖`. -/
lemma abs_fst_le_norm (ξ : ℝ × ℝ) : |ξ.1| ≤ ‖ξ‖ := by
  rw [Prod.norm_def]; exact le_max_left _ _

/-- The second coordinate of `ξ : ℝ × ℝ` is bounded by `‖ξ‖`. -/
lemma abs_snd_le_norm (ξ : ℝ × ℝ) : |ξ.2| ≤ ‖ξ‖ := by
  rw [Prod.norm_def]; exact le_max_right _ _

theorem theta_coord_bounds (L : Work.RPA3.LagFamilyAll) {X R : ℝ} (hX : 0 ≤ X) (hR : 0 ≤ R) :
    (∃ M : ℝ, ∀ τ x t (ξ : ℝ × ℝ), τ ∈ Set.Icc (-1 : ℝ) 2 → |x| ≤ X →
      t ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ ≤ R → |(Work.RPA3.theta L τ x t ξ).1.1| ≤ M) ∧
    (∃ M : ℝ, ∀ τ x t (ξ : ℝ × ℝ), τ ∈ Set.Icc (-1 : ℝ) 2 → |x| ≤ X →
      t ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ ≤ R → |(Work.RPA3.theta L τ x t ξ).1.2| ≤ M) := by
  have hK : IsCompact (Set.Icc (-1 : ℝ) 2 ×ˢ (Set.Icc (-X) X ×ˢ Set.Icc 0 (2 * Real.pi))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn (L.smooth.continuous.continuousOn)
  obtain ⟨M1, hM1⟩ :=
    hK.exists_bound_of_continuousOn ((contDiff_sliceDerivX L).continuous.continuousOn)
  obtain ⟨M2, hM2⟩ :=
    hK.exists_bound_of_continuousOn ((contDiff_sliceDerivT L).continuous.continuousOn)
  let M : ℝ := max M0 0 + (R * max M1 0 + R * max M2 0)
  have hMain : ∀ τ x t (ξ : ℝ × ℝ), τ ∈ Set.Icc (-1 : ℝ) 2 → |x| ≤ X →
      t ∈ Set.Icc 0 (2 * Real.pi) → ‖ξ‖ ≤ R → ‖theta L τ x t ξ‖ ≤ M := by
    intro τ x t ξ hτ hx ht hξ
    have hw : (τ, (x, t)) ∈
        Set.Icc (-1 : ℝ) 2 ×ˢ (Set.Icc (-X) X ×ˢ Set.Icc 0 (2 * Real.pi)) := by
      refine ⟨hτ, ?_, ht⟩
      exact ⟨by linarith [neg_abs_le x, hx], by linarith [le_abs_self x, hx]⟩
    have hb0 : ‖L.ℓ τ (x, t)‖ ≤ M0 := hM0 (τ, (x, t)) hw
    have hb1 : ‖deriv (fun y => L.ℓ τ (y, t)) x‖ ≤ M1 := hM1 (τ, (x, t)) hw
    have hb2 : ‖deriv (fun s => L.ℓ τ (x, s)) t‖ ≤ M2 := hM2 (τ, (x, t)) hw
    have hA : ‖L.ℓ τ (x, t)‖ ≤ max M0 0 := le_trans hb0 (le_max_left _ _)
    have hB : ‖deriv (fun y => L.ℓ τ (y, t)) x‖ ≤ max M1 0 := le_trans hb1 (le_max_left _ _)
    have hC : ‖deriv (fun s => L.ℓ τ (x, s)) t‖ ≤ max M2 0 := le_trans hb2 (le_max_left _ _)
    have hB0 : (0 : ℝ) ≤ max M1 0 := le_max_right _ _
    have hC0 : (0 : ℝ) ≤ max M2 0 := le_max_right _ _
    show ‖L.ℓ τ (x, t) + J (ξ.1 • deriv (fun y => L.ℓ τ (y, t)) x +
        ξ.2 • deriv (fun s => L.ℓ τ (x, s)) t)‖ ≤ M
    calc ‖L.ℓ τ (x, t) + J (ξ.1 • deriv (fun y => L.ℓ τ (y, t)) x +
            ξ.2 • deriv (fun s => L.ℓ τ (x, s)) t)‖
        ≤ ‖L.ℓ τ (x, t)‖ +
            ‖J (ξ.1 • deriv (fun y => L.ℓ τ (y, t)) x +
              ξ.2 • deriv (fun s => L.ℓ τ (x, s)) t)‖ := norm_add_le _ _
      _ = ‖L.ℓ τ (x, t)‖ +
            ‖ξ.1 • deriv (fun y => L.ℓ τ (y, t)) x +
              ξ.2 • deriv (fun s => L.ℓ τ (x, s)) t‖ := by rw [norm_J]
      _ ≤ max M0 0 + (|ξ.1| * max M1 0 + |ξ.2| * max M2 0) := by
            refine add_le_add hA ?_
            refine le_trans (norm_add_le _ _) ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            exact add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hC (abs_nonneg _))
      _ ≤ max M0 0 + (R * max M1 0 + R * max M2 0) := by
            refine add_le_add le_rfl (add_le_add ?_ ?_)
            · exact mul_le_mul_of_nonneg_right (le_trans (abs_fst_le_norm ξ) hξ) hB0
            · exact mul_le_mul_of_nonneg_right (le_trans (abs_snd_le_norm ξ) hξ) hC0
  exact ⟨⟨M, fun τ x t ξ hτ hx ht hξ =>
      le_trans (abs_fst_fst_le_norm (theta L τ x t ξ)) (hMain τ x t ξ hτ hx ht hξ)⟩,
    ⟨M, fun τ x t ξ hτ hx ht hξ =>
      le_trans (abs_fst_snd_le_norm (theta L τ x t ξ)) (hMain τ x t ξ hτ hx ht hξ)⟩⟩

end Work.RPA3
