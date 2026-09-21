import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Geometry.Ulam

open scoped Pointwise RealInnerProductSpace

set_option autoImplicit false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

lemma isCompact_body_of_revolution [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (-R₁) R₂)) :
    IsCompact {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} := by
  let S : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ (f (x 0))^2}
  have hS_closed : IsClosed S := by
    let A : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂}
    let g : ℝᵈ → ℝ := fun x => (∑ i > 0, (x i)^2) - (f (x 0))^2
    have hA_closed : IsClosed A := by
      dsimp [A]
      exact isClosed_Icc.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) (i := 0))
    have hg_cont : ContinuousOn g A := by
      dsimp [g, A]
      have hsum_cont : Continuous (fun x : ℝᵈ => ∑ i > 0, (x i)^2) := by
        refine continuous_finsetSum (Finset.Ioi (0 : Fin d)) ?_
        intro i hi
        fun_prop
      have hsum : ContinuousOn (fun x : ℝᵈ => ∑ i > 0, (x i)^2)
          {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂} := hsum_cont.continuousOn
      have hf2 : ContinuousOn (fun x : ℝᵈ => (f (x 0))^2)
          {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂} := by
        have hfcomp : ContinuousOn (fun x : ℝᵈ => f (x 0))
            {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂} := by
          apply hf_cont.comp
          · exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) (i := 0)).continuousOn
          · intro x hx; exact hx
        have hsq : ContinuousOn (fun x : ℝᵈ => f (x 0) * f (x 0))
            {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂} := hfcomp.mul hfcomp
        simpa [pow_two] using hsq
      exact hsum.sub hf2
    have hpre : IsClosed (A ∩ g ⁻¹' Set.Iic 0) :=
      hg_cont.preimage_isClosed_of_isClosed hA_closed isClosed_Iic
    convert hpre using 1
    ext x
    simp [S, A, g]
  have hS_bounded : Bornology.IsBounded S := by
    let A0 : ℝ := max |R₁| |R₂|
    have hA0_nonneg : 0 ≤ A0 := by
      dsimp [A0]
      positivity
    have hIcc_compact : IsCompact (Set.Icc (-R₁) R₂) := isCompact_Icc
    have hf_image_compact : IsCompact (f '' Set.Icc (-R₁) R₂) :=
      hIcc_compact.image_of_continuousOn hf_cont
    have hf_image_bounded : Bornology.IsBounded (f '' Set.Icc (-R₁) R₂) :=
      hf_image_compact.isBounded
    obtain ⟨B, hB⟩ := hf_image_bounded.subset_closedBall (0 : ℝ)
    let C : ℝ := max B 0
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact le_max_right B 0
    have hf_abs_le : ∀ t ∈ Set.Icc (-R₁) R₂, |f t| ≤ C := by
      intro t ht
      have hmem : f t ∈ f '' Set.Icc (-R₁) R₂ := ⟨t, ht, rfl⟩
      have hdist : dist (f t) 0 ≤ B := hB hmem
      have hle : |f t| ≤ B := by
        simpa [Real.dist_eq] using hdist
      exact hle.trans (le_max_left B 0)
    let r : ℝ := √(A0 ^ 2 + C ^ 2)
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℝᵈ)) (r := r)) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hx0Icc : x 0 ∈ Set.Icc (-R₁) R₂ := hx.1
    have htail : ∑ i > 0, (x i)^2 ≤ (f (x 0))^2 := hx.2
    have hx0_abs : |x 0| ≤ A0 := by
      dsimp [A0]
      simpa [abs_neg] using (abs_le_max_abs_abs (a := -R₁) (b := x 0) (c := R₂) hx0Icc.1 hx0Icc.2)
    have hx0_sq : (x 0)^2 ≤ A0 ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hA0_nonneg] using hx0_abs)
    have hf_abs_le_C : |f (x 0)| ≤ C := hf_abs_le (x 0) hx0Icc
    have hf_sq_le : (f (x 0))^2 ≤ C ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC_nonneg] using hf_abs_le_C)
    have htail_le : ∑ i > 0, (x i)^2 ≤ C ^ 2 := htail.trans hf_sq_le
    have hnorm_sq : ‖x‖ ^ 2 ≤ A0 ^ 2 + C ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ i : Fin d, (x i)^2) = (x 0)^2 + ∑ i > 0, (x i)^2 := by
          calc
            (∑ i : Fin d, (x i)^2) = (∑ i ∈ (Finset.univ : Finset (Fin d)).erase 0, (x i)^2) + (x 0)^2 := by
              rw [Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin d))]
            _ = (∑ i > 0, (x i)^2) + (x 0)^2 := by
              rw [show (Finset.univ : Finset (Fin d)).erase 0 = Finset.Ioi 0 by ext i; simp]
            _ = (x 0)^2 + ∑ i > 0, (x i)^2 := by abel
        _ ≤ A0 ^ 2 + C ^ 2 := add_le_add hx0_sq htail_le
    have hnorm_le : ‖x‖ ≤ r := Real.le_sqrt_of_sq_le hnorm_sq
    simpa using hnorm_le
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hS_closed, hS_bounded⟩

end Commons.Geometry.Ulam