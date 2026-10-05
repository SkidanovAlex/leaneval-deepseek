import Mathlib

namespace Work.RPB.B5

theorem slabMonoExistsUnique (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2))
    (h0 : ∀ τ t, S τ t 0 = 0)
    (δ ε₀ : ℝ) (hδ : 0 < δ) (hε₀ : 0 < ε₀)
    (hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
        δ ≤ deriv (fun ρ => S τ t ρ) ρ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t,
      StrictMonoOn (fun ρ => S τ t ρ) (Set.Icc (-ε₀) ε₀) ∧
      δ * ε₀ ≤ S τ t ε₀ ∧ S τ t (-ε₀) ≤ -(δ * ε₀) ∧
      (∀ σ, |σ| < δ * ε₀ → ∃! ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S τ t ρ = σ) := by
  intro τ hτ t
  -- The `ρ`-slice is `C⁸`, hence continuous and differentiable.
  have hslice : ContDiff ℝ 8 (fun ρ : ℝ => S τ t ρ) := by
    have h1 : ContDiff ℝ 8 (fun ρ : ℝ => (τ, (t, ρ)) : ℝ → ℝ × (ℝ × ℝ)) := by fun_prop
    exact hS.comp h1
  have hcont : ContinuousOn (fun ρ : ℝ => S τ t ρ) (Set.Icc (-ε₀) ε₀) :=
    hslice.continuous.continuousOn
  have hdiff : Differentiable ℝ (fun ρ : ℝ => S τ t ρ) := hslice.differentiable (by norm_num)
  have hderiv' : ∀ ρ ∈ Set.Icc (-ε₀) ε₀, δ ≤ deriv (fun ρ => S τ t ρ) ρ :=
    fun ρ hρ => hderiv τ hτ t ρ hρ
  -- Strict monotonicity from a strictly positive derivative.
  have hmono : StrictMonoOn (fun ρ : ℝ => S τ t ρ) (Set.Icc (-ε₀) ε₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro x hx
    rw [interior_Icc] at hx
    exact lt_of_lt_of_le hδ (hderiv' x (Set.Ioo_subset_Icc_self hx))
  -- Growth bound on `[0, ε₀]`.
  have hbnd_pos : δ * ε₀ ≤ S τ t ε₀ := by
    have h := Convex.mul_sub_le_image_sub_of_le_deriv (D := Set.Icc (0:ℝ) ε₀) (convex_Icc _ _)
      (f := fun ρ : ℝ => S τ t ρ) hslice.continuous.continuousOn hdiff.differentiableOn
      (C := δ) (fun x hx => by
        rw [interior_Icc] at hx
        exact hderiv' x ⟨by linarith [(Set.mem_Ioo.mp hx).1, hε₀], (Set.mem_Ioo.mp hx).2.le⟩)
      (x := 0) (y := ε₀)
      (by exact ⟨le_rfl, hε₀.le⟩) (by exact ⟨hε₀.le, le_rfl⟩) (by linarith [hε₀])
    simpa [h0 τ t] using h
  -- Growth bound on `[-ε₀, 0]`.
  have hbnd_neg : S τ t (-ε₀) ≤ -(δ * ε₀) := by
    have h := Convex.mul_sub_le_image_sub_of_le_deriv (D := Set.Icc (-ε₀) (0:ℝ)) (convex_Icc _ _)
      (f := fun ρ : ℝ => S τ t ρ) hslice.continuous.continuousOn hdiff.differentiableOn
      (C := δ) (fun x hx => by
        rw [interior_Icc] at hx
        exact hderiv' x ⟨(Set.mem_Ioo.mp hx).1.le, by linarith [(Set.mem_Ioo.mp hx).2, hε₀]⟩)
      (x := -ε₀) (y := 0)
      (by exact ⟨le_rfl, by linarith⟩) (by exact ⟨by linarith, le_rfl⟩) (by linarith)
    have h' : δ * ε₀ ≤ -(S τ t (-ε₀)) := by simpa [h0 τ t] using h
    linarith
  refine ⟨hmono, hbnd_pos, hbnd_neg, ?_⟩
  -- Intermediate value + strict monotonicity give the unique preimage.
  intro σ hσ
  rw [abs_lt] at hσ
  obtain ⟨hσ1, hσ2⟩ := hσ
  have hmem : σ ∈ Set.Icc ((fun ρ : ℝ => S τ t ρ) (-ε₀)) ((fun ρ : ℝ => S τ t ρ) ε₀) :=
    ⟨le_trans hbnd_neg hσ1.le, le_trans hσ2.le hbnd_pos⟩
  obtain ⟨ρ, hρmem, hρeq⟩ := (intermediate_value_Icc (by linarith [hε₀]) hcont) hmem
  have hρIoo : ρ ∈ Set.Ioo (-ε₀) ε₀ := by
    have hne1 : ρ ≠ -ε₀ := by
      intro h; rw [h] at hρeq; linarith [hbnd_neg, hσ1]
    have hne2 : ρ ≠ ε₀ := by
      intro h; rw [h] at hρeq; linarith [hbnd_pos, hσ2]
    exact ⟨lt_of_le_of_ne hρmem.1 (Ne.symm hne1), lt_of_le_of_ne hρmem.2 hne2⟩
  refine ⟨ρ, ⟨hρIoo, hρeq⟩, ?_⟩
  intro ρ' hρ'
  exact hmono.injOn (Set.Ioo_subset_Icc_self hρ'.1) (Set.Ioo_subset_Icc_self hρIoo)
    (hρ'.2.trans hρeq.symm)

end Work.RPB.B5
