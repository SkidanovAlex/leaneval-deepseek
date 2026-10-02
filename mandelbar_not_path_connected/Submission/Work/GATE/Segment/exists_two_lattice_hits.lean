import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE.Segment

theorem exists_two_lattice_hits {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) {A₀ : ℝ}
    (h0 : f 0 = A₀) {μ₀ : ℝ} (hμ₀ : μ₀ ∈ Set.Icc (0 : ℝ) 1) (hμ₀' : f μ₀ < A₀ - 2) (x : ℝ) :
    ∃ v₁ v₂ : ℝ, (∃ k : ℤ, v₁ = x + (k : ℝ)) ∧ (∃ k : ℤ, v₂ = x + 1 / 2 + (k : ℝ)) ∧
      v₁ ≠ v₂ ∧ ∃ μ₁ ∈ Set.Icc (0 : ℝ) 1, ∃ μ₂ ∈ Set.Icc (0 : ℝ) 1,
        f μ₁ = v₁ ∧ f μ₂ = v₂ := by
  -- the image of f on [0,1] contains the interval [f μ₀, A₀], whose length is > 2
  have hb : (0 : ℝ) ≤ μ₀ := hμ₀.1
  have hA : f μ₀ + 1 < A₀ := by linarith
  -- every half-open lattice line of mesh 1 meets [f μ₀, A₀]
  have key : ∀ c : ℝ, ∃ k : ℤ, f μ₀ ≤ x + c + (k : ℝ) ∧ x + c + (k : ℝ) ≤ A₀ := by
    intro c
    refine ⟨⌈f μ₀ - x - c⌉, ?_, ?_⟩
    · have := Int.le_ceil (f μ₀ - x - c); linarith
    · have := Int.ceil_lt_add_one (f μ₀ - x - c); linarith
  obtain ⟨k₁, hk₁⟩ := key 0
  obtain ⟨k₂, hk₂⟩ := key (1 / 2)
  have hsub : Set.Icc (0 : ℝ) μ₀ ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc le_rfl hμ₀.2
  -- intermediate value: every point of [f μ₀, A₀] is attained in [0,1]
  have ivt : ∀ v : ℝ, f μ₀ ≤ v → v ≤ A₀ → ∃ μ ∈ Set.Icc (0 : ℝ) 1, f μ = v := by
    intro v hv1 hv2
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) μ₀) := hf.mono hsub
    have himg := intermediate_value_Icc' hb hcont
    have hmem : v ∈ Set.Icc (f μ₀) (f 0) := by
      simp only [Set.mem_Icc]
      exact ⟨hv1, by rw [h0]; exact hv2⟩
    obtain ⟨μ, hμ, hfμ⟩ := himg hmem
    exact ⟨μ, hsub hμ, hfμ⟩
  obtain ⟨μ₁, hμ₁, hfμ₁⟩ := ivt (x + (k₁ : ℝ)) (by simpa using hk₁.1) (by simpa using hk₁.2)
  obtain ⟨μ₂, hμ₂, hfμ₂⟩ := ivt (x + 1 / 2 + (k₂ : ℝ)) hk₂.1 hk₂.2
  refine ⟨x + (k₁ : ℝ), x + 1 / 2 + (k₂ : ℝ), ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, ?_,
    μ₁, hμ₁, μ₂, hμ₂, hfμ₁, hfμ₂⟩
  -- the two lattice lines are disjoint since their mesh points differ by 1/2
  intro hc
  have hhalf : ((k₁ - k₂ : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
  have h2 : (2 * (k₁ - k₂) : ℤ) = 1 := by
    have := congrArg (fun r : ℝ => 2 * r) hhalf
    push_cast at this
    norm_num at this
    exact_mod_cast this
  omega

end Work.GATE.Segment
