import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.vkN

lemma increment_mem_of_deriv_bounds {N : ℕ} {F D : ℝ → ℝ} {c C : ℝ}
    (hcont : ContinuousOn F (Set.Icc 0 (N : ℝ)))
    (hdiff : DifferentiableOn ℝ F (Set.Ioo 0 (N : ℝ)))
    (hD : ∀ x : ℝ, deriv F x = D x)
    (hbound : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) → c ≤ D x ∧ D x ≤ C)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n < N) :
    c ≤ F ((n : ℝ) + 1) - F (n : ℝ) ∧ F ((n : ℝ) + 1) - F (n : ℝ) ≤ C := by
  have hbN : ((n : ℝ) + 1) ≤ (N : ℝ) := by
    have : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnN
    simpa using this
  have h0n : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hab : (n : ℝ) < (n : ℝ) + 1 := by linarith
  have hcont' : ContinuousOn F (Set.Icc (n : ℝ) ((n : ℝ) + 1)) :=
    hcont.mono (Set.Icc_subset_Icc h0n hbN)
  have hdiff' : DifferentiableOn ℝ F (Set.Ioo (n : ℝ) ((n : ℝ) + 1)) :=
    hdiff.mono (Set.Ioo_subset_Ioo h0n hbN)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope F hab hcont' hdiff'
  have hξmem : ξ ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) := by
    rw [Set.mem_Ioo] at hξ ⊢
    exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hb_eq : ((n : ℝ) + 1) - (n : ℝ) = 1 := by ring
  have h1 : deriv F ξ = F ((n : ℝ) + 1) - F (n : ℝ) := by
    rw [hξeq, hb_eq, div_one]
  have hderiv : F ((n : ℝ) + 1) - F (n : ℝ) = D ξ := h1.symm.trans (hD ξ)
  exact ⟨by rw [hderiv]; exact (hbound ξ hξmem).1,
         by rw [hderiv]; exact (hbound ξ hξmem).2⟩

end Work.BMF.vkN
