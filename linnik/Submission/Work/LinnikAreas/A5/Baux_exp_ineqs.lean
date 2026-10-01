import Mathlib

namespace Work.LinnikAreas.A5

theorem Baux_exp_ineqs (t : ℝ) (ht : 0 ≤ t) :
    (t + 1) * Real.exp (-t) ≤ 1 ∧ 0 ≤ t - 2 + (t + 2) * Real.exp (-t) := by
  -- Elementary auxiliary inequality: (s + 1) * exp (-s) ≤ 1 for s ≥ 0.
  have key : ∀ s : ℝ, 0 ≤ s → (s + 1) * Real.exp (-s) ≤ 1 := by
    intro s hs
    have h := Real.add_one_le_exp s
    have hpos : (0:ℝ) ≤ Real.exp (-s) := le_of_lt (Real.exp_pos _)
    have hmul := mul_le_mul_of_nonneg_right h hpos
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
    simpa using hmul
  refine ⟨key t ht, ?_⟩
  -- For the second inequality use monotonicity of F s = s - 2 + (s + 2) * exp (-s)
  -- on [0, ∞), since F 0 = 0 and F' s = 1 - (s + 1) * exp (-s) ≥ 0.
  have hderiv : ∀ x : ℝ,
      deriv (fun s : ℝ => s - 2 + (s + 2) * Real.exp (-s)) x
        = 1 - (x + 1) * Real.exp (-x) := by
    intro x
    have hd : HasDerivAt (fun s : ℝ => s - 2 + (s + 2) * Real.exp (-s))
        (1 + ((x + 2) * (Real.exp (-x) * (-1)) + 1 * Real.exp (-x))) x := by
      have h1 : HasDerivAt (fun s : ℝ => s - 2) 1 x := by
        simpa using (hasDerivAt_id (𝕜 := ℝ) x).sub_const (2 : ℝ)
      have h2 : HasDerivAt (fun s : ℝ => (s + 2) * Real.exp (-s))
          ((x + 2) * (Real.exp (-x) * (-1)) + 1 * Real.exp (-x)) x := by
        have hmul : HasDerivAt ((fun s : ℝ => s + 2) * fun s : ℝ => Real.exp (-s))
            (1 * Real.exp (-x) + (x + 2) * (Real.exp (-x) * (-1))) x := by
          refine HasDerivAt.mul ?_ ?_
          · simpa using (hasDerivAt_id (𝕜 := ℝ) x).add_const (2 : ℝ)
          · simpa using ((hasDerivAt_id (𝕜 := ℝ) x).neg).exp
        convert hmul using 1 <;> first | ring | (funext y; simp [Pi.mul_apply])
      exact h1.add h2
    rw [hd.deriv]; ring
  have hmono : MonotoneOn (fun s : ℝ => s - 2 + (s + 2) * Real.exp (-s)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      rw [hderiv x]
      rw [interior_Ici] at hx
      have hx0 : 0 ≤ x := le_of_lt hx
      have := key x hx0
      linarith
  have hmem0 : (0:ℝ) ∈ Set.Ici 0 := by simp
  have hle := hmono hmem0 ht ht
  have h0 : (fun s : ℝ => s - 2 + (s + 2) * Real.exp (-s)) 0 = 0 := by norm_num
  linarith [hle, h0]

end Work.LinnikAreas.A5
