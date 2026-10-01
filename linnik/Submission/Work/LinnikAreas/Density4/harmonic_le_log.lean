import Mathlib

namespace Work.LinnikAreas.Density4

/-- The elementary inequality `2(x-1)/(x+1) ≤ log x` for `x ≥ 1`.
It is the statement that `x ↦ (x+1)·log x - 2(x-1)` is nondecreasing on `[1, ∞)`,
whose derivative is `log x + 1/x - 1 ≥ 0`. -/
private lemma log_two_mul_div_le {x : ℝ} (hx : 1 ≤ x) :
    2*(x-1)/(x+1) ≤ Real.log x := by
  have hcont : ContinuousOn (fun z : ℝ => (z+1)*Real.log z - 2*(z-1)) (Set.Ici 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · exact (continuous_id.add continuous_const).continuousOn
      · refine Real.continuousOn_log.mono ?_
        intro y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ici] at hy ⊢
        exact ne_of_gt (by linarith)
    · exact (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
  have hderiv : ∀ y ∈ Set.Ioi (1:ℝ),
      HasDerivAt (fun z : ℝ => (z+1)*Real.log z - 2*(z-1)) (Real.log y + (y+1)*y⁻¹ - 2) y := by
    intro y hy
    simp only [Set.mem_Ioi] at hy
    have hy0 : y ≠ 0 := by linarith
    have h1 : HasDerivAt (fun z : ℝ => (z+1)*Real.log z) (Real.log y + (y+1)*y⁻¹) y := by
      have h := ((hasDerivAt_id y).add_const 1).mul (Real.hasDerivAt_log hy0)
      exact h.congr_deriv (by simp only [id_eq, one_mul])
    have h2 : HasDerivAt (fun z : ℝ => 2*(z-1)) 2 y := by
      simpa using ((hasDerivAt_id y).sub_const 1).const_mul 2
    exact (h1.sub h2).congr_deriv (by ring)
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => (z+1)*Real.log z - 2*(z-1))
      (interior (Set.Ici 1)) := by
    rw [interior_Ici]
    intro y hy
    exact (hderiv y hy).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun z : ℝ => (z+1)*Real.log z - 2*(z-1)) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont hdiff
    intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    rw [(hderiv y hy).deriv]
    have hy0 : y ≠ 0 := by linarith
    have hone : (y+1)*y⁻¹ = 1 + y⁻¹ := by rw [add_mul, one_mul, mul_inv_cancel₀ hy0]
    have hlog := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < y by linarith)
    linarith
  have h := hmono (by simp) (by simp [hx]) hx
  simp only [Real.log_one] at h
  have h2 : 2*(x-1) ≤ (x+1)*Real.log x := by linarith
  have hx1 : (0:ℝ) < x + 1 := by linarith
  rw [div_le_iff₀ hx1]
  nlinarith [h2]

/-- The telescoping step `1/(k+1) ≤ log((2k+3)/(2k+1))`, obtained from
`log_two_mul_div_le` at `x = (2k+3)/(2k+1)`. -/
private lemma inv_succ_le_log (k : ℕ) :
    (1:ℝ)/((k:ℝ)+1) ≤ Real.log ((2*(k:ℝ)+3)/(2*(k:ℝ)+1)) := by
  have hden : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
  have hx1 : 1 ≤ (2*(k:ℝ)+3)/(2*(k:ℝ)+1) := by
    rw [le_div_iff₀ hden]; linarith
  have h := log_two_mul_div_le hx1
  have heq : 2*((2*(k:ℝ)+3)/(2*(k:ℝ)+1) - 1) / ((2*(k:ℝ)+3)/(2*(k:ℝ)+1) + 1)
      = 1/((k:ℝ)+1) := by
    field_simp
    ring
  rwa [heq] at h

/-- Harmonic-sum bound: `∑_{k=1}^{N-1} 1/k - 1 ≤ log((2N-1)/3)` for `N ≥ 2`. -/
lemma harmonic_le_log (N : ℕ) (hN : 2 ≤ N) :
    (∑ k ∈ Finset.Icc 1 (N-1), (1:ℝ)/(k:ℝ)) - 1 ≤ Real.log ((2*(N:ℝ)-1)/3) := by
  -- Prove the statement for `∑_{k=1}^{n} 1/k - 1 ≤ log((2n+1)/3)`, `n ≥ 1`, by induction.
  have aux : ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.Icc 1 n, (1:ℝ)/(k:ℝ)) - 1 ≤ Real.log ((2*(n:ℝ)+1)/3) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        norm_num
      · have ihk := ih hkpos
        have key := inv_succ_le_log k
        calc (∑ i ∈ Finset.Icc 1 (k+1), (1:ℝ)/(i:ℝ)) - 1
            = ((∑ i ∈ Finset.Icc 1 k, (1:ℝ)/(i:ℝ)) - 1) + (1:ℝ)/((k:ℝ)+1) := by
              rw [Finset.sum_Icc_succ_top (by omega)]
              push_cast
              ring
          _ ≤ Real.log ((2*(k:ℝ)+1)/3) + (1:ℝ)/((k:ℝ)+1) := by linarith
          _ ≤ Real.log ((2*(k:ℝ)+1)/3) + Real.log ((2*(k:ℝ)+3)/(2*(k:ℝ)+1)) := by
              linarith
          _ = Real.log ((2*((k+1:ℕ):ℝ)+1)/3) := by
              rw [← Real.log_mul (by positivity) (by positivity)]
              congr 1
              push_cast
              field_simp
              ring
  have hN1 : 1 ≤ N - 1 := by omega
  have h := aux (N-1) hN1
  have hcast : (2*((N-1:ℕ):ℝ)+1) = (2*(N:ℝ)-1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hcast] at h
  exact h

end Work.LinnikAreas.Density4
