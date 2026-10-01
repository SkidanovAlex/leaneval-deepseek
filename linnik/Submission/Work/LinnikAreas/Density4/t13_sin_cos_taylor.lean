import Mathlib

/-!
# Taylor remainder bounds for `sin` and `cos`

This file proves the classical alternating-Taylor-remainder estimate
$|\sin x - \sum_{k<N} \frac{(-1)^k x^{2k+1}}{(2k+1)!}| \le \frac{x^{2N+1}}{(2N+1)!}, \qquad
  |\cos x - \sum_{k<N} \frac{(-1)^k x^{2k}}{(2k)!}| \le \frac{x^{2N}}{(2N)!}$
valid for every `x ≥ 0` and every `N` (no restriction on the size of `x`).

The proof is an induction on `N`.  Writing `A_N = sin - P_N^{sin}` and
`B_N = cos - P_N^{cos}` for the two remainders one has the differential
relations `A_N' = B_N` and `B_N' = - A_{N-1}`, together with `A_N(0) = B_N(0) = 0`.
The induction is driven by the "fencing" mean value theorem
`image_le_of_deriv_right_le_deriv_boundary`: if a function starts below a barrier
and its derivative is bounded by the derivative of the barrier, it stays below it.
-/

namespace Work.LinnikAreas.Density4

open Set

/-- `k`-th term of the Taylor expansion of `sin`. -/
noncomputable def sT (k : ℕ) (x : ℝ) : ℝ := (-1:ℝ)^k * x^(2*k+1)/((2*k+1).factorial : ℝ)

/-- `k`-th term of the Taylor expansion of `cos`. -/
noncomputable def cT (k : ℕ) (x : ℝ) : ℝ := (-1:ℝ)^k * x^(2*k)/((2*k).factorial : ℝ)

/-- Partial sums of the Taylor expansion of `sin`. -/
noncomputable def sinP (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, sT k x

/-- Partial sums of the Taylor expansion of `cos`. -/
noncomputable def cosP (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, cT k x

/-- The barrier function `x ↦ x^m / m!`. -/
noncomputable def bound (m : ℕ) (x : ℝ) : ℝ := x^m/(m.factorial : ℝ)

/-- The derivative of the `k`-th term of the sine expansion is the `k`-th term of
the cosine expansion. -/
theorem hasDerivAt_sT (k : ℕ) (x : ℝ) : HasDerivAt (sT k) (cT k x) x := by
  unfold sT cT
  have hfac : ((2*k+1).factorial : ℝ) = ((2*k+1) : ℝ) * ((2*k).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : HasDerivAt (fun y : ℝ => y^(2*k+1)) (((2*k+1):ℕ) * x^(2*k)) x := by
    simpa using hasDerivAt_pow (2*k+1) x
  have h2 : HasDerivAt (fun y : ℝ => (-1:ℝ)^k * (y^(2*k+1))/((2*k+1).factorial : ℝ))
      ((-1:ℝ)^k * ((2*k+1) * x^(2*k))/((2*k+1).factorial : ℝ)) x := by
    simpa using (h1.const_mul ((-1:ℝ)^k)).div_const ((2*k+1).factorial : ℝ)
  have key2 : (-1:ℝ)^k * ((2*k+1) * x^(2*k))/((2*k+1).factorial : ℝ) = cT k x := by
    unfold cT; rw [hfac]; field_simp
  rwa [key2] at h2

/-- The derivative of the `(k+1)`-st term of the cosine expansion is minus the
`k`-th term of the sine expansion. -/
theorem hasDerivAt_cT_succ (k : ℕ) (x : ℝ) : HasDerivAt (cT (k+1)) (-(sT k x)) x := by
  have hfac : ((2*(k+1)).factorial : ℝ) = ((2*(k+1)) : ℝ) * ((2*k+1).factorial : ℝ) := by
    have h : 2*(k+1) = 2*k+1+1 := by ring
    rw [h, Nat.factorial_succ]; push_cast; ring
  have h1 : HasDerivAt (fun y : ℝ => y^(2*(k+1))) (((2*(k+1)):ℕ) * x^(2*(k+1)-1)) x := by
    simpa using hasDerivAt_pow (2*(k+1)) x
  have h2 : HasDerivAt (cT (k+1))
      (((-1:ℝ)^(k+1)) * (((2*(k+1)):ℕ) * x^(2*(k+1)-1))/((2*(k+1)).factorial : ℝ)) x := by
    unfold cT
    simpa using (h1.const_mul ((-1:ℝ)^(k+1))).div_const ((2*(k+1)).factorial : ℝ)
  have key : (((-1:ℝ)^(k+1)) * (((2*(k+1)):ℕ) * x^(2*(k+1)-1))/((2*(k+1)).factorial : ℝ)) = -(sT k x) := by
    unfold sT
    have h2k : 2*(k+1)-1 = 2*k+1 := by omega
    rw [h2k, hfac]; field_simp; push_cast; ring
  rwa [key] at h2

/-- Derivative of the `n`-th sine Taylor polynomial. -/
theorem hasDerivAt_sinP (n : ℕ) (x : ℝ) : HasDerivAt (sinP n) (cosP n x) x := by
  have h : ∀ k ∈ Finset.range n, HasDerivAt (sT k) (cT k x) x := fun k _ => hasDerivAt_sT k x
  have hsum := HasDerivAt.sum h
  have heq : (∑ k ∈ Finset.range n, sT k) = sinP n := by
    funext y; simp only [sinP, Finset.sum_apply]
  rw [heq] at hsum
  simpa [cosP] using hsum

/-- Derivative of the `(n+1)`-st cosine Taylor polynomial. -/
theorem hasDerivAt_cosP_succ (n : ℕ) (x : ℝ) : HasDerivAt (cosP (n+1)) (-(sinP n x)) x := by
  have h0 : HasDerivAt (cT 0) 0 x := by
    have he : cT 0 = (fun _ : ℝ => (1:ℝ)) := by funext y; simp [cT]
    rw [he]; exact hasDerivAt_const x 1
  have hmain : ∀ k ∈ Finset.range n, HasDerivAt (cT (k+1)) (-(sT k x)) x :=
    fun k _ => hasDerivAt_cT_succ k x
  have hsum0 := HasDerivAt.sum hmain
  have heq : (∑ k ∈ Finset.range n, cT (k+1)) = (fun y => ∑ k ∈ Finset.range n, cT (k+1) y) := by
    funext y; rw [Finset.sum_apply]
  rw [heq] at hsum0
  have hcomb := hsum0.add h0
  have hfun : cosP (n+1) = (fun y => (∑ k ∈ Finset.range n, cT (k+1) y) + cT 0 y) := by
    funext y; rw [cosP, Finset.sum_range_succ']
  have hval : ((∑ k ∈ Finset.range n, -(sT k x)) + 0) = -(sinP n x) := by
    rw [add_zero, Finset.sum_neg_distrib]; rfl
  rw [hfun, ← hval]
  exact hcomb

/-- The derivative of the `(m+1)`-st barrier is the `m`-th barrier. -/
theorem hasDerivAt_bound (m : ℕ) (x : ℝ) : HasDerivAt (bound (m+1)) (bound m x) x := by
  unfold bound
  have h1 : HasDerivAt (fun y : ℝ => y^(m+1)) (((m+1):ℕ) * x^m) x := by
    simpa using hasDerivAt_pow (m+1) x
  have hfac : ((m+1).factorial : ℝ) = ((m+1):ℝ) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h2 : HasDerivAt (fun y => y^(m+1)/((m+1).factorial : ℝ))
      ((((m+1):ℕ) * x^m)/((m+1).factorial : ℝ)) x := h1.div_const _
  have key : ((((m+1):ℕ) * x^m)/((m+1).factorial : ℝ)) = x^m/(m.factorial : ℝ) := by
    rw [hfac]; field_simp; push_cast; ring
  rwa [key] at h2

theorem continuousOn_bound (m : ℕ) (a b : ℝ) : ContinuousOn (bound m) (Icc a b) := by
  unfold bound; fun_prop

theorem continuousOn_sinP (n : ℕ) (a b : ℝ) : ContinuousOn (sinP n) (Icc a b) := by
  have := continuousOn_finsetSum (Finset.range n) (f := sT) (t := Icc a b)
    (fun k _ => by unfold sT; fun_prop)
  exact this

theorem continuousOn_cosP (n : ℕ) (a b : ℝ) : ContinuousOn (cosP n) (Icc a b) := by
  have := continuousOn_finsetSum (Finset.range n) (f := cT) (t := Icc a b)
    (fun k _ => by unfold cT; fun_prop)
  exact this

theorem sinP_zero (n : ℕ) : sinP n 0 = 0 := by simp [sinP, sT]

theorem cosP_zero_succ (n : ℕ) : cosP (n+1) 0 = 1 := by
  rw [cosP, Finset.sum_range_succ']; simp [cT]

/-- Fencing step: if `f 0 ≤ 0` and `f' ≤ bound m` on `[0,T]`, then
`f T ≤ bound (m+1) T`. -/
theorem fence (m : ℕ) (f f' : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn f (Icc 0 T)) (hder : ∀ t, HasDerivAt f (f' t) t)
    (hf0 : f 0 ≤ 0) (hbd : ∀ t, 0 ≤ t → f' t ≤ bound m t) :
    f T ≤ bound (m+1) T := by
  have hb0 : bound (m+1) 0 = 0 := by unfold bound; rw [zero_pow (by omega), zero_div]
  have := image_le_of_deriv_right_le_deriv_boundary (f := f) (f' := f')
    (B := bound (m+1)) (B' := bound m) (a := 0) (b := T)
    hcont (fun t _ => (hder t).hasDerivWithinAt) (by rw [hb0]; exact hf0)
    (continuousOn_bound (m+1) 0 T) (fun t _ => (hasDerivAt_bound m t).hasDerivWithinAt)
    (fun t ht => hbd t ht.1)
  exact this (right_mem_Icc.mpr hT)

/-- Main induction: the two Taylor remainder estimates for every `x ≥ 0`. -/
theorem taylor_remainder (n : ℕ) : ∀ X : ℝ, 0 ≤ X →
    |Real.sin X - sinP n X| ≤ bound (2*n+1) X ∧ |Real.cos X - cosP n X| ≤ bound (2*n) X := by
  induction n with
  | zero =>
    intro X hX
    constructor
    · have h := Real.abs_sin_le_abs (x := X)
      rw [abs_of_nonneg hX] at h
      simpa [sinP, bound] using h
    · simpa [cosP, bound] using Real.abs_cos_le_one X
  | succ n ih =>
    intro X hX
    have ihA : ∀ t : ℝ, 0 ≤ t → |Real.sin t - sinP n t| ≤ bound (2*n+1) t :=
      fun t ht => (ih t ht).1
    -- derivative facts
    have hBderiv : ∀ t,
        HasDerivAt (fun t => Real.cos t - cosP (n+1) t) (-(Real.sin t - sinP n t)) t := by
      intro t
      have h := (Real.hasDerivAt_cos t).sub (hasDerivAt_cosP_succ n t)
      have hval : (-Real.sin t) - (-(sinP n t)) = -(Real.sin t - sinP n t) := by ring
      rw [hval] at h
      exact h
    have hBderiv' : ∀ t,
        HasDerivAt (fun t => -(Real.cos t - cosP (n+1) t)) (Real.sin t - sinP n t) t := by
      intro t
      have h := (hBderiv t).neg
      have hv : -(-(Real.sin t - sinP n t)) = Real.sin t - sinP n t := by ring
      rw [hv] at h
      exact h
    have hAderiv : ∀ t,
        HasDerivAt (fun t => Real.sin t - sinP (n+1) t) (Real.cos t - cosP (n+1) t) t := by
      intro t
      exact (Real.hasDerivAt_sin t).sub (hasDerivAt_sinP (n+1) t)
    have hAderiv' : ∀ t,
        HasDerivAt (fun t => -(Real.sin t - sinP (n+1) t)) (-(Real.cos t - cosP (n+1) t)) t := by
      intro t
      exact (hAderiv t).neg
    -- values at `0`
    have hB0 : (fun t => Real.cos t - cosP (n+1) t) 0 ≤ 0 := by simp [cosP_zero_succ]
    have hB0' : (fun t => -(Real.cos t - cosP (n+1) t)) 0 ≤ 0 := by simp [cosP_zero_succ]
    have hA0 : (fun t => Real.sin t - sinP (n+1) t) 0 ≤ 0 := by simp [sinP_zero]
    have hA0' : (fun t => -(Real.sin t - sinP (n+1) t)) 0 ≤ 0 := by simp [sinP_zero]
    -- pointwise cosine bounds (the `(n+1)`-st remainders)
    have hcos_pt : ∀ t, 0 ≤ t → Real.cos t - cosP (n+1) t ≤ bound (2*(n+1)) t := fun t ht =>
      fence (2*n+1) _ _ t ht
        ((Real.continuous_cos.continuousOn).sub (continuousOn_cosP (n+1) 0 t))
        hBderiv hB0 (fun s hs => le_trans (neg_le_abs _) (ihA s hs))
    have hcosneg_pt : ∀ t, 0 ≤ t → -(Real.cos t - cosP (n+1) t) ≤ bound (2*(n+1)) t := fun t ht =>
      fence (2*n+1) _ _ t ht
        (((Real.continuous_cos.continuousOn).sub (continuousOn_cosP (n+1) 0 t)).neg)
        hBderiv' hB0' (fun s hs => le_trans (le_abs_self _) (ihA s hs))
    -- pointwise sine bounds (the `(n+1)`-st remainders)
    have hsin_pt : ∀ t, 0 ≤ t → Real.sin t - sinP (n+1) t ≤ bound (2*(n+1)+1) t := fun t ht =>
      fence (2*(n+1)) _ _ t ht
        ((Real.continuous_sin.continuousOn).sub (continuousOn_sinP (n+1) 0 t))
        hAderiv hA0 (fun s hs => hcos_pt s hs)
    have hsinnneg_pt : ∀ t, 0 ≤ t →
        -(Real.sin t - sinP (n+1) t) ≤ bound (2*(n+1)+1) t := fun t ht =>
      fence (2*(n+1)) _ _ t ht
        (((Real.continuous_sin.continuousOn).sub (continuousOn_sinP (n+1) 0 t)).neg)
        hAderiv' hA0' (fun s hs => hcosneg_pt s hs)
    exact ⟨abs_le.mpr ⟨by linarith [hsinnneg_pt X hX], hsin_pt X hX⟩,
           abs_le.mpr ⟨by linarith [hcosneg_pt X hX], hcos_pt X hX⟩⟩

theorem t13_sin_cos_taylor (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    |Real.sin x - ∑ k ∈ Finset.range N, (-1)^k * x^(2*k+1)/((2*k+1).factorial : ℝ)|
        ≤ x^(2*N+1)/((2*N+1).factorial : ℝ) ∧
    |Real.cos x - ∑ k ∈ Finset.range N, (-1)^k * x^(2*k)/((2*k).factorial : ℝ)|
        ≤ x^(2*N)/((2*N).factorial : ℝ) := by
  simpa [sinP, cosP, bound, sT, cT] using taylor_remainder N x hx

end Work.LinnikAreas.Density4
