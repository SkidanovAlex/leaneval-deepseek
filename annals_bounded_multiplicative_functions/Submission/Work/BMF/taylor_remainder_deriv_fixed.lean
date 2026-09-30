import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary lemmas for `taylor_remainder_deriv_fixed`.

These are kept `private` so that they neither clash with nor depend on any other
`Work.BMF` development. -/

/-- The Taylor polynomial of `deriv f` of degree `n` at `x₀`, evaluated at `x`, equals
`Σ_{i=0}^{n} f^{(i+1)}(x₀) (x-x₀)^i / i!`. -/
private lemma taylor_remainder_deriv_hsum (n : ℕ) {N : ℕ} {f : ℝ → ℝ} {x₀ x : ℝ}
    (hderiv : ContDiffOn ℝ (n + 1) (deriv f) (Set.Ioo (0:ℝ) (N:ℝ)))
    (hx0 : x₀ ∈ Set.Ioo (0:ℝ) (N:ℝ)) (hlt : x₀ < x) :
    taylorWithinEval (deriv f) n (Set.uIcc x₀ x) x₀ x
      = ∑ i ∈ Finset.range (n + 1),
          iteratedDeriv (i + 1) f x₀ * (x - x₀) ^ i / (Nat.factorial i : ℝ) := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  have hcd0 : ContDiffAt ℝ ((n : WithTop ℕ∞) + 1) (deriv f) x₀ :=
    hderiv.contDiffAt (isOpen_Ioo.mem_nhds hx0)
  have hcd : ContDiffAt ℝ (i : WithTop ℕ∞) (deriv f) x₀ :=
    hcd0.of_le (by exact_mod_cast (by omega : i ≤ n + 1))
  have h1 : iteratedDerivWithin i (deriv f) (Set.uIcc x₀ x) x₀ = iteratedDeriv i (deriv f) x₀ :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hlt.ne) hcd Set.left_mem_uIcc
  rw [h1, ← iteratedDeriv_succ']
  simp only [smul_eq_mul]
  ring

/-- At the base point the Taylor expansion of `deriv f` is exact. -/
private lemma taylor_remainder_deriv_self (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
        iteratedDeriv (i + 1) f x * (x - x) ^ i / (Nat.factorial i : ℝ)) = deriv f x := by
  rw [Finset.sum_eq_single 0]
  · simp [iteratedDeriv_succ', iteratedDeriv_zero]
  · intro i hi hne
    simp [zero_pow hne]
  · intro h0not
    simp at h0not

/-- Taylor expansion of `deriv f` with the `n`-th order Lagrange remainder, phrased with
`k = n + 2` so that the internal summation and factorial indices stay clean. -/
private lemma taylor_remainder_deriv_aux (n : ℕ) {N : ℕ} {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ (n + 2) f (Set.Ioo (0:ℝ) (N:ℝ)))
    (hC : ∀ y ∈ Set.Ioo (0:ℝ) (N:ℝ), ‖iteratedDeriv (n + 2) f y‖ ≤ C)
    {x₀ x : ℝ} (h0 : 0 < x₀) (hx : x₀ ≤ x) (hN : x < (N:ℝ)) :
    ‖deriv f x - ∑ i ∈ Finset.range (n + 1),
        iteratedDeriv (i + 1) f x₀ * (x - x₀) ^ i / (Nat.factorial i : ℝ)‖
      ≤ C * (x - x₀) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · have hx0N : x₀ < (N:ℝ) := lt_of_le_of_lt hx hN
    have hx0 : x₀ ∈ Set.Ioo (0:ℝ) (N:ℝ) := ⟨h0, hx0N⟩
    have hderiv : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (deriv f) (Set.Ioo (0:ℝ) (N:ℝ)) :=
      ContDiffOn.deriv_of_isOpen (m := ((n : WithTop ℕ∞) + 1)) hf isOpen_Ioo
        (le_refl _)
    have hsub : Set.uIcc x₀ x ⊆ Set.Ioo (0:ℝ) (N:ℝ) := by
      intro y hy
      rw [Set.uIcc_of_le hx] at hy
      exact ⟨lt_of_lt_of_le h0 hy.1, lt_of_le_of_lt hy.2 hN⟩
    have hderiv_sub : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (deriv f) (Set.uIcc x₀ x) :=
      hderiv.mono hsub
    obtain ⟨x', hx'mem, hx'eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := deriv f) (x := x) (x₀ := x₀) (n := n)
        hlt.ne hderiv_sub
    have hsum := taylor_remainder_deriv_hsum n hderiv hx0 hlt
    have hx'N : x' ∈ Set.Ioo (0:ℝ) (N:ℝ) := by
      rw [Set.uIoo_of_lt hlt] at hx'mem
      exact ⟨lt_trans h0 hx'mem.1, lt_trans hx'mem.2 hN⟩
    have hfac : (0:ℝ) < (Nat.factorial (n + 1) : ℝ) := by positivity
    have hpow : (0:ℝ) ≤ (x - x₀) ^ (n + 1) := pow_nonneg (by linarith) _
    rw [← hsum]
    calc ‖deriv f x - taylorWithinEval (deriv f) n (Set.uIcc x₀ x) x₀ x‖
        = ‖iteratedDeriv (n + 2) f x' * (x - x₀) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)‖ := by
          rw [hx'eq, ← iteratedDeriv_succ']
      _ = ‖iteratedDeriv (n + 2) f x'‖ * (x - x₀) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
          rw [norm_div, norm_mul, Real.norm_of_nonneg hpow, Real.norm_of_nonneg hfac.le]
      _ ≤ C * (x - x₀) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC x' hx'N) hpow) hfac.le
  · rw [heq]
    rw [taylor_remainder_deriv_self n f x, sub_self, norm_zero]
    have hR : C * (x - x) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) = 0 := by
      rw [sub_self, zero_pow (by omega : n + 1 ≠ 0), mul_zero, zero_div]
    rw [hR]

namespace Work.BMF

namespace Work.BMF

/-- **Taylor expansion of the derivative, with `(k-1)`-st order remainder.**
If `f` is `C^k` on `(0,N)` with `‖f^{(k)}‖ ≤ C` there, then for `0 < x₀ ≤ x < N`,
`‖f'(x) - Σ_{i=0}^{k-2} f^{(i+1)}(x₀)(x-x₀)^i/i!‖ ≤ C (x-x₀)^{k-1}/(k-1)!`.

Both `Set.Ioo (0:ℝ) (N:ℝ)` are explicitly real, so that `hC` really bounds `f^{(k)}` on all of
`(0,N)` (an earlier version wrote `Set.Ioo 0 N` with `N : ℕ`, which Lean elaborated as `Set ℕ`,
bounding `f^{(k)}` only at integer points).

Route: apply `taylor_mean_remainder_lagrange_iteratedDeriv` to `g := deriv f` with `n := k-2` on
`uIcc x₀ x`; the Taylor polynomial of `g` of degree `k-2` is
`Σ_{i=0}^{k-2} f^{(i+1)}(x₀)(x-x₀)^i/i!` (via `iteratedDerivWithin_eq_iteratedDeriv`, and
`iteratedDeriv (i+1) f = iteratedDeriv i (deriv f)`), and the remainder is
`iteratedDeriv k f x' * (x-x₀)^{k-1}/(k-1)!` for some `x' ∈ uIoo x₀ x ⊂ (0,N)`, bounded by `C`.
The needed `ContDiffOn ℝ (k-1) (deriv f) (Ioo (0:ℝ) (N:ℝ))` follows from `ContDiffOn.derivWithin`
on the open set together with `derivWithin_of_isOpen`.  The case `x₀ = x` is trivial (both sides
are `0`). -/
theorem taylor_remainder_deriv_fixed (k : ℕ) (hk : 2 ≤ k) {N : ℕ} {f : ℝ → ℝ} {C : ℝ}
    (hf : ContDiffOn ℝ k f (Set.Ioo (0:ℝ) (N:ℝ)))
    (hC : ∀ y ∈ Set.Ioo (0:ℝ) (N:ℝ), ‖iteratedDeriv k f y‖ ≤ C)
    {x₀ x : ℝ} (h0 : 0 < x₀) (hx : x₀ ≤ x) (hN : x < (N:ℝ)) :
    ‖deriv f x - ∑ i ∈ Finset.range (k - 1),
        iteratedDeriv (i + 1) f x₀ * (x - x₀) ^ i / (Nat.factorial i : ℝ)‖
      ≤ C * (x - x₀) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  exact taylor_remainder_deriv_aux n hf hC h0 hx hN

end Work.BMF
