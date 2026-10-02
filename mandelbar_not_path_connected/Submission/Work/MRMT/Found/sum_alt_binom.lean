import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- Alternating-binomial summation by parts: the `(M+1)`-st alternating binomial
combination of `a` equals the `M`-th alternating binomial combination of the
forward differences `a (j+1) - a j`.  Equivalently it records the compatibility
`Δ^{M+1} a = Δ^M (Δ a)` between the discrete difference operator and Pascal's
triangle. -/
theorem sum_alt_binom (a : ℕ → ℂ) (M : ℕ) :
    ∑ j ∈ Finset.range (M+2), (-1 : ℂ)^(M+1-j) * ((M+1).choose j : ℂ) * a j
      = ∑ j ∈ Finset.range (M+1), (-1 : ℂ)^(M-j) * (M.choose j : ℂ) * (a (j+1) - a j) := by
  -- Per-term Pascal identity: `(-1)^(M-k) C(M+1,k+1) = (-1)^(M-k) C(M,k) - (-1)^(M-(k+1)) C(M,k+1)`.
  have key : ∀ k, k ≤ M →
      (-1:ℂ)^(M-k) * ((M+1).choose (k+1) : ℂ)
        = (-1:ℂ)^(M-k) * (M.choose k : ℂ) - (-1:ℂ)^(M-(k+1)) * (M.choose (k+1) : ℂ) := by
    intro k hk
    rcases eq_or_lt_of_le hk with h | h
    · subst h; simp
    · have hpow : (-1:ℂ)^(M-k) = - (-1:ℂ)^(M-(k+1)) := by
        have hh : M - k = (M - (k+1)) + 1 := by omega
        rw [hh, pow_succ]; ring
      have hchoose : (((M+1).choose (k+1) : ℕ) : ℂ) = ((M.choose k : ℕ):ℂ) + ((M.choose (k+1) : ℕ):ℂ) := by
        rw [Nat.choose_succ_succ']; push_cast; ring
      rw [hchoose, hpow]; ring
  -- Peel off the `j = 0` term of the left-hand side.
  rw [Finset.sum_range_succ']
  have h1 : (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M+1-(j+1)) * ((M+1).choose (j+1) : ℂ) * a (j+1))
      = ∑ j ∈ Finset.range (M+1), ((-1:ℂ)^(M-j) * (M.choose j : ℂ) - (-1:ℂ)^(M-(j+1)) * (M.choose (j+1) : ℂ)) * a (j+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ M := by rw [Finset.mem_range] at hj; omega
    have he : M + 1 - (j + 1) = M - j := by omega
    rw [he, key j hj']
  rw [h1]
  have h2 : (∑ j ∈ Finset.range (M+1), ((-1:ℂ)^(M-j) * (M.choose j : ℂ) - (-1:ℂ)^(M-(j+1)) * (M.choose (j+1) : ℂ)) * a (j+1))
      = (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-j) * (M.choose j : ℂ) * a (j+1))
        - (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-(j+1)) * (M.choose (j+1) : ℂ) * a (j+1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h2]
  have h3 : (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-j) * (M.choose j : ℂ) * (a (j+1) - a j))
      = (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-j) * (M.choose j : ℂ) * a (j+1))
        - (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-j) * (M.choose j : ℂ) * a j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h3]
  -- Telescoping: the shifted `M`-th combination of `a` differs from the unshifted one by a boundary term.
  have htel : (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-(j+1)) * (M.choose (j+1) : ℂ) * a (j+1))
      - (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-j) * (M.choose j : ℂ) * a j)
      = (-1:ℂ)^(M-(M+1)) * (M.choose (M+1) : ℂ) * a (M+1)
        - (-1:ℂ)^(M-0) * (M.choose 0 : ℂ) * a 0 := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_range_sub (fun k => (-1:ℂ)^(M-k) * (M.choose k : ℂ) * a k) (M+1)]
  have hZ : (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-j) * (M.choose j : ℂ) * a j)
      = (∑ j ∈ Finset.range (M+1), (-1:ℂ)^(M-(j+1)) * (M.choose (j+1) : ℂ) * a (j+1))
        - ((-1:ℂ)^(M-(M+1)) * (M.choose (M+1) : ℂ) * a (M+1)
            - (-1:ℂ)^(M-0) * (M.choose 0 : ℂ) * a 0) := by
    rw [← htel]; ring
  rw [hZ]
  -- The remaining boundary arithmetic: `(-1)^(M+1) a 0 = 0 - (-1)^M a 0`.
  have hF : (-1:ℂ)^(M+1-0) * ((M+1).choose 0 : ℂ) * a 0
      = (-1:ℂ)^(M-(M+1)) * (M.choose (M+1) : ℂ) * a (M+1)
        - (-1:ℂ)^(M-0) * (M.choose 0 : ℂ) * a 0 := by
    have e1 : M + 1 - 0 = M + 1 := by omega
    have e2 : M - (M + 1) = 0 := by omega
    have e3 : M - 0 = M := by omega
    rw [e1, e2, e3, pow_zero, one_mul, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self M),
      Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [pow_succ]; ring
  rw [hF]; ring

end Work.MRMT.Found
