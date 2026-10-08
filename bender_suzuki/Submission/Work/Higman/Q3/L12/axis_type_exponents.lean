import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- **The axis exponent is `2 ^ j * (1 + 2 ^ r)`.**

Let `𝔽 = 𝔽_{2ⁿ}` (`n ≥ 1`), `ν ≠ 0` with `orderOf ν = 2 ^ n - 1` (so `ν` generates `𝔽^×`),
and suppose `ν ^ (2 ^ i) * ν ^ (2 ^ j) = ν ^ a` for some `i, j < n` (this is what
`Work.Higman.Q3.L12.axis_realizable` produces, with `ν ^ a = lam`).  Then `a` is congruent,
modulo `2 ^ n - 1`, to `2 ^ j' * (1 + 2 ^ r)` for some `j', r < n`; i.e. the axis is of type
`A(n, θ)` with `θ = α ↦ α ^ (2 ^ r)`, `r = 0` being the abelian `A(n,1)`.

Proof: `ν^{2 ^ i + 2 ^ j} = ν ^ a` and `orderOf ν = 2 ^ n - 1` give `a ≡ 2 ^ i + 2 ^ j
(mod 2 ^ n - 1)` (`pow_eq_pow_iff_modEq`); if `i ≤ j` then `2 ^ i + 2 ^ j = 2 ^ i * (1 + 2 ^ (j - i))`
as integers and `j - i < n`; the case `j ≤ i` is symmetric. -/
theorem axis_type_exponents {n : ℕ} (hn : 1 ≤ n) {ν : GaloisField 2 n} (hν : ν ≠ 0)
    (hord : orderOf ν = 2 ^ n - 1)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2 ^ n - 1)
    (h : ∃ i j : ℕ, i < n ∧ j < n ∧ ν ^ (2 ^ i) * ν ^ (2 ^ j) = ν ^ a) :
    ∃ j' r : ℕ, j' < n ∧ r < n ∧ a ≡ 2 ^ j' * (1 + 2 ^ r) [MOD 2 ^ n - 1] := by
  obtain ⟨i, j, hi, hj, hh⟩ := h
  -- `ν` has finite order, since `orderOf ν = 2 ^ n - 1 > 0`.
  have hfin : IsOfFinOrder ν := by
    rw [← orderOf_pos_iff, hord]
    have := Nat.one_le_two_pow (n := n)
    omega
  -- `ν ^ (2 ^ i + 2 ^ j) = ν ^ a`, hence the exponents are congruent mod `orderOf ν`.
  have hp : ν ^ (2 ^ i + 2 ^ j) = ν ^ a := by
    rw [pow_add]; exact hh
  have hmod : (2 ^ i + 2 ^ j) ≡ a [MOD orderOf ν] := (hfin.pow_eq_pow_iff_modEq).mp hp
  rw [hord] at hmod
  -- the binary rewriting `2 ^ i + 2 ^ j = 2 ^ i * (1 + 2 ^ (j - i))`
  have key : ∀ i j : ℕ, i ≤ j → 2 ^ i * (1 + 2 ^ (j - i)) = 2 ^ i + 2 ^ j := by
    intro i j hij
    calc 2 ^ i * (1 + 2 ^ (j - i)) = 2 ^ i * 1 + 2 ^ i * 2 ^ (j - i) := Nat.mul_add _ _ _
      _ = 2 ^ i + 2 ^ (i + (j - i)) := by rw [mul_one, ← pow_add]
      _ = 2 ^ i + 2 ^ j := by rw [Nat.add_sub_cancel' hij]
  rcases le_total i j with hij | hji
  · refine ⟨i, j - i, hi, lt_of_le_of_lt (Nat.sub_le j i) hj, ?_⟩
    rw [key i j hij]
    exact hmod.symm
  · refine ⟨j, i - j, hj, lt_of_le_of_lt (Nat.sub_le i j) hi, ?_⟩
    rw [key j i hji, Nat.add_comm]
    exact hmod.symm

end Work.Higman.Q3.L12
