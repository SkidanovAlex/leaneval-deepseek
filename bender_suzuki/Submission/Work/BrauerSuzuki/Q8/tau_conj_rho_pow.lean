import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_index_zpowers_tau

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-!
# `Q₈`: conjugation by `τ` of the coset `ρ ⟨τ⟩`

Let `P = ⟨τ, ρ⟩` be a generalized quaternion group in Dade's normal form (`n ≥ 2`,
`orderOf τ = 2 ^ n`, `ρ τ ρ⁻¹ = τ⁻¹`, `ρ ^ 2 = τ ^ (2 ^ (n-1))`), and assume `n = 2`, so that
`P ≅ Q₈`, `orderOf τ = 4` and `ρ ^ 2 = τ ^ 2` is the central involution.

**The goal.**  Every element of the coset `ρ ⟨τ⟩` is *inverted* by conjugation by `τ`:
`τ * (ρ * τ ^ i) * τ⁻¹ = (ρ * τ ^ i)⁻¹` for every `i : ℕ`.

**Where the hypothesis `n = 2` enters.**  In the group defined by the above relations,

* `τ * ρ = ρ * τ⁻¹`, hence `τ * ρ * τ^i * τ⁻¹ = ρ * τ^{i-2}` (conjugation by `τ` acts on
  `ρ⟨τ⟩` as `exp ↦ exp - 2`), while
* `(ρ * τ^i)⁻¹ = τ^{-i} ρ⁻¹` and `ρ⁻¹ = ρ · ρ^2 = ρ · τ^{2^{n-1}}`, so
  `(ρ * τ^i)⁻¹ = ρ · τ^{i + 2^{n-1}}`.

The two expressions agree precisely when `2^{n-1} ≡ -2 (mod 2^n)`, i.e. when `2^{n-1} = 2`.
For `n = 2` both exponents differ by `4 = 2 ^ n`, and `τ ^ 4 = 1` makes them equal; for `n ≥ 3`
the statement is *false* in `Q_{2^{n+1}}` — conjugating `ρ` by `τ` gives `ρ τ^{-2}`, which is
different from `ρ τ^{2^{n-1}} = ρ⁻¹`.  This is why the theorem carries the hypothesis `d.n = 2`.

Everything is proved uniformly in the exponent `i` using the commutation rule
`τ ^ i * ρ * τ ^ i = ρ` (valid for every `n ≥ 2`), which is the "index-free" form of
`τ * ρ = ρ * τ⁻¹`.
-/

/-- In the normal form of a generalized quaternion group, conjugating `ρ` by `τ` inverts it:
`τ * ρ = ρ * τ⁻¹`.  Equivalently `ρ * τ = τ⁻¹ * ρ` is `ρ * τ * ρ⁻¹ = τ⁻¹` rearranged. -/
theorem tau_mul_rho_eq_rho_mul_tau_inv {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) : d.tau * d.rho = d.rho * d.tau⁻¹ := by
  have h1 : d.rho * d.tau = d.tau⁻¹ * d.rho := by rw [← d.rho_conj]; group
  calc d.tau * d.rho = d.tau * (d.rho * d.tau) * d.tau⁻¹ := by group
    _ = d.tau * (d.tau⁻¹ * d.rho) * d.tau⁻¹ := by rw [h1]
    _ = d.rho * d.tau⁻¹ := by group

/-- In the normal form of a generalized quaternion group, `τ ^ k * ρ * τ ^ k = ρ` for every
`k : ℕ`: equivalently `τ ^ k * ρ = ρ * (τ ^ k)⁻¹`, i.e. `τ ^ k` conjugates `ρ` to its inverse.
(No hypothesis on `n` beyond `n ≥ 2` is needed.) -/
theorem tau_pow_mul_rho_mul_tau_pow {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (k : ℕ) :
    d.tau ^ k * d.rho * d.tau ^ k = d.rho := by
  have hτρ : d.tau * d.rho = d.rho * d.tau⁻¹ := tau_mul_rho_eq_rho_mul_tau_inv d
  have hτρτ : d.tau * d.rho * d.tau = d.rho := by rw [hτρ]; group
  induction k with
  | zero => simp
  | succ k ih =>
    calc d.tau ^ (k + 1) * d.rho * d.tau ^ (k + 1)
        = d.tau * (d.tau ^ k * d.rho * d.tau ^ k) * d.tau := by group
      _ = d.tau * d.rho * d.tau := by rw [ih]
      _ = d.rho := hτρτ

/-- With `n = 2` (so `P ≅ Q₈`), the generator `τ` has order `4`, hence `τ ^ 4 = 1`. -/
theorem tau_pow_four_eq_one_of_n_eq_two {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (h2 : d.n = 2) : d.tau ^ 4 = 1 := by
  have h : orderOf d.tau = 4 := by rw [d.tau_order, h2]; norm_num
  rw [← h]; exact pow_orderOf_eq_one d.tau

/-- With `n = 2` (so `P ≅ Q₈`), `τ⁻¹ = τ ^ 3`. -/
theorem tau_inv_eq_tau_cube_of_n_eq_two {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (h2 : d.n = 2) : d.tau⁻¹ = d.tau ^ 3 :=
  inv_eq_of_mul_eq_one_left
    (by rw [← pow_succ, show (3 + 1 : ℕ) = 4 from rfl, tau_pow_four_eq_one_of_n_eq_two d h2])

/-- With `n = 2` (so `P ≅ Q₈`), `ρ ^ 2 = τ ^ 2` is the central involution, written here as a
product so that it is directly usable as a rewrite rule in a group computation. -/
theorem rho_mul_rho_eq_tau_mul_tau_of_n_eq_two {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (h2 : d.n = 2) :
    d.rho * d.rho = d.tau * d.tau := by
  have h := d.rho_sq
  rw [h2] at h
  norm_num at h
  rw [← pow_two, ← pow_two]
  exact h

/-- **`Q₈`**: conjugation by `τ` inverts every element of the coset `ρ ⟨τ⟩`, i.e. every element
`ρ * τ ^ i`.  This is the `n = 2` case of the general computation described in the module
docstring; `n = 2` is exactly the case in which the two exponents can be matched. -/
theorem tau_conj_rho_pow {P : Type*} [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P)
    (h2 : d.n = 2) (i : ℕ) :
    d.tau * (d.rho * d.tau ^ i) * d.tau⁻¹ = (d.rho * d.tau ^ i)⁻¹ := by
  have htau4 : d.tau ^ 4 = 1 := tau_pow_four_eq_one_of_n_eq_two d h2
  have htau_inv : d.tau⁻¹ = d.tau ^ 3 := tau_inv_eq_tau_cube_of_n_eq_two d h2
  -- the commutation rule `τ ^ i * ρ * τ ^ i = ρ`
  have hconj : d.tau ^ i * d.rho * d.tau ^ i = d.rho := tau_pow_mul_rho_mul_tau_pow d i
  -- hence `τ ^ i * ρ = ρ * (τ ^ i)⁻¹`
  have hswap : d.tau ^ i * d.rho = d.rho * (d.tau ^ i)⁻¹ := by
    calc d.tau ^ i * d.rho = d.tau ^ i * d.rho * d.tau ^ i * (d.tau ^ i)⁻¹ := by group
      _ = d.rho * (d.tau ^ i)⁻¹ := by rw [hconj]
  -- `ρ * τ ^ i` and `ρ * τ ^ (i+2)` are inverse to one another
  have hR : (d.rho * d.tau ^ i)⁻¹ = d.rho * d.tau ^ (i + 2) := by
    apply inv_eq_of_mul_eq_one_right
    calc (d.rho * d.tau ^ i) * (d.rho * d.tau ^ (i + 2))
        = d.rho * (d.tau ^ i * d.rho) * d.tau ^ (i + 2) := by group
      _ = d.rho * (d.rho * (d.tau ^ i)⁻¹) * d.tau ^ (i + 2) := by rw [hswap]
      _ = d.rho * d.rho * (d.tau ^ i)⁻¹ * d.tau ^ (i + 2) := by group
      _ = d.tau * d.tau * (d.tau ^ i)⁻¹ * d.tau ^ (i + 2) := by
            rw [rho_mul_rho_eq_tau_mul_tau_of_n_eq_two d h2]
      _ = 1 := by
        -- `τ ^ 2 * (τ ^ i)⁻¹ * τ ^ (i+2) = τ ^ (4 * (i+1)) = (τ ^ 4) ^ (i+1) = 1`
        rw [← pow_two, ← inv_pow, htau_inv, ← pow_mul]
        rw [← pow_add, ← pow_add]
        rw [show 2 + 3 * i + (i + 2) = 4 * (i + 1) from by ring, pow_mul, htau4, one_pow]
  -- conjugation by `τ`: `τ * ρ * τ ^ i * τ⁻¹ = ρ * τ ^ 3 * τ ^ i * τ ^ 3 = ρ * τ ^ (i+2)`
  have hL : d.tau * (d.rho * d.tau ^ i) * d.tau⁻¹ = d.rho * d.tau ^ (i + 2) := by
    calc d.tau * (d.rho * d.tau ^ i) * d.tau⁻¹
        = d.tau * d.rho * d.tau ^ i * d.tau⁻¹ := by group
      _ = d.rho * d.tau⁻¹ * d.tau ^ i * d.tau⁻¹ := by rw [tau_mul_rho_eq_rho_mul_tau_inv d]
      _ = d.rho * d.tau ^ 3 * d.tau ^ i * d.tau ^ 3 := by rw [htau_inv]
      _ = d.rho * (d.tau ^ 3 * d.tau ^ i * d.tau ^ 3) := by group
      _ = d.rho * d.tau ^ (i + 2) := by
            rw [← pow_add, ← pow_add]
            rw [show 3 + i + 3 = i + 2 + 4 from by ring, pow_add, htau4, mul_one]
  rw [hL, hR]

end Work.BrauerSuzuki.Q8
