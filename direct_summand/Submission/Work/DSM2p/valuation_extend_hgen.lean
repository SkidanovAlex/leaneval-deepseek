import Mathlib

/-!
# `Work.DSM2p.valuation_extend_hgen`

Let `S ⊆ R` be a subring and let `x ∈ S` be such that every `y ∈ R` becomes an element of `S`
after multiplication by a suitable power of `x` (`y * xⁿ ∈ S`).  Then any valuation `v` on `S`
with `v x ≠ 0` extends to `R` (agreeing with `v` on `S` and at `x`).

The extension is the "expected" one: for `y ∈ R` choose `n, s` with `y * x ^ n = s` and set
`v' y = v s / (v x) ^ n`.  This is well defined: if also `y * x ^ m = s'` then `s * x ^ m` and
`s' * x ^ n` are two elements of `S` with the same image in `R`, hence are equal (the inclusion
`S ↪ R` is injective), and then cross multiplying by the nonzero element `v x` shows that the
two candidate values coincide.

## Main results

* `div_pow_eq_div_pow`, `max_div_div_eq`, `mul_pow_div_pow_add` : elementary arithmetic in a
  commutative group with zero, used to run the verification of the valuation axioms.
* `valuation_extend_hgen` : the extension theorem.
-/

namespace Work.DSM2p

open scoped Classical

/-- In a commutative group with zero, `a / u ^ m = b / u ^ n` as soon as `a * u ^ n = b * u ^ m`
and `u ≠ 0`. -/
lemma div_pow_eq_div_pow {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b u : Γ} (hu : u ≠ 0)
    {m n : ℕ} (h : a * u ^ n = b * u ^ m) : a / u ^ m = b / u ^ n := by
  rw [div_eq_div_iff (pow_ne_zero m hu) (pow_ne_zero n hu)]
  exact h

/-- Division by `c` distributes over `max`. -/
lemma max_div_div_eq {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (a b c : Γ) :
    max a b / c = max (a / c) (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, max_mul_mul_right]

/-- `a * u ^ m / u ^ (n + m) = a / u ^ n` for `u ≠ 0`. -/
lemma mul_pow_div_pow_add {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a u : Γ} (hu : u ≠ 0)
    (m n : ℕ) : a * u ^ m / u ^ (n + m) = a / u ^ n := by
  rw [pow_add, mul_div_mul_right a (u ^ n) (pow_ne_zero m hu)]

theorem valuation_extend_hgen {R : Type*} [CommRing R] (S : Subring R) (x : S)
    (hgen : ∀ y : R, ∃ n : ℕ, ∃ s : S, y * (x : R) ^ n = (s : R))
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation S Γ) (hvx : v x ≠ 0) :
    ∃ v' : Valuation R Γ, (∀ s : S, v' (s : R) = v s) ∧ v' (x : R) = v x := by
  classical
  -- choose, for every `y : R`, an exponent `N y` and an element `sOf y : S` with
  -- `y * x ^ (N y) = sOf y`.
  let N : R → ℕ := fun y => (hgen y).choose
  let sOf : R → S := fun y => (hgen y).choose_spec.choose
  have spec : ∀ y : R, y * (x : R) ^ (N y) = (sOf y : R) :=
    fun y => (hgen y).choose_spec.choose_spec
  have hu : v x ≠ 0 := hvx
  -- the candidate extension
  let v' : R → Γ := fun y => v (sOf y) / (v x) ^ (N y)
  -- `v'` does not depend on the chosen representative
  have key : ∀ (y : R) (n : ℕ) (s : S), y * (x : R) ^ n = (s : R) → v' y = v s / (v x) ^ n := by
    intro y n s hy
    have hS : (sOf y) * x ^ n = s * x ^ (N y) := by
      apply Subtype.coe_injective
      push_cast
      rw [← spec y, ← hy]
      ring
    have hv : v (sOf y) * (v x) ^ n = v s * (v x) ^ (N y) := by
      have h2 := congrArg v hS
      simpa [Valuation.map_mul, Valuation.map_pow] using h2
    exact div_pow_eq_div_pow hu hv
  have hzero : v' 0 = 0 := by
    rw [key 0 0 (0 : S) (by simp)]
    simp
  have hone : v' 1 = 1 := by
    rw [key 1 0 (1 : S) (by simp)]
    simp
  have hmul : ∀ y z : R, v' (y * z) = v' y * v' z := by
    intro y z
    have hyz : (y * z) * (x : R) ^ (N y + N z) = ((sOf y * sOf z : S) : R) := by
      push_cast
      rw [← spec y, ← spec z, pow_add]
      ring
    rw [key (y * z) (N y + N z) (sOf y * sOf z) hyz]
    show v (sOf y * sOf z) / (v x) ^ (N y + N z)
        = v (sOf y) / (v x) ^ (N y) * (v (sOf z) / (v x) ^ (N z))
    rw [Valuation.map_mul, div_mul_div_comm, ← pow_add]
  have hadd : ∀ y z : R, v' (y + z) ≤ max (v' y) (v' z) := by
    intro y z
    have hyd : (y + z) * (x : R) ^ (N y + N z)
        = ((sOf y * x ^ (N z) + sOf z * x ^ (N y) : S) : R) := by
      push_cast
      rw [← spec y, ← spec z, pow_add]
      ring
    rw [key (y + z) (N y + N z) (sOf y * x ^ (N z) + sOf z * x ^ (N y)) hyd]
    have hc : (0 : Γ) < (v x) ^ (N y + N z) := pow_pos (pos_iff_ne_zero.mpr hu) _
    calc v (sOf y * x ^ (N z) + sOf z * x ^ (N y)) / (v x) ^ (N y + N z)
        ≤ max (v (sOf y) * (v x) ^ (N z)) (v (sOf z) * (v x) ^ (N y))
            / (v x) ^ (N y + N z) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hc)
          simpa [Valuation.map_mul, Valuation.map_pow] using
            Valuation.map_add v (sOf y * x ^ (N z)) (sOf z * x ^ (N y))
      _ = max (v (sOf y) / (v x) ^ (N y)) (v (sOf z) / (v x) ^ (N z)) := by
          rw [max_div_div_eq]
          congr 1
          · exact mul_pow_div_pow_add hu (N z) (N y)
          · rw [Nat.add_comm (N y) (N z)]
            exact mul_pow_div_pow_add hu (N y) (N z)
      _ = max (v' y) (v' z) := rfl
  have h1 : ∀ s : S, v' (s : R) = v s := by
    intro s
    rw [key (s : R) 0 s (by simp)]
    simp
  have h2 : v' (x : R) = v x := by
    rw [key (x : R) 1 (x * x) (by rw [pow_one, Subring.coe_mul])]
    rw [Valuation.map_mul, pow_one, mul_div_cancel_right₀ _ hu]
  let F : R →*₀ Γ :=
    { toFun := v'
      map_zero' := hzero
      map_one' := hone
      map_mul' := hmul }
  let v'' : Valuation R Γ := { toMonoidWithZeroHom := F, map_add_le_max' := hadd }
  exact ⟨v'', h1, h2⟩

end Work.DSM2p
