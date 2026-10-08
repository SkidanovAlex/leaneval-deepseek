/-
Copyright (c) 2024. All rights reserved.

# The `r`-`r` reduction of Higman's Lemma 12

This file reduces the "pinned" squaring form of Higman's Lemma 12 (case `B`) to its normal
form.  Let `F = 𝔽_{2ⁿ}`, `σ : x ↦ x^{2 ^ r}` and

`Q x y = C * x ^ (1 + 2 ^ r) + C' * y ^ (1 + 2 ^ r) + f1 * x * y ^ (2 ^ r) + f2 * x ^ (2 ^ r) * y`.

Assume `C`, `C' ≠ 0`, `Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1)` and `Q` anisotropic.  Then a change of
coordinates `Φ` and an additive automorphism `Ψ` of `F × F`, `F` bring `Q` into the normal form

`x ^ (1 + 2 ^ r) + ε * x * y ^ (2 ^ r) + y ^ (1 + 2 ^ r)`.

The reduction is explicit: with `D = C * C' + f1 * f2`, anisotropy forces `D ≠ 0`; choose `A0`
with `A0 ^ (1 + 2 ^ r) = C' ^ 2 / D` and `p` with `p ^ (2 ^ r) = f2 * A0 ^ (2 ^ r) / C'`.  Then
`Φ (x, y) = (A0 * x, y + p * x)` and `Ψ = (C'⁻¹ * ·)` do the job, with
`ε = (C' * p + f1 * A0) / C'`.

The existence of `A0` uses the coprimality hypothesis: `x ↦ x ^ (1 + 2 ^ r)` is a bijection of
`Fˣ` when `1 + 2 ^ r` is coprime to `|Fˣ| = 2 ^ n - 1`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3

/-! ## Auxiliary: powers in a finite field -/

/-- In a finite field `F`, the map `x ↦ x ^ A` is surjective on the units whenever `A` is
coprime to `|F| - 1`. -/
lemma units_pow_surjective {F : Type*} [Field F] [Finite F] {A : ℕ}
    (hcop : Nat.Coprime A (Nat.card F - 1)) :
    ∀ t : Fˣ, ∃ u : Fˣ, u ^ A = t := by
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hinj : Function.Injective fun u : Fˣ => u ^ A := by
    intro u v huv
    have huv' : u ^ A = v ^ A := huv
    have h1 : (u * v⁻¹) ^ A = 1 := by
      rw [mul_pow, inv_pow, huv', mul_inv_cancel]
    have h2 : orderOf (u * v⁻¹) ∣ A := orderOf_dvd_iff_pow_eq_one.mpr h1
    have h3 : orderOf (u * v⁻¹) ∣ Nat.card Fˣ := orderOf_dvd_natCard _
    rw [hcard] at h3
    have h4 : orderOf (u * v⁻¹) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h2 h3
    have h5 : orderOf (u * v⁻¹) = 1 := Nat.dvd_one.mp h4
    have h6 : u * v⁻¹ = 1 := orderOf_eq_one_iff.mp h5
    have h7 : u = v := by
      have h8 := mul_eq_one_iff_eq_inv.mp h6
      simpa using h8
    exact h7
  exact Finite.injective_iff_surjective.mp hinj

/-- The `r`-fold Frobenius of `GF(2 ^ n)` is the map `x ↦ x ^ (2 ^ r)`. -/
lemma frobpow_apply (n r : ℕ) (x : GaloisField 2 n) :
    ((frobeniusEquiv (GaloisField 2 n) 2) ^ r) x = x ^ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    show (frobeniusEquiv (GaloisField 2 n) 2)
        (((frobeniusEquiv (GaloisField 2 n) 2) ^ r) x) = x ^ 2 ^ (r + 1)
    rw [frobeniusEquiv_def, ih, ← pow_mul, pow_succ]

/-- Every element of `GF(2 ^ n)` is a `2 ^ r`-th power. -/
lemma exists_sq_r_eq (n r : ℕ) (y : GaloisField 2 n) : ∃ x : GaloisField 2 n, x ^ 2 ^ r = y :=
  ⟨((frobeniusEquiv (GaloisField 2 n) 2) ^ r).symm y, by
    rw [← frobpow_apply n r, RingEquiv.apply_symm_apply]⟩

/-! ## The core computation -/

/-- The algebraic content of the reduction: given the two defining relations for `A0` and `p`,
the form is brought into normal form by the substitution `(x, y) ↦ (A0 * x, y + p * x)`. -/
lemma reduce_r_r_core {F : Type*} [Field F] [CharP F 2] (r : ℕ) (C C' f1 f2 A0 p : F)
    (hC' : C' ≠ 0)
    (hA0 : A0 ^ (1 + 2 ^ r) * (C * C' + f1 * f2) = C' ^ 2)
    (hp : p ^ 2 ^ r * C' = f2 * A0 ^ 2 ^ r) :
    ∀ x y : F,
      C * (A0 * x) ^ (1 + 2 ^ r) + C' * (y + p * x) ^ (1 + 2 ^ r)
        + f1 * (A0 * x) * (y + p * x) ^ (2 ^ r) + f2 * (A0 * x) ^ (2 ^ r) * (y + p * x)
      = C' * (x ^ (1 + 2 ^ r) + (C'⁻¹ * (C' * p + f1 * A0)) * x * y ^ (2 ^ r)
          + y ^ (1 + 2 ^ r)) := by
  intro x y
  have hc1 : C' * p ^ 2 ^ r + f2 * A0 ^ 2 ^ r = 0 := by
    have h1 : f2 * A0 ^ 2 ^ r = C' * p ^ 2 ^ r := by rw [← hp, mul_comm]
    rw [h1]
    exact CharTwo.add_self_eq_zero _
  have hc2 : C' * p * p ^ 2 ^ r + f2 * A0 ^ 2 ^ r * p = 0 := by
    have h1 : f2 * A0 ^ 2 ^ r * p = C' * p * p ^ 2 ^ r := by
      rw [← hp]; ring
    rw [h1]
    exact CharTwo.add_self_eq_zero _
  have hc3 : C * A0 * A0 ^ 2 ^ r + f1 * A0 * p ^ 2 ^ r = C' := by
    apply mul_left_cancel₀ hC'
    have h2 : C' * (C * A0 * A0 ^ 2 ^ r + f1 * A0 * p ^ 2 ^ r) = C' ^ 2 := by
      rw [mul_add]
      rw [show C' * (C * A0 * A0 ^ 2 ^ r) = C * A0 * A0 ^ 2 ^ r * C' by ring]
      rw [show C' * (f1 * A0 * p ^ 2 ^ r) = f1 * A0 * (p ^ 2 ^ r * C') by ring]
      rw [hp]
      rw [show C * A0 * A0 ^ 2 ^ r * C' + f1 * A0 * (f2 * A0 ^ 2 ^ r)
          = A0 ^ (1 + 2 ^ r) * (C * C' + f1 * f2) by rw [pow_add, pow_one]; ring]
      rw [hA0]
    rw [h2, pow_two]
  have hε : C' * (C'⁻¹ * (C' * p + f1 * A0)) = C' * p + f1 * A0 := by
    rw [← mul_assoc, mul_inv_cancel₀ hC', one_mul]
  simp only [pow_add, pow_one, mul_pow, add_pow_char_pow]
  trans (((C * A0 * A0 ^ 2 ^ r + f1 * A0 * p ^ 2 ^ r)
          + (C' * p * p ^ 2 ^ r + f2 * A0 ^ 2 ^ r * p)) * (x * x ^ 2 ^ r)
        + (C' * p ^ 2 ^ r + f2 * A0 ^ 2 ^ r) * (x ^ 2 ^ r * y)
        + (C' * p + f1 * A0) * (x * y ^ 2 ^ r)
        + C' * (y * y ^ 2 ^ r))
  · ring
  · rw [hc3, hc2, hc1]
    linear_combination (norm := ring) (-(x * y ^ 2 ^ r)) * hε

/-! ## The reduction -/

theorem reduce_r_r {n : ℕ} (hn : 1 ≤ n) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    (hcop : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1))
    {C C' f1 f2 : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    (hanis : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 →
      C * v.1 ^ (1 + 2 ^ r) + C' * v.2 ^ (1 + 2 ^ r) + f1 * v.1 * v.2 ^ (2 ^ r) +
        f2 * v.1 ^ (2 ^ r) * v.2 ≠ 0) :
    ∃ (Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n))
      (Ψ : GaloisField 2 n ≃+ GaloisField 2 n) (ε : GaloisField 2 n),
      ∀ v : GaloisField 2 n × GaloisField 2 n,
        Ψ (C * (Φ v).1 ^ (1 + 2 ^ r) + C' * (Φ v).2 ^ (1 + 2 ^ r) +
            f1 * (Φ v).1 * (Φ v).2 ^ (2 ^ r) + f2 * (Φ v).1 ^ (2 ^ r) * (Φ v).2)
          = v.1 ^ (1 + 2 ^ r) + ε * v.1 * v.2 ^ (2 ^ r) + v.2 ^ (1 + 2 ^ r) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  -- Step 1: `D ≠ 0` from anisotropy.
  set D : GaloisField 2 n := C * C' + f1 * f2 with hDdef
  obtain ⟨t, ht⟩ : ∃ t : GaloisField 2 n, t ^ 2 ^ r = f2 * C'⁻¹ := exists_sq_r_eq n r _
  have hDne : D ≠ 0 := by
    have h1 := hanis (1, t) (by simp)
    simp only [one_pow, mul_one] at h1
    have hX : C + f1 * f2 * C'⁻¹ ≠ 0 := by
      intro hX0
      apply h1
      have hC't : C' * (t * (f2 * C'⁻¹)) = f2 * t := by
        rw [show C' * (t * (f2 * C'⁻¹)) = t * f2 * (C' * C'⁻¹) by ring,
          mul_inv_cancel₀ hC', mul_one]
        ring
      rw [pow_add, pow_one, ht, hC't]
      linear_combination (norm := ring) 1 * CharTwo.add_self_eq_zero (f2 * t) + 1 * hX0
    rw [hDdef]
    rw [show C * C' + f1 * f2 = C' * (C + f1 * f2 * C'⁻¹) by
      rw [mul_add]
      rw [show C' * (f1 * f2 * C'⁻¹) = f1 * f2 by
        rw [show C' * (f1 * f2 * C'⁻¹) = (f1 * f2) * (C' * C'⁻¹) by ring,
          mul_inv_cancel₀ hC', mul_one]]
      ring]
    exact mul_ne_zero hC' hX
  -- Step 2: choose `A0` with `A0 ^ (1 + 2 ^ r) = C' ^ 2 / D`.
  obtain ⟨A0, hA0⟩ : ∃ A0 : GaloisField 2 n, A0 ^ (1 + 2 ^ r) = C' ^ 2 * D⁻¹ := by
    have hne : (C' ^ 2 * D⁻¹ : GaloisField 2 n) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hC') (inv_ne_zero hDne)
    have hcopU : Nat.Coprime (1 + 2 ^ r) (Nat.card (GaloisField 2 n) - 1) := by
      rw [hcard]; exact hcop
    obtain ⟨u, hu⟩ := units_pow_surjective (F := GaloisField 2 n) hcopU
      (Units.mk0 (C' ^ 2 * D⁻¹) hne)
    refine ⟨(u : GaloisField 2 n), ?_⟩
    rw [← Units.val_pow_eq_pow_val u (1 + 2 ^ r), hu, Units.val_mk0]
  have hA0' : A0 ^ (1 + 2 ^ r) * D = C' ^ 2 := by
    rw [hA0, mul_assoc, inv_mul_cancel₀ hDne, mul_one]
  have hA0ne : A0 ≠ 0 := by
    intro h0
    have hval : A0 ^ (1 + 2 ^ r) ≠ 0 := by
      rw [hA0]
      exact mul_ne_zero (pow_ne_zero 2 hC') (inv_ne_zero hDne)
    exact hval (by rw [h0]; exact zero_pow (by positivity))
  -- Step 3: choose `p` with `p ^ (2 ^ r) = f2 * A0 ^ (2 ^ r) / C'`.
  obtain ⟨p, hp⟩ : ∃ p : GaloisField 2 n, p ^ 2 ^ r = f2 * A0 ^ 2 ^ r * C'⁻¹ :=
    exists_sq_r_eq n r _
  have hp' : p ^ 2 ^ r * C' = f2 * A0 ^ 2 ^ r := by
    rw [hp, mul_assoc, inv_mul_cancel₀ hC', mul_one]
  -- Step 4: the additive automorphisms and the constant.
  let ε : GaloisField 2 n := C'⁻¹ * (C' * p + f1 * A0)
  let Ψ : GaloisField 2 n ≃+ GaloisField 2 n :=
    { toFun := fun z => C'⁻¹ * z
      invFun := fun z => C' * z
      left_inv := fun z => by
        show C' * (C'⁻¹ * z) = z
        rw [← mul_assoc, mul_inv_cancel₀ hC', one_mul]
      right_inv := fun z => by
        show C'⁻¹ * (C' * z) = z
        rw [← mul_assoc, inv_mul_cancel₀ hC', one_mul]
      map_add' := fun a b => by rw [mul_add] }
  let Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n) :=
    { toFun := fun v => (A0 * v.1, v.2 + p * v.1)
      invFun := fun v => (A0⁻¹ * v.1, v.2 + p * (A0⁻¹ * v.1))
      left_inv := fun v => by
        ext
        · show A0⁻¹ * (A0 * v.1) = v.1
          rw [← mul_assoc, inv_mul_cancel₀ hA0ne, one_mul]
        · show (v.2 + p * v.1) + p * (A0⁻¹ * (A0 * v.1)) = v.2
          rw [show A0⁻¹ * (A0 * v.1) = v.1 by rw [← mul_assoc, inv_mul_cancel₀ hA0ne, one_mul]]
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      right_inv := fun v => by
        ext
        · show A0 * (A0⁻¹ * v.1) = v.1
          rw [← mul_assoc, mul_inv_cancel₀ hA0ne, one_mul]
        · show (v.2 + p * (A0⁻¹ * v.1)) + p * (A0⁻¹ * v.1) = v.2
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      map_add' := fun v w => by
        ext
        · show A0 * (v.1 + w.1) = A0 * v.1 + A0 * w.1
          rw [mul_add]
        · show (v.2 + w.2) + p * (v.1 + w.1) =
            (v.2 + p * v.1) + (w.2 + p * w.1)
          rw [mul_add]
          abel }
  refine ⟨Φ, Ψ, ε, fun v => ?_⟩
  have hv := reduce_r_r_core r C C' f1 f2 A0 p hC' hA0' hp' v.1 v.2
  have hΨ : ∀ z : GaloisField 2 n, Ψ z = C'⁻¹ * z := fun z => rfl
  have hΦ1 : (Φ v).1 = A0 * v.1 := rfl
  have hΦ2 : (Φ v).2 = v.2 + p * v.1 := rfl
  have hε : ε = C'⁻¹ * (C' * p + f1 * A0) := rfl
  rw [hΨ, hΦ1, hΦ2, hε, hv, ← mul_assoc, inv_mul_cancel₀ hC', one_mul]

end Work.Higman.Q3
