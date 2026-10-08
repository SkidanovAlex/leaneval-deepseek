/-
# The reduction `reduce_r_s`: rescaling one coordinate of a two-step squaring form

This file proves `Work.Higman.Q3.reduce_r_s`, one of the "reductions" used in the
classification (Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), Lemma 12) of the
squaring form of a two-step group of order `q ^ 3`, `q = 2 ^ n`.

Concretely, over the field `F = GF(2ⁿ)` (here `GaloisField 2 n`) one considers the map

  `v ↦ C * v.1 ^ (1 + 2 ^ r) + C' * v.2 ^ (1 + 2 ^ (2 * r)) + f * v.1 ^ (2 ^ (3 * r)) * v.2 ^ (2 ^ r)`,

an expression with two pure terms of exponents `1 + 2 ^ r`, `1 + 2 ^ (2r)` and one mixed term.
The statement asserts that, for `C`, `C'` nonzero and `1 + 2 ^ r` coprime to `2 ^ n - 1`, one
can bring the two pure coefficients to `1` by an *additive* change of coordinates `Φ` of
`F × F` followed by an additive isomorphism `Ψ` of `F`, at the cost of a residual coefficient
`ε` on the mixed term.

The proof is elementary: because `1 + 2 ^ r` is coprime to `|Fˣ| = 2 ^ n - 1`, the power map
`a ↦ a ^ (1 + 2 ^ r)` is a bijection of `Fˣ` (`pow_surjective_units`), so we may choose
`a ≠ 0` with `C * a ^ (1 + 2 ^ r) = C'`.  Then the diagonal transformation
`Φ (x, y) = (a * x, y)` together with the scalar isomorphism `Ψ z = C'⁻¹ * z` does the job, with
`ε = C'⁻¹ * f * a ^ (2 ^ (3 * r))`.  The remaining hypotheses (`0 < r`, `r < n`, coprimality of
`1 + 2 ^ (2 * r)`, `5 * r % n = 0`) are part of the ambient setting and are not needed here.

## Main results

* `Work.Higman.Q3.scaleEquiv`, `Work.Higman.Q3.prodScaleEquiv`: the additive equivalences
  `x ↦ a * x` (for `a ≠ 0`) on `F` and on `F × F`.
* `Work.Higman.Q3.pow_surjective_units`: in a finite field, `a ↦ a ^ k` is onto `Fˣ` as soon as
  `k` is coprime to `|Fˣ| = Fintype.card F - 1`.
* `Work.Higman.Q3.reduce_r_s`: the requested reduction.
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
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Q3

/-! ## Additive equivalences given by scaling -/

/-- Multiplication by a nonzero element of a field, as an additive equivalence. -/
def scaleEquiv {F : Type*} [Field F] (a : F) (ha : a ≠ 0) : F ≃+ F where
  toFun := fun x => a * x
  invFun := fun x => a⁻¹ * x
  left_inv := by
    intro x
    change a⁻¹ * (a * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  right_inv := by
    intro x
    change a * (a⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  map_add' := by
    intro x y
    rw [mul_add]

@[simp] theorem scaleEquiv_apply {F : Type*} [Field F] (a : F) (ha : a ≠ 0) (x : F) :
    scaleEquiv a ha x = a * x := rfl

/-- `(x, y) ↦ (a * x, y)` on `F × F`, as an additive equivalence (for `a ≠ 0`). -/
def prodScaleEquiv {F : Type*} [Field F] (a : F) (ha : a ≠ 0) : F × F ≃+ F × F where
  toFun := fun v => (a * v.1, v.2)
  invFun := fun v => (a⁻¹ * v.1, v.2)
  left_inv := by
    intro v
    change (a⁻¹ * (a * v.1), v.2) = v
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  right_inv := by
    intro v
    change (a * (a⁻¹ * v.1), v.2) = v
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  map_add' := by
    intro u v
    change (a * (u.1 + v.1), u.2 + v.2) = (a * u.1, u.2) + (a * v.1, v.2)
    rw [mul_add]
    rfl

@[simp] theorem prodScaleEquiv_apply {F : Type*} [Field F] (a : F) (ha : a ≠ 0) (v : F × F) :
    prodScaleEquiv a ha v = (a * v.1, v.2) := rfl

/-! ## Power maps on the units of a finite field -/

/-- In a finite field `F`, if `k` is coprime to `Fintype.card F - 1 = |Fˣ|`, then the power map
`a ↦ a ^ k` is surjective on the units: every nonzero element of `F` is a `k`-th power. -/
theorem pow_surjective_units {F : Type*} [Field F] [Fintype F]
    {k : ℕ} (hk : Nat.Coprime k (Fintype.card F - 1)) {y : F} (hy : y ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a ^ k = y := by
  have hinj : Function.Injective (fun x : Fˣ => x ^ k) := by
    intro x z hxz
    have hxz' : x ^ k = z ^ k := hxz
    have hc : (x * z⁻¹) ^ k = 1 := by
      rw [mul_pow, inv_pow, hxz', mul_inv_cancel]
    have h1 : orderOf (x * z⁻¹) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hc
    have h2 : orderOf (x * z⁻¹) ∣ Fintype.card F - 1 := by
      refine orderOf_dvd_iff_pow_eq_one.mpr ?_
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
    have h3 : orderOf (x * z⁻¹) ∣ 1 := by
      have h := Nat.dvd_gcd h1 h2
      have hk' : k.gcd (Fintype.card F - 1) = 1 := hk
      rwa [hk'] at h
    have h4 : x * z⁻¹ = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.dvd_one.mp h3
    exact mul_inv_eq_one.mp h4
  have hsurj : Function.Surjective (fun x : Fˣ => x ^ k) :=
    Finite.injective_iff_surjective.mp hinj
  obtain ⟨a, ha⟩ := hsurj (Units.mk0 y hy)
  have ha' : a ^ k = Units.mk0 y hy := ha
  exact ⟨(a : F), Units.ne_zero a, by rw [← Units.val_pow_eq_pow_val, ha', Units.val_mk0]⟩

/-! ## The algebraic normal form -/

/-- Pure bookkeeping: with `C * P = C'`, `ψ * C' = 1` and `ε = ψ * f * Q`, rescaling the three
terms of the form by `ψ` puts the two pure coefficients equal to `1`. -/
theorem rescale_identity {F : Type*} [CommSemiring F] (C C' f P X Y Q W y ψ ε : F)
    (hCa : C * P = C') (hψ : ψ * C' = 1) (hε : ε = ψ * f * Q) :
    ψ * (C * (P * X) + C' * Y + f * (Q * W) * y) = X + ε * W * y + Y := by
  have h1' : C * (P * X) = C' * X := by rw [← mul_assoc, hCa]
  have h1 : ψ * (C * (P * X)) = X := by rw [h1', ← mul_assoc, hψ, one_mul]
  have h2 : ψ * (C' * Y) = Y := by rw [← mul_assoc, hψ, one_mul]
  have h3 : ψ * (f * (Q * W) * y) = ε * W * y := by
    rw [hε]; ring
  rw [mul_add, mul_add, h1, h2, h3]
  ring

/-! ## The reduction -/

theorem reduce_r_s {n : ℕ} (hn : 1 ≤ n) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    (hcop : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1))
    (hcop2 : Nat.Coprime (1 + 2 ^ (2 * r)) (2 ^ n - 1)) (h5 : 5 * r % n = 0)
    {C C' f : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0) :
    ∃ (Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n))
      (Ψ : GaloisField 2 n ≃+ GaloisField 2 n) (ε : GaloisField 2 n),
      ∀ v : GaloisField 2 n × GaloisField 2 n,
        Ψ (C * (Φ v).1 ^ (1 + 2 ^ r) + C' * (Φ v).2 ^ (1 + 2 ^ (2 * r)) +
            f * (Φ v).1 ^ (2 ^ (3 * r)) * (Φ v).2 ^ (2 ^ r))
          = v.1 ^ (1 + 2 ^ r) + ε * v.1 ^ (2 ^ (3 * r)) * v.2 ^ (2 ^ r) +
              v.2 ^ (1 + 2 ^ (2 * r)) := by
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  -- the cardinality of the field is `2 ^ n`
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have hcop' : Nat.Coprime (1 + 2 ^ r) (Fintype.card (GaloisField 2 n) - 1) := by
    rw [hcard]; exact hcop
  -- choose `a ≠ 0` with `a ^ (1 + 2 ^ r) = C' / C`, so that `C * a ^ (1 + 2 ^ r) = C'`
  obtain ⟨a, ha, haeq⟩ :=
    pow_surjective_units hcop' (y := C' / C) (div_ne_zero hC' hC)
  have hCa : C * a ^ (1 + 2 ^ r) = C' := by
    rw [haeq]
    field_simp
  refine ⟨prodScaleEquiv a ha, scaleEquiv C'⁻¹ (inv_ne_zero hC'),
    C'⁻¹ * f * a ^ (2 ^ (3 * r)), ?_⟩
  intro v
  simp only [prodScaleEquiv_apply, scaleEquiv_apply, mul_pow]
  exact rescale_identity C C' f (a ^ (1 + 2 ^ r)) (v.1 ^ (1 + 2 ^ r))
    (v.2 ^ (1 + 2 ^ (2 * r))) (a ^ (2 ^ (3 * r))) (v.1 ^ (2 ^ (3 * r))) (v.2 ^ (2 ^ r))
    C'⁻¹ (C'⁻¹ * f * a ^ (2 ^ (3 * r))) hCa (inv_mul_cancel₀ hC') rfl

end Work.Higman.Q3
