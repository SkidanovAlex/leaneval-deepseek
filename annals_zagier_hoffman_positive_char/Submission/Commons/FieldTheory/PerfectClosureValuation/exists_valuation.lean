import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.RingTheory.Valuation.Basic

/-!
# Extending a `ℚᵐ⁰`-valued valuation to the perfect closure

Let `K` be a field of prime characteristic `p` and let `v : K → ℚᵐ⁰` be a valuation.
Since the value group `ℚᵐ⁰` is `p`-divisible (indeed divisible), `v` admits a unique extension
`w` to the perfect closure `PerfectClosure K p` of `K` with the property that the value of the
`p ^ n`-th root `PerfectClosure.mk K p (n, a)` of `a` is a `p ^ n`-th root of `v a`, i.e.

`w (PerfectClosure.mk K p (n, a)) ^ (p ^ n) = v a`.

This file constructs that extension.

## Implementation

The `p ^ n`-th root in the multiplicative group `ℚᵐ⁰` is realised by the map
`root p n x = exp (log x / p ^ n)` (with `root p n 0 = 0`), which is the unique `y` with
`y ^ (p ^ n) = x`.  It is multiplicative and monotone, and satisfies
`root p (m + n) (x ^ (p ^ n)) = root p m x`.  These are exactly the properties needed to check
that the formula `w (mk (n, a)) = root p n (v a)` is well defined (compatible with the relation
defining the perfect closure), multiplicative and satisfies the ultrametric inequality.
-/

namespace Commons.FieldTheory.PerfectClosureValuation

open scoped WithZero

section Root

/-- For `x : ℚᵐ⁰` and `n : ℕ`, `root p n x` is the unique `y` with `y ^ (p ^ n) = x`. -/
noncomputable def root (p n : ℕ) (x : WithZero (Multiplicative ℚ)) : WithZero (Multiplicative ℚ) :=
  if x = 0 then 0 else WithZero.exp (WithZero.log x / (p : ℚ) ^ n)

@[simp] lemma root_zero (p n : ℕ) : root p n 0 = 0 := by
  simp [root]

lemma root_of_ne_zero (p n : ℕ) {x : WithZero (Multiplicative ℚ)} (hx : x ≠ 0) :
    root p n x = WithZero.exp (WithZero.log x / (p : ℚ) ^ n) := by
  rw [root, if_neg hx]

lemma root_ne_zero (p n : ℕ) {x : WithZero (Multiplicative ℚ)} (hx : x ≠ 0) :
    root p n x ≠ 0 := by
  rw [root_of_ne_zero p n hx]
  exact WithZero.exp_ne_zero

lemma root_pow (p n : ℕ) (hp : p ≠ 0) (x : WithZero (Multiplicative ℚ)) :
    root p n x ^ (p ^ n) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [root_zero, zero_pow (pow_ne_zero n hp)]
  · rw [root_of_ne_zero p n hx, ← WithZero.exp_nsmul]
    have hp0 : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
    have hc : (p : ℚ) ^ n ≠ 0 := ne_of_gt (pow_pos hp0 n)
    have harith : (p ^ n) • (WithZero.log x / (p : ℚ) ^ n) = WithZero.log x := by
      rw [nsmul_eq_mul, Nat.cast_pow, ← mul_div_assoc, mul_div_cancel_left₀ _ hc]
    rw [harith, WithZero.exp_log hx]

lemma root_mono (p n : ℕ) (hp : p ≠ 0) : Monotone (root p n) := by
  intro x y hxy
  rcases eq_or_ne x 0 with rfl | hx
  · rw [root_zero]; exact zero_le
  rcases eq_or_ne y 0 with rfl | hy
  · exact absurd (le_antisymm hxy zero_le) hx
  rw [root_of_ne_zero p n hx, root_of_ne_zero p n hy, WithZero.exp_le_exp]
  have hp0 : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
  rw [div_le_div_iff_of_pos_right (pow_pos hp0 n)]
  exact (WithZero.log_le_log hx hy).mpr hxy

lemma root_mul (p n : ℕ) (x y : WithZero (Multiplicative ℚ)) :
    root p n (x * y) = root p n x * root p n y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [root]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [root]
  rw [root_of_ne_zero p n (mul_ne_zero hx hy), root_of_ne_zero p n hx, root_of_ne_zero p n hy,
    WithZero.log_mul hx hy, add_div, WithZero.exp_add]

lemma root_max (p n : ℕ) (hp : p ≠ 0) (x y : WithZero (Multiplicative ℚ)) :
    root p n (max x y) = max (root p n x) (root p n y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (root_mono p n hp h)]
  · rw [max_eq_left h, max_eq_left (root_mono p n hp h)]

lemma root_pow_eq (p m n : ℕ) (hp : p ≠ 0) (x : WithZero (Multiplicative ℚ)) :
    root p (m + n) (x ^ (p ^ n)) = root p m x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_pow (pow_ne_zero n hp), root_zero, root_zero]
  · rw [root_of_ne_zero p (m + n) (pow_ne_zero _ hx), root_of_ne_zero p m hx, WithZero.log_pow]
    have hp0 : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
    have hc : (p : ℚ) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hp0)
    rw [nsmul_eq_mul, Nat.cast_pow, pow_add]
    congr 1
    rw [mul_comm ((p : ℚ) ^ m) ((p : ℚ) ^ n), mul_div_mul_left _ _ hc]

lemma root_pow_eq' (p m n : ℕ) (hp : p ≠ 0) (x : WithZero (Multiplicative ℚ)) :
    root p (m + n) (x ^ (p ^ m)) = root p n x := by
  rw [Nat.add_comm]
  exact root_pow_eq p n m hp x

end Root

section Valuation

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The candidate valuation on `PerfectClosure K p`, defined by
`w (mk (n, a)) = root p n (v a)`. -/
noncomputable def wFun (v : Valuation K (WithZero (Multiplicative ℚ))) :
    PerfectClosure K p → WithZero (Multiplicative ℚ) :=
  fun x => PerfectClosure.liftOn x (fun z : ℕ × K => root p z.1 (v z.2)) (by
    rintro ⟨n, a⟩ ⟨m, b⟩ h
    cases h
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    simp only []
    rw [frobenius_def, map_pow]
    simpa only [pow_one] using (root_pow_eq p n 1 hp (v a)).symm)

@[simp] lemma wFun_mk (v : Valuation K (WithZero (Multiplicative ℚ))) (n : ℕ) (a : K) :
    wFun v (PerfectClosure.mk K p (n, a)) = root p n (v a) := by
  rw [wFun, PerfectClosure.liftOn_mk]

lemma wFun_mul_mk (v : Valuation K (WithZero (Multiplicative ℚ))) (m n : ℕ) (a b : K) :
    wFun v (PerfectClosure.mk K p (m, a) * PerfectClosure.mk K p (n, b)) =
      wFun v (PerfectClosure.mk K p (m, a)) * wFun v (PerfectClosure.mk K p (n, b)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [PerfectClosure.mk_mul_mk]
  simp only [wFun_mk]
  rw [map_mul, root_mul]
  have hA : root p (m + n) (v ((⇑(frobenius K p))^[n] a)) = root p m (v a) := by
    rw [iterate_frobenius, map_pow, root_pow_eq p m n hp]
  have hB : root p (m + n) (v ((⇑(frobenius K p))^[m] b)) = root p n (v b) := by
    rw [iterate_frobenius, map_pow, root_pow_eq' p m n hp]
  rw [hA, hB]

lemma wFun_add_mk (v : Valuation K (WithZero (Multiplicative ℚ))) (m n : ℕ) (a b : K) :
    wFun v (PerfectClosure.mk K p (m, a) + PerfectClosure.mk K p (n, b)) ≤
      max (wFun v (PerfectClosure.mk K p (m, a))) (wFun v (PerfectClosure.mk K p (n, b))) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [PerfectClosure.mk_add_mk]
  simp only [wFun_mk]
  have hA : root p (m + n) (v ((⇑(frobenius K p))^[n] a)) = root p m (v a) := by
    rw [iterate_frobenius, map_pow, root_pow_eq p m n hp]
  have hB : root p (m + n) (v ((⇑(frobenius K p))^[m] b)) = root p n (v b) := by
    rw [iterate_frobenius, map_pow, root_pow_eq' p m n hp]
  refine le_trans (root_mono p (m + n) hp (map_add_le_max v _ _)) ?_
  rw [root_max p (m + n) hp, hA, hB]

/-- The extension of `v` to the perfect closure as a valuation. -/
noncomputable def toValuation (v : Valuation K (WithZero (Multiplicative ℚ))) :
    Valuation (PerfectClosure K p) (WithZero (Multiplicative ℚ)) where
  toFun := wFun v
  map_one' := by
    rw [PerfectClosure.one_def, wFun_mk, map_one]
    simp [root]
  map_zero' := by
    rw [PerfectClosure.zero_def, wFun_mk, map_zero, root_zero]
  map_mul' := by
    intro x y
    revert y
    refine PerfectClosure.induction_on x ?_
    rintro ⟨m, a⟩ y
    refine PerfectClosure.induction_on y ?_
    rintro ⟨n, b⟩
    exact wFun_mul_mk v m n a b
  map_add_le_max' := by
    intro x y
    revert y
    refine PerfectClosure.induction_on x ?_
    rintro ⟨m, a⟩ y
    refine PerfectClosure.induction_on y ?_
    rintro ⟨n, b⟩
    exact wFun_add_mk v m n a b

end Valuation

theorem exists_valuation {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (v : Valuation K (WithZero (Multiplicative ℚ))) :
    ∃ w : Valuation (PerfectClosure K p) (WithZero (Multiplicative ℚ)),
      (∀ a : K, w (PerfectClosure.of K p a) = v a) ∧
      (∀ (n : ℕ) (a : K), w (PerfectClosure.mk K p (n, a)) ^ p ^ n = v a) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  refine ⟨toValuation v, ?_, ?_⟩
  · intro a
    change wFun v (PerfectClosure.of K p a) = v a
    rw [PerfectClosure.of_apply, wFun_mk]
    have h := root_pow p 0 hp (v a)
    simpa using h
  · intro n a
    change wFun v (PerfectClosure.mk K p (n, a)) ^ p ^ n = v a
    rw [wFun_mk]
    exact root_pow p n hp (v a)

end Commons.FieldTheory.PerfectClosureValuation