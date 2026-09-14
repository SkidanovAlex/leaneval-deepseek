import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval

namespace Commons.Algebra.Polynomial

open _root_.Polynomial

/-- In a domain of characteristic zero, the `k`-th Hasse derivative of `p` vanishes at `r`
if and only if the `k`-th ordinary derivative of `p` vanishes at `r`. -/
lemma hasseDeriv_eval_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : R[X]) (k : ℕ) (r : R) :
    (hasseDeriv k p).eval r = 0 ↔ (derivative^[k] p).eval r = 0 := by
  have key : (derivative^[k] p).eval r = (Nat.factorial k : R) * (hasseDeriv k p).eval r := by
    have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := R) k) p
    have h2 := congrArg (fun q : R[X] => Polynomial.eval r q) h
    rw [← h2]
    simp
  rw [key, mul_eq_zero, or_iff_right]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

/-- If the `k`-th Hasse derivative of `f` vanishes at `r` for all `k < m`, then `(X - r)^m`
divides `f`. This is Taylor's formula read coefficientwise. -/
lemma X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero {R : Type*} [CommRing R]
    (f : R[X]) (r : R) (m : ℕ)
    (h : ∀ k, k < m → (hasseDeriv k f).eval r = 0) :
    (X - C r) ^ m ∣ f := by
  rw [← sum_taylor_eq f r]
  rw [Polynomial.sum]
  apply Finset.dvd_sum
  intro i hi
  have hmi : m ≤ i := by
    by_contra hlt
    rw [not_le] at hlt
    exact (mem_support_iff.mp hi) (by rw [taylor_coeff, h i hlt])
  exact dvd_mul_of_dvd_right (pow_dvd_pow (X - C r) hmi) (C ((taylor r f).coeff i))

/-- **Univariate non-vanishing lemma.**  Let `R` be a domain of characteristic zero and let
`p ∈ R[X]` be nonzero with `natDegree p ≤ e`, and let `B ≥ 1`.  Then there is an integer `z`
with `|z| ≤ B` and a `k ≤ e / B` such that the `k`-th derivative of `p` does not vanish at `z`.

Proof: if not, then for every `z` with `|z| ≤ B` the point `z` is a root of `p` of multiplicity
at least `e/B + 1`, so summing multiplicities over the `2B + 1` distinct points of the box gives
`(2B+1)*(e/B+1) ≤ natDegree p ≤ e`, which is false. -/
theorem exists_derivative_eval_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (hp : p ≠ 0) (e B : ℕ) (hdeg : p.natDegree ≤ e) (hB : 1 ≤ B) :
    ∃ (z : ℤ) (k : ℕ), |z| ≤ (B : ℤ) ∧ k ≤ e / B ∧
      (Polynomial.derivative^[k] p).eval (z : R) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ z k, |z| ≤ B → k ≤ e / B → (derivative^[k] p).eval (z : R) = 0`
  set m : ℕ := e / B + 1 with hm
  have hm_ge : 1 ≤ m := by rw [hm]; exact Nat.le_add_left 1 _
  -- Every box point is a root of `p` of multiplicity at least `m`.
  have hroot : ∀ z : ℤ, |z| ≤ (B : ℤ) → (X - C ((z : R))) ^ m ∣ p := by
    intro z hz
    apply X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero
    intro k hk
    rw [hasseDeriv_eval_eq_zero_iff p k (z : R)]
    have hkm : k < e / B + 1 := by rw [hm] at hk; exact hk
    exact hcon z k hz (Nat.lt_succ_iff.mp hkm)
  set S : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ) with hS
  set T : Finset R := S.image (fun z : ℤ => (z : R)) with hT
  have hinj : Function.Injective (fun z : ℤ => (z : R)) :=
    fun a b hab => Int.cast_injective hab
  have hcard : T.card = 2 * B + 1 := by
    rw [hT, hS, Finset.card_image_of_injective _ hinj, Int.card_Icc]
    have hz : (B : ℤ) + 1 - (-(B : ℤ)) = ((2 * B + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hz, Int.toNat_natCast]
  -- Each point of `T` divides `p` to order `m`.
  have hdiv : ∀ t ∈ T, (X - C t) ^ m ∣ p := by
    intro t ht
    rw [hT] at ht
    obtain ⟨z, hzS, hzt⟩ := Finset.mem_image.mp ht
    rw [← hzt]
    apply hroot z
    rw [hS, Finset.mem_Icc] at hzS
    exact abs_le.mpr hzS
  have hcount : ∀ t ∈ T, m ≤ Multiset.count t p.roots := by
    intro t ht
    rw [Polynomial.count_roots, Polynomial.le_rootMultiplicity_iff hp]
    exact hdiv t ht
  -- Bundling the multiplicities of the `2B+1` distinct box points.
  have hbound : T.card * m ≤ p.natDegree := by
    have h1 : T.card * m ≤ ∑ t ∈ T, Multiset.count t p.roots := by
      rw [show T.card * m = ∑ _t ∈ T, m from
        (Finset.sum_const_nat (s := T) (f := fun _ => m) (fun _ _ => rfl)).symm]
      exact Finset.sum_le_sum hcount
    have hsub : T ⊆ p.roots.toFinset := by
      intro t ht
      rw [hT] at ht
      obtain ⟨z, hzS, hzt⟩ := Finset.mem_image.mp ht
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, ← Polynomial.dvd_iff_isRoot, ← hzt]
      exact dvd_trans (dvd_pow_self (X - C (z : R)) (by omega : m ≠ 0))
        (hroot z (by rw [hS, Finset.mem_Icc] at hzS; exact abs_le.mpr hzS))
    have h2 : ∑ t ∈ T, Multiset.count t p.roots ≤ p.natDegree :=
      calc ∑ t ∈ T, Multiset.count t p.roots
          ≤ ∑ t ∈ p.roots.toFinset, Multiset.count t p.roots :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro t _ _; exact Nat.zero_le _)
        _ = p.roots.card := Multiset.toFinset_sum_count_eq p.roots
        _ ≤ p.natDegree := Polynomial.card_roots' p
    exact h1.trans h2
  -- Arithmetic contradiction: `(2B+1)*(e/B+1) > e`.
  have harith : e < (2 * B + 1) * m := by
    rw [hm]
    have hmod : e % B < B := Nat.mod_lt e (by omega)
    have hdec : e = B * (e / B) + e % B := (Nat.div_add_mod e B).symm
    have h1 : e < B * (e / B) + B := by
      calc e = B * (e / B) + e % B := hdec
        _ < B * (e / B) + B := Nat.add_lt_add_left hmod _
    have h2 : B * (e / B) + B ≤ (2 * B + 1) * (e / B + 1) := by
      have heq : B * (e / B) + B = B * (e / B + 1) := by ring
      rw [heq]
      exact Nat.mul_le_mul_right _ (by omega)
    exact h1.trans_le h2
  rw [hcard] at hbound
  exact (not_le.mpr harith) (hbound.trans hdeg)

end Commons.Algebra.Polynomial