import Mathlib
import Submission.Work.HP.Vero.MulDefs

/-!
# Associativity of `mulVec`

`mulVec a b d A B` (`Work.HP.Vero.mulVec`) is the coefficient vector of the product of the forms
with coefficient vectors `A` and `B`.  This file proves that this product is associative, i.e.
that multiplying the degree-`a` vector `A` by the product `B · C` (a degree-`b+c` vector) gives
the same result as multiplying the product `A · B` (a degree-`a+b` vector) by `C`.

The proof is a purely combinatorial rearrangement of the finite sums defining `mulVec`.  The
defining condition

`DecP x y M : ∀ i, (x.1 i : ℕ) + (y.1 i : ℕ) = (M.1 i : ℕ)`

only involves the *components* of `x`, `y` and `M` (not their degrees), which lets us treat the
degree mismatch `a + (b + c)` vs `(a + b) + c` uniformly.  The three elementary ingredients are

* `DecP_iff_addMon` : the componentwise condition is the equation `addMon x y = M`;
* `collapse_left`/`collapse_right` : the standard collapse of a sum in which an indicator on the
  middle index `q` is used to substitute `q = addMon p1 p2`;
* `DecP_assoc` : `DecP (addMon p q) r M ↔ DecP p (addMon q r) M` (associativity of `Nat` addition).
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

/-- The componentwise vanishing condition appearing in the definition of `mulVec`:
`DecP x y M` says that the exponents of `M` are the sums of those of `x` and `y`.  It is stated
without reference to the ambient degree, so it can be used across different `Mon _ n`. -/
abbrev DecP {n : ℕ} {a b d : ℕ} (x : Mon a n) (y : Mon b n) (M : Mon d n) : Prop :=
  ∀ i, (x.1 i : ℕ) + (y.1 i : ℕ) = (M.1 i : ℕ)

/-- `mulVec` is definitionally a sum of `A p * B q` over the pairs `(p,q)` whose exponent vectors
add up to that of `M`. -/
lemma mulVec_eq {a b d n : ℕ} {R : Type*} [CommSemiring R]
    (A : Mon a n → R) (B : Mon b n → R) (M : Mon d n) :
    mulVec a b d A B M = ∑ p : Mon a n, ∑ q : Mon b n,
      if DecP p q M then A p * B q else 0 := rfl

/-- When the target has the degree of the product, the componentwise condition is exactly the
equation `addMon p q = M`. -/
lemma DecP_iff_addMon {n b c : ℕ} (p1 : Mon b n) (p2 : Mon c n) (q : Mon (b+c) n) :
    DecP p1 p2 q ↔ addMon p1 p2 = q := by
  constructor
  · intro h
    apply Subtype.ext; funext i; apply Fin.ext
    show ((addMon p1 p2).1 i : ℕ) = (q.1 i : ℕ)
    rw [addMon_val]; exact h i
  · intro h i
    have := congrArg (fun M : Mon (b+c) n => ((M.1 i : ℕ))) h
    rwa [addMon_val] at this

/-- Associativity of the exponent condition: comparing `M` with `p + q + r` grouped in the two
possible ways is the same condition. -/
lemma DecP_assoc {n a b c d : ℕ} (p : Mon a n) (q : Mon b n) (r : Mon c n) (M : Mon d n) :
    DecP (addMon p q) r M ↔ DecP p (addMon q r) M := by
  unfold DecP
  simp only [addMon_val]
  constructor
  · intro h i; rw [← Nat.add_assoc]; exact h i
  · intro h i; rw [Nat.add_assoc]; exact h i

/-- Collapsing the sum over the middle index: multiplying `F q` by the expansion of `mulVec`
in the variable `q` and summing over `q` reduces to summing over the pairs with `F` evaluated at
`addMon p1 p2`. -/
lemma collapse_left {n b c : ℕ} {R : Type*} [Semiring R]
    (F : Mon (b+c) n → R) (w : Mon b n → Mon c n → R) :
    (∑ q : Mon (b+c) n, F q * (∑ p1 : Mon b n, ∑ p2 : Mon c n,
        (if addMon p1 p2 = q then w p1 p2 else 0)))
      = ∑ p1 : Mon b n, ∑ p2 : Mon c n, F (addMon p1 p2) * w p1 p2 := by
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The mirror image of `collapse_left`, with the `mulVec` expansion appearing on the left. -/
lemma collapse_right {n b c : ℕ} {R : Type*} [Semiring R]
    (G : Mon (b+c) n → R) (w : Mon b n → Mon c n → R) :
    (∑ q : Mon (b+c) n, (∑ p1 : Mon b n, ∑ p2 : Mon c n,
        (if addMon p1 p2 = q then w p1 p2 else 0)) * G q)
      = ∑ p1 : Mon b n, ∑ p2 : Mon c n, w p1 p2 * G (addMon p1 p2) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- `collapse_left` in the shape produced by `mulVec`: the outer factor is `A'` multiplied by the
coefficient vector `A'` when the condition holds. -/
lemma collapse_ite_left {n b c : ℕ} {R : Type*} [Semiring R]
    (cnd : Mon (b+c) n → Prop) [DecidablePred cnd] (A' : R)
    (w : Mon b n → Mon c n → R) :
    (∑ q : Mon (b+c) n, (if cnd q then A' * (∑ q1 : Mon b n, ∑ q2 : Mon c n,
        (if addMon q1 q2 = q then w q1 q2 else 0)) else 0))
      = ∑ q1 : Mon b n, ∑ q2 : Mon c n, (if cnd (addMon q1 q2) then A' * w q1 q2 else 0) := by
  rw [show (∑ q : Mon (b+c) n, (if cnd q then A' * (∑ q1 : Mon b n, ∑ q2 : Mon c n,
        (if addMon q1 q2 = q then w q1 q2 else 0)) else 0))
      = ∑ q : Mon (b+c) n, (if cnd q then A' else 0) * (∑ q1 : Mon b n, ∑ q2 : Mon c n,
        (if addMon q1 q2 = q then w q1 q2 else 0)) from
      Finset.sum_congr rfl fun q _ => by by_cases h : cnd q <;> simp [h]]
  rw [collapse_left]
  apply Finset.sum_congr rfl; intro q1 _
  apply Finset.sum_congr rfl; intro q2 _
  by_cases h : cnd (addMon q1 q2) <;> simp [h]

/-- `collapse_right` in the shape produced by `mulVec`. -/
lemma collapse_ite_right {n b c : ℕ} {R : Type*} [Semiring R]
    (cnd : Mon (b+c) n → Prop) [DecidablePred cnd] (A' : R)
    (w : Mon b n → Mon c n → R) :
    (∑ q : Mon (b+c) n, (if cnd q then (∑ q1 : Mon b n, ∑ q2 : Mon c n,
        (if addMon q1 q2 = q then w q1 q2 else 0)) * A' else 0))
      = ∑ q1 : Mon b n, ∑ q2 : Mon c n, (if cnd (addMon q1 q2) then w q1 q2 * A' else 0) := by
  rw [show (∑ q : Mon (b+c) n, (if cnd q then (∑ q1 : Mon b n, ∑ q2 : Mon c n,
        (if addMon q1 q2 = q then w q1 q2 else 0)) * A' else 0))
      = ∑ q : Mon (b+c) n, (∑ q1 : Mon b n, ∑ q2 : Mon c n,
        (if addMon q1 q2 = q then w q1 q2 else 0)) * (if cnd q then A' else 0) from
      Finset.sum_congr rfl fun q _ => by by_cases h : cnd q <;> simp [h]]
  rw [collapse_right]
  apply Finset.sum_congr rfl; intro q1 _
  apply Finset.sum_congr rfl; intro q2 _
  by_cases h : cnd (addMon q1 q2) <;> simp [h]

/-- **Associativity of `mulVec`**: `A · (B · C) = (A · B) · C`. -/
theorem mulVec_assoc {a b c d n : ℕ} {R : Type*} [CommSemiring R]
    (A : Mon a n → R) (B : Mon b n → R) (C : Mon c n → R) :
    mulVec a (b + c) d A (mulVec b c (b + c) B C)
      = mulVec (a + b) c d (mulVec a b (a + b) A B) C := by
  funext M
  have hL : mulVec a (b + c) d A (mulVec b c (b + c) B C) M
      = ∑ p : Mon a n, ∑ q1 : Mon b n, ∑ q2 : Mon c n,
          (if DecP p (addMon q1 q2) M then A p * (B q1 * C q2) else 0) := by
    simp only [mulVec_eq, DecP_iff_addMon]
    apply Finset.sum_congr rfl; intro p _
    exact collapse_ite_left (fun q => DecP p q M) (A p) (fun q1 q2 => B q1 * C q2)
  have hR : mulVec (a + b) c d (mulVec a b (a + b) A B) C M
      = ∑ p : Mon a n, ∑ q1 : Mon b n, ∑ q2 : Mon c n,
          (if DecP p (addMon q1 q2) M then A p * (B q1 * C q2) else 0) := by
    simp only [mulVec_eq, DecP_iff_addMon]
    rw [Finset.sum_comm]
    trans ∑ r : Mon c n, ∑ p1 : Mon a n, ∑ p2 : Mon b n,
        (if DecP (addMon p1 p2) r M then (A p1 * B p2) * C r else 0)
    · apply Finset.sum_congr rfl; intro r _
      exact collapse_ite_right (fun p' => DecP p' r M) (C r) (fun p1 p2 => A p1 * B p2)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p1 _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p2 _
      apply Finset.sum_congr rfl; intro r _
      by_cases h : DecP (addMon p1 p2) r M
      · have h' : DecP p1 (addMon p2 r) M := (DecP_assoc p1 p2 r M).mp h
        rw [ite_eq_left h, ite_eq_left h', mul_assoc]
      · have h' : ¬ DecP p1 (addMon p2 r) M := fun hc => h ((DecP_assoc p1 p2 r M).mpr hc)
        rw [ite_eq_right h, ite_eq_right h']
  rw [hL, hR]

end Work.HP.Vero
