import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clean cone copy of the parts of `bf4_defs` needed by the `(4,4)` free-Lie computation

This is a clash-free copy of the definitions of `Submission.Work.SSGRoute.bf4_defs` that the
`(4,4)` graded step needs, with the clashing declaration `V` (and the other unused ones) omitted.
It keeps the original names; the original module is *not* imported anywhere in the `CC` cone.
-/

namespace Work.SSGRoute.CC

instance instDecidableEqFreeMonoidFinFour : DecidableEq (FreeMonoid (Fin 4)) :=
  inferInstanceAs (DecidableEq (List (Fin 4)))

/-- The free associative `𝔽₂`-algebra on four letters. -/
abbrev A4 : Type := MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 4))

/-- The letter `x` as an element of `A4`. -/
noncomputable def ltr (x : Fin 4) : A4 := MonoidAlgebra.single (FreeMonoid.of x) 1

/-- Number of occurrences of a letter in a word. -/
def wcnt (x : Fin 4) (w : FreeMonoid (Fin 4)) : ℕ :=
  (w.toList.map (fun z => if z = x then (1 : ℕ) else 0)).sum

/-- The letter-count (weight) vector of a word. -/
def wvec (w : FreeMonoid (Fin 4)) : Fin 4 → ℕ := fun x => wcnt x w

/-- The letter-count of a `4`-tuple (as a weight vector). -/
def tvec (t : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Fin 4 → ℕ :=
  wvec (FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.2.2)

/-- The representative of the second `σ`-orbit (the letters `0` and `σ 0` form the first). -/
def rep2 (σ : Fin 4 ≃ Fin 4) : Fin 4 := if σ 0 = 1 then 2 else 1

/-- The balanced letter-count (all four letters once). -/
def alpha1111 : Fin 4 → ℕ := tvec (0, 1, 2, 3)

/-- `t` has four distinct letters (equivalently letter-count `alpha1111`). -/
def IsPerm4 (t : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop := tvec t = alpha1111

section Ring

lemma two_A4 : (2 : A4) = 0 := by
  show MonoidAlgebra.single (1 : FreeMonoid (Fin 4)) (2 : ZMod 2) = 0
  rw [show (2 : ZMod 2) = 0 from by decide, MonoidAlgebra.single_eq_zero]

lemma neg_A4 (x : A4) : -x = x := by
  have h : x + x = (2 : A4) * x := by rw [two_mul]
  rw [two_A4, zero_mul] at h
  exact neg_eq_of_add_eq_zero_right h

lemma add_add_cancel (x y : A4) : (x + y) + x = y := by
  rw [add_assoc, add_comm y x, ← add_assoc, ← two_mul, two_A4, zero_mul, zero_add]

lemma eq_add_of_add_add_eq_zero {x y z : A4} (h : x + y + z = 0) : x = y + z := by
  have h2 : x + (y + z) = 0 := by rw [← h]; abel
  have h3 : x = -(y + z) := eq_neg_of_add_eq_zero_left h2
  rw [h3, neg_add_rev, neg_A4, neg_A4, add_comm]

lemma eq_add_of_add_add_eq_zero' {x y z : A4} (h : x + y + z = 0) : y = x + z := by
  have h2 : y + (x + z) = 0 := by rw [← h]; abel
  have h3 : y = -(x + z) := eq_neg_of_add_eq_zero_left h2
  rw [h3, neg_add_rev, neg_A4, neg_A4, add_comm]

lemma brk_symm (a b : A4) : brk (Fin 4) a b = brk (Fin 4) b a := by
  simp only [brk]; ac_rfl

lemma brk_lin (x y z : A4) : brk (Fin 4) (x + y) z = brk (Fin 4) x z + brk (Fin 4) y z := by
  simp only [brk, add_mul, mul_add]; abel

lemma brk_lin' (z x y : A4) : brk (Fin 4) z (x + y) = brk (Fin 4) z x + brk (Fin 4) z y := by
  simp only [brk, add_mul, mul_add]; abel

lemma jac3 (x y z : A4) :
    brk (Fin 4) (brk (Fin 4) x y) z + brk (Fin 4) (brk (Fin 4) y z) x
      + brk (Fin 4) (brk (Fin 4) z x) y = 0 := by
  simp only [brk]
  noncomm_ring
  simp [two_A4]

lemma brk_jac (a b c : A4) : brk (Fin 4) (brk (Fin 4) a b) c
    = brk (Fin 4) (brk (Fin 4) a c) b + brk (Fin 4) a (brk (Fin 4) b c) := by
  simp only [brk]
  noncomm_ring
  simp [two_A4]

lemma brk_brk (a b c : A4) : brk (Fin 4) a (brk (Fin 4) b c)
    = brk (Fin 4) (brk (Fin 4) a b) c + brk (Fin 4) (brk (Fin 4) a c) b := by
  have h := brk_jac a b c
  rw [h, add_add_cancel]

lemma brk4_symm (a b c d : Fin 4) : brk4 (Fin 4) (a, b, c, d) = brk4 (Fin 4) (b, a, c, d) := by
  show brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr b)) (ltr c)) (ltr d)
    = brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr b) (ltr a)) (ltr c)) (ltr d)
  rw [brk_symm (ltr a) (ltr b)]

lemma brk4_rot (a b c d : Fin 4) :
    brk4 (Fin 4) (a, b, c, d) = brk4 (Fin 4) (b, c, a, d) + brk4 (Fin 4) (c, a, b, d) := by
  show brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr b)) (ltr c)) (ltr d)
    = brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr b) (ltr c)) (ltr a)) (ltr d)
      + brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr c) (ltr a)) (ltr b)) (ltr d)
  rw [eq_add_of_add_add_eq_zero (jac3 (ltr a) (ltr b) (ltr c)), brk_lin]

/-- Decompose a nested commutator whose last letter occurs nowhere else. -/
lemma brk4_pos4 (x y z a : Fin 4) :
    brk4 (Fin 4) (x, y, z, a) = brk4 (Fin 4) (a, x, y, z) + brk4 (Fin 4) (a, z, x, y)
      + brk4 (Fin 4) (a, z, y, x) + brk4 (Fin 4) (a, y, x, z) := by
  have h1 : brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr x) (ltr y)) (ltr z)) (ltr a)
      = brk (Fin 4) (brk (Fin 4) (ltr z) (ltr a)) (brk (Fin 4) (ltr x) (ltr y))
        + brk (Fin 4) (brk (Fin 4) (ltr a) (brk (Fin 4) (ltr x) (ltr y))) (ltr z) :=
    eq_add_of_add_add_eq_zero (jac3 (brk (Fin 4) (ltr x) (ltr y)) (ltr z) (ltr a))
  have h2 : brk (Fin 4) (brk (Fin 4) (ltr a) (brk (Fin 4) (ltr x) (ltr y))) (ltr z)
      = brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr y)) (ltr x)) (ltr z)
        + brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr x)) (ltr y)) (ltr z) := by
    rw [brk_brk (ltr a) (ltr x) (ltr y), brk_lin]
    abel
  have h3 : brk (Fin 4) (brk (Fin 4) (ltr z) (ltr a)) (brk (Fin 4) (ltr x) (ltr y))
      = brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr z)) (ltr x)) (ltr y)
        + brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr z)) (ltr y)) (ltr x) := by
    rw [brk_symm (brk (Fin 4) (ltr z) (ltr a)) (brk (Fin 4) (ltr x) (ltr y))]
    rw [eq_add_of_add_add_eq_zero'
      (jac3 (brk (Fin 4) (ltr z) (ltr a)) (ltr x) (ltr y))]
    rw [brk_symm (ltr y) (brk (Fin 4) (ltr z) (ltr a)), brk_symm (ltr z) (ltr a)]
  show brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr x) (ltr y)) (ltr z)) (ltr a)
    = brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr x)) (ltr y)) (ltr z)
      + brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr z)) (ltr x)) (ltr y)
      + brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr z)) (ltr y)) (ltr x)
      + brk (Fin 4) (brk (Fin 4) (brk (Fin 4) (ltr a) (ltr y)) (ltr x)) (ltr z)
  rw [h1, h2, h3]
  abel

/-- Reduction at the third slot. -/
lemma brk4_pos3 (x y a z : Fin 4) :
    brk4 (Fin 4) (x, y, a, z) = brk4 (Fin 4) (a, y, x, z) + brk4 (Fin 4) (a, x, y, z) := by
  rw [brk4_rot x y a z, brk4_symm y a x z]

end Ring

end Work.SSGRoute.CC
