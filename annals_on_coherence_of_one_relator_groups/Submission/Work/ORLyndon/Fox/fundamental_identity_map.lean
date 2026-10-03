import Mathlib
import Submission.Work.ORLyndon.Fox

/-!
# The fundamental identity of the Fox calculus, after applying a ring homomorphism

`Work.ORLyndon.foxFD w` is the vector of Fox derivatives `(∂w/∂x)_x` of an element `w` of a free
group `F(X)`, lying in `X →₀ K[F(X)]`.  The *fundamental identity* of the Fox calculus is

`∑_x (∂w/∂x) · (x - 1) = w - 1`   in `K[F(X)]`.

This file proves the "mapped" form of that identity, needed for the Lyndon resolution: for any ring
homomorphism `f` out of `K[F(X)]`,

`∑_x f(∂w/∂x) · (f(x) - 1) = f(w) - 1`,

where the left hand side is the `Finsupp.sum` of the `Finsupp.mapRange f` of `foxFD w`.  The proof
is a direct induction on a word representative of `w`; the auxiliary functional `foxMapSum` pushes
`f` inside the finitely supported sum.
-/

namespace Work.ORLyndon.Fox

open MonoidAlgebra

section FoxMapAux

variable {X : Type*} {K : Type*} [Ring K] [DecidableEq X]

/-- `letterGroup (y, true)` is the generator `y`. -/
@[simp] theorem letterGroup_one_true (y : X) :
    letterGroup (y, true) = FreeGroup.of y := rfl

/-- `letterGroup (y, false)` is the inverse of the generator `y`. -/
@[simp] theorem letterGroup_one_false (y : X) :
    letterGroup (y, false) = (FreeGroup.of y)⁻¹ := rfl

/-- As a function of `x`, the Fox derivative of a single letter `c` is the finitely supported
function `Finsupp.single c.1 (∂c/∂c.1)`. -/
theorem foxLetter_eq_single (x : X) (c : X × Bool) :
    foxLetter (K := K) x c = Finsupp.single c.1 (foxLetter (K := K) c.1 c) x := by
  obtain ⟨y, b⟩ := c
  cases b
  · rw [foxLetter_false, Finsupp.single_apply]
    by_cases h : y = x
    · subst h; simp [foxLetter_false]
    · simp [h]
  · rw [foxLetter_true, Finsupp.single_apply]
    by_cases h : y = x
    · subst h; simp [foxLetter_true]
    · simp [h]

/-- The vector of Fox derivatives of a word `c :: L`, split off its first letter. -/
theorem foxFD_mk_cons (c : X × Bool) (L : List (X × Bool)) :
    foxFD (K := K) (FreeGroup.mk (c :: L)) =
      Finsupp.single c.1 (foxLetter (K := K) c.1 c) +
        (MonoidAlgebra.of K (FreeGroup X) (letterGroup c)) •
          foxFD (K := K) (FreeGroup.mk L) := by
  ext x
  rw [foxFD_mk, Finsupp.add_apply, Finsupp.smul_apply, foxFD_mk, foxWord_cons, foxLetter_eq_single]
  rw [smul_eq_mul]

/-- `of` of a word `c :: L` is the product of `of` of the first letter and `of` of the rest. -/
theorem of_mk_cons (c : X × Bool) (L : List (X × Bool)) :
    (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.mk (c :: L)) =
      (MonoidAlgebra.of K (FreeGroup X)) (letterGroup c) *
        (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.mk L) := by
  rw [← letterGroup_mul_mk c L, map_mul]

/-- The monomial of the inverse generator is a left inverse of the monomial of the generator. -/
theorem of_inv_mul_of (y : X) :
    (MonoidAlgebra.of K (FreeGroup X)) ((FreeGroup.of y)⁻¹) *
      (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y) = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

/-- The image under a ring homomorphism `f` of the fundamental sum `∑_x (∂w/∂x)·(x-1)`,
with `f` pushed inside the finitely supported sum. -/
noncomputable def foxMapSum {S : Type*} [Ring S]
    (f : MonoidAlgebra K (FreeGroup X) →+* S) (D : X →₀ MonoidAlgebra K (FreeGroup X)) : S :=
  D.sum fun x d => f d * (f ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x)) - 1)

/-- `foxMapSum` is additive. -/
theorem foxMapSum_add {S : Type*} [Ring S] (f : MonoidAlgebra K (FreeGroup X) →+* S)
    (D E : X →₀ MonoidAlgebra K (FreeGroup X)) :
    foxMapSum (K := K) f (D + E) = foxMapSum (K := K) f D + foxMapSum (K := K) f E := by
  simp only [foxMapSum]
  exact Finsupp.sum_add_index (fun a _ => by simp) (fun a _ b₁ b₂ => by rw [map_add, add_mul])

/-- Value of `foxMapSum` on a single finitely supported generator. -/
theorem foxMapSum_single {S : Type*} [Ring S] (f : MonoidAlgebra K (FreeGroup X) →+* S)
    (x : X) (v : MonoidAlgebra K (FreeGroup X)) :
    foxMapSum (K := K) f (Finsupp.single x v) =
      f v * (f ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x)) - 1) := by
  simp only [foxMapSum]
  rw [Finsupp.sum_single_index (by simp)]

/-- `foxMapSum` is compatible with left multiplication by a constant. -/
theorem foxMapSum_smul {S : Type*} [Ring S] (f : MonoidAlgebra K (FreeGroup X) →+* S)
    (a : MonoidAlgebra K (FreeGroup X)) (D : X →₀ MonoidAlgebra K (FreeGroup X)) :
    foxMapSum (K := K) f (a • D) = f a * foxMapSum (K := K) f D := by
  simp only [foxMapSum]
  rw [Finsupp.sum_smul_index (fun i => by simp)]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro i _
  rw [map_mul, mul_assoc]

/-- The elementary ring identity used in the `true` step of the induction. -/
theorem fox_cons_algebra_true {S : Type*} [Ring S] (U B : S) :
    U - 1 + U * (B - 1) = U * B - 1 := by noncomm_ring

/-- The elementary ring identity used in the `false` step of the induction. -/
theorem fox_cons_algebra_false {S : Type*} [Ring S] (V U B : S) (h : V * U = 1) :
    -V * (U - 1) + V * (B - 1) = V * B - 1 := by
  rw [← h]
  noncomm_ring

/-- The fundamental identity for a word: `∑_x f(∂w/∂x)·(f(x)-1) = f(w)-1`. -/
theorem foxMapSum_foxFD_mk {S : Type*} [Ring S] (f : MonoidAlgebra K (FreeGroup X) →+* S)
    (L : List (X × Bool)) :
    foxMapSum (K := K) f (foxFD (K := K) (FreeGroup.mk L)) =
      f ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.mk L)) - 1 := by
  induction L with
  | nil =>
    have h0 : foxFD (K := K) (FreeGroup.mk ([] : List (X × Bool))) = 0 := by
      ext x; rw [foxFD_mk, foxWord_nil]; rfl
    have h1 : FreeGroup.mk ([] : List (X × Bool)) = 1 := FreeGroup.one_eq_mk.symm
    rw [h0, h1]
    change foxMapSum (K := K) f 0 = f 1 - 1
    rw [show foxMapSum (K := K) f 0 = 0 from by
        simp only [foxMapSum, Finsupp.sum_zero_index],
      map_one, sub_self]
  | cons c L ih =>
    obtain ⟨y, b⟩ := c
    cases b
    · rw [foxFD_mk_cons, foxMapSum_add, foxMapSum_single, foxMapSum_smul, ih]
      rw [show ((y, false) : X × Bool).1 = y from rfl]
      rw [show foxLetter (K := K) y (y, false) =
          -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) from by
        rw [foxLetter_false, if_pos rfl]]
      rw [map_neg, of_mk_cons, letterGroup_one_false, map_mul]
      have hVU : f ((MonoidAlgebra.of K (FreeGroup X)) ((FreeGroup.of y)⁻¹)) *
          f ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y)) = 1 := by
        rw [← map_mul, of_inv_mul_of (K := K) y, map_one]
      exact fox_cons_algebra_false _ _ _ hVU
    · rw [foxFD_mk_cons, foxMapSum_add, foxMapSum_single, foxMapSum_smul, ih]
      rw [show ((y, true) : X × Bool).1 = y from rfl]
      rw [show foxLetter (K := K) y (y, true) = 1 from by rw [foxLetter_true, if_pos rfl]]
      rw [map_one, one_mul, of_mk_cons, letterGroup_one_true, map_mul]
      exact fox_cons_algebra_true _ _

end FoxMapAux

theorem fundamental_identity_map {X : Type*} {K : Type*} [Ring K] [DecidableEq X]
    {S : Type*} [Ring S] (f : MonoidAlgebra K (FreeGroup X) →+* S) (w : FreeGroup X) :
    ((Work.ORLyndon.foxFD (K := K) w).mapRange f (map_zero f)).sum
        (fun x d => d * (f ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x)) - 1)) =
      f ((MonoidAlgebra.of K (FreeGroup X)) w) - 1 := by
  have h : ((foxFD (K := K) w).mapRange f (map_zero f)).sum
        (fun x d => d * (f ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x)) - 1)) =
      foxMapSum (K := K) f (foxFD (K := K) w) := by
    rw [Finsupp.sum_mapRange_index (fun a => by simp)]
    rfl
  rw [h]
  induction w using Quot.inductionOn with
  | h L => exact foxMapSum_foxFD_mk (K := K) f L

end Work.ORLyndon.Fox
