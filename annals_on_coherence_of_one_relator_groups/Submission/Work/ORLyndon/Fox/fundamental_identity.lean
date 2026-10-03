import Mathlib
import Submission.Work.ORLyndon.Fox

/-!
# The fundamental identity of the Fox calculus

For a word `w` in the free group `F(X)` and a ring `K`, the Fox derivatives
`∂w/∂x ∈ K[F(X)]` satisfy

`w - 1 = ∑_x ∂w/∂x · (x - 1)`

in the group algebra `K[F(X)]`; equivalently

`of w - 1 = (foxFD w).sum (fun x d => d * (of (FreeGroup.of x) - 1))`.

We prove this here by induction on the underlying list of letters (the Fox derivative
`foxFD` is defined on `FreeGroup X` as the quotient of `foxWord` on lists).  The
single-letter computation `foxLetter_mul_sub_one` is the only place where the group
algebra is used; the induction step is formal.

This is the identity that expresses the augmentation ideal of `K[F(X)]` in terms of the
Fox derivatives; it is the starting point for the Fox matrix and the Fox calculus
argument in the proof of the coherence theorem.
-/

set_option autoImplicit false

namespace Work.ORLyndon.Fox

open MonoidAlgebra

universe u v

variable {X : Type u} {K : Type v}

section FundamentalIdentity

variable [Ring K] [DecidableEq X]

/-- **Single letter computation.** The contribution `∂c/∂x · (x - 1)` of one letter
`c : X × Bool` to the fundamental identity: it equals `letterGroup c - 1` when `x` is the
generator occurring in `c`, and vanishes otherwise. -/
theorem foxLetter_mul_sub_one (c : X × Bool) (x : X) :
    foxLetter (K := K) x c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1) =
      if x = c.1 then (MonoidAlgebra.of K (FreeGroup X)) (letterGroup c) - 1 else 0 := by
  obtain ⟨y, b⟩ := c
  cases b
  · rw [show foxLetter (K := K) x (y, false) =
        (if y = x then -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) else 0)
        from rfl]
    by_cases h : y = x
    · subst h
      rw [if_pos rfl, if_pos rfl]
      show -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) *
          ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y) - 1) =
        (MonoidAlgebra.of K (FreeGroup X)) (letterGroup (y, false)) - 1
      have hab : (MonoidAlgebra.of K (FreeGroup X)) ((FreeGroup.of y)⁻¹) *
          (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y) = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      show -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) *
          ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y) - 1) =
        (MonoidAlgebra.of K (FreeGroup X)) ((FreeGroup.of y)⁻¹) - 1
      calc -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) *
            ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y) - 1)
          = -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹) *
              (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of y))
            + MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹) := by noncomm_ring
        _ = MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹) - 1 := by
              rw [hab]; noncomm_ring
    · rw [if_neg h, if_neg (Ne.symm h), zero_mul]
  · rw [foxLetter_true]
    by_cases h : y = x
    · subst h
      rw [if_pos rfl, if_pos rfl, one_mul]
      rfl
    · rw [if_neg h, if_neg (Ne.symm h), zero_mul]

/-- Summing the single letter computation over a finite set of generators containing the
generator occurring in `c`. -/
theorem sum_foxLetter (c : X × Bool) (s : Finset X) (hc : c.1 ∈ s) :
    s.sum (fun x => foxLetter (K := K) x c *
        ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) =
      (MonoidAlgebra.of K (FreeGroup X)) (letterGroup c) - 1 := by
  rw [Finset.sum_congr rfl (fun x _ => foxLetter_mul_sub_one c x),
    Finset.sum_ite_eq' s c.1 (fun _ => (MonoidAlgebra.of K (FreeGroup X)) (letterGroup c) - 1),
    if_pos hc]

/-- **The fundamental identity on a list of letters**, in the form needed for the
induction: the sum may be taken over an arbitrary finite set of generators `s` containing
all the generators occurring in the word `L`. -/
theorem foxWord_sum_of_subset (L : List (X × Bool)) (s : Finset X) (hs : letters L ⊆ s) :
    s.sum (fun x => foxWord (K := K) x L *
        ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) =
      (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.mk L) - 1 := by
  induction L generalizing s with
  | nil =>
      rw [← FreeGroup.one_eq_mk, map_one]
      simp
  | cons c L ih =>
      rw [letters_cons, Finset.insert_subset_iff] at hs
      obtain ⟨hc, hL⟩ := hs
      have hstep : ∀ x : X,
          foxWord (K := K) x (c :: L) *
              ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)
            = foxLetter (K := K) x c *
                ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)
              + (MonoidAlgebra.of K (FreeGroup X)) (letterGroup c) *
                (foxWord (K := K) x L *
                  ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) := by
        intro x
        rw [foxWord_cons]
        noncomm_ring
      rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_foxLetter c s hc, ih s hL]
      rw [← letterGroup_mul_mk c L, map_mul]
      noncomm_ring

/-- **The fundamental identity on a list of letters.** -/
theorem foxWord_sum (L : List (X × Bool)) :
    (letters L).sum (fun x => foxWord (K := K) x L *
        ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) =
      (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.mk L) - 1 :=
  foxWord_sum_of_subset L (letters L) (Finset.Subset.refl _)

/-- The support of `foxFD w` is contained in the set of generators occurring in `w`. -/
theorem support_foxFD_subset_letters (L : List (X × Bool)) :
    (foxFD (K := K) (FreeGroup.mk L)).support ⊆ letters L := by
  intro x hx
  by_contra hxL
  rw [Finsupp.mem_support_iff] at hx
  rw [foxFD_mk] at hx
  exact hx (foxWord_eq_zero_of_notMem hxL)

/-- Rewriting the `Finsupp.sum` defining the fundamental identity as a sum over the finite
set of generators occurring in the word. -/
theorem foxFD_sum (L : List (X × Bool)) :
    (foxFD (K := K) (FreeGroup.mk L)).sum
        (fun x d => d * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) =
      (letters L).sum (fun x => foxWord (K := K) x L *
        ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) := by
  rw [Finsupp.sum]
  rw [Finset.sum_congr rfl (fun x _ => by rw [foxFD_mk])]
  exact Finset.sum_subset (support_foxFD_subset_letters L)
    (fun x _ hxnot => by
      rw [Finsupp.notMem_support_iff, foxFD_mk] at hxnot
      rw [hxnot, zero_mul])

/-- **The fundamental identity of the Fox calculus.** For every `w` in the free group on
`X`, the Fox derivatives of `w` weighted by `x - 1` reconstruct `w - 1` in the group
algebra `K[F(X)]`. -/
theorem fundamental_identity {X : Type*} {K : Type*} [Ring K] [DecidableEq X] (w : FreeGroup X) :
    (Work.ORLyndon.foxFD (K := K) w).sum
        (fun x d => d * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) =
      (MonoidAlgebra.of K (FreeGroup X)) w - 1 := by
  induction w using Quot.inductionOn with
  | h L =>
      show (Work.ORLyndon.foxFD (K := K) (FreeGroup.mk L)).sum
          (fun x d => d * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) =
        (MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.mk L) - 1
      rw [foxFD_sum L, foxWord_sum L]

end FundamentalIdentity

end Work.ORLyndon.Fox
