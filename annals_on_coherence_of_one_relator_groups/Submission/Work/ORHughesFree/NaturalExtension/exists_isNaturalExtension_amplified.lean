/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Amplification of a natural extension

Let `R` be a ring carrying an action of `Multiplicative ℤ` (the twist `τ` of the skew Laurent
polynomial ring `R[t^{±1};τ]`), `rk` a Sylvester rank function on `R` and `rkE` a natural extension
of `rk` to `R[t^{±1};τ]`.  Then the amplified rank function `amplifiedRank rk N hN` on the matrix
ring `Mat_N(R)` admits a natural extension to `Mat_N(R)[t^{±1};τ]`, namely the rank function

  `Y ↦ rkE (flattenBlocks (Y.map (skewMatrixEquiv R N))) / N`

obtained by transporting `amplifiedRank rkE N hN` (a rank function on `Mat_N(R[t^{±1};τ])`)
backwards along the ring isomorphism `skewMatrixEquiv R N : Mat_N(R)[t^{±1};τ] ≃+* Mat_N(R[t^{±1};τ])`.

This is the amplification step of the proof of uniqueness of the natural extension
([JZLA20, §3]): applied twice it shows that two natural extensions of the same `rk` agree on
`Mat_N(R[t^{±1};τ])`, hence on `N × N` matrices over `R[t^{±1};τ]`.

The proof has three ingredients.

* `sylvesterRank_transport_pullback` : a Sylvester rank function pulls back along a ring
  isomorphism (the rank axioms are all transported by `Matrix.map` of a ring isomorphism);
* the flattening identities for the two defining shapes of `IsNaturalExtension`, namely
  `flattenBlocks_skewLaurentConst_skewMatrixEquiv` (constant block matrices, the axiom (a)) and
  `flattenBlocks_onePlusAt_skewMatrixEquiv` (`1 + A t`, the axiom (b));
* the defining formula `amplifiedRank_apply` of the amplified rank function.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.ampDefs
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.MatrixBlocks.exists_sylvesterRank_matrix_unfaithful
import Submission.Work.ORHughesFree.NaturalExtension.amplificationFlatten

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## Pulling a Sylvester rank function back along a ring isomorphism -/

/-- **A Sylvester rank function pulls back along a ring isomorphism.**  If `e : A ≃+* B` and `rk`
is a Sylvester rank function on `B`, then `M ↦ rk (M.map e)` is a Sylvester rank function on `A`.
All the rank axioms are transported because `Matrix.map ⇑e` is additive, multiplicative and
preserves the block constructions (`blockDiagFin_map`, `blockUpperFin_map`). -/
theorem sylvesterRank_transport_pullback {A B : Type u} [Ring A] [Ring B] (e : A ≃+* B)
    (rk : SylvesterRank B) :
    ∃ rkA : SylvesterRank A, ∀ (n m : ℕ) (M : Matrix (Fin n) (Fin m) A),
      rkA.rk n m M = rk.rk n m (M.map ⇑e) := by
  let g : A →+* B := e
  have hg : ∀ x : A, g x = e x := fun _ => rfl
  refine ⟨{ rk := fun n m M => rk.rk n m (M.map ⇑g),
            rk_nonneg := fun n m M => rk.rk_nonneg _ _ _,
            rk_zero := fun n m => by
              rw [show (0 : Matrix (Fin n) (Fin m) A).map ⇑g = 0 from by
                ext i j; simp [Matrix.map_apply], rk.rk_zero],
            rk_one := by
              rw [Matrix.map_one ⇑g (map_zero g) (map_one g), rk.rk_one],
            rk_mul_le_left := fun {n m k} X Y => by
              rw [Matrix.map_mul (f := g)]
              exact rk.rk_mul_le_left _ _,
            rk_mul_le_right := fun {n m k} X Y => by
              rw [Matrix.map_mul (f := g)]
              exact rk.rk_mul_le_right _ _,
            rk_blockDiag := fun {n m p q} X Y => by
              rw [blockDiagFin_map g, rk.rk_blockDiag],
            rk_blockUpper := fun {n m p q} X Y Z => by
              rw [blockUpperFin_map g]
              exact rk.rk_blockUpper _ _ _ },
        fun n m M => congrArg (fun h => rk.rk n m (M.map h)) (funext hg)⟩

/-! ## Flattening the two defining shapes of the natural extension -/

/-- Flattening commutes with lifting the entries of a block matrix over `R` to rectangular
matrices over `S` entry by entry (via a fixed function `g : R → S`), for a block size `k`. -/
theorem flattenBlocks_map_map {a b k : ℕ} {R : Type u} {S : Type*}
    (X : Matrix (Fin a) (Fin b) (Matrix (Fin k) (Fin k) R)) (g : R → S) :
    flattenBlocks (X.map (fun A => A.map g)) = (flattenBlocks X).map g := by
  ext i j
  simp [flattenBlocks, Matrix.map_apply]

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- **Flattening a constant block matrix** over `M_k(R)[t^{±1};τ]` after the isomorphism
`M_k(R)[t^{±1};τ] ≃+* M_k(R[t^{±1};τ])`: the result is the constant block matrix over
`M_k(R)` flattened.  This is the shape of the extension axiom (a) of `IsNaturalExtension`. -/
theorem flattenBlocks_skewLaurentConst_skewMatrixEquiv {a b k : ℕ}
    (X : Matrix (Fin a) (Fin b) (Matrix (Fin k) (Fin k) R)) :
    flattenBlocks ((Work.ORHughesFree.skewLaurentConst a b X).map (skewMatrixEquiv R k)) =
      Work.ORHughesFree.skewLaurentConst (a * k) (b * k) (flattenBlocks X) := by
  have h : Work.ORHughesFree.skewLaurentConst a b X
      = X.map (fun x => SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) := rfl
  rw [h, Matrix.map_map]
  have hfun : (⇑(skewMatrixEquiv R k) ∘ fun x : Matrix (Fin k) (Fin k) R =>
      SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) =
      fun x => x.map (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)) := by
    funext x
    exact skewMatrixEquiv_single R k 1 x
  rw [hfun, flattenBlocks_map_map]
  rfl

/-- **Flattening `1 + A t`** over `M_k(R)[t^{±1};τ]` after the isomorphism
`M_k(R)[t^{±1};τ] ≃+* M_k(R[t^{±1};τ])`: the result is `1 + (flattenBlocks A) t` over
`R[t^{±1};τ]`.  This is the shape of the extension axiom (b) of `IsNaturalExtension`. -/
theorem flattenBlocks_onePlusAt_skewMatrixEquiv {a k : ℕ}
    (A : Matrix (Fin a) (Fin a) (Matrix (Fin k) (Fin k) R)) :
    flattenBlocks ((Work.ORHughesFree.onePlusAt a A).map (skewMatrixEquiv R k)) =
      Work.ORHughesFree.onePlusAt (a * k) (flattenBlocks A) := by
  have h : Work.ORHughesFree.onePlusAt a A
      = 1 + A.map (fun x => SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) x) := rfl
  have h' : Work.ORHughesFree.onePlusAt (a * k) (flattenBlocks A)
      = 1 + (flattenBlocks A).map
          (fun x => SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) x) := rfl
  rw [h, h', Matrix.map_add (skewMatrixEquiv R k) (map_add _),
    Matrix.map_one (skewMatrixEquiv R k) (map_zero _) (map_one _), Matrix.map_map,
    flattenBlocks_add, flattenBlocks_one]
  have hfun : (⇑(skewMatrixEquiv R k) ∘ fun x : Matrix (Fin k) (Fin k) R =>
      SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) x) =
      fun x => x.map (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1)) := by
    funext x
    exact skewMatrixEquiv_single R k (Multiplicative.ofAdd 1) x
  rw [hfun, flattenBlocks_map_map]

/-! ## The amplification theorem -/

theorem exists_isNaturalExtension_amplified {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {rk : Work.ORHughesFree.SylvesterRank R} {rkE : Work.ORHughesFree.SylvesterRank (Work.ORHughesFree.NaturalExtension.SkewL R)}
    (h : Work.ORHughesFree.IsNaturalExtension rk rkE) (N : ℕ) (hN : 0 < N) :
    ∃ rkEN : Work.ORHughesFree.SylvesterRank (Work.ORHughesFree.NaturalExtension.SkewL (Matrix (Fin N) (Fin N) R)),
      (∀ (p q : ℕ) (Y : Matrix (Fin p) (Fin q) (Work.ORHughesFree.NaturalExtension.SkewL (Matrix (Fin N) (Fin N) R))),
        rkEN.rk p q Y = rkE.rk (p * N) (q * N)
          (Work.ORHughesFree.flattenBlocks (Y.map (Work.ORHughesFree.NaturalExtension.skewMatrixEquiv R N))) / (N : ℝ)) ∧
      Work.ORHughesFree.IsNaturalExtension (Work.ORHughesFree.NaturalExtension.amplifiedRank rk N hN) rkEN := by
  -- Transport the amplified rank function of `rkE` (a rank function on `M_N(R[t^{±1};τ])`)
  -- backwards along `M_N(R)[t^{±1};τ] ≃+* M_N(R[t^{±1};τ])`.
  obtain ⟨rkEN, hrkEN⟩ :=
    sylvesterRank_transport_pullback (skewMatrixEquiv R N) (amplifiedRank rkE N hN)
  refine ⟨rkEN, ?_, ?_⟩
  · -- the defining formula, from `hrkEN` and `amplifiedRank_apply`
    intro p q Y
    rw [hrkEN p q Y, amplifiedRank_apply rkE N hN p q (Y.map (skewMatrixEquiv R N))]
  · refine ⟨?_, ?_⟩
    · -- axiom (a): constant matrices
      intro n m A
      rw [hrkEN n m (Work.ORHughesFree.skewLaurentConst n m A),
        amplifiedRank_apply rkE N hN n m
          ((Work.ORHughesFree.skewLaurentConst n m A).map (skewMatrixEquiv R N)),
        flattenBlocks_skewLaurentConst_skewMatrixEquiv A,
        h.1 (n * N) (m * N) (flattenBlocks A)]
      exact (amplifiedRank_apply rk N hN n m A).symm
    · -- axiom (b): `1 + A t`
      intro n A
      rw [hrkEN n n (Work.ORHughesFree.onePlusAt n A),
        amplifiedRank_apply rkE N hN n n
          ((Work.ORHughesFree.onePlusAt n A).map (skewMatrixEquiv R N)),
        flattenBlocks_onePlusAt_skewMatrixEquiv A,
        h.2 (n * N) (flattenBlocks A), Nat.cast_mul,
        mul_div_cancel_right₀ _ (by exact_mod_cast hN.ne')]

end Work.ORHughesFree.NaturalExtension
