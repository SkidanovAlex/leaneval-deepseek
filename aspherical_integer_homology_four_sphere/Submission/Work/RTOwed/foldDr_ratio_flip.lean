/-
# The ratio of the developing matrices of two reps with the same walls

`Work.FoldInst.foldDr i r` is the developing matrix of the rep `r` of the fold class `i`, and
`Work.FoldInst.foldWalls i r t` are the sides of its `c = foldCodim i` walls.  The transition of
the fold charts of two classes on a common piece is the Möbius map of
`coordPermMat j * (N_j D_s) * (N_i D_r)⁻¹ * coordPermMat i⁻¹` (`Work.RTOwed.transMat`), and it is
well defined only if the *ratio* `D_{r'}⁻¹ D_r` with `r' = flipSet r Δ` depends on the rep pair only
through the *set* of sides that the walls in `Δ` have.

This file proves exactly that: if two triples `(i, r, Δi)` and `(j, s, Δj)` have the same image
`Δ.image (foldWalls i r ·)` of walls in `Fin 24`, then

  `(D_{i,flip_r Δi})⁻¹ D_{i,r} = (D_{j,flip_s Δj})⁻¹ D_{j,s}`   over `ℚ`.

## The mathematics

The proof is the "glue" of the fold block.  Its two inputs are

* the **single flip identity** `D_{flip r {t}} = D_r P_{wall}`, where `P_S = pairMat S` is the side
  pairing matrix of the side `S` (`foldDr_flipSet_singleton`, a finite check on the tables of
  `Data.lean`), and
* the **transport of the walls** under a flip: flipping at the wall `t` moves the other walls by the
  side permutation of the *type* of that wall (`foldWalls_flipSet_singleton`), a consequence of the
  flip certificate `fold_state_flipSet` and of `sideType_sidePerm`.

Telescoping the single flip identity along a set `Δ` of walls gives

  `D_{flip r Δ} = D_r · ∏_{j} P_{A_j}`,

the product running over the *chain* `A₁, A₂, …` of walls met while flipping the walls of `Δ` in
increasing `t`-order.  The key observation is that this chain, and hence the product, is a function
of the *set* `{foldWalls i r t : t ∈ Δ}` alone: it is computed by taking the smallest side, transport-
ing the remaining walls by the type of that side, and iterating (`psi`).  The product `psi S` is
therefore the common value of `D_{flip r Δ} D_r⁻¹` for every triple with wall set `S`, and the target
identity follows by cancelling `D_{flip}` against its inverse (`nonsing_inv_mul`, using that every
`D_r` is invertible because `D_r · psi S = 1` for the full wall set `S` of `r`).

Only the single flip identity is a finite check on the tables; everything else is proved in general.
-/
import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

open Matrix
open scoped Matrix

open Work.FoldInst

namespace Work.RTOwed

/-! ### The transport of the walls under a flip -/

/-- The side permutation attached to the *type* of a side: the image of a side under the Klein sign
change of the type of `S`. -/
def tauSide (S : Fin 24) : Fin 24 → Fin 24 :=
  sidePerm (sideType S).1

/-- **The type of the `t`-th wall does not depend on the rep**: it is the type of the root wall of
the class. -/
theorem sideType_foldWalls (i : Fin 98) (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)) :
    sideType (foldWalls i r t) = sideType (foldWallAt i t) := by
  rw [foldWalls, sideType_sidePerm]

/-- The Klein part of the wall generator of the `t`-th wall of `i` is the type of any wall of that
class with the same index. -/
theorem foldGen_fst (i : Fin 98) (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)) :
    (foldGen i t).1 = (sideType (foldWalls i r t)).1 := by
  rw [foldGen]
  exact congrArg Prod.fst (sideType_foldWalls i r t).symm

/-- **The walls of a flipped rep are the transported walls.**  Flipping the sign index at the wall
`t` and reading the `u`-th wall gives the `u`-th wall of the original rep, transported by the side
permutation of the type of the flipped wall. -/
theorem foldWalls_flipSet_singleton (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (t u : Fin (foldCodim i)) :
    foldWalls i (flipSet r {t}) u = sidePerm ((foldGen i t).1) (foldWalls i r u) := by
  have h1 : toG (foldKr i (flipSet r {t})) = (foldGen i t).1 + toG (foldKr i r) := by
    have h := congrArg Prod.fst (fold_state_flip i t r)
    simpa [Prod.fst_add] using h
  simp only [foldWalls, h1, sidePerm_add]

/-! ### The canonical correction of a set of walls -/

/-- **The canonical correction matrix of a set of walls.**  For a set `S` of sides, take its smallest
element `a`, multiply it by the correction of the set obtained by transporting the remaining sides
by the type of `a`, and iterate.  This is the common value of `D_{flip r Δ} · D_r⁻¹` for every
triple `(i, r, Δ)` with `Δ.image (foldWalls i r ·) = S`. -/
def psi : Finset (Fin 24) → Matrix (Fin 5) (Fin 5) ℤ
  | S => if h : S.Nonempty then
      pairMat (S.min' h) * psi ((S.erase (S.min' h)).image (tauSide (S.min' h)))
    else 1
termination_by S => S.card
decreasing_by
  exact lt_of_le_of_lt Finset.card_image_le
    (Finset.card_erase_lt_of_mem (Finset.min'_mem S h))

theorem psi_eq (S : Finset (Fin 24)) (h : S.Nonempty) :
    psi S = pairMat (S.min' h) * psi ((S.erase (S.min' h)).image (tauSide (S.min' h))) := by
  rw [psi.eq_def, dite_eq_left h]

theorem psi_empty : psi (∅ : Finset (Fin 24)) = 1 := by
  rw [psi.eq_def]
  simp

/-! ### The single flip identity (finite check on the tables) -/

/-- The single flip identity, checked on the fold classes `i` with `i.val < 17` (`codim ≤ 1`). -/
theorem flipDr_chunk_0_17_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_0_17 :
    (∀ (i : Fin 98), i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_0_17_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_0_17_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_0_17_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_0_17_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_0_17_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_0_17_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_0_17_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_0_17_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_0_17_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_0_17_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_0_17_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_0_17_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_0_17_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_0_17_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_0_17_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_0_17_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_0_17_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_0_17_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_0_17_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_0_17_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_0_17_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_0_17_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_0_17_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_0_17_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_0_17_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_0_17_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_0_17_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_0_17_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_0_17_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_0_17_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_0_17_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_0_17_c31 i (by omega) h31
  exact flipDr_chunk_0_17_c32 i (by omega)

/-- The single flip identity, checked on the fold classes with `17 ≤ i.val < 37`. -/
theorem flipDr_chunk_17_37_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_17_37 :
    (∀ (i : Fin 98), 17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_17_37_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_17_37_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_17_37_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_17_37_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_17_37_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_17_37_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_17_37_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_17_37_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_17_37_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_17_37_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_17_37_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_17_37_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_17_37_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_17_37_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_17_37_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_17_37_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_17_37_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_17_37_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_17_37_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_17_37_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_17_37_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_17_37_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_17_37_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_17_37_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_17_37_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_17_37_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_17_37_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_17_37_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_17_37_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_17_37_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_17_37_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_17_37_c31 i (by omega) h31
  exact flipDr_chunk_17_37_c32 i (by omega)

/-- The single flip identity, checked on the fold classes with `37 ≤ i.val < 57`. -/
theorem flipDr_chunk_37_57_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_37_57 :
    (∀ (i : Fin 98), 37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_37_57_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_37_57_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_37_57_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_37_57_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_37_57_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_37_57_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_37_57_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_37_57_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_37_57_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_37_57_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_37_57_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_37_57_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_37_57_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_37_57_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_37_57_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_37_57_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_37_57_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_37_57_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_37_57_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_37_57_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_37_57_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_37_57_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_37_57_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_37_57_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_37_57_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_37_57_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_37_57_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_37_57_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_37_57_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_37_57_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_37_57_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_37_57_c31 i (by omega) h31
  exact flipDr_chunk_37_57_c32 i (by omega)

/-- The single flip identity, checked on the fold classes with `57 ≤ i.val < 67`. -/
theorem flipDr_chunk_57_67_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_57_67 :
    (∀ (i : Fin 98), 57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_57_67_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_57_67_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_57_67_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_57_67_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_57_67_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_57_67_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_57_67_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_57_67_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_57_67_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_57_67_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_57_67_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_57_67_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_57_67_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_57_67_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_57_67_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_57_67_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_57_67_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_57_67_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_57_67_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_57_67_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_57_67_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_57_67_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_57_67_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_57_67_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_57_67_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_57_67_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_57_67_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_57_67_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_57_67_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_57_67_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_57_67_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_57_67_c31 i (by omega) h31
  exact flipDr_chunk_57_67_c32 i (by omega)

/-- The single flip identity, checked on the fold classes with `67 ≤ i.val < 77`. -/
theorem flipDr_chunk_67_77_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_67_77 :
    (∀ (i : Fin 98), 67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_67_77_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_67_77_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_67_77_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_67_77_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_67_77_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_67_77_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_67_77_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_67_77_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_67_77_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_67_77_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_67_77_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_67_77_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_67_77_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_67_77_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_67_77_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_67_77_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_67_77_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_67_77_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_67_77_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_67_77_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_67_77_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_67_77_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_67_77_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_67_77_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_67_77_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_67_77_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_67_77_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_67_77_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_67_77_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_67_77_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_67_77_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_67_77_c31 i (by omega) h31
  exact flipDr_chunk_67_77_c32 i (by omega)

/-- The single flip identity, checked on the fold classes with `77 ≤ i.val < 87`. -/
theorem flipDr_chunk_77_87_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_77_87 :
    (∀ (i : Fin 98), 77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_77_87_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_77_87_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_77_87_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_77_87_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_77_87_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_77_87_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_77_87_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_77_87_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_77_87_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_77_87_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_77_87_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_77_87_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_77_87_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_77_87_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_77_87_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_77_87_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_77_87_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_77_87_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_77_87_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_77_87_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_77_87_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_77_87_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_77_87_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_77_87_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_77_87_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_77_87_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_77_87_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_77_87_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_77_87_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_77_87_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_77_87_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_77_87_c31 i (by omega) h31
  exact flipDr_chunk_77_87_c32 i (by omega)

/-- The single flip identity, checked on the fold classes with `87 ≤ i.val`. -/
theorem flipDr_chunk_87_98_c0 : ∀ (i : Fin 98), 0 ≤ i.val → i.val < 3 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c1 : ∀ (i : Fin 98), 3 ≤ i.val → i.val < 6 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c2 : ∀ (i : Fin 98), 6 ≤ i.val → i.val < 9 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c3 : ∀ (i : Fin 98), 9 ≤ i.val → i.val < 12 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c4 : ∀ (i : Fin 98), 12 ≤ i.val → i.val < 15 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c5 : ∀ (i : Fin 98), 15 ≤ i.val → i.val < 18 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c6 : ∀ (i : Fin 98), 18 ≤ i.val → i.val < 21 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c7 : ∀ (i : Fin 98), 21 ≤ i.val → i.val < 24 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c8 : ∀ (i : Fin 98), 24 ≤ i.val → i.val < 27 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c9 : ∀ (i : Fin 98), 27 ≤ i.val → i.val < 30 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c10 : ∀ (i : Fin 98), 30 ≤ i.val → i.val < 33 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c11 : ∀ (i : Fin 98), 33 ≤ i.val → i.val < 36 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c12 : ∀ (i : Fin 98), 36 ≤ i.val → i.val < 39 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c13 : ∀ (i : Fin 98), 39 ≤ i.val → i.val < 42 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c14 : ∀ (i : Fin 98), 42 ≤ i.val → i.val < 45 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c15 : ∀ (i : Fin 98), 45 ≤ i.val → i.val < 48 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c16 : ∀ (i : Fin 98), 48 ≤ i.val → i.val < 51 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c17 : ∀ (i : Fin 98), 51 ≤ i.val → i.val < 54 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c18 : ∀ (i : Fin 98), 54 ≤ i.val → i.val < 57 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c19 : ∀ (i : Fin 98), 57 ≤ i.val → i.val < 60 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c20 : ∀ (i : Fin 98), 60 ≤ i.val → i.val < 63 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c21 : ∀ (i : Fin 98), 63 ≤ i.val → i.val < 66 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c22 : ∀ (i : Fin 98), 66 ≤ i.val → i.val < 69 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c23 : ∀ (i : Fin 98), 69 ≤ i.val → i.val < 72 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c24 : ∀ (i : Fin 98), 72 ≤ i.val → i.val < 75 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c25 : ∀ (i : Fin 98), 75 ≤ i.val → i.val < 78 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c26 : ∀ (i : Fin 98), 78 ≤ i.val → i.val < 81 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c27 : ∀ (i : Fin 98), 81 ≤ i.val → i.val < 84 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c28 : ∀ (i : Fin 98), 84 ≤ i.val → i.val < 87 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c29 : ∀ (i : Fin 98), 87 ≤ i.val → i.val < 90 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c30 : ∀ (i : Fin 98), 90 ≤ i.val → i.val < 93 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c31 : ∀ (i : Fin 98), 93 ≤ i.val → i.val < 96 → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98_c32 : ∀ (i : Fin 98), 96 ≤ i.val → (87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by decide +kernel
theorem flipDr_chunk_87_98 :
    (∀ (i : Fin 98), 87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  intro i
  by_cases h0 : i.val < 3
  · exact flipDr_chunk_87_98_c0 i (by omega) h0
  by_cases h1 : i.val < 6
  · exact flipDr_chunk_87_98_c1 i (by omega) h1
  by_cases h2 : i.val < 9
  · exact flipDr_chunk_87_98_c2 i (by omega) h2
  by_cases h3 : i.val < 12
  · exact flipDr_chunk_87_98_c3 i (by omega) h3
  by_cases h4 : i.val < 15
  · exact flipDr_chunk_87_98_c4 i (by omega) h4
  by_cases h5 : i.val < 18
  · exact flipDr_chunk_87_98_c5 i (by omega) h5
  by_cases h6 : i.val < 21
  · exact flipDr_chunk_87_98_c6 i (by omega) h6
  by_cases h7 : i.val < 24
  · exact flipDr_chunk_87_98_c7 i (by omega) h7
  by_cases h8 : i.val < 27
  · exact flipDr_chunk_87_98_c8 i (by omega) h8
  by_cases h9 : i.val < 30
  · exact flipDr_chunk_87_98_c9 i (by omega) h9
  by_cases h10 : i.val < 33
  · exact flipDr_chunk_87_98_c10 i (by omega) h10
  by_cases h11 : i.val < 36
  · exact flipDr_chunk_87_98_c11 i (by omega) h11
  by_cases h12 : i.val < 39
  · exact flipDr_chunk_87_98_c12 i (by omega) h12
  by_cases h13 : i.val < 42
  · exact flipDr_chunk_87_98_c13 i (by omega) h13
  by_cases h14 : i.val < 45
  · exact flipDr_chunk_87_98_c14 i (by omega) h14
  by_cases h15 : i.val < 48
  · exact flipDr_chunk_87_98_c15 i (by omega) h15
  by_cases h16 : i.val < 51
  · exact flipDr_chunk_87_98_c16 i (by omega) h16
  by_cases h17 : i.val < 54
  · exact flipDr_chunk_87_98_c17 i (by omega) h17
  by_cases h18 : i.val < 57
  · exact flipDr_chunk_87_98_c18 i (by omega) h18
  by_cases h19 : i.val < 60
  · exact flipDr_chunk_87_98_c19 i (by omega) h19
  by_cases h20 : i.val < 63
  · exact flipDr_chunk_87_98_c20 i (by omega) h20
  by_cases h21 : i.val < 66
  · exact flipDr_chunk_87_98_c21 i (by omega) h21
  by_cases h22 : i.val < 69
  · exact flipDr_chunk_87_98_c22 i (by omega) h22
  by_cases h23 : i.val < 72
  · exact flipDr_chunk_87_98_c23 i (by omega) h23
  by_cases h24 : i.val < 75
  · exact flipDr_chunk_87_98_c24 i (by omega) h24
  by_cases h25 : i.val < 78
  · exact flipDr_chunk_87_98_c25 i (by omega) h25
  by_cases h26 : i.val < 81
  · exact flipDr_chunk_87_98_c26 i (by omega) h26
  by_cases h27 : i.val < 84
  · exact flipDr_chunk_87_98_c27 i (by omega) h27
  by_cases h28 : i.val < 87
  · exact flipDr_chunk_87_98_c28 i (by omega) h28
  by_cases h29 : i.val < 90
  · exact flipDr_chunk_87_98_c29 i (by omega) h29
  by_cases h30 : i.val < 93
  · exact flipDr_chunk_87_98_c30 i (by omega) h30
  by_cases h31 : i.val < 96
  · exact flipDr_chunk_87_98_c31 i (by omega) h31
  exact flipDr_chunk_87_98_c32 i (by omega)

/-- **The single flip identity.**  Flipping the sign index at the `t`-th wall multiplies the
developing matrix on the right by the side pairing matrix of that wall.  (Finite check on the
tables of `Data.lean`.) -/
theorem foldDr_flipSet_singleton (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (t : Fin (foldCodim i)) :
    foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t) := by
  rcases lt_or_ge i.val 17 with h | h
  · exact flipDr_chunk_0_17 i h r t
  · rcases lt_or_ge i.val 37 with h2 | h2
    · exact flipDr_chunk_17_37 i h h2 r t
    · rcases lt_or_ge i.val 57 with h3 | h3
      · exact flipDr_chunk_37_57 i h2 h3 r t
      · rcases lt_or_ge i.val 67 with h4 | h4
        · exact flipDr_chunk_57_67 i h3 h4 r t
        · rcases lt_or_ge i.val 77 with h5 | h5
          · exact flipDr_chunk_67_77 i h4 h5 r t
          · rcases lt_or_ge i.val 87 with h6 | h6
            · exact flipDr_chunk_77_87 i h5 h6 r t
            · exact flipDr_chunk_87_98 i h6 r t

/-! ### The telescoped flip along a set of walls -/

/-- **The telescoped flip identity.**  Flipping the sign index `r` at all the walls of `Δ` multiplies
the developing matrix on the right by `psi` of the set of sides of those walls. -/
theorem foldDr_flipSet_eq_psi (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) :
    foldDr i (flipSet r Δ) = foldDr i r * psi (Δ.image (fun t => foldWalls i r t)) := by
  have main : ∀ (n : ℕ) (i : Fin 98) (r : Fin (foldCodim i) → Bool)
      (Δ : Finset (Fin (foldCodim i))), Δ.card ≤ n →
      foldDr i (flipSet r Δ) = foldDr i r * psi (Δ.image (fun t => foldWalls i r t)) := by
    intro n
    induction n with
    | zero =>
        intro i r Δ h0
        have hΔ : Δ = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h0)
        subst hΔ
        simp [psi]
    | succ n ih =>
        intro i r Δ hle
        rcases Finset.eq_empty_or_nonempty Δ with h0 | hne
        · subst h0
          simp [psi]
        · have hSne : (Δ.image (fun t => foldWalls i r t)).Nonempty :=
            Finset.image_nonempty.mpr hne
          obtain ⟨t, htΔ, hta⟩ := Finset.mem_image.mp (Finset.min'_mem _ hSne)
          -- the flip identity of the set
          have hflip : flipSet r Δ = flipSet (flipSet r {t}) (Δ.erase t) := by
            conv_lhs => rw [← Finset.insert_erase htΔ]
            rw [flipSet_insert (r := r) (Δ := Δ.erase t) (t := t) (Finset.notMem_erase t Δ)]
          -- the erased part under the flipped rep
          have himg : (Δ.erase t).image (fun u => foldWalls i (flipSet r {t}) u)
              = ((Δ.image (fun u => foldWalls i r u)).erase
                  ((Δ.image (fun u => foldWalls i r u)).min' hSne)).image
                (tauSide ((Δ.image (fun u => foldWalls i r u)).min' hSne)) := by
            have h1 : (Δ.erase t).image (fun u => foldWalls i (flipSet r {t}) u)
                = (Δ.erase t).image (fun u => sidePerm ((foldGen i t).1) (foldWalls i r u)) := by
              congr 1
              funext u
              exact foldWalls_flipSet_singleton i r t u
            have h2 : (Δ.erase t).image (fun u => sidePerm ((foldGen i t).1) (foldWalls i r u))
                = ((Δ.erase t).image (fun u => foldWalls i r u)).image
                  (sidePerm ((foldGen i t).1)) := by
              rw [Finset.image_image]
              rfl
            have h3 : (Δ.erase t).image (fun u => foldWalls i r u)
                = (Δ.image (fun u => foldWalls i r u)).erase
                  ((Δ.image (fun u => foldWalls i r u)).min' hSne) := by
              rw [Finset.image_erase (foldWalls_apply_injective i r) Δ t, hta]
            have h4 : sidePerm ((foldGen i t).1)
                = tauSide ((Δ.image (fun u => foldWalls i r u)).min' hSne) := by
              funext x
              rw [tauSide, foldGen_fst i r t, hta]
            rw [h1, h2, h3, h4]
          -- the induction hypothesis
          have hcard : (Δ.erase t).card ≤ n := by
            have h1 : (Δ.erase t).card < Δ.card := Finset.card_erase_lt_of_mem htΔ
            have h2 : 0 < Δ.card := Finset.card_pos.mpr hne
            omega
          have hIH := ih i (flipSet r {t}) (Δ.erase t) hcard
          -- the recursion of `psi`
          have hpsi := psi_eq (Δ.image (fun u => foldWalls i r u)) hSne
          rw [hflip, hIH, himg, foldDr_flipSet_singleton, hta, hpsi, Matrix.mul_assoc]
  exact main Δ.card i r Δ le_rfl

/-! ### The side pairing matrices and `psi` are invertible -/

/-- The side pairing involution on the sides. -/
def sideInv : Fin 24 → Fin 24 := fun
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5
  | 8 => 11 | 9 => 10 | 10 => 9 | 11 => 8 | 12 => 15 | 13 => 14 | 14 => 13 | 15 => 12
  | 16 => 17 | 17 => 16 | 18 => 19 | 19 => 18 | 20 => 22 | 21 => 23 | 22 => 20 | 23 => 21
  | _ => 0

/-- The side pairing matrices are involutions (finite check). -/
theorem pairMat_mul_sideInv_c0 : ∀ (S : Fin 24), 0 ≤ S.val → S.val < 3 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c1 : ∀ (S : Fin 24), 3 ≤ S.val → S.val < 6 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c2 : ∀ (S : Fin 24), 6 ≤ S.val → S.val < 9 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c3 : ∀ (S : Fin 24), 9 ≤ S.val → S.val < 12 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c4 : ∀ (S : Fin 24), 12 ≤ S.val → S.val < 15 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c5 : ∀ (S : Fin 24), 15 ≤ S.val → S.val < 18 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c6 : ∀ (S : Fin 24), 18 ≤ S.val → S.val < 21 → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv_c7 : ∀ (S : Fin 24), 21 ≤ S.val → (pairMat S * pairMat (sideInv S) = 1) := by decide +kernel
theorem pairMat_mul_sideInv (S : Fin 24) : pairMat S * pairMat (sideInv S) = 1 := by
  by_cases h0 : S.val < 3
  · exact pairMat_mul_sideInv_c0 S (by omega) h0
  by_cases h1 : S.val < 6
  · exact pairMat_mul_sideInv_c1 S (by omega) h1
  by_cases h2 : S.val < 9
  · exact pairMat_mul_sideInv_c2 S (by omega) h2
  by_cases h3 : S.val < 12
  · exact pairMat_mul_sideInv_c3 S (by omega) h3
  by_cases h4 : S.val < 15
  · exact pairMat_mul_sideInv_c4 S (by omega) h4
  by_cases h5 : S.val < 18
  · exact pairMat_mul_sideInv_c5 S (by omega) h5
  by_cases h6 : S.val < 21
  · exact pairMat_mul_sideInv_c6 S (by omega) h6
  exact pairMat_mul_sideInv_c7 S (by omega)

/-- The determinant of a side pairing matrix is a unit. -/
theorem isUnit_det_pairMat (S : Fin 24) : IsUnit (pairMat S).det :=
  isUnit_iff_exists_inv.mpr ⟨(pairMat (sideInv S)).det,
    by rw [← Matrix.det_mul, pairMat_mul_sideInv S, Matrix.det_one]⟩

/-- The determinant of the canonical correction of a set of walls is a unit. -/
theorem isUnit_det_psi (S : Finset (Fin 24)) : IsUnit (psi S).det := by
  have main : ∀ n (S : Finset (Fin 24)), S.card ≤ n → IsUnit (psi S).det := by
    intro n
    induction n with
    | zero =>
        intro S hS
        have h0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
        subst h0
        rw [psi_empty, Matrix.det_one]
        exact isUnit_one
    | succ n ih =>
        intro S hS
        rcases Finset.eq_empty_or_nonempty S with h0 | hne
        · subst h0
          rw [psi_empty, Matrix.det_one]
          exact isUnit_one
        · rw [psi_eq S hne, Matrix.det_mul]
          refine (isUnit_det_pairMat _).mul (ih _ ?_)
          have h1 : (S.erase (S.min' hne)).card < S.card :=
            Finset.card_erase_lt_of_mem (Finset.min'_mem S hne)
          have h2 : ((S.erase (S.min' hne)).image (tauSide (S.min' hne))).card ≤
              (S.erase (S.min' hne)).card := Finset.card_image_le
          omega
  exact main S.card S le_rfl

/-- **The developing matrices are invertible.**  For the rep `r`, the set `Δ` of its `true`
positions satisfies `flipSet r Δ = fun _ => false`, so the telescoped flip identity and
`fold_root` give `D_r · psi S = 1`, and the determinant of `D_r` is therefore a unit. -/
theorem isUnit_det_foldDr (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    IsUnit (foldDr i r).det := by
  have hflip : flipSet r (Finset.univ.filter (fun t => r t = true)) = fun _ => false := by
    funext t
    simp only [flipSet_apply, Finset.mem_filter, Finset.mem_univ, true_and]
    cases r t <;> simp
  have h1 : foldDr i r * psi ((Finset.univ.filter (fun t => r t = true)).image
      (fun t => foldWalls i r t)) = 1 := by
    rw [← foldDr_flipSet_eq_psi i r (Finset.univ.filter (fun t => r t = true)), hflip,
      (fold_root i).2]
  have h2 : (foldDr i r).det *
      (psi ((Finset.univ.filter (fun t => r t = true)).image (fun t => foldWalls i r t))).det
      = 1 := by
    have h := congrArg Matrix.det h1
    rwa [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h2⟩

/-- The determinant of a developing matrix is a unit after the change of scalars to `ℚ`. -/
theorem isUnit_det_foldDr_rat (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    IsUnit (((foldDr i r).map (Int.castRingHom ℚ)).det) := by
  have h := (isUnit_det_foldDr i r).map (Int.castRingHom ℚ)
  rwa [RingHom.map_det] at h

/-- The determinant of the canonical correction is a unit after the change of scalars to `ℚ`. -/
theorem isUnit_det_psi_rat (S : Finset (Fin 24)) :
    IsUnit (((psi S).map (Int.castRingHom ℚ)).det) := by
  have h := (isUnit_det_psi S).map (Int.castRingHom ℚ)
  rwa [RingHom.map_det] at h

/-- **The algebraic core**: if `X = Y · Q` with `X` and `Q` invertible then `X⁻¹ · Y = Q⁻¹`. -/
theorem inv_mul_of_eq_mul {X Y Q : Matrix (Fin 5) (Fin 5) ℚ} (hX : IsUnit X.det)
    (hQ : IsUnit Q.det) (h : X = Y * Q) : X⁻¹ * Y = Q⁻¹ := by
  have hY : Y = X * Q⁻¹ := by
    rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ, Matrix.mul_one]
  rw [hY, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul X hX, Matrix.one_mul]

/-! ### The glue: the ratio depends only on the set of walls -/

/-- **The ratio of the developing matrices of a rep and of its flip at a set of walls** is the
inverse of the canonical correction of the set of sides of those walls. -/
theorem flipDr_ratio_eq (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) :
    ((foldDr i (flipSet r Δ)).map (Int.castRingHom ℚ))⁻¹ * ((foldDr i r).map (Int.castRingHom ℚ))
      = ((psi (Δ.image (fun t => foldWalls i r t))).map (Int.castRingHom ℚ))⁻¹ := by
  have h1 : (foldDr i (flipSet r Δ)).map (Int.castRingHom ℚ)
      = (foldDr i r).map (Int.castRingHom ℚ)
        * (psi (Δ.image (fun t => foldWalls i r t))).map (Int.castRingHom ℚ) := by
    rw [foldDr_flipSet_eq_psi i r Δ, Matrix.map_mul]
  exact inv_mul_of_eq_mul (isUnit_det_foldDr_rat i (flipSet r Δ))
    (isUnit_det_psi_rat _) h1

theorem foldDr_ratio_flip (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) (Δi : Finset (Fin (Work.FoldInst.foldCodim i)))
    (Δj : Finset (Fin (Work.FoldInst.foldCodim j)))
    (h : Δi.image (fun t => Work.FoldInst.foldWalls i r t)
          = Δj.image (fun t => Work.FoldInst.foldWalls j s t)) :
    ((Work.FoldInst.foldDr i (Work.FoldInst.flipSet r Δi)).map (Int.castRingHom ℚ))⁻¹
        * ((Work.FoldInst.foldDr i r).map (Int.castRingHom ℚ))
      = ((Work.FoldInst.foldDr j (Work.FoldInst.flipSet s Δj)).map (Int.castRingHom ℚ))⁻¹
        * ((Work.FoldInst.foldDr j s).map (Int.castRingHom ℚ)) := by
  rw [flipDr_ratio_eq i r Δi, flipDr_ratio_eq j s Δj, h]

end Work.RTOwed
