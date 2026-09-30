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
theorem flipDr_chunk_0_17 :
    (∀ (i : Fin 98), i.val < 17 → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

/-- The single flip identity, checked on the fold classes with `17 ≤ i.val < 37`. -/
theorem flipDr_chunk_17_37 :
    (∀ (i : Fin 98), 17 ≤ i.val → i.val < 37 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

/-- The single flip identity, checked on the fold classes with `37 ≤ i.val < 57`. -/
theorem flipDr_chunk_37_57 :
    (∀ (i : Fin 98), 37 ≤ i.val → i.val < 57 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

/-- The single flip identity, checked on the fold classes with `57 ≤ i.val < 67`. -/
theorem flipDr_chunk_57_67 :
    (∀ (i : Fin 98), 57 ≤ i.val → i.val < 67 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

/-- The single flip identity, checked on the fold classes with `67 ≤ i.val < 77`. -/
theorem flipDr_chunk_67_77 :
    (∀ (i : Fin 98), 67 ≤ i.val → i.val < 77 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

/-- The single flip identity, checked on the fold classes with `77 ≤ i.val < 87`. -/
theorem flipDr_chunk_77_87 :
    (∀ (i : Fin 98), 77 ≤ i.val → i.val < 87 → ∀ (r : Fin (foldCodim i) → Bool)
      (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

/-- The single flip identity, checked on the fold classes with `87 ≤ i.val`. -/
theorem flipDr_chunk_87_98 :
    (∀ (i : Fin 98), 87 ≤ i.val → ∀ (r : Fin (foldCodim i) → Bool) (t : Fin (foldCodim i)),
      foldDr i (flipSet r {t}) = foldDr i r * pairMat (foldWalls i r t)) := by
  decide +kernel

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
theorem pairMat_mul_sideInv (S : Fin 24) : pairMat S * pairMat (sideInv S) = 1 := by
  fin_cases S <;> decide +kernel

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
