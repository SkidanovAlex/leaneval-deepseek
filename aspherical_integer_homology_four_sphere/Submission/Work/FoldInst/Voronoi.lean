/-
# The Voronoi pieces of the fold charts

This file replaces the "open star" pieces `Dlift` of `FoldPiece.lean` (which are **not** the
blueprint's `D_{F_r}`: they contain the whole interior of the copy and therefore overlap) by the
blueprint's Voronoi pieces

  `D_{F_r} = {y ∈ Q̄ : max_{t} s_{w_t}(y) < min_{j ∉ walls} s_j(y)}`,

with the `24` truncation constraints included among the "others" (so that the source of the fold
chart does not touch the truncation facets, which is what makes its image relatively open in the
orthant).

## Contents

* `foldGen`, `wallSum` — the group element attached to a set of walls;
* `flipSet` — flipping the sign index at a set of walls;
* `reflCoords` — the corresponding coordinate reflection of `E4`;
* `VoronoiOpen` (the open conditions on `y ∈ E4`) and `Dvor i r ⊆ Xbar`, the pieces.

The pieces `Dvor i r` (`r : Fin (foldCodim i) → Bool`) are pairwise disjoint and their images in `M̄`
are the pieces of the fold chart of the face class `i` (`FoldPsi.lean`, `FoldChart.lean`).
-/
import Mathlib
import Submission.Work.Fold.Basic
import Submission.Work.FoldInst.FoldPiece
import Submission.Work.FoldInst.fold_source_open
import Submission.Work.FoldInst.fold_theta_orthant

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.FoldInst

/-! ### The wall group of a fold class -/

/-- The sum of the wall generators over a set of walls (`foldGen` is defined in
`fold_source_open.lean`: the type of the `t`-th wall of the class). -/
def wallSum (i : Fin 98) (Δ : Finset (Fin (foldCodim i))) : Gg := ∑ t ∈ Δ, foldGen i t

@[simp] theorem wallSum_empty (i : Fin 98) : wallSum i ∅ = 0 := by simp [wallSum]

theorem wallSum_insert (i : Fin 98) (t : Fin (foldCodim i)) (Δ : Finset (Fin (foldCodim i)))
    (ht : t ∉ Δ) : wallSum i (insert t Δ) = foldGen i t + wallSum i Δ := by
  simp [wallSum, Finset.sum_insert ht]

/-! ### Flipping the sign index -/

/-- Flip a sign index at the entries in `Δ`. -/
def flipSet {c : ℕ} (r : Fin c → Bool) (Δ : Finset (Fin c)) : Fin c → Bool :=
  fun t => xor (r t) (decide (t ∈ Δ))

@[simp] theorem flipSet_apply {c : ℕ} (r : Fin c → Bool) (Δ : Finset (Fin c)) (t : Fin c) :
    flipSet r Δ t = xor (r t) (decide (t ∈ Δ)) := rfl

@[simp] theorem flipSet_empty {c : ℕ} (r : Fin c → Bool) : flipSet r ∅ = r := by
  funext t; simp [flipSet]

theorem flipSet_insert {c : ℕ} (r : Fin c → Bool) (Δ : Finset (Fin c)) {t : Fin c}
    (ht : t ∉ Δ) : flipSet r (insert t Δ) = flipSet (flipSet r {t}) Δ := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp [flipSet, ht]
  · simp [flipSet, hu, Finset.mem_insert, hu]

@[simp] theorem flipSet_flipSet {c : ℕ} (r : Fin c → Bool) (Δ : Finset (Fin c)) :
    flipSet (flipSet r Δ) Δ = r := by
  funext t
  simp [flipSet, Bool.xor_assoc]

/-! ### The coordinate reflection attached to a set of walls -/

/-- Negate the first `c` coordinates of `z` at the positions in `Δ` (coordinates `≥ c` are fixed).
This is `Work.Fold.reflVec` with the sign index `t ↦ decide (t ∉ Δ)`: Fold's `signVal` is `+1` on
`true`, so the coordinates that get *flipped* are exactly those in `Δ`. -/
def reflCoords {c : ℕ} (Δ : Finset (Fin c)) (z : E4) : E4 :=
  Work.Fold.e4Of fun i =>
    if h : (i : ℕ) < c then (if (⟨i, h⟩ : Fin c) ∈ Δ then -1 else 1) * z i else z i

theorem reflCoords_apply {c : ℕ} (Δ : Finset (Fin c)) (z : E4) (i : Fin 4) :
    reflCoords Δ z i =
      if h : (i : ℕ) < c then (if (⟨i, h⟩ : Fin c) ∈ Δ then -1 else 1) * z i else z i := by
  rw [reflCoords, Work.Fold.e4Of_apply]

/-- `reflCoords Δ` is the coordinate reflection of the fold framework with sign index
`t ↦ decide (t ∉ Δ)`. -/
theorem reflCoords_eq_reflVec {c : ℕ} (Δ : Finset (Fin c)) :
    reflCoords Δ = Work.Fold.reflVec (fun t => decide (t ∉ Δ)) := by
  funext z
  refine Work.Fold.e4_ext fun i => ?_
  rw [reflCoords_apply, Work.Fold.reflVec_apply]
  by_cases h : (i : ℕ) < c
  · rw [dif_pos h, dif_pos h, Work.Fold.signVal]
    by_cases hi : (⟨i, h⟩ : Fin c) ∈ Δ <;> simp [hi]
  · rw [dif_neg h, dif_neg h]

@[simp] theorem reflCoords_empty {c : ℕ} (z : E4) : reflCoords (∅ : Finset (Fin c)) z = z := by
  refine Work.Fold.e4_ext fun i => ?_
  rw [reflCoords_apply]
  by_cases h : (i : ℕ) < c
  · rw [dif_pos h]; simp
  · rw [dif_neg h]

@[simp] theorem reflCoords_reflCoords {c : ℕ} (Δ : Finset (Fin c)) (z : E4) :
    reflCoords Δ (reflCoords Δ z) = z := by
  refine Work.Fold.e4_ext fun i => ?_
  rw [reflCoords_apply, reflCoords_apply]
  by_cases h : (i : ℕ) < c
  · rw [dif_pos h, dif_pos h]
    by_cases hi : (⟨i, h⟩ : Fin c) ∈ Δ <;> simp [hi]
  · rw [dif_neg h, dif_neg h]

/-- The sign index `signVecNeg r` of the fold framework corresponds, under `reflCoords`, to the
set of walls `{t | r t}`. -/
theorem signVecNeg_eq_decide {c : ℕ} (r : Work.Fold.Sign c) :
    Work.Fold.signVecNeg r = fun t => decide (t ∉ ({t | r t = true} : Finset (Fin c))) := by
  funext t
  simp only [Work.Fold.signVecNeg]
  by_cases h : r t = true <;> simp [h]

theorem reflVec_signVecNeg {c : ℕ} (r : Work.Fold.Sign c) :
    Work.Fold.reflVec (Work.Fold.signVecNeg r)
      = reflCoords ({t | r t = true} : Finset (Fin c)) := by
  rw [reflCoords_eq_reflVec, signVecNeg_eq_decide]

/-! ### The Voronoi pieces -/

/-- The open conditions defining the Voronoi region of the representative `r`: every non-wall
constraint (the `24` sides and the `24` truncations) is strictly positive and strictly larger than
every wall. -/
def VoronoiOpen (i : Fin 98) (r : Fin (foldCodim i) → Bool) : Set E4 :=
  {y | (∀ S : Fin 24, (∀ t : Fin (foldCodim i), foldWalls i r t ≠ S) →
          0 < sideSlack S y ∧
            ∀ t : Fin (foldCodim i), sideSlack (foldWalls i r t) y < sideSlack S y) ∧
       (∀ w : Fin 24, 0 < truncSlack w y ∧
         ∀ t : Fin (foldCodim i), sideSlack (foldWalls i r t) y < truncSlack w y)}

theorem mem_VoronoiOpen {i : Fin 98} {r : Fin (foldCodim i) → Bool} {y : E4} :
    y ∈ VoronoiOpen i r ↔
      (∀ S : Fin 24, (∀ t : Fin (foldCodim i), foldWalls i r t ≠ S) →
          0 < sideSlack S y ∧
            ∀ t : Fin (foldCodim i), sideSlack (foldWalls i r t) y < sideSlack S y) ∧
      (∀ w : Fin 24, 0 < truncSlack w y ∧
         ∀ t : Fin (foldCodim i), sideSlack (foldWalls i r t) y < truncSlack w y) := Iff.rfl

/-- **The Voronoi region is open in `E4`**: it is a finite intersection of strict linear
inequalities in the continuous slack functions. -/
theorem isOpen_VoronoiOpen (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    IsOpen (VoronoiOpen i r) := by
  have hset : VoronoiOpen i r =
      (⋂ (S : Fin 24), ⋂ (_ : ∀ t : Fin (foldCodim i), foldWalls i r t ≠ S),
        ({p : E4 | 0 < sideSlack S p} ∩
          ⋂ (t : Fin (foldCodim i)), {p : E4 | sideSlack (foldWalls i r t) p < sideSlack S p})) ∩
      (⋂ (w : Fin 24), ({p : E4 | 0 < truncSlack w p} ∩
          ⋂ (t : Fin (foldCodim i)),
            {p : E4 | sideSlack (foldWalls i r t) p < truncSlack w p})) := by
    ext p
    simp only [mem_VoronoiOpen, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsOpen.inter (isOpen_iInter_of_finite fun S => isOpen_iInter_of_finite fun _ => ?_)
    (isOpen_iInter_of_finite fun w => ?_)
  · refine IsOpen.inter (isOpen_lt continuous_const (continuous_sideSlack S)) ?_
    exact isOpen_iInter_of_finite fun t =>
      isOpen_lt (continuous_sideSlack _) (continuous_sideSlack S)
  · refine IsOpen.inter (isOpen_lt continuous_const (continuous_truncSlack w)) ?_
    exact isOpen_iInter_of_finite fun t =>
      isOpen_lt (continuous_sideSlack _) (continuous_truncSlack w)

/-- **The Voronoi piece of the fold chart** of the class `i` and the sign index `r`: the points of
the copy `foldCr i r` of `Q̄` which are strictly closer (in the slack sense) to every wall of `r`
than to any other constraint, with all non-wall constraints strictly positive. -/
def Dvor (i : Fin 98) (r : Fin (foldCodim i) → Bool) : Set Xbar :=
  {x | x.1 = foldCr i r ∧ x.2.1 ∈ VoronoiOpen i r}

theorem mem_Dvor {i : Fin 98} {r : Fin (foldCodim i) → Bool} {x : Xbar} :
    x ∈ Dvor i r ↔ x.1 = foldCr i r ∧ x.2.1 ∈ VoronoiOpen i r := Iff.rfl

theorem Dvor_subset_copy (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    Dvor i r ⊆ {x : Xbar | x.1 = foldCr i r} := fun _ hx => hx.1

/-- The Voronoi piece is open in `Xbar`. -/
theorem isOpen_Dvor (i : Fin 98) (r : Fin (foldCodim i) → Bool) : IsOpen (Dvor i r) := by
  have h : Dvor i r = {x : Xbar | x.1 = foldCr i r} ∩
      {x : Xbar | x.2.1 ∈ VoronoiOpen i r} := by
    ext x; simp [Dvor]
  rw [h]
  exact IsOpen.inter ((isOpen_discrete (s := {foldCr i r})).preimage continuous_fst)
    ((isOpen_VoronoiOpen i r).preimage
      ((continuous_subtype_val : Continuous (Subtype.val : Qbar → E4)).comp continuous_snd))

/-- A point of a Voronoi piece lies in the open unit ball (so that `foldTheta` applies to it). -/
theorem Dvor_subset_ball (i : Fin 98) (r : Fin (foldCodim i) → Bool) {x : Xbar}
    (hx : x ∈ Dvor i r) : x.2.1 ∈ HypModel.ball := Qbar_subset_ball x.2.2

/-- Every side that is *tight* at a point of a Voronoi piece is a wall of the representative. -/
theorem Dvor_tight (i : Fin 98) (r : Fin (foldCodim i) → Bool) {x : Xbar} (hx : x ∈ Dvor i r)
    {S : Fin 24} (hS : sideSlack S x.2.1 = 0) :
    ∃ t : Fin (foldCodim i), foldWalls i r t = S := by
  by_contra h
  exact absurd hS (ne_of_gt (hx.2.1 S (fun t ht => h ⟨t, ht⟩)).1)

/-! ### The glued chart value

The pieces `Dvor i r` are pairwise disjoint, so the following is well defined; the two lemmas
`foldPsi_eq` (`FoldPsi.lean`) and `foldPhi_mk` identify it with `foldTheta i r` on a piece. -/

/-- **The glued chart value** of the fold class `i`, at the level of `Xbar`: it is
`foldTheta i r x.2.1` on the (unique) piece `Dvor i r` containing `x`, and `0` off the union of the
pieces (where the value is irrelevant). -/
def foldPsi (i : Fin 98) (x : Xbar) : E4 := by
  classical
  exact if h : ∃ r : Fin (foldCodim i) → Bool, x ∈ Dvor i r then foldTheta i h.choose x.2.1 else 0

/-- **The chart value of the fold class `i` on `M̄`**, evaluated on any lift of the class. -/
def foldPhi (i : Fin 98) (p : Mbar) : E4 := foldPsi i (Quotient.out p)

end Work.FoldInst
