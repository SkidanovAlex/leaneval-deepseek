/-
  `Work.WilE7.SheetData.BelowLevelX`: the "below-level" presentation — the mirror image of
  `Work.WilE7.AboveAux.aboveLevel_subPf`.

  `AboveAux.aboveLevel_subPf` presents the set of levels `t = y (Fin.last p)` lying strictly
  *above* `k` points of the fibre of `X` over the base `Fin.init y`:

      Y⁺ = {y | y ∈ cubeC (p+1) ∧ (∃ w, Fin.append (Fin.init y) w ∈ XC.set) ∧ y (Fin.last p) < 1 ∧
             ∃ z : Fin k → ℝ^{p+q}, (∀ l, z l ∈ X.set) ∧ (∀ l, projFirst p q (z l) = Fin.init y) ∧
               (∀ l l', l < l' → level (z l) < level (z l')) ∧
               (∀ l, level (z l) < y (Fin.last p))}

  (with `level (z l) = (z l) (Fin.natAdd p j)`).  This module sets up the mirror image

      Y⁻ = {y | y ∈ cubeC (p+1) ∧ (∃ w, Fin.append (Fin.init y) w ∈ XC.set) ∧
             -1 < y (Fin.last p) ∧ y (Fin.last p) < 1 ∧
             ∃ z : Fin k → ℝ^{p+q}, (∀ l, z l ∈ X.set) ∧ (∀ l, projFirst p q (z l) = Fin.init y) ∧
               (∀ l l', l < l' → z l ≠ z l') ∧
               (∀ l, y (Fin.last p) < level (z l))}

  where the `k` points of the fibre now lie *above* the level `t` (and the level is bounded below
  by `-1` in addition to `1`).  The ambient layout, the coordinate maps (`tIdx`, `blkD`, `rdY`,
  `rdW`, `rdBlk`, `rdBlkPt`) and the base equations `eqAtoms` are those of
  `AboveAux.AboveLevelDefs`, reused verbatim; the level atoms change sign and the *ordering*
  atoms `ordAtoms` are replaced by **distinctness** atoms `Σ_c (z l c - z l' c)² > 0`.

  Why distinctness rather than the order: for the sheet data of `WilE7` (the fibre of `X` over
  `x ∈ C` is exactly the `k` sheets `s j x`, and their levels are *non-decreasing* in `j`), the
  region strictly below the level of the `i`-th sheet is exactly the set of `t` below the levels
  of `k - i` pairwise distinct points of the fibre — and nothing more.  The levels of the chosen
  points need **not** be distinct: two sheets of one stratum may share their level (the
  "duplicate-level obstruction" of `NOTES_S32_CoreLT_succ_design.md` §5.4, e.g. the two branches
  of `y₁² = x₁` with level `y₂ ≡ 0`), and then the `k - i` fibre points above `t` have
  non-decreasing but not strictly increasing levels.  A strictly increasing ordering of them does
  not exist, while their pairwise distinctness (as *points* of `ℝ^{p+q}`, which is what the
  counting argument needs) always does.  Since `eqAtoms` already forces the base coordinates of
  all the blocks to agree, the distinctness atom on the coordinates of the block is exactly the
  distinctness of the fibre points.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.AboveAux.aboveLevel_subPf
import Submission.Work.WilE7.AboveAux.gapInj_proj
import Submission.Work.WilE7.AboveAux.blocksOf_fibBlkIdx
import Submission.Work.WilE7.AboveAux.blocksOf_mem_cube
import Submission.Work.WilE7.LevelFibre.withAtoms

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators
namespace Work.WilE7.SheetData

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.AboveAux

/-! ## §1. The atoms of the below-level presentation -/

/-- The atom `level (z l) - t`: positive exactly when the level of the `l`-th fibre point lies
strictly above `t`.  This is the negative of `AboveAux.lvlAtom`. -/
def lvlAtomBelow (p q M k : ℕ) (j : Fin q) (l : Fin k) :
    MvPolynomial (Fin (levDim p q M k)) ℝ :=
  MvPolynomial.X (blkD p q M k l (Fin.natAdd p j)) - MvPolynomial.X (tIdx p q M k)

/-- The list of level inequalities `t < level (z l)`. -/
def lvlAtomsBelow (p q M k : ℕ) (j : Fin q) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (List.finRange k).map fun l => lvlAtomBelow p q M k j l

/-- The atom `Σ_c (z l c - z l' c)²`, positive exactly when the two blocks are different points
(same shape as `LevelFibre.lf3DistAtom`). -/
def distAtomBelow (p q M k : ℕ) (l l' : Fin k) :
    MvPolynomial (Fin (levDim p q M k)) ℝ :=
  ∑ c : Fin (p + q),
    (MvPolynomial.X (blkD p q M k l c) - MvPolynomial.X (blkD p q M k l' c)) ^ 2

/-- The list of distinctness atoms, for the unordered pairs of distinct blocks. -/
def distAtomsBelow (p q M k : ℕ) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (((List.finRange k).product (List.finRange k)).filter
      (fun pr : Fin k × Fin k => pr.1 < pr.2)).map
    fun pr => distAtomBelow p q M k pr.1 pr.2

/-- All the positive atoms of the below-level presentation: `-1 < t`, `t < 1`, the level
inequalities `t < level (z l)` and the pairwise distinctness of the blocks. -/
def posAtomsBelow (p q M k : ℕ) (j : Fin q) : List (MvPolynomial (Fin (levDim p q M k)) ℝ) :=
  (1 + MvPolynomial.X (tIdx p q M k)) :: (1 - MvPolynomial.X (tIdx p q M k)) ::
    (lvlAtomsBelow p q M k j ++ distAtomsBelow p q M k)

/-! ## §2. The presentation -/

/-- The semi-Pfaffian set presenting `belowLevelSet` in `ℝ^{levDim p q M k}`: the base data
`(x, w, z 0, …, z (k-1))` of `AboveAux.Z0`, cut by the base equations, the level inequalities
`t < level (z l)`, the distinctness atoms and the two bounds `-1 < t < 1`. -/
def belowLevelZ (p q M k : ℕ) (j : Fin q) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SemiPf (levDim p q M k) :=
  Work.WilE7.LevelFibre.addAtoms (Z0 p q M k X XC)
    ((eqAtoms p q M k).map fun Q => Work.WilE7.LevelFibre.eaEmbed Q)
    ((posAtomsBelow p q M k j).map fun Q => Work.WilE7.LevelFibre.eaEmbed Q)

/-- The set presented by `belowLevelZ`: the level `t` lies strictly between `-1` and `1` and
strictly below the levels of `k` pairwise distinct points of the fibre of `X` over the base, the
base itself ranging over the projection of `XC`. -/
def belowLevelSet (p q M k : ℕ) (j : Fin q) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    Set (Fin (p + 1) → ℝ) :=
  {y : Fin (p + 1) → ℝ |
    y ∈ cubeC (p + 1) ∧
    (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
    -1 < y (Fin.last p) ∧ y (Fin.last p) < 1 ∧
    ∃ z : Fin k → (Fin (p + q) → ℝ),
      (∀ l : Fin k, z l ∈ X.set) ∧
      (∀ l : Fin k, projFirst p q (z l) = Fin.init y) ∧
      (∀ l l' : Fin k, l < l' → z l ≠ z l') ∧
      (∀ l : Fin k, y (Fin.last p) < (z l) (Fin.natAdd p j))}

/-! ## §3. Evaluating and locating the atoms -/

theorem lvlAtomBelow_eval (p q M k : ℕ) (j : Fin q) (V : Fin (levDim p q M k) → ℝ)
    (l : Fin k) :
    MvPolynomial.eval V (lvlAtomBelow p q M k j l) =
      V (blkD p q M k l (Fin.natAdd p j)) - V (tIdx p q M k) := by
  simp [lvlAtomBelow]

theorem tAtomP1_eval (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) :
    MvPolynomial.eval V ((1 + MvPolynomial.X (tIdx p q M k) :
      MvPolynomial (Fin (levDim p q M k)) ℝ)) = 1 + V (tIdx p q M k) := by
  simp

theorem distAtomBelow_eval (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (l l' : Fin k) :
    MvPolynomial.eval V (distAtomBelow p q M k l l') =
      ∑ c : Fin (p + q), (V (blkD p q M k l c) - V (blkD p q M k l' c)) ^ 2 := by
  simp only [distAtomBelow, map_sum, map_pow, map_sub, MvPolynomial.eval_X]

/-- The distinctness atom is positive exactly when the two blocks are different. -/
theorem distAtomBelow_pos_iff (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (l l' : Fin k) :
    0 < MvPolynomial.eval V (distAtomBelow p q M k l l') ↔
      (fun c : Fin (p + q) => V (blkD p q M k l c)) ≠
        (fun c : Fin (p + q) => V (blkD p q M k l' c)) := by
  rw [distAtomBelow_eval]
  constructor
  · intro h hfun
    have hzero : ∑ c : Fin (p + q),
        (V (blkD p q M k l c) - V (blkD p q M k l' c)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [sub_eq_zero.mpr (congrFun hfun c), zero_pow (by norm_num)]
    rw [hzero] at h
    exact lt_irrefl _ h
  · intro hne
    have hex : ∃ c : Fin (p + q),
        V (blkD p q M k l c) ≠ V (blkD p q M k l' c) := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    obtain ⟨c, hc⟩ := hex
    exact Finset.sum_pos' (fun c _ => sq_nonneg _)
      ⟨c, Finset.mem_univ c, sq_pos_of_ne_zero (sub_ne_zero.mpr hc)⟩

theorem lvlAtomBelow_mem (p q M k : ℕ) (j : Fin q) (l : Fin k) :
    lvlAtomBelow p q M k j l ∈ posAtomsBelow p q M k j := by
  rw [posAtomsBelow]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)))

theorem distAtomBelow_mem (p q M k : ℕ) (j : Fin q) (l l' : Fin k) (h : l < l') :
    distAtomBelow p q M k l l' ∈ posAtomsBelow p q M k j := by
  rw [posAtomsBelow]
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
  rw [distAtomsBelow]
  exact List.mem_map.mpr ⟨(l, l'),
    List.mem_filter.mpr ⟨List.mem_product.mpr ⟨List.mem_finRange l, List.mem_finRange l'⟩,
      by simpa using h⟩, rfl⟩

theorem tAtomP1_mem (p q M k : ℕ) (j : Fin q) :
    (1 + MvPolynomial.X (tIdx p q M k) : MvPolynomial (Fin (levDim p q M k)) ℝ) ∈
      posAtomsBelow p q M k j := List.mem_cons_self ..

theorem tAtomM1_mem (p q M k : ℕ) (j : Fin q) :
    (1 - MvPolynomial.X (tIdx p q M k) : MvPolynomial (Fin (levDim p q M k)) ℝ) ∈
      posAtomsBelow p q M k j :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- Every positive atom of the below-level presentation is positive, given the bounds on the
level, the level conditions and the distinctness of the blocks. -/
theorem posAtomsBelow_eval_pos (p q M k : ℕ) (j : Fin q) (V : Fin (levDim p q M k) → ℝ)
    (hgt : -1 < V (tIdx p q M k)) (hlt : V (tIdx p q M k) < 1)
    (hlvl : ∀ l : Fin k, V (tIdx p q M k) < V (blkD p q M k l (Fin.natAdd p j)))
    (hdist : ∀ l l' : Fin k, l < l' →
      (fun c : Fin (p + q) => V (blkD p q M k l c)) ≠
        (fun c : Fin (p + q) => V (blkD p q M k l' c))) :
    ∀ Q ∈ posAtomsBelow p q M k j, 0 < MvPolynomial.eval V Q := by
  intro Q hQ
  rw [posAtomsBelow] at hQ
  rcases List.mem_cons.mp hQ with rfl | hQ
  · rw [tAtomP1_eval p q M k V]
    linarith
  · rcases List.mem_cons.mp hQ with rfl | hQ
    · rw [tAtom_eval p q M k j V]
      linarith
    · rcases List.mem_append.mp hQ with hQ | hQ
      · rw [lvlAtomsBelow] at hQ
        obtain ⟨l, -, rfl⟩ := List.mem_map.mp hQ
        rw [lvlAtomBelow_eval p q M k j V l]
        linarith [hlvl l]
      · rw [distAtomsBelow] at hQ
        obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hQ
        rw [List.mem_filter] at hpr
        have hpr' : pr.1 < pr.2 := by simpa using hpr.2
        rw [distAtomBelow_pos_iff]
        exact hdist pr.1 pr.2 hpr'

end Work.WilE7.SheetData
