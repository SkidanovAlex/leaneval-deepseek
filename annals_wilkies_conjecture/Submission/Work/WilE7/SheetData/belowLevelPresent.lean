/-
  `Work.WilE7.SheetData.belowLevelPresent`: the "below-level" presentation really presents the
  set `belowLevelSet`.

  `belowLevelZ` is the semi-Pfaffian set in `ℝ^{levDim p q M k}` whose coordinates are laid out
  as `(y, w, z 0, …, z (k-1))` with `y = Fin.append (Fin.init y) (y (Fin.last p))` (see
  `AboveAux.AboveLevelDefs`): the point `(Fin.init y, w)` ranges over `XC`, the `k` blocks
  `z l` over `X`, the `l`-th block shares its base with `y` (`eqAtoms`), the level
  `t = y (Fin.last p)` lies strictly between `-1` and `1` and strictly below the level
  `(z l) (Fin.natAdd p j)` of every block (`1 ± X (tIdx)`, `lvlAtomsBelow`), and the blocks are
  pairwise distinct as points (`distAtomsBelow`).

  The two lemmas of this file are

  * `belowLevelZ_mem_iff`: the point set of `belowLevelZ` in coordinates, and
  * `belowLevelPresent`: `belowLevelSet` is the projection of that point set to the first
    `p + 1` coordinates.

  They mirror `AboveAux.aboveLevelZ_mem_iff` / `AboveAux.aboveLevel_subPf`, with two changes:
  the level atoms have the opposite sign, and the ordering atoms `ordAtoms` are replaced by the
  distinctness atoms `distAtomsBelow` (see the header of `BelowLevelX` for why the levels of the
  chosen fibre points need not be ordered, only the points need to be pairwise distinct).
-/
import Mathlib
import Submission.Work.WilE7.SheetData.BelowLevelX
import Submission.Work.WilE7.AboveAux.aboveLevel_subPf

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.SheetData

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.AboveAux

/-! ## §1. The point set of `belowLevelZ` in coordinates -/

/-- The point set of `belowLevelZ`: the ambient cube, the `XC`-block, the `k` blocks in `X`
sharing their base with `y`, the level bounds `-1 < t < 1`, the level inequalities `t < level`
and the pairwise distinctness of the blocks. -/
private theorem belowLevelZ_mem_iff (p q M k : ℕ) (j : Fin q)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M)) (V : Fin (levDim p q M k) → ℝ) :
    V ∈ (belowLevelZ p q M k j X XC).set ↔
      V ∈ cubeC (levDim p q M k) ∧
      Fin.append (Fin.init (rdY p q M k V)) (rdW p q M k V) ∈ XC.set ∧
      (∀ l : Fin k, rdBlk p q M k V l ∈ X.set) ∧
      (∀ (l : Fin k) (a : Fin p),
        (rdBlk p q M k V l) (Fin.castAdd q a) = (Fin.init (rdY p q M k V)) a) ∧
      -1 < (rdY p q M k V) (Fin.last p) ∧
      (rdY p q M k V) (Fin.last p) < 1 ∧
      (∀ l : Fin k, (rdY p q M k V) (Fin.last p) <
        (rdBlk p q M k V l) (Fin.natAdd p j)) ∧
      (∀ l l' : Fin k, l < l' → rdBlk p q M k V l ≠ rdBlk p q M k V l') := by
  constructor
  · -- a point of `belowLevelZ` satisfies each of the listed conditions
    intro hV
    rw [belowLevelZ, Work.WilE7.LevelFibre.addAtoms_set, Set.mem_inter_iff,
      Set.mem_inter_iff] at hV
    obtain ⟨⟨hZ0, heq⟩, hpos⟩ := hV
    rw [Z0, Work.WilE8.Extend.semipf_set_extend (gapInj_injective p q M k)] at hZ0
    obtain ⟨hcube, hW⟩ := hZ0
    rw [Work.WilE7.prodSet XC (fibBlocks X k)] at hW
    obtain ⟨hXC, hB⟩ := hW
    rw [fibBlocks_set X k] at hB
    refine ⟨hcube, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(gapInj_proj p q M k).2.1 V] at hXC
      exact hXC
    · intro l
      have h := hB l
      rw [(gapInj_proj p q M k).2.2.1 V, (gapInj_proj p q M k).2.2.2 V l] at h
      exact h
    · intro l a
      have h0 := heq (Work.WilE7.LevelFibre.eaEmbed (eqAtom p q M k l a))
        (List.mem_map.mpr ⟨eqAtom p q M k l a, eqAtom_mem p q M k l a, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, eqAtom_eval p q M k V l a, sub_eq_zero] at h0
      exact h0.trans (init_rdY_apply p q M k V a)
    · have h0 := hpos (Work.WilE7.LevelFibre.eaEmbed
          (1 + MvPolynomial.X (tIdx p q M k) : MvPolynomial (Fin (levDim p q M k)) ℝ))
        (List.mem_map.mpr ⟨_, tAtomP1_mem p q M k j, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, tAtomP1_eval p q M k V] at h0
      rw [rdY_last p q M k V]
      linarith
    · have h0 := hpos (Work.WilE7.LevelFibre.eaEmbed
          (1 - MvPolynomial.X (tIdx p q M k) : MvPolynomial (Fin (levDim p q M k)) ℝ))
        (List.mem_map.mpr ⟨_, tAtomM1_mem p q M k j, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, tAtom_eval p q M k j V] at h0
      rw [rdY_last p q M k V]
      linarith
    · intro l
      have h0 := hpos (Work.WilE7.LevelFibre.eaEmbed (lvlAtomBelow p q M k j l))
        (List.mem_map.mpr ⟨_, lvlAtomBelow_mem p q M k j l, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, lvlAtomBelow_eval p q M k j V l,
        ← rdY_last p q M k V, ← rdBlk_apply p q M k V l (Fin.natAdd p j)] at h0
      linarith
    · intro l l' hl
      have h0 := hpos (Work.WilE7.LevelFibre.eaEmbed (distAtomBelow p q M k l l'))
        (List.mem_map.mpr ⟨_, distAtomBelow_mem p q M k j l l' hl, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, distAtomBelow_pos_iff p q M k V l l'] at h0
      exact fun hfun => h0 (by funext c; exact congrFun hfun c)
  · -- conversely the listed conditions make all the atoms hold
    rintro ⟨hcube, hXC, hblk, heq, hgt, hlt, hlvl, hdist⟩
    rw [belowLevelZ, Work.WilE7.LevelFibre.addAtoms_set, Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Z0, Work.WilE8.Extend.semipf_set_extend (gapInj_injective p q M k)]
      refine ⟨hcube, ?_⟩
      rw [Work.WilE7.prodSet XC (fibBlocks X k)]
      refine ⟨?_, ?_⟩
      · rw [(gapInj_proj p q M k).2.1 V]
        exact hXC
      · rw [(gapInj_proj p q M k).2.2.1 V, fibBlocks_set X k]
        intro l
        rw [(gapInj_proj p q M k).2.2.2 V l]
        exact hblk l
    · intro f hf
      rw [List.mem_map] at hf
      obtain ⟨Q, hQ, rfl⟩ := hf
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed]
      exact eqAtoms_eval_zero p q M k V heq Q hQ
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨Q, hQ, rfl⟩ := hg
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed]
      refine posAtomsBelow_eval_pos p q M k j V ?_ ?_ ?_ ?_ Q hQ
      · rw [← rdY_last p q M k V]; exact hgt
      · rw [← rdY_last p q M k V]; exact hlt
      · intro l
        rw [← rdY_last p q M k V, ← rdBlk_apply p q M k V l (Fin.natAdd p j)]
        exact hlvl l
      · intro l l' hl
        exact fun hfun => hdist l l' hl (by funext c; exact congrFun hfun c)

/-! ## §2. The projection of `belowLevelZ` is `belowLevelSet` -/

theorem belowLevelPresent (p q M k : ℕ) (j : Fin q)
    (X : WilkiesDesign.E.SemiPf (p + q)) (XC : WilkiesDesign.E.SemiPf (p + M)) :
    Work.WilE7.SheetData.belowLevelSet p q M k j X XC =
      WilkiesDesign.E.projFirst (p + 1) (M + (p + q) * k) ''
        (Work.WilE7.SheetData.belowLevelZ p q M k j X XC).set := by
  refine Set.Subset.antisymm ?_ ?_
  · -- `belowLevelSet ⊆ projFirst '' Z.set`: glue `y`, the witness `w` and the fibre points
    intro y hy
    obtain ⟨hycube, ⟨w, hw⟩, hygt, hylt, z, hzmem, hzbase, hzdist, hzlvl⟩ := hy
    have hwcube : w ∈ cubeC M := ((mem_cubeC_append (Fin.init y) w).mp hw.1).2
    refine ⟨glue p q M k y w z, ?_, rdY_glue p q M k y w z⟩
    rw [belowLevelZ_mem_iff p q M k j X XC]
    refine ⟨glue_mem_cubeC p q M k y w z hycube hwcube fun l => (hzmem l).1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rdY_glue, rdW_glue]; exact hw
    · intro l; rw [rdBlk_glue]; exact hzmem l
    · intro l a; rw [rdBlk_glue, init_rdY_apply, glue_xIdx]
      exact congrFun (hzbase l) a
    · rw [rdY_glue]; exact hygt
    · rw [rdY_glue]; exact hylt
    · intro l; rw [rdBlk_glue, rdY_glue]; exact hzlvl l
    · intro l l' hl; rw [rdBlk_glue, rdBlk_glue]; exact hzdist l l' hl
  · -- `projFirst '' Z.set ⊆ belowLevelSet`: read `w` and the `k` fibre points off the point
    rintro y ⟨V, hV, rfl⟩
    change rdY p q M k V ∈ belowLevelSet p q M k j X XC
    obtain ⟨hcube, hXC, hblk, heq, hgt, hlt, hlvl, hdist⟩ :=
      (belowLevelZ_mem_iff p q M k j X XC V).mp hV
    refine ⟨fun i => hcube _, ⟨rdW p q M k V, hXC⟩, ?_, ?_,
      ⟨fun l => rdBlk p q M k V l, ?_, ?_, ?_, ?_⟩⟩
    · rw [rdY_last]; exact hgt
    · rw [rdY_last]; exact hlt
    · intro l; exact hblk l
    · intro l; funext a; rw [init_rdY_apply]; exact heq l a
    · intro l l' hl; exact hdist l l' hl
    · intro l; rw [rdY_last]; exact hlvl l

end Work.WilE7.SheetData
