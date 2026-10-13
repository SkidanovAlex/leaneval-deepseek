/-
  Area E7 (`Submission.Work.WilE7.AboveAux.aboveLevel_subPf`).

  The "above level" set of a fibre of a restricted semi-Pfaffian set is sub-Pfaffian: for
  `X : SemiPf (p+q)`, `XC : SemiPf (p+M)` and `j : Fin q`,

      Y = {y : Fin (p+1) → ℝ | y ∈ cubeC (p+1) ∧ (∃ w, Fin.append (Fin.init y) w ∈ XC.set) ∧
             y (Fin.last p) < 1 ∧
             ∃ z : Fin k → (Fin (p+q) → ℝ),
               (∀ l, z l ∈ X.set) ∧ (∀ l, projFirst p q (z l) = Fin.init y) ∧
               (∀ l l', l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
               (∀ l, (z l) (Fin.natAdd p j) < y (Fin.last p))}

  is `SubPf (p+1) Y`.

  The presentation is fixed in `Submission.Work.WilE7.AboveAux.AboveLevelDefs` (see there for the
  layout of the ambient space `ℝ^{levDim}`): it is the `SemiPf.prod` of `XC` with the `k`-fold
  self-product of `X` (`fibBlocks`), pulled back along the "gap" injection `gapInj` (which drops
  the level coordinate), and cut by the atoms `eqAtoms`, `lvlAtoms`, `ordAtoms` and `1 - X (tIdx)`.
  This file computes its point set (`aboveLevelZ_mem_iff`) and derives the two inclusions of `Y`
  against the projection.

  The helper lemmas `fibBlocks_set`, `gapInj_proj`, `blocksOf_fibBlkIdx`, `blocksOf_mem_cube` are
  proved in the sibling files of the same directory (`.../fibBlocks_set.lean`, `.../gapInj_proj.lean`,
  `.../blocksOf_fibBlkIdx.lean`, `.../blocksOf_mem_cube.lean`); they are imported below.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.AboveAux.AboveLevelDefs
import Submission.Work.WilE7.AboveAux.fibBlocks_set
import Submission.Work.WilE7.AboveAux.gapInj_proj
import Submission.Work.WilE7.AboveAux.blocksOf_fibBlkIdx
import Submission.Work.WilE7.AboveAux.blocksOf_mem_cube
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE8.Extend.semipf_set_extend

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Appending coordinates -/

theorem projFirst_append {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    projFirst n m (Fin.append a b) = a := by
  funext i; exact Fin.append_left a b i

theorem projSnd_append {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    projSnd n m (Fin.append a b) = b := by
  funext i; exact Fin.append_right a b i

/-- The cube of a concatenation is the product of the cubes. -/
theorem mem_cubeC_append {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    Fin.append a b ∈ cubeC (n + m) ↔ a ∈ cubeC n ∧ b ∈ cubeC m := by
  constructor
  · intro h
    exact ⟨fun i => by rw [← Fin.append_left a b i]; exact h _,
      fun j => by rw [← Fin.append_right a b j]; exact h _⟩
  · rintro ⟨ha, hb⟩ i
    exact Fin.addCases (motive := fun i => |Fin.append a b i| ≤ 1)
      (fun i => by rw [Fin.append_left]; exact ha i)
      (fun j => by rw [Fin.append_right]; exact hb j) i

/-! ## The coordinates of the large space -/

theorem xIdx_eq (p q M k : ℕ) (a : Fin p) :
    xIdx p q M k a = Fin.castAdd (M + (p + q) * k) (Fin.castSucc a) :=
  Fin.ext (by simp [xIdx, Fin.val_castAdd])

theorem tIdx_eq (p q M k : ℕ) :
    tIdx p q M k = Fin.castAdd (M + (p + q) * k) (Fin.last p) :=
  Fin.ext (by simp [tIdx, Fin.val_castAdd])

theorem init_rdY_apply (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (a : Fin p) :
    (Fin.init (rdY p q M k V)) a = V (xIdx p q M k a) := by
  rw [xIdx_eq]; rfl

theorem rdY_last (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) :
    (rdY p q M k V) (Fin.last p) = V (tIdx p q M k) := by
  rw [tIdx_eq]; rfl

theorem blkD_eq (p q M k : ℕ) (l : Fin k) (i : Fin (p + q)) :
    blkD p q M k l i = Fin.natAdd (p + 1) (Fin.natAdd M (fibBlkIdx (p + q) k l i)) :=
  Fin.ext (by simp [blkD, fibBlkIdx_val, Fin.val_natAdd]; ring)

/-- The block `l` of a point of the large space is the value at the block coordinates. -/
theorem rdBlk_apply (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (l : Fin k)
    (i : Fin (p + q)) : rdBlk p q M k V l i = V (blkD p q M k l i) := rfl

/-! ## The atoms -/

theorem eqAtom_eval (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (l : Fin k) (a : Fin p) :
    MvPolynomial.eval V (eqAtom p q M k l a) =
      V (blkD p q M k l (Fin.castAdd q a)) - V (xIdx p q M k a) := by
  simp [eqAtom]

theorem lvlAtom_eval (p q M k : ℕ) (j : Fin q) (V : Fin (levDim p q M k) → ℝ) (l : Fin k) :
    MvPolynomial.eval V (lvlAtom p q M k j l) =
      V (tIdx p q M k) - V (blkD p q M k l (Fin.natAdd p j)) := by
  simp [lvlAtom]

theorem ordAtom_eval (p q M k : ℕ) (j : Fin q) (V : Fin (levDim p q M k) → ℝ)
    (l l' : Fin k) :
    MvPolynomial.eval V (ordAtom p q M k j l l') =
      V (blkD p q M k l' (Fin.natAdd p j)) - V (blkD p q M k l (Fin.natAdd p j)) := by
  simp [ordAtom]

theorem tAtom_eval (p q M k : ℕ) (j : Fin q) (V : Fin (levDim p q M k) → ℝ) :
    MvPolynomial.eval V (1 - MvPolynomial.X (tIdx p q M k) :
      MvPolynomial (Fin (levDim p q M k)) ℝ) = 1 - V (tIdx p q M k) := by
  simp

theorem eqAtom_mem (p q M k : ℕ) (l : Fin k) (a : Fin p) :
    eqAtom p q M k l a ∈ eqAtoms p q M k := by
  rw [eqAtoms]
  exact List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
    List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩⟩

theorem lvlAtom_mem (p q M k : ℕ) (j : Fin q) (l : Fin k) :
    lvlAtom p q M k j l ∈ posAtoms p q M k j := by
  rw [posAtoms]
  exact List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩))

theorem ordAtom_mem (p q M k : ℕ) (j : Fin q) (l l' : Fin k) (h : l < l') :
    ordAtom p q M k j l l' ∈ posAtoms p q M k j := by
  rw [posAtoms]
  refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
  rw [ordAtoms]
  exact List.mem_map.mpr ⟨(l, l'),
    List.mem_filter.mpr ⟨List.mem_product.mpr ⟨List.mem_finRange l, List.mem_finRange l'⟩,
      by simpa using h⟩, rfl⟩

theorem tAtom_mem (p q M k : ℕ) (j : Fin q) :
    (1 - MvPolynomial.X (tIdx p q M k) : MvPolynomial (Fin (levDim p q M k)) ℝ) ∈
      posAtoms p q M k j := List.mem_cons_self ..

/-- Every equation atom vanishes, given the base conditions. -/
theorem eqAtoms_eval_zero (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ)
    (h : ∀ (l : Fin k) (a : Fin p),
      (rdBlk p q M k V l) (Fin.castAdd q a) = (Fin.init (rdY p q M k V)) a) :
    ∀ Q ∈ eqAtoms p q M k, MvPolynomial.eval V Q = 0 := by
  intro Q hQ
  rw [eqAtoms, List.mem_flatMap] at hQ
  obtain ⟨l, -, hQ⟩ := hQ
  rw [List.mem_map] at hQ
  obtain ⟨a, -, rfl⟩ := hQ
  rw [eqAtom_eval p q M k V l a, sub_eq_zero]
  exact (h l a).trans (init_rdY_apply p q M k V a)

/-- Every inequality atom is positive, given the level and order conditions. -/
theorem posAtoms_eval_pos (p q M k : ℕ) (j : Fin q) (V : Fin (levDim p q M k) → ℝ)
    (hlt : (rdY p q M k V) (Fin.last p) < 1)
    (hlvl : ∀ l : Fin k, (rdBlk p q M k V l) (Fin.natAdd p j) < (rdY p q M k V) (Fin.last p))
    (hord : ∀ l l' : Fin k, l < l' →
      (rdBlk p q M k V l) (Fin.natAdd p j) < (rdBlk p q M k V l') (Fin.natAdd p j)) :
    ∀ Q ∈ posAtoms p q M k j, 0 < MvPolynomial.eval V Q := by
  intro Q hQ
  rw [posAtoms] at hQ
  rcases List.mem_cons.mp hQ with rfl | hQ
  · rw [tAtom_eval p q M k j V, ← rdY_last p q M k V]
    linarith
  · rw [List.mem_append] at hQ
    rcases hQ with hQ | hQ
    · rw [lvlAtoms] at hQ
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hQ
      rw [lvlAtom_eval p q M k j V l, ← rdY_last p q M k V,
        ← rdBlk_apply p q M k V l (Fin.natAdd p j)]
      linarith [hlvl l]
    · rw [ordAtoms] at hQ
      obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hQ
      rw [List.mem_filter] at hpr
      have hpr' : pr.1 < pr.2 := by simpa using hpr.2
      rw [ordAtom_eval p q M k j V pr.1 pr.2,
        ← rdBlk_apply p q M k V pr.1 (Fin.natAdd p j),
        ← rdBlk_apply p q M k V pr.2 (Fin.natAdd p j)]
      linarith [hord pr.1 pr.2 hpr']

/-! ## The point set of the presentation -/

/-- The point set of `aboveLevelZ`, in coordinates. -/
theorem aboveLevelZ_mem_iff (p q M k : ℕ) (j : Fin q) (X : SemiPf (p + q))
    (XC : SemiPf (p + M)) (V : Fin (levDim p q M k) → ℝ) :
    V ∈ (aboveLevelZ p q M k j X XC).set ↔
      V ∈ cubeC (levDim p q M k) ∧
      Fin.append (Fin.init (rdY p q M k V)) (rdW p q M k V) ∈ XC.set ∧
      (∀ l : Fin k, rdBlk p q M k V l ∈ X.set) ∧
      (∀ (l : Fin k) (a : Fin p),
        (rdBlk p q M k V l) (Fin.castAdd q a) = (Fin.init (rdY p q M k V)) a) ∧
      (rdY p q M k V) (Fin.last p) < 1 ∧
      (∀ l : Fin k, (rdBlk p q M k V l) (Fin.natAdd p j) < (rdY p q M k V) (Fin.last p)) ∧
      (∀ l l' : Fin k, l < l' →
        (rdBlk p q M k V l) (Fin.natAdd p j) < (rdBlk p q M k V l') (Fin.natAdd p j)) := by
  constructor
  · intro hV
    rw [aboveLevelZ, Work.WilE7.LevelFibre.addAtoms_set, Set.mem_inter_iff,
      Set.mem_inter_iff] at hV
    obtain ⟨⟨hZ0, heq⟩, hpos⟩ := hV
    rw [Z0, Work.WilE8.Extend.semipf_set_extend (gapInj_injective p q M k)] at hZ0
    obtain ⟨hcube, hW⟩ := hZ0
    rw [Work.WilE7.prodSet XC (fibBlocks X k)] at hW
    obtain ⟨hXC, hB⟩ := hW
    rw [fibBlocks_set X k] at hB
    refine ⟨hcube, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          (1 - MvPolynomial.X (tIdx p q M k) : MvPolynomial (Fin (levDim p q M k)) ℝ))
        (List.mem_map.mpr ⟨_, tAtom_mem p q M k j, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, tAtom_eval p q M k j V] at h0
      rw [rdY_last p q M k V]
      linarith
    · intro l
      have h0 := hpos (Work.WilE7.LevelFibre.eaEmbed (lvlAtom p q M k j l))
        (List.mem_map.mpr ⟨_, lvlAtom_mem p q M k j l, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, lvlAtom_eval p q M k j V l,
        ← rdY_last p q M k V, ← rdBlk_apply p q M k V l (Fin.natAdd p j)] at h0
      linarith
    · intro l l' hl
      have h0 := hpos (Work.WilE7.LevelFibre.eaEmbed (ordAtom p q M k j l l'))
        (List.mem_map.mpr ⟨_, ordAtom_mem p q M k j l l' hl, rfl⟩)
      rw [Work.WilE7.LevelFibre.eaEval_eaEmbed, ordAtom_eval p q M k j V l l',
        ← rdBlk_apply p q M k V l (Fin.natAdd p j),
        ← rdBlk_apply p q M k V l' (Fin.natAdd p j)] at h0
      linarith
  · rintro ⟨hcube, hXC, hblk, heq, hlt, hlvl, hord⟩
    rw [aboveLevelZ, Work.WilE7.LevelFibre.addAtoms_set, Set.mem_inter_iff, Set.mem_inter_iff]
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
      exact posAtoms_eval_pos p q M k j V hlt hlvl hord Q hQ

/-! ## The set `Y` and the point glued from `y`, `w`, `z` -/

/-- The set `Y` of `aboveLevel_subPf`, under its own name. -/
def aboveLevelSet (p q M k : ℕ) (j : Fin q) (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    Set (Fin (p + 1) → ℝ) :=
  {y : Fin (p + 1) → ℝ |
    y ∈ cubeC (p + 1) ∧
    (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
    y (Fin.last p) < 1 ∧
    ∃ z : Fin k → (Fin (p + q) → ℝ),
      (∀ l, z l ∈ X.set) ∧
      (∀ l, projFirst p q (z l) = Fin.init y) ∧
      (∀ l l', l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
      (∀ l, (z l) (Fin.natAdd p j) < y (Fin.last p))}

/-- The point of the large space glued from a point `y`, a witness `w` and points `z l`. -/
def glue (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) : Fin (levDim p q M k) → ℝ :=
  Fin.append y (Fin.append w (blocksOf k z))

theorem rdY_glue (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) : rdY p q M k (glue p q M k y w z) = y :=
  projFirst_append y _

theorem rdW_glue (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) : rdW p q M k (glue p q M k y w z) = w := by
  rw [rdW, glue, projSnd_append]
  exact projFirst_append w _

theorem rdBlkPt_glue (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) :
    rdBlkPt p q M k (glue p q M k y w z) = blocksOf k z := by
  rw [rdBlkPt, glue, projSnd_append]
  exact projSnd_append w _

theorem rdBlk_glue (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) (l : Fin k) :
    rdBlk p q M k (glue p q M k y w z) l = z l := by
  funext i
  show (Fin.append y (Fin.append w (blocksOf k z))) (blkD p q M k l i) = z l i
  rw [blkD_eq, Fin.append_right, Fin.append_right]
  exact (blocksOf_fibBlkIdx z).1 l i

theorem glue_xIdx (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) (a : Fin p) :
    glue p q M k y w z (xIdx p q M k a) = (Fin.init y) a := by
  rw [glue, xIdx_eq, Fin.append_left]
  rfl

theorem glue_tIdx (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) :
    glue p q M k y w z (tIdx p q M k) = y (Fin.last p) := by
  rw [glue, tIdx_eq, Fin.append_left]

theorem glue_mem_cubeC (p q M k : ℕ) (y : Fin (p + 1) → ℝ) (w : Fin M → ℝ)
    (z : Fin k → Fin (p + q) → ℝ) (hy : y ∈ cubeC (p + 1)) (hw : w ∈ cubeC M)
    (hz : ∀ l, z l ∈ cubeC (p + q)) :
    glue p q M k y w z ∈ cubeC (levDim p q M k) := by
  have hbl : blocksOf k z ∈ cubeC ((p + q) * k) := blocksOf_mem_cube z hz
  show Fin.append y (Fin.append w (blocksOf k z)) ∈ cubeC ((p + 1) + (M + (p + q) * k))
  refine (mem_cubeC_append _ _).mpr ⟨hy, ?_⟩
  exact (mem_cubeC_append _ _).mpr ⟨hw, hbl⟩

/-! ## The target -/

theorem aboveLevel_subPf {p q M k : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (j : Fin q)
    (XC : WilkiesDesign.E.SemiPf (p + M)) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ |
        y ∈ WilkiesDesign.E.cubeC (p + 1) ∧
        (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
        y (Fin.last p) < 1 ∧
        ∃ z : Fin k → (Fin (p + q) → ℝ),
          (∀ l, z l ∈ X.set) ∧
          (∀ l, WilkiesDesign.E.projFirst p q (z l) = Fin.init y) ∧
          (∀ l l', l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
          (∀ l, (z l) (Fin.natAdd p j) < y (Fin.last p))} := by
  change SubPf (p + 1) (aboveLevelSet p q M k j X XC)
  refine ⟨M + (p + q) * k, aboveLevelZ p q M k j X XC, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · -- `Y ⊆ projFirst '' Z.set`
    intro y hy
    obtain ⟨hycube, ⟨w, hw⟩, hylt, z, hzmem, hzbase, hzord, hzlvl⟩ := hy
    have hwcube : w ∈ cubeC M := ((mem_cubeC_append (Fin.init y) w).mp hw.1).2
    refine ⟨glue p q M k y w z, ?_, rdY_glue p q M k y w z⟩
    rw [aboveLevelZ_mem_iff p q M k j X XC]
    refine ⟨glue_mem_cubeC p q M k y w z hycube hwcube fun l => (hzmem l).1,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rdY_glue, rdW_glue]; exact hw
    · intro l; rw [rdBlk_glue]; exact hzmem l
    · intro l a
      rw [rdBlk_glue, init_rdY_apply, glue_xIdx]
      exact congrFun (hzbase l) a
    · rw [rdY_glue]; exact hylt
    · intro l; rw [rdBlk_glue, rdY_glue]; exact hzlvl l
    · intro l l' hl; rw [rdBlk_glue, rdBlk_glue]; exact hzord l l' hl
  · -- `projFirst '' Z.set ⊆ Y`
    rintro y ⟨V, hV, rfl⟩
    change rdY p q M k V ∈ aboveLevelSet p q M k j X XC
    have hV' := (aboveLevelZ_mem_iff p q M k j X XC V).mp hV
    obtain ⟨hcube, hXC, hblk, heq, hlt, hlvl, hord⟩ := hV'
    refine ⟨fun i => hcube _, ⟨rdW p q M k V, hXC⟩, ?_,
      ⟨fun l => rdBlk p q M k V l, ?_, ?_, ?_, ?_⟩⟩
    · rw [rdY_last p q M k V]; exact hlt
    · intro l; exact hblk l
    · intro l
      funext a
      rw [init_rdY_apply]
      exact heq l a
    · intro l l' hl; exact hord l l' hl
    · intro l; rw [rdY_last p q M k V]; exact hlvl l

end Work.WilE7.AboveAux
