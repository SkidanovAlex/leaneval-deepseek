/-
  Area E7: `Work.WilE7.LevelFibre.levelFibre_subPf`.

  The layout and the ambient semi-Pfaffian set `lfW2` used here are defined in
  `Submission/Work/WilE7/LevelFibre/lfDefs.lean`; the point set of `lfW2` is characterised in
  `Work.WilE7.LevelFibre.lf_mem_W2`, and the two coordinate facts about the transposition `lfE`
  in `Work.WilE7.LevelFibre.lfE_xIdx` / `lfE_lvIdx`.

  The proof has two halves:
  * `lf_proj_subset`: a point of the projection gives the witnesses (the `XC`-witness is read off
    the `XC`-coordinates of `U`, the blocks are read off the block coordinates);
  * `lf_proj_supset`: conversely, from the witnesses `w₀`, `z` one builds the ambient point
    `U = Fin.append (Fin.append (Fin.init y) w₀) (lfFlat z)` and puts `Z := U ∘ e⁻¹`; the
    transposition `e` has brought the level coordinate of block `i` to position `p`, so
    `projFirst (p+1) … Z = y`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.LevelFibre.Defs
import Submission.Work.WilE7.LevelFibre.lfDefs
import Submission.Work.WilE7.LevelFibre.lf_mem_W2
import Submission.Work.WilE7.LevelFibre.lfE_xIdx
import Submission.Work.WilE7.LevelFibre.lfE_lvIdx
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.projFirst_fiberClosure

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.LevelFibre

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The two inclusions -/

theorem lf_proj_subset {p q M k : ℕ} (j : Fin q) (i : Fin k)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M))
    (e : Fin (lfD p q M k) ≃ Fin ((p + 1) + lfM p q M k))
    (hx : ∀ a : Fin p, e (lfXIdx a) = Fin.castAdd (lfM p q M k) (Fin.castSucc a))
    (ht : e (lfLvIdx j i) = Fin.castAdd (lfM p q M k) (Fin.last p)) :
    projFirst (p + 1) (lfM p q M k) '' (SemiPf.reindex e (lfW2 j X XC)).set ⊆ lfY j i X XC := by
  rintro y ⟨Z, hZ, hZy⟩
  have hmem : (fun d => Z (e d)) ∈ (lfW2 j X XC).set := by
    have h := hZ
    rw [reindex_set] at h
    exact h
  set U : Fin (lfD p q M k) → ℝ := fun d => Z (e d) with hUdef
  have hU : U ∈ (lfW2 j X XC).set := hmem
  rw [lf_mem_W2] at hU
  obtain ⟨hXC, hblk, heq, hlt⟩ := hU
  have hyx : ∀ a : Fin p, Z (Fin.castAdd (lfM p q M k) (Fin.castSucc a)) = y (Fin.castSucc a) :=
    fun a => congrFun hZy (Fin.castSucc a)
  have hyt : Z (Fin.castAdd (lfM p q M k) (Fin.last p)) = y (Fin.last p) :=
    congrFun hZy (Fin.last p)
  have Ux : ∀ a : Fin p, U (lfXIdx a) = y (Fin.castSucc a) := by
    intro a
    show Z (e (lfXIdx a)) = y (Fin.castSucc a)
    rw [hx a]
    exact hyx a
  have Ut : U (lfLvIdx j i) = y (Fin.last p) := by
    show Z (e (lfLvIdx j i)) = y (Fin.last p)
    rw [ht]
    exact hyt
  refine ⟨⟨fun t : Fin M => U (lfWIdx t), ?_⟩,
    fun l : Fin k => blk (projSnd (p + M) ((p + q) * k) U) l, ?_, ?_, ?_, ?_⟩
  · have hEq : Fin.append (Fin.init y) (fun t : Fin M => U (lfWIdx t)) =
        projFirst (p + M) ((p + q) * k) U := by
      funext a
      refine Fin.addCases (fun ā => ?_) (fun t => ?_) a
      · show Fin.append (Fin.init y) (fun t : Fin M => U (lfWIdx t)) (Fin.castAdd M ā) =
          U (lfXIdx ā)
        rw [Fin.append_left]
        show Fin.init y ā = U (lfXIdx ā)
        rw [Ux ā]
        rfl
      · show Fin.append (Fin.init y) (fun t : Fin M => U (lfWIdx t)) (Fin.natAdd p t) =
          U (lfWIdx t)
        rw [Fin.append_right]
    rw [hEq]
    exact hXC
  · intro l
    exact hblk l
  · intro l
    funext a
    show blk (projSnd (p + M) ((p + q) * k) U) l (Fin.castAdd q a) = Fin.init y a
    rw [show blk (projSnd (p + M) ((p + q) * k) U) l (Fin.castAdd q a) =
        U (lfBIdx l (Fin.castAdd q a)) from rfl, heq l a]
    show U (lfXIdx a) = y (Fin.castSucc a)
    exact Ux a
  · intro l l' hll
    show blk (projSnd (p + M) ((p + q) * k) U) l (Fin.natAdd p j) <
      blk (projSnd (p + M) ((p + q) * k) U) l' (Fin.natAdd p j)
    rw [show blk (projSnd (p + M) ((p + q) * k) U) l (Fin.natAdd p j) =
        U (lfLvIdx j l) from rfl,
      show blk (projSnd (p + M) ((p + q) * k) U) l' (Fin.natAdd p j) =
        U (lfLvIdx j l') from rfl]
    exact hlt l l' hll
  · show blk (projSnd (p + M) ((p + q) * k) U) i (Fin.natAdd p j) = y (Fin.last p)
    rw [show blk (projSnd (p + M) ((p + q) * k) U) i (Fin.natAdd p j) =
        U (lfLvIdx j i) from rfl]
    exact Ut

theorem lf_proj_supset {p q M k : ℕ} (j : Fin q) (i : Fin k)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M)) (hN : 0 < p + q)
    (e : Fin (lfD p q M k) ≃ Fin ((p + 1) + lfM p q M k))
    (hx : ∀ a : Fin p, e (lfXIdx a) = Fin.castAdd (lfM p q M k) (Fin.castSucc a))
    (ht : e (lfLvIdx j i) = Fin.castAdd (lfM p q M k) (Fin.last p)) :
    lfY j i X XC ⊆ projFirst (p + 1) (lfM p q M k) '' (SemiPf.reindex e (lfW2 j X XC)).set := by
  intro y hy
  obtain ⟨⟨w₀, hw₀⟩, z, hzmem, hzproj, hzmono, hzpin⟩ := hy
  set Zxw : Fin (p + M) → ℝ := Fin.append (Fin.init y) w₀ with hZxw
  set Zblk : Fin ((p + q) * k) → ℝ := lfFlat hN z with hZblk
  set U : Fin (lfD p q M k) → ℝ := Fin.append Zxw Zblk with hUdef
  have Ux : ∀ a : Fin p, U (lfXIdx a) = y (Fin.castSucc a) := by
    intro a
    show Fin.append Zxw Zblk (Fin.castAdd ((p + q) * k) (Fin.castAdd M a)) = y (Fin.castSucc a)
    rw [Fin.append_left, hZxw, Fin.append_left]
    rfl
  have Ublk : ∀ (l : Fin k) (c : Fin (p + q)), U (lfBIdx l c) = z l c := by
    intro l c
    show Fin.append Zxw Zblk (Fin.natAdd (p + M) (blkIdx (p + q) k l c)) = z l c
    rw [Fin.append_right, hZblk]
    exact lfFlat_blkIdx hN z l c
  have hUmem : U ∈ (lfW2 j X XC).set := by
    rw [lf_mem_W2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show projFirst (p + M) ((p + q) * k) U = Zxw from by
        rw [hUdef]
        exact projFirst_append Zxw Zblk]
      rw [hZxw]
      exact hw₀
    · intro l
      rw [show blk (projSnd (p + M) ((p + q) * k) U) l = z l from by
        funext c
        exact Ublk l c]
      exact hzmem l
    · intro l a
      rw [Ublk l (Fin.castAdd q a), Ux a]
      exact congrFun (hzproj l) a
    · intro l l' hll
      show U (lfBIdx l (Fin.natAdd p j)) < U (lfBIdx l' (Fin.natAdd p j))
      rw [Ublk l (Fin.natAdd p j), Ublk l' (Fin.natAdd p j)]
      exact hzmono l l' hll
  set Z : Fin ((p + 1) + lfM p q M k) → ℝ := fun a => U (e.symm a) with hZdef
  have Zx : ∀ a : Fin p, Z (Fin.castAdd (lfM p q M k) (Fin.castSucc a)) = y (Fin.castSucc a) := by
    intro a
    have hs : e.symm (Fin.castAdd (lfM p q M k) (Fin.castSucc a)) = lfXIdx a := by
      rw [Equiv.symm_apply_eq, hx a]
    show U (e.symm (Fin.castAdd (lfM p q M k) (Fin.castSucc a))) = y (Fin.castSucc a)
    rw [hs, Ux a]
  have Zt : Z (Fin.castAdd (lfM p q M k) (Fin.last p)) = y (Fin.last p) := by
    have hs : e.symm (Fin.castAdd (lfM p q M k) (Fin.last p)) = lfLvIdx j i := by
      rw [Equiv.symm_apply_eq, ht]
    show U (e.symm (Fin.castAdd (lfM p q M k) (Fin.last p))) = y (Fin.last p)
    rw [hs]
    show U (lfBIdx i (Fin.natAdd p j)) = y (Fin.last p)
    rw [Ublk i (Fin.natAdd p j), hzpin]
  refine ⟨Z, ?_, ?_⟩
  · rw [reindex_set]
    show (fun d => Z (e d)) ∈ (lfW2 j X XC).set
    have hZU : (fun d => Z (e d)) = U := by
      funext d
      show U (e.symm (e d)) = U d
      rw [Equiv.symm_apply_apply]
    rw [hZU]
    exact hUmem
  · funext b
    rcases Fin.eq_castSucc_or_eq_last b with ⟨ā, rfl⟩ | rfl
    · show Z (Fin.castAdd (lfM p q M k) (Fin.castSucc ā)) = y (Fin.castSucc ā)
      exact Zx ā
    · show Z (Fin.castAdd (lfM p q M k) (Fin.last p)) = y (Fin.last p)
      exact Zt

/-! ## The theorem -/

theorem levelFibre_subPf {p q M k : ℕ} (j : Fin q) (i : Fin k)
    (X : WilkiesDesign.E.SemiPf (p + q)) (XC : WilkiesDesign.E.SemiPf (p + M)) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ |
        (∃ w : Fin M → ℝ, Fin.append (Fin.init y) w ∈ XC.set) ∧
        ∃ z : Fin k → (Fin (p + q) → ℝ),
          (∀ l : Fin k, z l ∈ X.set) ∧
          (∀ l : Fin k, WilkiesDesign.E.projFirst p q (z l) = Fin.init y) ∧
          (∀ l l' : Fin k, l < l' → (z l) (Fin.natAdd p j) < (z l') (Fin.natAdd p j)) ∧
          (z i) (Fin.natAdd p j) = y (Fin.last p)} := by
  by_cases hk : k = 0
  · subst hk
    exact Fin.elim0 i
  by_cases hq : q = 0
  · subst hq
    exact Fin.elim0 j
  have hk1 : 1 ≤ k := by omega
  have hN : 0 < p + q := by
    have : 1 ≤ p + q := by omega
    omega
  have hNk : 1 ≤ (p + q) * k := Nat.mul_le_mul hN hk1
  refine ⟨lfM p q M k, lfFinal hNk j i X XC, ?_⟩
  have hx : ∀ a : Fin p,
      lfE hNk j i (lfD_eq_add p q M k hNk) (lfXIdx a) =
        Fin.castAdd (lfM p q M k) (Fin.castSucc a) :=
    fun a => lfE_xIdx hNk j i (lfD_eq_add p q M k hNk) a
  have ht : lfE hNk j i (lfD_eq_add p q M k hNk) (lfLvIdx j i) =
      Fin.castAdd (lfM p q M k) (Fin.last p) :=
    lfE_lvIdx hNk j i (lfD_eq_add p q M k hNk)
  show lfY j i X XC = projFirst (p + 1) (lfM p q M k) ''
    (SemiPf.reindex (lfE hNk j i (lfD_eq_add p q M k hNk)) (lfW2 j X XC)).set
  exact Set.Subset.antisymm (lf_proj_supset j i X XC hN _ hx ht)
    (lf_proj_subset j i X XC _ hx ht)

end Work.WilE7.LevelFibre
