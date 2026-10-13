/-
  `Work.WilE7.CoreStep.ProjTopTransfer`: moving the `(n+1)`-projection of a piece in the
  `((n+1)+m)`-split to the `projTop` of the `(n+(m+1))`-split (the "vertSwap-normalised" picture
  in which the vertical coordinate that `π_{n+1}` keeps is the **last** fibre coordinate).

  The level-`(n+1)` pieces produced by `Work.WilE7.CoreStep.piFamily` / `piFamilyTop` live in
  `Stratum 0 ((n+1)+m)`, where `π_{n+1}` is `projFirst (n+1) m`: the base together with the
  **first** fibre coordinate.  All the cell lemmas
  (`Work.WilE7.SheetData.multiStrata_cellsX`, `faceCell_star`, `cylOpenBand`, …) work in the
  `(n, m+1)`-split where the vertical coordinate is the **last** fibre coordinate and their
  `(n+1)`-projection is `Work.WilE7.CoreStep.projTop n m = (π_n, last fibre coordinate)`.

  The bridge is the coordinate equivalence `swapEquiv n m : Fin ((n+1)+m) ≃ Fin (n+(m+1))`,
  which is the identity on the base coordinates `0, …, n-1` and exchanges the positions `n` and
  `n+m` (the two possible "vertical" coordinates).
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.VertSwap
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The value-preserving reindexing `Fin ((n+1)+m) ≃ Fin (n+(m+1))` followed by the transposition
`vertSwap n m` of the first and last fibre coordinates of the `(n, m+1)`-split. -/
def swapEquiv (n m : ℕ) : Fin ((n + 1) + m) ≃ Fin (n + (m + 1)) :=
  (Work.WilE7.finEquiv (by omega : (n + 1) + m = n + (m + 1))).trans (Work.WilE7.vertSwap n m)

/-- The transposition `vertSwap n m` is an involution. -/
theorem vertSwap_apply_apply (n m : ℕ) (x : Fin (n + (m + 1))) :
    Work.WilE7.vertSwap n m (Work.WilE7.vertSwap n m x) = x := by
  rw [Work.WilE7.vertSwap]
  exact Equiv.swap_apply_self _ _ x

/-- `swapEquiv n m` fixes the base coordinates `0, …, n-1`, as an identity of `Fin (n+(m+1))`. -/
theorem swapEquiv_apply_of_lt {n m : ℕ} (i : Fin ((n + 1) + m)) (h : (i : ℕ) < n) :
    swapEquiv n m i = (⟨i.val, by omega⟩ : Fin (n + (m + 1))) := by
  show (Work.WilE7.vertSwap n m
      (Work.WilE7.finEquiv (by omega : (n + 1) + m = n + (m + 1)) i) : Fin (n + (m + 1)))
    = ⟨i.val, by omega⟩
  rw [show Work.WilE7.finEquiv (by omega : (n + 1) + m = n + (m + 1)) i
      = (⟨i.val, by omega⟩ : Fin (n + (m + 1))) from
    Fin.ext (by rw [Work.WilE7.finEquiv_apply_val])]
  rw [Work.WilE7.vertSwap]
  exact Equiv.swap_apply_of_ne_of_ne
    (fun hh => by have hc := congrArg Fin.val hh; simp only [Fin.val_mk] at hc; omega)
    (fun hh => by have hc := congrArg Fin.val hh; simp only [Fin.val_mk] at hc; omega)

/-- `swapEquiv n m` sends the vertical coordinate `n` to the last fibre coordinate `n+m`. -/
theorem swapEquiv_apply_vertical (n m : ℕ) :
    swapEquiv n m (⟨n, by omega⟩ : Fin ((n + 1) + m))
      = (⟨n + m, by omega⟩ : Fin (n + (m + 1))) := by
  show (Work.WilE7.vertSwap n m
      (Work.WilE7.finEquiv (by omega : (n + 1) + m = n + (m + 1)) ⟨n, by omega⟩)
      : Fin (n + (m + 1))) = ⟨n + m, by omega⟩
  rw [show Work.WilE7.finEquiv (by omega : (n + 1) + m = n + (m + 1)) ⟨n, by omega⟩
      = (⟨n, by omega⟩ : Fin (n + (m + 1))) from
    Fin.ext (by rw [Work.WilE7.finEquiv_apply_val])]
  rw [Work.WilE7.vertSwap]
  exact Equiv.swap_apply_left _ _

/-- `(swapEquiv n m).symm` fixes the base coordinates. -/
theorem swapEquiv_symm_base {n m : ℕ} (i : Fin ((n + 1) + m)) (h : (i : ℕ) < n) :
    (swapEquiv n m).symm ((⟨i.val, by omega⟩ : Fin (n + (m + 1))))
      = (⟨i.val, by omega⟩ : Fin ((n + 1) + m)) :=
  (Equiv.symm_apply_eq (swapEquiv n m)).mpr (by simp only [swapEquiv_apply_of_lt i h])

/-- `(swapEquiv n m).symm` sends the last fibre coordinate `n+m` to the vertical coordinate `n`. -/
theorem swapEquiv_symm_last (n m : ℕ) :
    (swapEquiv n m).symm ((⟨n + m, by omega⟩ : Fin (n + (m + 1))))
      = (⟨n, by omega⟩ : Fin ((n + 1) + m)) :=
  (Equiv.symm_apply_eq (swapEquiv n m)).mpr (by simp only [swapEquiv_apply_vertical])

/-- **The key function identity.**  `projTop` of the `σ⁻¹`-pullback of `z` is the `π_{n+1}` of
`z`. -/
theorem projTop_comp_tau (n m : ℕ) (z : Fin ((n + 1) + m) → ℝ) :
    projTop n m (fun i => z ((swapEquiv n m).symm i)) = projFirst (n + 1) m z := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [projTop_last]
    simp only [projFirst, projSnd]
    congr 1
    rw [show Fin.natAdd n (Fin.last m) = (⟨n + m, by omega⟩ : Fin (n + (m + 1))) from rfl]
    exact swapEquiv_symm_last n m
  · intro i
    rw [projTop_castSucc]
    simp only [projFirst]
    congr 1
    exact swapEquiv_symm_base (Fin.castAdd m (Fin.castSucc i))
      (by simp only [Fin.val_castAdd, Fin.val_castSucc]; exact i.isLt)

/-- The `σ`-pushforward of the `σ⁻¹`-pullback is the identity. -/
theorem tau_symm (n m : ℕ) (z : Fin ((n + 1) + m) → ℝ) :
    (fun i => (fun j => z ((swapEquiv n m).symm j)) (swapEquiv n m i)) = z := by
  funext i
  exact congrArg z (Equiv.symm_apply_apply (swapEquiv n m) i)

/-- **The coordinate transfer.**  Reindexing a semi-Pfaffian set in the `((n+1)+m)`-split along
`swapEquiv n m` turns the `(n+1)`-projection `projFirst (n+1) m` into the `projTop n m` of the
`(n, m+1)`-split. -/
theorem projTop_transfer (n m : ℕ) (X : WilkiesDesign.E.SemiPf ((n + 1) + m)) :
    WilkiesDesign.E.projFirst (n + 1) m '' X.set
      = projTop n m '' (Work.WilE7.SemiPf.reindex (swapEquiv n m) X).set := by
  have hset : (Work.WilE7.SemiPf.reindex (swapEquiv n m) X).set
      = (fun z i => z ((swapEquiv n m).symm i)) '' X.set := by
    rw [Work.WilE7.sp_reindex_set]
    ext y
    constructor
    · intro hy
      rw [Set.mem_setOf_eq] at hy
      refine ⟨fun i => y (swapEquiv n m i), hy, ?_⟩
      funext i
      exact congrArg y (Equiv.apply_symm_apply (swapEquiv n m) i)
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_setOf_eq, tau_symm n m z]
      exact hz
  rw [hset, Set.image_image]
  exact Set.image_congr fun z _ => (projTop_comp_tau n m z).symm

end Work.WilE7.CoreStep
