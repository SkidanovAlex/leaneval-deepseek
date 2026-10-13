/-
  `Work.WilE7.coreLT_succ.SwapEquiv0`: the coordinate equivalence between the two ambient splits
  `ℝ^{(n+1)+m}` and `ℝ^{n+(m+1)}`, lifted through the `0 + ·` bookkeeping of `Stratum 0 ·`.

  `Work.WilE7.CoreStep.swapEquiv n m` is the "vertical swap" of `ProjTopTransfer.lean`: it fixes
  the `n` base coordinates `0, …, n-1` and exchanges the two possible vertical coordinates `n`
  and `n + m`.  An absolute stratum lives in `ℝ^{0+N}` (`N = (n+1)+m`), so a coordinate
  equivalence of the *unlifted* spaces has to be transported along the (value preserving)
  identifications `Fin (0+N) ≃ Fin N`; that is `swapEquiv0`.

  The two facts about it that the `(n+1) → (n, m+1)` transfer needs are

  * `swapEquiv0_symm_cast`: `(swapEquiv0 n m).symm` commutes with the two value preserving
    identifications `Fin N → Fin (0+N)` / `Fin N' → Fin (0+N')`;
  * `projTop_absPt_swapEquiv0`: pulled back along `swapEquiv0`, the `(n+1)`-projection
    `projFirst (n+1) m` of the `((n+1)+m)`-split becomes the projection `projTop n m` of the
    `(n, m+1)`-split (which keeps the first `n` coordinates and the *last* fibre coordinate).

  Everything here is proved; the file is imported by both the assembly
  (`stratReindex_projTop.lean`) and the lemmas delegated on top of it.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.ProjTopTransfer
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.FibreEndDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E

/-- The coordinate equivalence between the ambient spaces of the two splits, lifted to the
`Stratum 0 ·` bookkeeping: `Fin (0 + ((n+1)+m)) ≃ Fin (0 + (n+(m+1)))`.  It is the identity on
the base coordinates `0, …, n-1` and exchanges the vertical coordinates `n` and `n+m`. -/
def swapEquiv0 (n m : ℕ) : Fin (0 + ((n + 1) + m)) ≃ Fin (0 + (n + (m + 1))) :=
  (Work.WilE7.finEquiv (Nat.zero_add ((n + 1) + m))).trans
    ((Work.WilE7.CoreStep.swapEquiv n m).trans
      (Work.WilE7.finEquiv (Nat.zero_add (n + (m + 1))).symm))

/-- The value of `swapEquiv0` is the value of `swapEquiv` on the corresponding (unlifted)
index. -/
theorem swapEquiv0_val (n m : ℕ) (i : Fin (0 + ((n + 1) + m))) :
    (swapEquiv0 n m i).val
      = (Work.WilE7.CoreStep.swapEquiv n m (⟨i.val, by omega⟩ : Fin ((n + 1) + m))).val :=
  rfl

/-- The value of the inverse of `swapEquiv0` is the value of the inverse of `swapEquiv`. -/
theorem swapEquiv0_symm_val (n m : ℕ) (j : Fin (0 + (n + (m + 1)))) :
    ((swapEquiv0 n m).symm j).val
      = ((Work.WilE7.CoreStep.swapEquiv n m).symm (⟨j.val, by omega⟩ : Fin (n + (m + 1)))).val :=
  rfl

/-- **The key cast identity.**  `(swapEquiv0 n m).symm` commutes with the value preserving
identifications of `Fin N` with `Fin (0+N)` and of `Fin N'` with `Fin (0+N')`
(`N = (n+1)+m`, `N' = n+(m+1)`). -/
theorem swapEquiv0_symm_cast (n m : ℕ) (j : Fin (n + (m + 1))) :
    (swapEquiv0 n m).symm (Fin.cast (Nat.zero_add (n + (m + 1))).symm j)
      = Fin.cast (Nat.zero_add ((n + 1) + m)).symm
          ((Work.WilE7.CoreStep.swapEquiv n m).symm j) := by
  apply Fin.ext
  have h : (Fin.cast (Nat.zero_add (n + (m + 1))).symm j)
      = (⟨j.val, by omega⟩ : Fin (0 + (n + (m + 1)))) := Fin.ext rfl
  rw [h]
  rfl

/-- `π_{n+1}` of an absolute stratum point is the base projection of its `Fin N`-version. -/
theorem projFirst_absPt_eq_basePrLin (n m : ℕ) (z : Fin (0 + ((n + 1) + m)) → ℝ) :
    WilkiesDesign.E.projFirst (n + 1) m (Work.WilE7.MainDesign.absPt z)
      = Work.WilE7.MainDesign.basePrLin (n + 1) m z := by
  funext i
  simp only [WilkiesDesign.E.projFirst, Work.WilE7.MainDesign.absPt,
    Work.WilE7.MainDesign.basePrLin, LinearMap.funLeft_apply]

/-- **The projection transfer on the level of points.**  Pulling an absolute point back along
`swapEquiv0` and projecting with `projTop` (the `(n, m+1)`-projection) is the same as projecting
the original point with `projFirst (n+1) m` (the `(n+1)`-projection of the `((n+1)+m)`-split). -/
theorem projTop_absPt_swapEquiv0 (n m : ℕ) (z : Fin (0 + ((n + 1) + m)) → ℝ) :
    Work.WilE7.CoreStep.projTop n m
      (Work.WilE7.MainDesign.absPt (fun i => z ((swapEquiv0 n m).symm i)))
      = Work.WilE7.MainDesign.basePrLin (n + 1) m z := by
  have h1 : Work.WilE7.MainDesign.absPt (fun i => z ((swapEquiv0 n m).symm i))
      = (fun j => Work.WilE7.MainDesign.absPt z
          ((Work.WilE7.CoreStep.swapEquiv n m).symm j)) := by
    funext j
    simp only [Work.WilE7.MainDesign.absPt]
    rw [swapEquiv0_symm_cast]
  rw [h1, Work.WilE7.CoreStep.projTop_comp_tau]
  exact projFirst_absPt_eq_basePrLin n m z

/-- **The projection transfer for the linear maps.**  The linear map `projTopLin n m` of the
`(n, m+1)`-split, composed with the linear identification `absPtLin (n+(m+1))`, is the base
projection `basePrLin (n+1) m` of the `((n+1)+m)`-split after pulling back along `swapEquiv0`. -/
theorem projTopLin_absPtLin_swapEquiv0 (n m : ℕ) (v : Fin (0 + ((n + 1) + m)) → ℝ) :
    (Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))
        (fun j => v ((swapEquiv0 n m).symm j))
      = Work.WilE7.MainDesign.basePrLin (n + 1) m v := by
  rw [LinearMap.comp_apply, Work.WilE7.CoreStep.projTopLin_apply,
    Work.WilE7.CoreStep.absPtLin_apply]
  exact projTop_absPt_swapEquiv0 n m v

end Work.WilE7.coreLT_succ
