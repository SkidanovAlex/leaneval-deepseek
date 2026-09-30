/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Piece
import Submission.Work.Subdivision.Level
import Submission.Work.Subdivision.PieceIso
import Submission.Work.Subdivision.SubDataEq
import Submission.Work.Subdivision.SkelLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The refined filtration maps and the cell-by-cell induction

`PolyCW.levelMap hdd haug n E` is the restriction of the subdivision chain map to
the refined filtrations of `Level.lean`,

`(cellTop P hdd n E).chain ⟶ (sdTop P n E).chain`,

which subsumes both the skeletal restrictions `subdivSkel n` (`E = ∅`, `E = P.faces (n+1)`)
and the intermediate stages of the cell-by-cell refinement.

`PolyCW.cellPiece_hf` is the compatibility of the subdivision with the *pieces*
`cellPiece P hdd n E a ⊆ cellTop n (insert a E)` and `sdPiece P n E a`, which is
the input of the five lemma in the induction step.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

/-- The compatibility of the subdivision with the refined filtration, in the form
needed by `SubData.restrictMap`. -/
noncomputable def levelHf (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (E : Finset P.Cell) :
    ∀ k, cellTopMod P hdd n E k ≤ (sdTopMod P n E k).comap ((subdiv P hdd haug).f k).hom :=
  subdivCpt_mem_top P hdd haug n E

/-- **The subdivision restricted to a refined pair of filtrations.** -/
noncomputable def levelMap (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (E : Finset P.Cell) :
    (cellTop P hdd n E).chain ⟶ (sdTop P n E).chain :=
  (cellTop P hdd n E).restrictMap (sdTop P n E) (subdiv P hdd haug)
    (levelHf P hdd haug n E)

@[simp] theorem levelMap_f (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (E : Finset P.Cell) (k : ℕ) :
    (levelMap P hdd haug n E).f k =
      (cellTop P hdd n E).restrictCptMap (sdTop P n E) (subdiv P hdd haug)
        (levelHf P hdd haug n E) k := rfl

/-! ### The endpoints of the induction -/

/-- At `E = ∅` the refined map is the restriction of the subdivision to the
`n`-skeleta. -/
theorem quasiIso_levelMap_empty_iff (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) :
    QuasiIso (subdivSkel P hdd haug n) ↔ QuasiIso (levelMap P hdd haug n ∅) :=
  SubData.quasiIso_of_sub_data_eq (cellTop P hdd n ∅) (cellSub P hdd n) (sdTop P n ∅)
    (sdSub P n) (cellTop_empty P hdd n).symm (sdTop_empty P n).symm (subdiv P hdd haug)
    (levelHf P hdd haug n ∅) (fun k => subdivCpt_mem P hdd haug n k)

/-- At `E = P.faces (n+1)` the refined map is the restriction of the subdivision
to the `(n+1)`-skeleta. -/
theorem quasiIso_levelMap_faces_iff (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) :
    QuasiIso (subdivSkel P hdd haug (n + 1)) ↔
      QuasiIso (levelMap P hdd haug n (P.faces (n + 1))) :=
  SubData.quasiIso_of_sub_data_eq (cellTop P hdd n (P.faces (n + 1))) (cellSub P hdd (n + 1))
    (sdTop P n (P.faces (n + 1))) (sdSub P (n + 1))
    (cellTop_faces P hdd n).symm (sdTop_faces P n).symm (subdiv P hdd haug)
    (levelHf P hdd haug n (P.faces (n + 1)))
    (fun k => subdivCpt_mem P hdd haug (n + 1) k)

/-! ### The compatibility with the pieces -/

/-- The subdivision carries the cellular piece into the subdivided piece. -/
theorem cellPiece_hf (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) (E : Finset P.Cell)
    (a : P.Cell) (ha : P.dim a = n + 1) :
    ∀ k, (cellPiece P hdd n E a).sub k ≤
      ((sdPiece P n E a).sub k).comap ((levelMap P hdd haug n (insert a E)).f k).hom := by
  intro k x hx
  have hx' : ((x : ↥(cellTopMod P hdd n (insert a E) k)) : (cellChain P hdd).X k) ∈
    cellTopMod P hdd n E k := hx
  have hmem : subdivLM P k (((x : ↥(cellTopMod P hdd n (insert a E) k)) :
      (cellChain P hdd).X k)) ∈ sdTopMod P n E k := subdivCpt_mem_top P hdd haug n E k hx'
  refine Submodule.mem_comap.mpr ?_
  show ((((cellTop P hdd n (insert a E)).restrictCptMap (sdTop P n (insert a E))
      (subdiv P hdd haug) (levelHf P hdd haug n (insert a E)) k) x :
        ↥(sdTopMod P n (insert a E) k)) : (sdChain P).X k) ∈ sdTopMod P n E k
  rw [show (((cellTop P hdd n (insert a E)).restrictCptMap (sdTop P n (insert a E))
      (subdiv P hdd haug) (levelHf P hdd haug n (insert a E)) k) x :
        ↥(sdTopMod P n (insert a E) k)) =
      (⟨subdivLM P k (((x : ↥(cellTopMod P hdd n (insert a E) k)) : (cellChain P hdd).X k)),
        subdivCpt_mem_top P hdd haug n (insert a E) k x.2⟩ :
        ↥(sdTopMod P n (insert a E) k)) from rfl]
  exact hmem

end PolyCW

end

end Work.Subdivision
