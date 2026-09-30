import Mathlib
import Submission.Work.SymQuot.DivOf.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- The stabilizer `S_{n-1} ⊆ S_n` of the last coordinate is isomorphic, via restriction to the
complement of that coordinate, to the full symmetric group on the `n - 1` remaining coordinates. -/
theorem card_symStab (n : ℕ) [NeZero n] [Fintype ↥(Work.SymQuot.symStab n)] :
    Fintype.card ↥(Work.SymQuot.symStab n) = (n - 1).factorial := by
  classical
  rw [Fintype.card_eq_nat_card]
  have e : ↥(Work.SymQuot.symStab n) ≃
      Equiv.Perm {a : Fin n // a ≠ Work.SymQuot.lastIdx n} :=
    (Equiv.subtypeEquivRight (fun f => by
      constructor
      · intro hf a ha
        rw [Work.SymQuot.mem_symStab] at hf
        rw [not_not] at ha
        subst ha
        exact hf
      · intro hf
        rw [Work.SymQuot.mem_symStab]
        exact hf (Work.SymQuot.lastIdx n) (by simp))).trans
      (Equiv.Perm.subtypeEquivSubtypePerm
        (fun a : Fin n => a ≠ Work.SymQuot.lastIdx n)).symm
  rw [Nat.card_congr e, Nat.card_perm]
  congr 1
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun a : Fin n => a = Work.SymQuot.lastIdx n)]
  rw [Fintype.card_fin, Fintype.card_subtype_eq]

end Work.SymQuot.DivOf
