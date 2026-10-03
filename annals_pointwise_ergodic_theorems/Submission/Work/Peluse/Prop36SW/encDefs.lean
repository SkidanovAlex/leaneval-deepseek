import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The canonical encoding of `D.Idx a` into `Fin n → ℤ`

`PeluseLadderA` (and hence the whole §5 chain, see `NOTES_prop36SW_of_ladderA_SESSION6.md`) has
parameter type `Fin n → ℤ`, while the data of the paper live on `D.Idx a = (i : Fin a) → D.S i → ℤ`.
This module provides the canonical, **data-independent** coordinate enumeration
`encD D a : D.Idx a → (Fin (nD D a) → ℤ)`, where `nD D a := Fintype.card (Σ i : Fin a, D.S i)`, and
its inverse `decD D a`.  The terms depend on `D` and `a` only — never on the instance data — which
is what keeps the ladder's constants data-independent.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- The number of coordinates of the level-`a` parameter family. -/
def nD (D : IdxDatum) (a : ℕ) : ℕ := Fintype.card (Σ i : Fin a, D.S i)

/-- The canonical coordinate enumeration of `D.Idx a` by `Fin (nD D a)`. -/
def encEquiv (D : IdxDatum) (a : ℕ) : D.Idx a ≃ (Fin (nD D a) → ℤ) :=
  (Equiv.piCurry (fun _ _ => ℤ)).symm.trans
    (Equiv.arrowCongr (Fintype.equivFin (Σ i : Fin a, D.S i)) (Equiv.refl ℤ))

/-- The canonical encoding of a parameter family as a flat parameter. -/
def encD (D : IdxDatum) (a : ℕ) : D.Idx a → (Fin (nD D a) → ℤ) := encEquiv D a

/-- The decoding of a flat parameter. -/
def decD (D : IdxDatum) (a : ℕ) : (Fin (nD D a) → ℤ) → D.Idx a := (encEquiv D a).symm

/-- `decD` is a left inverse of `encD`. -/
theorem decD_encD (D : IdxDatum) (a : ℕ) (x : D.Idx a) : decD D a (encD D a x) = x := by
  simp [decD, encD]

/-- `encD` is injective. -/
theorem encD_injective (D : IdxDatum) (a : ℕ) : Function.Injective (encD D a) :=
  (encEquiv D a).injective

end

end Work.Peluse.Prop36SW
