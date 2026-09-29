import Mathlib
import Submission.Work.A14.defs

/-!
# `Work.A14D.su_om1_pieces`

The four convex open pieces covering the punctured slit plane `Om1 \ {2}`:

* `pieceU = {0 < Im z}` (open upper half-plane),
* `pieceD = {Im z < 0}` (open lower half-plane),
* `piece1 = {1 < Re z ∧ Re z < 2}` (open strip, avoiding `2`),
* `piece2 = {2 < Re z}` (open half-plane, avoiding `2`),

together with explicit points used to seed the four solutions of the linear ODE system and to
test agreement on the overlaps:
`ptU`, `ptD`, `pt1`, `pt2` lie in the respective piece, in `SU \ {2}`; `qU1 ∈ pieceU ∩ piece1`,
`qD1 ∈ pieceD ∩ piece1`, `qU2 ∈ pieceU ∩ piece2`, `qD2 ∈ pieceD ∩ piece2`, all inside `SU \ {2}`.
-/

namespace Work.A14D

open Work.A14D

noncomputable section

/-- The open upper half-plane. -/
def pieceU : Set ℂ := {z : ℂ | 0 < z.im}

/-- The open lower half-plane. -/
def pieceD : Set ℂ := {z : ℂ | z.im < 0}

/-- The open strip `1 < Re z < 2`. -/
def piece1 : Set ℂ := {z : ℂ | 1 < z.re ∧ z.re < 2}

/-- The open half-plane `2 < Re z`. -/
def piece2 : Set ℂ := {z : ℂ | 2 < z.re}

/-- A point of `pieceU ∩ SU \ {2}`. -/
def ptU : ℂ := ⟨3 / 2, 1⟩

/-- A point of `pieceD ∩ SU \ {2}`. -/
def ptD : ℂ := ⟨100, -1⟩

/-- A point of `piece1 ∩ SU \ {2}`. -/
def pt1 : ℂ := ⟨3 / 2, 0⟩

/-- A point of `piece2 ∩ SU \ {2}`. -/
def pt2 : ℂ := ⟨3, 0⟩

/-- A point of `pieceU ∩ piece1 ∩ (SU \ {2})`. -/
def qU1 : ℂ := ⟨3 / 2, 1⟩

/-- A point of `pieceD ∩ piece1 ∩ (SU \ {2})`. -/
def qD1 : ℂ := ⟨19 / 10, -1 / 10⟩

/-- A point of `pieceU ∩ piece2 ∩ (SU \ {2})`. -/
def qU2 : ℂ := ⟨3, 1⟩

/-- A point of `pieceD ∩ piece2 ∩ (SU \ {2})`. -/
def qD2 : ℂ := ⟨100, -1⟩

end

end Work.A14D
