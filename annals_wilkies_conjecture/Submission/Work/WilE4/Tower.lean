/-
  WilE4 — the CAD data of area E4: derivative tower, projection family, cells.
-/
import Submission.Work.WilE4.Poly

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4
open MvPolynomial

/-- The derivative tower of a family: all iterated derivatives in the last variable, up to the
degree of the member in that variable. -/
def tower {m : ℕ} (l : List (MvPolynomial (Fin (m+1)) ℝ)) : List (MvPolynomial (Fin (m+1)) ℝ) :=
  l.flatMap fun P =>
    (List.range (P.degreeOf (Fin.last m) + 1)).map fun k =>
      (MvPolynomial.pderiv (Fin.last m))^[k] P

/-! The projection family used by the CAD (coefficients and resultants, with uniform degree
bounds) is `Work.WilE4.CAD.projData`, in `Submission/Work/WilE4/CAD/Proj.lean`. -/

namespace BasicD

/-- The basic set attached to a sign vector of a family: equations are the zero atoms, inequalities
are the positive atoms and the negated negative atoms. -/
def ofSign {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (v : Fin G.length → SignType) :
    BasicD m :=
  ⟨(List.finRange G.length).filterMap fun i => if v i = 0 then some (G.get i) else none,
   (List.finRange G.length).filterMap fun i =>
     if v i = 1 then some (G.get i) else if v i = -1 then some (-(G.get i)) else none⟩

end BasicD

/-- A cylindrical cell at level `m+1`: a base cell at level `m` together with a sign condition of
the family `G` in the last variable. -/
def cell {m : ℕ} (C : SAd m) (G : List (MvPolynomial (Fin (m+1)) ℝ))
    (v : Fin G.length → SignType) : SAd (m+1) :=
  C.pad.interBasic (BasicD.ofSign G v)

end Work.WilE4
