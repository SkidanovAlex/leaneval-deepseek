import Mathlib
import Submission.Work.Mostow.hlDefsAccess
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.HaarBase

/-!
# The `R`-short elements at an arbitrary base point form a finite set

`finite_nearStab` (proved in `Submission/Work/Mostow/finite_nearStab.lean`) says that for a
discrete subgroup `Γ ≤ PO n 1` the set of `γ` displacing the *origin* by at most `R` is finite.

The statement here is the same at an arbitrary base point `z`.  The reduction is the triangle
inequality: for `γ ∈ Γ`,

  `hdist 0 (γ • 0) ≤ hdist 0 (γ • z) + hdist (γ • z) (γ • 0)`
                    `= hdist 0 (γ • z) + hdist z 0`
                   `≤ (hdist 0 z + hdist z (γ • z)) + hdist z 0`
                   `= 2 * hdist 0 z + hdist z (γ • z)`,

because `γ` acts by isometries.  Hence `{γ | hdist z (γ • z) ≤ R}` is contained in the
near-stabiliser of the origin at radius `2 * hdist 0 z + R`, which is finite by
`finite_nearStab`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- A discrete subgroup of `PO n 1` has only finitely many elements displacing a fixed base
point `z` by at most `R`. -/
theorem finite_shortAt (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ)) (z : Submission.Mostow.E n) (R : ℝ) :
    {γ : Γ | Submission.Mostow.hdist z
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • z) ≤ R}.Finite := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  refine (finite_nearStab hA' hI' hdisc (2 * hdist (0 : E n) z + R)).subset ?_
  intro γ hγ
  have h1 : hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤
      hdist (0 : E n) ((γ : PO n 1) • z) +
        hdist ((γ : PO n 1) • z) ((γ : PO n 1) • (0 : E n)) :=
    hI'.triangle _ _ _
  have h2 : hdist ((γ : PO n 1) • z) ((γ : PO n 1) • (0 : E n)) =
      hdist z (0 : E n) :=
    hI'.isom_smul _ _ _
  have h3 : hdist (0 : E n) ((γ : PO n 1) • z) ≤
      hdist (0 : E n) z + hdist z ((γ : PO n 1) • z) :=
    hI'.triangle _ _ _
  have h4 : hdist z (0 : E n) = hdist (0 : E n) z := hI'.symm _ _
  simp only [Set.mem_ofPred_eq] at hγ ⊢
  linarith

end Work.Mostow
