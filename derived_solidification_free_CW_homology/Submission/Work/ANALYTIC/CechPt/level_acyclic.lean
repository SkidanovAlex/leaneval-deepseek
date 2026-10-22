import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelDefs
import Submission.Work.ANALYTIC.CechPt.Assembly
import Submission.Work.ANALYTIC.CechPt.prism_identity

/-!
# Acyclicity of the level-`n` dyadic nerve of the interval

The cochain complex `(C^p, d)` with `C^p = (lev M p → ℤ)` and `d = diff` (the alternating sum of
the pullbacks along the face maps, `Submission/Work/ANALYTIC/CechPt/LevelDefs.lean`) is acyclic in
positive degrees, with `H^0` the constants.  This is the combinatorial input for the exactness of
the dual Čech complex of the cover of the interval by the level-`n` dyadic intervals
(`Submission/Work/ANALYTIC/NOTES_HI_pt.md`).

The proof is by strong induction on the number `M` of vertices, using the explicit simplicial
retraction `rhoS` of the `M`-vertex interval onto the `(M-1)`-vertex sub-interval and the
associated prism homotopy (`Submission/Work/ANALYTIC/CechPt/LevelAux.lean`,
`Submission/Work/ANALYTIC/CechPt/prism_identity.lean`); the induction is assembled in
`Submission/Work/ANALYTIC/CechPt/Assembly.lean`.
-/

namespace Work.ANALYTIC.CechPt

theorem level_acyclic (M : ℕ) :
    (∀ (p : ℕ) (f : Work.ANALYTIC.CechPt.Level.lev M (p + 1) → ℤ),
        Work.ANALYTIC.CechPt.Level.diff f = 0 →
          ∃ g : Work.ANALYTIC.CechPt.Level.lev M p → ℤ,
            Work.ANALYTIC.CechPt.Level.diff g = f) ∧
    (∀ f : Work.ANALYTIC.CechPt.Level.lev M 0 → ℤ,
        Work.ANALYTIC.CechPt.Level.diff f = 0 → ∃ c : ℤ, f = fun _ => c) :=
  Work.ANALYTIC.CechPt.Level.level_acyclic_prop_all_of
    (fun {_} q G y => Work.ANALYTIC.CechPt.prism_identity q G y) M

end Work.ANALYTIC.CechPt
