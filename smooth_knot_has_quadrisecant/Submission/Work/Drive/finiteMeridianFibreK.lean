import Mathlib
import Submission.Work.Drive.countable_badTraceColumns
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.genericFullDenseK

/-!
# A finite meridian trace of the lifted trisecant locus, from the countability of the bad columns

`Work.Drive.FiniteMeridianFibre r` (there is a meridian `ξ` over which the lifted trisecant locus has
a finite vertical trace) is the hypothesis `hfib` of the corrected `O'` construction.  This module
derives it from `Work.Drive.countable_badTraceColumns`
(`Submission/Work/Drive/countable_badTraceColumns.lean`), which says that the columns over which the
trace is *infinite* form a countable set: since `ℝ` is uncountable, one of the remaining columns has a
finite trace.

The countability statement is the sharp form of `fmf_exists_good_column` and its proof uses the
analytic local structure of the trisecant locus: an infinite trace produces a cluster point of the
slice of the trisecant zero set, which is either off-diagonal (handled by the slice dichotomy and
`Work.Drive.countable_verticalColumn`) or diagonal (the middles escaping to an endpoint of the chord,
which `Work.Drive.cross_zero_of_tendsto_middle_endpoint_a/_b` turn into a tangency, i.e. a column of
`Work.Drive.TangentColumns r`, countable by `TangentChordGP`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **A finite meridian trace, from the countability of the bad columns.**  If the set of columns over
which the lifted trisecant locus has an infinite vertical trace is countable, then some column has a
finite trace: `Work.Drive.FiniteMeridianFibre r`. -/
theorem finiteMeridianFibre_of_tangentChordK {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hg : TorusGeneralPositionTransverse r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) : FiniteMeridianFibre r := by
  rw [FiniteMeridianFibre]
  by_contra hcon
  push_neg at hcon
  have hbad := countable_badTraceColumns hr hg hinfl htc
  have huniv :
      {ξ : ℝ | ¬ (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite} = Set.univ := by
    ext ξ
    simp [hcon ξ]
  have : (Set.univ : Set ℝ).Countable := huniv ▸ hbad
  exact Cardinal.not_countable_real this

/-- **The extended density with the finite meridian trace.**  `Work.Drive.GenericFullDenseK` (the
genericity package with quadrisecant isolation) together with `Work.Drive.FiniteMeridianFibre`: this
is the density hypothesis of the corrected `O'`/`OPrimeK` assembly, which needs the approximant to be
in transverse general position, inflection-free, five-collinear-free, in tangent-chord general
position, quadrisecant-isolated, and to carry a finite vertical trace of its lifted trisecant
locus. -/
def GenericFullFiniteDenseK : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ∀ ε : ℝ, 0 < ε → ∃ r' : ℝ → Space,
    IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      NoFiveCollinear r' ∧ TangentChordGP r' ∧ QuadrisecantIsolated r' ∧
      FiniteMeridianFibre r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε ∧
        ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε

/-- **The extended density with the finite meridian trace, proved.**  Combine the proved
`Work.Drive.genericFullDenseK` with the finite-meridian-trace lemma
`Work.Drive.finiteMeridianFibre_of_tangentChordK` (which is the sharp form of
`fmf_exists_good_column`, derived from `Work.Drive.countable_badTraceColumns`). -/
theorem genericFullFiniteDenseK : GenericFullFiniteDenseK := by
  intro r hr ε hε
  obtain ⟨r', h1, h2, h3, h4, h5, h6, hclose⟩ := genericFullDenseK r hr ε hε
  exact ⟨r', h1, h2, h3, h4, h5, h6,
    finiteMeridianFibre_of_tangentChordK h1 h2 h3 h5, hclose⟩


end

end Work.Drive
