import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.spreadBookkeepingFullK
import Submission.Work.Drive.genericFullDefs

/-!
# The spread bookkeeping when the crux delivers the *spread* directly

Answer to the project lead's 00:10 question ("confirm that the spread bookkeeping accepts `ρ`-fat in
place of non-trivial").

`Work.Drive.SpreadQuadrisecantFullCloseK_v2` (`Drive/spreadBookkeepingFullK_v2.lean`) asks, for every
non-unknotted `r`, for a `δ > 0` and an `ε > 0` such that every `QuadrisecantIsolated`
general-position approximant `r'` within `C¹`-distance `ε` of `r` has a quadrisecant whose four
parameters `a, b, z, w` (with `z`, `w` the two middles) satisfy `Work.Drive.SpreadQuad δ a b z w`,
i.e. **all six pairwise parameter distances are at least `δ`**.  The proved bookkeeping
`Work.Drive.spreadBookkeepingFullK` *derives* that spread from

* `NontrivialSecant` at the three consecutive pairs of the parameter order given by
  `Work.Drive.middle_dichotomy`, together with
* `Work.Drive.NoFiveCollinear` (interior-freeness of the consecutive sub-secants) and
* `Work.Drive.collapseResistanceRibbon` (a narrow interior-free secant is trivial).

The lemma below shows that if the crux delivers the *spread itself* — uniformly over the `C¹`-ball —
then the bookkeeping accepts it **verbatim**, with no nontriviality and no collapse resistance at
all: `δ` is simply the crux's own `ρ`.  That is the exact sense in which "`ρ`-fat" is accepted.

**Caveat (for the design), recorded here so that it is not lost.**  `ρ`-fatness of the two middles
*individually* (each middle at parameter-distance `≥ ρ` from both chord endpoints `a`, `b`) only
supplies four of the six required bounds, namely `circSep a z`, `circSep z b`, `circSep a w`,
`circSep w b ≥ ρ`.  It says **nothing** about the *middle gap* `circSep z w`; and in *both* possible
orders of `middle_dichotomy` (`a, w, z, b` and `a, z, w, b`) the pair `(z, w)` of the two middles is
one of the three *consecutive* pairs, whose lower bound the bookkeeping obtains exactly from
`NontrivialSecant r z w` (via `collapseResistanceRibbon` + interior-freeness).  So a crux concluding
only "the middles are `ρ`-fat against the chord endpoints" is *not* enough; the conclusion must also
bound the middle gap — the cleanest form being `SpreadQuad ρ a b z w` outright (which is what the
adapter consumes), or `NontrivialSecant r z w`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The spread bookkeeping from a crux that already concludes the spread.**  If for every
non-unknotted `r` there is `ρ > 0` and `ε > 0` such that every `QuadrisecantIsolated`
general-position approximant `r'` within `C¹`-distance `ε` of `r` has a quadrisecant whose four
parameters are `ρ`-spread and whose two middles lie on its chord, then
`Work.Drive.SpreadQuadrisecantFullCloseK_v2` holds (with `δ := ρ`). -/
theorem spreadQuadrisecantFullCloseK_of_spreadCrux
    (hspread : ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r →
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ r' : ℝ → Space, IsSmoothKnot r' → TorusGeneralPositionTransverse r' →
          (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
          NoFiveCollinear r' → TangentChordGP r' → FiniteMeridianFibre r' →
          QuadrisecantIsolated r' →
          (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε ∧
            ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε) →
          ∃ a b z w : ℝ, SpreadQuad ρ a b z w ∧
            IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
            IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)) :
    SpreadQuadrisecantFullCloseK_v2 := by
  intro r hr hnu
  obtain ⟨ρ, hρpos, ε, hεpos, hS⟩ := hspread r hr hnu
  exact ⟨ρ, hρpos, ε, hεpos, hS⟩

/-- **The interface of the lead's 00:10 design** (`OFat ρ`, uniform over `C²`-bounded families):
for every non-unknotted smooth knot there is a *uniform* `ρ > 0` and a `C¹`-ball such that every
`QuadrisecantIsolated` general-position approximant in the ball has a quadrisecant whose four
parameters are `ρ`-spread and whose two middles lie on its chord.  This is exactly the shape in which
the corner-local crossing removal (the lead's E1–E4) delivers its quadrisecant. -/
def SpreadCrux (r : ℝ → Space) : Prop :=
  IsSmoothKnot r → ¬ IsUnknotted r →
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' → TorusGeneralPositionTransverse r' →
        (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
        NoFiveCollinear r' → TangentChordGP r' → FiniteMeridianFibre r' →
        QuadrisecantIsolated r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε ∧
            ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε) →
        ∃ a b z w : ℝ, SpreadQuad ρ a b z w ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)

/-- `Work.Drive.SpreadQuadrisecantFullCloseK_v2` follows from the interface `Work.Drive.SpreadCrux` for
every knot, i.e. from the lead's `OFat ρ` design. -/
theorem spreadQuadrisecantFullCloseK_of_spreadCrux_all
    (h : ∀ r : ℝ → Space, SpreadCrux r) : SpreadQuadrisecantFullCloseK_v2 :=
  spreadQuadrisecantFullCloseK_of_spreadCrux (fun r hr hnu => h r hr hnu)


end Work.Drive
