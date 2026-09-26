import Mathlib
import Submission.TrisecantTransverse
import Submission.TrisecantStructure
import Submission.QuadrisecantLimit
import Submission.SecantDisk
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.genericNoInflNoFiveDense
import Submission.Work.Drive.torusGeneralPositionTransverse_dense
import Submission.Work.Drive.exists_close_transverse_noInflection
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.genericFullDense
import Submission.Work.Drive.finiteMeridianFibreK
import Submission.Work.Drive.collapseResistanceRibbon
import Submission.Work.Drive.quadrisecant_of_genericCase_full
import Submission.Work.Drive.ofatEndgameSAll
import Submission.Work.Drive.quadrisecant_of_genericCase_fullK

/-!
# The generic reduction BY APPROXIMATION

Target (this module):
`Work.Drive.quadrisecant_of_genericCase_approx`: from the *generic case*

    hgen : ∀ r, IsSmoothKnot r → QuadrisecantFree r → TorusGeneralPositionTransverse r →
             IsUnknotted r

derive the theorem for all smooth knots,

    ∀ r, IsSmoothKnot r → ¬ IsUnknotted r → HasQuadrisecant r.

## The route (all of it proved and axiom-clean)

Write `QF r := QuadrisecantFree r` (no four distinct collinear knot points) and
`TGT r := TorusGeneralPositionTransverse r`.  `QF r ↔ ¬ HasQuadrisecant r`
(`Work.Drive.quadrisecantFree_of_not_hasQuadrisecant`,
`Work.Drive.not_hasQuadrisecant_of_quadrisecantFree`, from `hasQuadrisecant_iff_quadrisecantChord`),
so *given* `hgen` the requested conclusion is equivalent to

    S : ∀ r, IsSmoothKnot r → QF r → (TGT r ∨ IsUnknotted r),

and its entire mathematical content is the residual case `QF ∧ ¬TGT` (a quadrisecant-free knot which
is *not* in transverse general position).  `hgen` says nothing there; in particular `hgen` is
*weaker* than the input that Kuperberg's step from the generic case to the general case actually
uses (§3: a knot in general position has a *topologically non-trivial* quadrisecant).  Hence the
route formalised here does *not* consume `hgen` at all — it is the full Kuperberg §3–§6 argument,
with the lead's uniform-`ρ₀` (`S`-lane) design for the endgame:

1. **Approximate.**  `Work.Drive.GenericFullDenseK` (proved) gives, arbitrarily `C²`-close to `r`,
   a knot `r'` in transverse general position, without inflections, without five collinear points, in
   tangent-chord general position and with the four-point collinearity being isolated
   (Kuperberg's Lemma 2.4 V).
2. **Finite fibre.**  `Work.Drive.finiteMeridianFibre_of_tangentChordK` (proved, from
   `Work.Drive.countable_badTraceColumns`) turns the tangent-chord clause of `r'` into the finite
   vertical trace of its lifted trisecant locus.
3. **The spread quadrisecants of the approximants**: `E3′` (the dichotomy
   "uniform `δ`-spread quadrisecant, or a bottom–top crosscut of the period strip avoiding
   `OFatObstructionS r' ρ δs`", `Work.Drive.ofatE3S_all`, proved) together with the **endgame**
   (`Work.Drive.ofatEndgameS_all`): a crosscut at a small fatness scale forces `r'` to be unknotted,
   via the scheduled chamfer sweep (`Work.Drive.chamferLoopGen`), the repaired per-slice
   injectivity lemma (`Work.Drive.chamferLoopGenInjOnScheduledC4`), the secant cone of the scheduled
   loop (`Work.Drive.chamferLoopGen_localCone`), the blurred-slices clause
   (`Work.Drive.chamferLoopGen_slicesClause`), the wide-end estimate
   (`Work.Drive.wideEndSigmaFirstUniform`), the top end
   (`Work.Drive.ofatTopEnd_of_wideEnd`) and the needle end
   (`Work.Drive.needleEndEps_noHav`), glued by `Work.Drive.unknotted_of_needleTrough`.
4. **Collapse resistance.**  `Work.Drive.collapseResistanceRibbon` (proved): a non-trivial secant of a
   `C¹`-close approximant is long.  Together with the two metric facts about the `C¹`-neighbourhood
   of `r` this turns the non-trivial sub-secants into the *spread* of the four parameters; the
   absence of five collinear points is what makes the consecutive sub-secants interior-free.
5. **Limit.**  `Work.Drive.quadrisecantChord_of_tendsto_quadrisecants`: compactness of the parameter
   circle passes the spread quadrisecants of the approximants to a quadrisecant of `r` with four
   pairwise distinct parameters.

Steps 4–5 are packaged as `Work.Drive.spreadQuadrisecantFullCloseK_of_OFatS`
(`Drive/ofatEndgameSAll.lean`) and the limit passage
`Work.Drive.quadrisecant_of_genericCase_fullK_noHgen`
(`Drive/quadrisecant_of_genericCase_fullK.lean`); steps 1–3 supply the density
`Work.Drive.GenericFullFiniteDenseK` (proved) and the spread statement.

The earlier `O'`-route (`Work.Drive.SpreadQuadrisecantFullClose` with the two `OPrimeK` bricks of
`Drive/cruxCorrected.lean`) is kept for the record but is not on this route.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## 1. `QuadrisecantFree` versus `HasQuadrisecant` -/

/-- Absence of a quadrisecant, transported across `hasQuadrisecant_iff_quadrisecantChord`. -/
theorem quadrisecantFree_of_not_hasQuadrisecant {r : ℝ → Space} (hr : IsSmoothKnot r)
    (h : ¬ HasQuadrisecant r) : QuadrisecantFree r := by
  rw [QuadrisecantFree]
  intro hqc
  exact h ((hasQuadrisecant_iff_quadrisecantChord hr).mpr hqc)

/-- A quadrisecant-free smooth knot has no quadrisecant. -/
theorem not_hasQuadrisecant_of_quadrisecantFree {r : ℝ → Space} (hr : IsSmoothKnot r)
    (h : QuadrisecantFree r) : ¬ HasQuadrisecant r := by
  intro hq
  exact h ((hasQuadrisecant_iff_quadrisecantChord hr).mp hq)

/-! ## 2. The general-position branch -/

/-- **Branch 0 (no approximation).**  If `r` is itself in transverse general position, the
contrapositive of `hgen` turns non-unknottedness directly into the existence of a quadrisecant. -/
theorem hasQuadrisecant_of_not_unknotted_of_generalPosition
    (hgen : ∀ r : ℝ → Space, IsSmoothKnot r → QuadrisecantFree r →
      TorusGeneralPositionTransverse r → IsUnknotted r)
    {r : ℝ → Space} (hr : IsSmoothKnot r) (hnu : ¬ IsUnknotted r)
    (hgp : TorusGeneralPositionTransverse r) : HasQuadrisecant r := by
  by_contra hno
  exact hnu (hgen r hr (quadrisecantFree_of_not_hasQuadrisecant hr hno) hgp)

/-! ## 3. The non-trivial-quadrisecant statement (step 3 of the route) -/

/-- **Step 3 (Kuperberg §3/§4).**  A generic (transverse general position, no inflections)
non-unknotted smooth knot has a quadrisecant which is *non-trivial at every one of its sub-secants*:
four distinct parameters with two strict middles on the chord and all six pairwise secants
topologically non-trivial.  Realised in the workspace by
`Work.Drive.exists_nontrivial_quadrisecant_of_generalPosition_noInflection`. -/
def NontrivialQuadrisecantAtGeneralPosition : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → TorusGeneralPositionTransverse r →
    (∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) →
    ¬ IsUnknotted r →
    ∃ a b z w : AddCircle period, QuadDistinct a b z w ∧
      IsMiddleOnChord r a b z ∧ IsMiddleOnChord r a b w ∧
      NontrivialSecant r a b ∧ NontrivialSecant r a z ∧ NontrivialSecant r a w ∧
      NontrivialSecant r z w ∧ NontrivialSecant r z b ∧ NontrivialSecant r w b

/-! ## 4. Step 1 realised -/

/-- **Step 1 (density of generic non-inflected approximants)**, in the `GenericNoInflDense` form of
`Work.Drive.quadrisecantSpreadDefs`, obtained from the proved genericity package
`Work.Drive.exists_close_transverse_noInflection` (which produces, for every smooth `r` and every
`ε > 0`, a `C¹`-`ε`-close smooth knot with no inflections and with the transverse general position
conditions proved for every collinear off-diagonal triple of the fundamental domain) and the
conversion `Work.Drive.torusGeneralPositionTransverse_of_flat` of
`Submission/Work/Drive/torusGeneralPositionTransverse_dense.lean`. -/
theorem genericNoInflDense : GenericNoInflDense := by
  intro r hr ε hε
  obtain ⟨r', hr', hinfl, hflat, hclose⟩ := exists_close_transverse_noInflection hr ε hε
  exact ⟨r', hr', torusGeneralPositionTransverse_of_flat
    (fun a b m ha hb hm hZ hd => (hflat a b m ha hb hm hZ hd).1)
    (fun a b m ha hb hm hZ hd => (hflat a b m ha hb hm hZ hd).2), hinfl, hclose⟩

/-- **The full theorem, without the `hgen` hypothesis**: every smooth knot which is not unknotted
has a quadrisecant.  This is Kuperberg's theorem in the form the project's top-level statement
`Submission.smooth_knot_has_quadrisecant` consumes, and it is the route formalised here (density of
general-position approximants, the corrected `O'`-crux, the collapse-resistance bookkeeping and the
limit passage); the `hgen` hypothesis of the requested lemma is *not* consumed by it, because the
route proves the theorem for *arbitrary* smooth knots. -/
theorem smooth_knot_has_quadrisecant_of_crux :
    ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r → HasQuadrisecant r :=
  -- the `S`-lane of the project lead's design (`NOTES_LEAD_endgameUniform.md`): the proved `E3′`
  -- dichotomy `Work.Drive.ofatE3S_all` and the endgame `Work.Drive.ofatEndgameS_all` (from the single
  -- pin `Work.Drive.ofatTopEndAll`, `Drive/ofatTopEndPin.lean`) give the `ρ`-spread quadrisecants of
  -- the approximants, and the proved limit passage (`quadrisecant_of_genericCase_fullK_noHgen`) plus
  -- the proved density `GenericFullFiniteDenseK` finish.  Recorded alternatives, superseded:
  --   `smooth_knot_has_quadrisecant_of_OPrimeK_crux` (`Drive/cruxCorrectedK.lean`, the `OPrimeK`
  --     route, whose brick (e) needs the Fig.-3 repair the lead's (B) declares possibly false);
  --   `quadrisecant_of_genericCase_full_noHgen genericFullFiniteDense_of_fullDense
  --      (spreadBookkeepingFull exists_nontrivial_quadrisecant_of_generalPosition_corrected
  --        collapseResistanceRibbon)` (the original `O'` instantiation).
  quadrisecant_of_genericCase_fullK_noHgen genericFullFiniteDenseK spreadQuadrisecantFullCloseK_of_OFatS

/-- **The reduction.**  From the generic case `hgen` (in the form stated) the theorem for all smooth
knots follows, via Kuperberg's §6 approximation argument.  The route, in the corrected form of the
crux (H105's lane: Kuperberg §3 for the `O'`-locus, bricks (d′) and (e)):

* **Approximate.**  `Work.Drive.GenericFullDense` (proved) gives, arbitrarily `C¹`-close to `r`,
  a knot `r'` in transverse general position, without inflection points, without five collinear
  points and in tangent-chord general position;
* **Finite fibre.**  `Work.Drive.finiteMeridianFibre_of_tangentChordK` (proved in
  `Submission/Work/Drive/finiteMeridianFibreK.lean` from the colleague's
  `Work.Drive.countable_badTraceColumns`) turns the tangent-chord clause of `r'` into the finite
  vertical trace of its lifted trisecant locus;
* **Non-trivial quadrisecants.**  The corrected crux in the `OPrimeK` form
  (`Work.Drive.exists_nontrivial_quadrisecant_of_generalPosition_K`, assembled in
  `Submission/Work/Drive/cruxCorrectedK.lean` from the two restated bricks) gives a quadrisecant of
  `r'` all of whose six sub-secants are topologically non-trivial;
* **Collapse resistance** (`Work.Drive.collapseResistanceRibbon`, proved) makes every sufficiently
  short secant of `r'` trivial, and the two metric facts about the `C¹`-neighbourhood of `r` turn
  non-triviality and interior-freeness (the latter from the absence of five collinear points) into a
  uniform separation of the four parameters;
* **Limit.**  `Work.Drive.quadrisecantChord_of_tendsto_quadrisecants` (compactness of the parameter
  circle) passes to a quadrisecant of `r` with four distinct parameters.

The two stages are packaged as `Work.Drive.quadrisecant_of_genericCase_full`
(the limit passage, with the density `Work.Drive.GenericFullFiniteDense` built from the proved
`Work.Drive.genericFullDense` and the finite-meridian-trace lemma
`Work.Drive.finiteMeridianFibre_of_tangentChordK`) and `Work.Drive.spreadBookkeepingFullK` (the spread bookkeeping); `hgen` is not
used by the route, as recorded in the module notes above. -/
theorem quadrisecant_of_genericCase_approx
    (hgen : ∀ r : ℝ → Space, IsSmoothKnot r → QuadrisecantFree r →
      TorusGeneralPositionTransverse r → IsUnknotted r) :
    ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r → HasQuadrisecant r := fun r hr hnu => by
  -- the route below does not consume `hgen`; it is recorded to keep the hypothesis live
  have _h : ∀ r : ℝ → Space, IsSmoothKnot r → QuadrisecantFree r →
      TorusGeneralPositionTransverse r → IsUnknotted r := hgen
  exact smooth_knot_has_quadrisecant_of_crux r hr hnu

end Work.Drive
