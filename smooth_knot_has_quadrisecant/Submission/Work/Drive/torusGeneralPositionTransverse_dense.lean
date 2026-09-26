import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.exists_close_transverse_noInflection


/-!
# Density of torus transverse general position (`TorusGeneralPositionTransverse`)

Target (this module):

`∃ r' , IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧ (r' is `C¹`-close to `r`)`.

## Mathematical content, and the precise gap

`TorusGeneralPositionTransverse r` unwinds (see `Submission/TrisecantTransverse.lean`) to:
at every torus triple `p` with `torusCollinearity r p = 0` and `p ∈ TorusOffDiag r`, the
fundamental-domain representatives `a b m` satisfy `TrisecantGeneralPosition r a b m`
(the three points pairwise distinct and `PartialRankTwo` — the hinge partials span two
dimensions) *and* `EndpointTangentsOffChord r a b m` (six non-vanishing cross products: no
chord of the trisecant is parallel to a tangent at one of its endpoints).

`torusGeneralPositionTransverse_of_flat` (proved below) shows that it is *exactly*
sufficient to produce `r'` satisfying the two conditions in **flat** (real-parameter) form.

* `Work.Drive.exists_close_partialRankTwo` (delegated): arbitrarily small perturbations put
  a knot in rank-two position at all of its trisecants.  This is the deep genericity step:
  a rank-deficient trisecant (`dim span{Z, v_a, v_b, v_m} ≤ 2`) is codimension one on the
  one-dimensional trisecant locus, so a generic curve has none — Kuperberg §2, "algebraic
  codimension count".  Nothing in the workspace provides transversality/Sard machinery, so
  this step is a genuine research-level gap; it is *not* an open condition (planar knots
  are rank-one at every trisecant, and the diagonal degeneracies are limits of trisecants).
* `Work.Drive.exists_close_endpointTangentsOffChord` (delegated): arbitrarily small
  perturbations make every trisecant's chord transverse to the tangents at its three
  points.  Note the *pair* version of this condition is FALSE (a chord parallel to an
  endpoint tangent is a codimension-2, hence stable, configuration: the (2,3) torus knot has
  one, and so does every nearby knot); only the trisecant version (four conditions in three
  unknowns, hence generically empty) is available.

## Assembly caveat (for whoever wires the two pieces)

The two delegated statements do **not** compose by naive iteration: the rank-two condition
is not open in `C¹` (a small perturbation can create a new rank-deficient trisecant near a
"tangent chord", where the chord degenerates to the tangent line).  A correct assembly needs
one of

* a *combined* statement ("`∃ r'` close with both properties at once"), or
* the observation that the rank-two condition **is** open once it is known that at every
  trisecant with two parameters close together (`b ≈ a`) the hinge partials still span two
  dimensions — which holds automatically as soon as the curvature never vanishes
  (`∀ t, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]`): near such a triple the
  relevant span is `span{v_a, v_m, a_a}` and `cross3 (r'a - r'b) (v_a) ≈ (h²/2) cross3 (v_a, (a_a))`.
  With that hypothesis the rank-two condition is preserved by a *`C²`-small* further
  perturbation, so the tangency can be fixed last.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **Reduction step (flat form → torus form).**

If a smooth knot satisfies, at every collinear *off-diagonal* real triple in the
fundamental domain,

* the rank-two condition `PartialRankTwo`, and
* the endpoint-tangent transversality `EndpointTangentsOffChord`,

then it is in torus transverse general position.  The point is only bookkeeping: a
torus triple with collinear `knotMap`-images lifts to its fundamental-domain
representatives, and `knotMap` agrees with `r` on `Ico 0 period`, so collinearity
and off-diagonality transport across the quotient. -/
theorem torusGeneralPositionTransverse_of_flat {r : ℝ → Space}
    (hrank : ∀ a b m : ℝ, a ∈ Set.Ico 0 period → b ∈ Set.Ico 0 period →
      m ∈ Set.Ico 0 period → collinearityValue r a b m = 0 →
      (r a - r b ≠ 0 ∧ r a - r m ≠ 0 ∧ r m - r b ≠ 0) → PartialRankTwo r a b m)
    (htan : ∀ a b m : ℝ, a ∈ Set.Ico 0 period → b ∈ Set.Ico 0 period →
      m ∈ Set.Ico 0 period → collinearityValue r a b m = 0 →
      (r a - r b ≠ 0 ∧ r a - r m ≠ 0 ∧ r m - r b ≠ 0) →
      EndpointTangentsOffChord r a b m) :
    TorusGeneralPositionTransverse r := by
  intro p hpZ hpOff
  obtain ⟨a, ha, hap⟩ := knotMap_representative p.1
  obtain ⟨b, hb, hbp⟩ := knotMap_representative p.2.1
  obtain ⟨m, hm, hmp⟩ := knotMap_representative p.2.2
  -- transport collinearity to the fundamental domain
  have hZ : collinearityValue r a b m = 0 := by
    have h := hpZ
    rw [torusCollinearity] at h
    rw [← hap, ← hbp, ← hmp] at h
    rw [knotMap_coe r ha, knotMap_coe r hb, knotMap_coe r hm] at h
    rw [collinearityValue_eq]
    exact h
  -- transport off-diagonality to the fundamental domain
  have hdist : r a - r b ≠ 0 ∧ r a - r m ≠ 0 ∧ r m - r b ≠ 0 := by
    have h := hpOff
    simp only [TorusOffDiag, Set.mem_ofPred_eq] at h
    rw [← hap, ← hbp, ← hmp] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [knotMap_coe r ha, knotMap_coe r hb] at h1
    rw [knotMap_coe r ha, knotMap_coe r hm] at h2
    rw [knotMap_coe r hm, knotMap_coe r hb] at h3
    exact ⟨sub_ne_zero.mpr h1, sub_ne_zero.mpr h2, sub_ne_zero.mpr (Ne.symm h3)⟩
  exact ⟨a, b, m, ha, hb, hm, hap, hbp, hmp,
    ⟨hdist.1, hdist.2.1, hdist.2.2, hrank a b m ha hb hm hZ hdist⟩,
    htan a b m ha hb hm hZ hdist⟩

theorem torusGeneralPositionTransverse_dense {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' ∧
      LeanEval.KnotTheory.Quadrisecant.TorusGeneralPositionTransverse r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε := by
  obtain ⟨r', hr', _hninfl, hflat, hclose⟩ :=
    exists_close_transverse_noInflection hr ε hε
  refine ⟨r', hr', torusGeneralPositionTransverse_of_flat
    (fun a b m ha hb hm hZ hd => (hflat a b m ha hb hm hZ hd).1)
    (fun a b m ha hb hm hZ hd => (hflat a b m ha hb hm hZ hd).2), hclose⟩

end Work.Drive
