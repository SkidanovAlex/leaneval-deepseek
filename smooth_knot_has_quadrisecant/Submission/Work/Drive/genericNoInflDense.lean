import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.exists_close_transverse_noInflection

/-!
# Density of the generic, non-inflected approximants

`Work.Drive.genericNoInflDense : Work.Drive.GenericNoInflDense` — every smooth knot has arbitrarily
`C¹`-close smooth approximants that are in *transverse general position*
(`TorusGeneralPositionTransverse`) and have *no inflection points*.

This is Kuperberg's genericity step (a codimension count, §2).  It is obtained here from the
*sorry-free* module `Work.Drive.exists_close_transverse_noInflection`, which produces `C¹`-close
approximants with no inflection points satisfying the *pointwise* general-position condition at
every collinear triple of parameters of the fundamental domain; the only missing link, proved
below, is the passage from that pointwise condition to the torus-level predicate
`TorusGeneralPositionTransverse`.
-/

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **From pointwise general position on the fundamental domain to the torus predicate.**  If every
collinear off-diagonal triple of parameters in `[0, period)³` is in rank-two general position with
the endpoint tangents off the chord, then `r` is in torus transverse general position: every
collinear off-diagonal class triple has fundamental-domain representatives in transverse general
position. -/
theorem torusGeneralPositionTransverse_of_pointwise {r : ℝ → Space}
    (h : ∀ a b m : ℝ, a ∈ Set.Ico 0 period → b ∈ Set.Ico 0 period → m ∈ Set.Ico 0 period →
      collinearityValue r a b m = 0 →
      (r a - r b ≠ 0 ∧ r a - r m ≠ 0 ∧ r m - r b ≠ 0) →
      PartialRankTwo r a b m ∧ EndpointTangentsOffChord r a b m) :
    TorusGeneralPositionTransverse r := by
  intro p hZ hOff
  obtain ⟨a, ha, hae⟩ := AddCircle.eq_coe_Ico p.1
  obtain ⟨b, hb, hbe⟩ := AddCircle.eq_coe_Ico p.2.1
  obtain ⟨m, hm, hme⟩ := AddCircle.eq_coe_Ico p.2.2
  -- the collinearity value at the representatives vanishes
  have hΦ : collinearityValue r a b m = 0 := by
    have h1 : knotMap r p.1 = r a := by
      rw [← hae]; exact knotMap_coe r ha
    have h2 : knotMap r p.2.1 = r b := by
      rw [← hbe]; exact knotMap_coe r hb
    have h3 : knotMap r p.2.2 = r m := by
      rw [← hme]; exact knotMap_coe r hm
    rw [torusCollinearity, h1, h2, h3] at hZ
    rwa [collinearityValue_eq]
  -- pairwise distinctness of the three knots points
  rw [TorusOffDiag, Set.mem_ofPred_eq] at hOff
  obtain ⟨hZne, hWne, hmbne⟩ := hOff
  have h1 : knotMap r p.1 = r a := by rw [← hae]; exact knotMap_coe r ha
  have h2 : knotMap r p.2.1 = r b := by rw [← hbe]; exact knotMap_coe r hb
  have h3 : knotMap r p.2.2 = r m := by rw [← hme]; exact knotMap_coe r hm
  have hAB : r a - r b ≠ 0 := by
    intro h0; exact hZne (by rw [h1, h2, sub_eq_zero.mp h0])
  have hAM : r a - r m ≠ 0 := by
    intro h0; exact hWne (by rw [h1, h3, sub_eq_zero.mp h0])
  have hMB : r m - r b ≠ 0 := by
    intro h0; exact hmbne (by rw [h2, h3, (sub_eq_zero.mp h0).symm])
  have hoff : r a - r b ≠ 0 ∧ r a - r m ≠ 0 ∧ r m - r b ≠ 0 := ⟨hAB, hAM, hMB⟩
  obtain ⟨hrank, hend⟩ := h a b m ha hb hm hΦ hoff
  exact ⟨a, b, m, ha, hb, hm, hae, hbe, hme, ⟨hAB, hAM, hMB, hrank⟩, hend⟩

/-- **The density of generic non-inflected approximants.** -/
theorem genericNoInflDenseOfPointwise : GenericNoInflDense := by
  intro r hr ε hε
  obtain ⟨r', hr'knot, hr'infl, hr'pt, hr'close⟩ :=
    exists_close_transverse_noInflection hr ε hε
  exact ⟨r', hr'knot, torusGeneralPositionTransverse_of_pointwise hr'pt, hr'infl, hr'close⟩

end

end Work.Drive
