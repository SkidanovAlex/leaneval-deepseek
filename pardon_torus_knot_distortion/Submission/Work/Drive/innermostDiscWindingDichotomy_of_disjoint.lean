import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Transport
import Submission.Work.CoreTopology.compressing_winding_dichotomy
import Submission.Work.Drive.CleanDiscsDefs
import Submission.Work.Drive.InnermostPlaneCurve
import Submission.Work.Drive.PushedNullHomotopyProfile
import Submission.Work.CoreTopology.disk_sign_dichotomy
import Submission.Work.Drive.SurgeryStrict
import Submission.Work.Drive.InnermostSignStrict
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts
import Submission.Work.CoreTopology.pardonsI_mapHomeomorph

/-!
# The winding dichotomy of an innermost disc with traces off its boundary

This file proves `Work.Drive.innermostDiscWindingDichotomy_of_disjoint`: if the boundary curve
`D.α` of an innermost-disc datum `D` is disjoint from all the other intersection curves
`D.curves i` of the disc with the torus, then one component of the winding vector of `D.α`
vanishes for every lift.

The mathematical content is Pardon's second innermost step, in the following *weak* form:

* **the cut-and-paste.**  The datum `D` is turned into a `Work.Drive.WeakDatum` whose traces
  `D.kappa i` are the preimages of the intersection curves in the model disc
  (`Work.Drive.WeakDatum.ofInnermostDisc`).  The hypothesis that the curves miss `D.α` says
  exactly that every trace is *strictly inside* the model disc (no trace is tangent to the
  boundary circle).  In that case the single-sign datum `Work.Drive.InnermostSignData` exists
  (`Work.Drive.exists_innermostSignData_of_strict`), and the surgery
  `Work.Drive.SurgStrict.WeakDatumStepOfSignStrict` removes one trace at a time, keeping the
  boundary curve `D.α` *and* keeping the remaining traces strictly inside the model disc.
  Induction on the number of traces therefore produces a *continuous* disc map bounded
  by `D.α` whose open part misses the torus
  (`Work.Drive.BoundsDiskInComplementW`), with no injectivity and no Jordan input.

  The variant of the surgery step carrying the strictness of the remaining traces is in the
  auxiliary modules `Submission/Work/Drive/SurgeryStrictAux.lean` and
  `Submission/Work/Drive/SurgeryStrict.lean` (namespace `Work.Drive.SurgStrict`): they are the
  files `WeakDatumStepAux.lean` and `WeakDatumStepOfSign.lean` with the import of the
  (still open) `CleanDiscsWAll` replaced by `CleanDiscsDefs`, and with the conclusion of the
  step strengthened by the clause `∀ i t, ‖(D'.kappa i).γ t‖ < 1` (which holds because the new
  datum keeps the old traces), so that the induction hypothesis applies to the new datum.

* **the classification.**  A curve bounding such a weak disc has a vanishing winding component,
  because the open disc part lies on one side of the torus
  (`Work.CoreTopology.compressing_winding_dichotomyW`, transported along the homeomorphism
  `ψ`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

noncomputable section

/-! ## A collar push for every torus of the challenge -/

/-- The collar push of `Work.Drive.CollarPushAll`, packaged as a `Work.Drive.PushData`. -/
theorem nonempty_pushData (ψ : R3 ≃ₜ R3) : Nonempty (PushData ψ) := by
  obtain ⟨pushP, levP, hlev, hcont_lev, hcont, hzero, hshift, hge, hmono, hmono'⟩ :=
    CollarPushAll ψ
  exact ⟨{ pushP := pushP
           levP := levP
           hlev := hlev
           hcont_lev := hcont_lev
           hcont := hcont
           hzero := hzero
           hshift := hshift
           hge := hge
           hmono := hmono
           hmono' := hmono' }⟩

/-! ## The cut-and-paste: a weak bounding disc from a weak datum with traces off the boundary -/

/-- **The weak cut-and-paste, for a weak datum whose traces are strictly inside the model disc.**

Iterating the single surgery step `Work.Drive.SurgStrict.WeakDatumStepOfSignStrict` on the number
of traces
produces a continuous disc map bounded by `D.α` whose open part misses the torus.  At each step
the innermost trace is removed (the signed bump moves its level off `1`) while the other traces
are left untouched, so that the number of traces strictly decreases. -/
theorem boundsDiskInComplementW_of_weakDatum_strict {ψ : R3 ≃ₜ R3} (PD : PushData ψ)
    (D : WeakDatum ψ) (hint : ∀ i t, ‖(D.kappa i).γ t‖ < 1) :
    BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) D.α := by
  classical
  have hmain : ∀ n : ℕ, ∀ D : WeakDatum ψ, Fintype.card D.ι = n →
      (∀ i t, ‖(D.kappa i).γ t‖ < 1) →
      BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) D.α := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro D hcard hint
      rcases Nat.eq_zero_or_pos (Fintype.card D.ι) with h0 | hpos
      · haveI : IsEmpty D.ι := Fintype.card_eq_zero_iff.mp h0
        exact WeakDatum.boundsDiskInComplementW_of_isEmpty D inferInstance
      · obtain ⟨S⟩ := exists_innermostSignData_of_strict ψ PD D hpos hint
        obtain ⟨D', hα, hlt, hstr⟩ := SurgStrict.WeakDatumStepOfSignStrict ψ PD D S hpos hint
        have hcard' : Fintype.card D'.ι < n := by rw [← hcard]; exact hlt
        have hres := ih (Fintype.card D'.ι) hcard' D' rfl hstr
        rwa [hα] at hres
  exact hmain (Fintype.card D.ι) D rfl hint

/-- The traces of the weak datum attached to an innermost disc whose interior curves miss the
boundary curve lie strictly inside the model disc: a trace meeting the boundary circle would map
to a common point of `D.curves i` and `D.α`. -/
theorem kappa_strict_of_disjoint {ψ : R3 ≃ₜ R3} {S : Set R3}
    (D : Work.InnermostDisk.InnermostDisc (ParamTorus.mapHomeomorph ψ) S)
    (hdisj : ∀ i : D.ι, Disjoint (Set.range (D.curves i).γ) (Set.range D.α.γ)) :
    ∀ i t, ‖((WeakDatum.ofInnermostDisc D).kappa i).γ t‖ < 1 := by
  classical
  intro i t
  have hmem := (WeakDatum.ofInnermostDisc D).kappa_mem i t
  have hle : ‖((WeakDatum.ofInnermostDisc D).kappa i).γ t‖ ≤ 1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    -- the point of the model disc where the trace would cross the boundary circle
    set z : Work.InnermostDisk.Disc :=
      ⟨((WeakDatum.ofInnermostDisc D).kappa i).γ t,
        (WeakDatum.ofInnermostDisc D).kappa_mem i t⟩ with hz
    have hznorm : ‖(z : ℂ)‖ = 1 := h
    obtain ⟨θ, hθ⟩ := Work.CoreTopology.exists_circlePoint_eq (z : ℂ) hznorm
    have hsub : (Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) = z :=
      Subtype.ext hθ
    have h1 : D.e (Work.CoreTopology.circlePoint θ) = D.α.γ θ := D.boundary θ
    have h2 : D.e (Work.CoreTopology.circlePoint θ) = (D.curves i).γ t := by
      rw [hsub]
      exact (WeakDatum.ofInnermostDisc D).maps_kappa i t
    have h3 : (D.curves i).γ t = D.α.γ θ := by rw [← h2, h1]
    exact Set.disjoint_left.mp (hdisj i) ⟨t, rfl⟩ ⟨θ, h3.symm⟩

/-- **The weak cut-and-paste for an innermost disc whose interior curves miss the boundary
curve.**  The boundary curve `D.α` bounds a continuous disc map whose open part misses the
torus. -/
theorem boundsDiskInComplementW_of_innermostDisc_of_disjoint {ψ : R3 ≃ₜ R3} {S : Set R3}
    (D : Work.InnermostDisk.InnermostDisc (ParamTorus.mapHomeomorph ψ) S)
    (hdisj : ∀ i : D.ι, Disjoint (Set.range (D.curves i).γ) (Set.range D.α.γ)) :
    BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) D.α := by
  obtain ⟨PD⟩ := nonempty_pushData ψ
  exact boundsDiskInComplementW_of_weakDatum_strict PD (WeakDatum.ofInnermostDisc D)
    (kappa_strict_of_disjoint D hdisj)

/-! ## Transport of lifts along the homeomorphism -/

/-- A lift of a curve of `ψ(F_std)` gives a lift of its preimage on the standard torus with the
same winding vector: the parameters of a lift are unchanged.  (This is the converse direction of
`Work.Drive.winding_mapHomeomorphInv`.) -/
theorem exists_lift_winding_mapHomeomorphInv {ψ : R3 ≃ₜ R3}
    {γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)}
    (L : LiftOf (ParamTorus.mapHomeomorph ψ) γ) :
    ∃ L₀ : LiftOf standard (ClosedCurve.mapHomeomorphInv ψ γ), L₀.winding = L.winding := by
  refine ⟨{ Θ := L.Θ, Φ := L.Φ, contΘ := L.contΘ, contΦ := L.contΦ, lifts := ?_ }, ?_⟩
  · intro t
    have h := congrArg (⇑ψ.symm) (L.lifts t)
    simpa only [Function.comp_apply, ParamTorus.mapHomeomorph_psi, standard_psi,
      ClosedCurve.mapHomeomorphInv_apply, ψ.symm_apply_apply] using h
  · exact LiftOf.winding_congr L _ (fun _ => rfl) (fun _ => rfl)

/-- **The classification of curves of `ψ(F_std)` bounding a weak disc**: one component of the
winding vector vanishes for every lift.  This is
`Work.CoreTopology.compressing_winding_dichotomyW` pulled back along `ψ`. -/
theorem windingDichotomy_of_boundsDiskW {ψ : R3 ≃ₜ R3}
    {α : ClosedCurve (ParamTorus.mapHomeomorph ψ)}
    (hess : IsEssential (ParamTorus.mapHomeomorph ψ) α)
    (hb : BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) α) :
    (∀ L : LiftOf (ParamTorus.mapHomeomorph ψ) α, (L.winding).1 = 0) ∨
      (∀ L : LiftOf (ParamTorus.mapHomeomorph ψ) α, (L.winding).2 = 0) := by
  have hb' : BoundsDiskInComplementW standard (ClosedCurve.mapHomeomorphInv ψ α) :=
    (boundsDiskInComplementW_mapHomeomorphInv_iff ψ α).mpr hb
  have hess' : IsEssential standard (ClosedCurve.mapHomeomorphInv ψ α) :=
    (ClosedCurve.isEssential_mapHomeomorphInv_iff ψ α).mpr hess
  rcases compressing_winding_dichotomyW _ hess' hb' with h | h
  · right
    intro L
    obtain ⟨L₀, hw⟩ := exists_lift_winding_mapHomeomorphInv L
    rw [← hw]
    exact h L₀
  · left
    intro L
    obtain ⟨L₀, hw⟩ := exists_lift_winding_mapHomeomorphInv L
    rw [← hw]
    exact h L₀

/-! ## The target statement -/

theorem innermostDiscWindingDichotomy_of_disjoint
    (ψ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3)
    (S : Set LeanEval.KnotTheory.PardonDistortion.R3)
    (D : Work.InnermostDisk.InnermostDisc
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) S)
    (hdisj : ∀ i : D.ι, Disjoint (Set.range (D.curves i).γ) (Set.range D.α.γ)) :
    (∀ L : Work.CoreTopology.LiftOf (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) D.α,
        (L.winding).1 = 0) ∨
      (∀ L : Work.CoreTopology.LiftOf (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) D.α,
        (L.winding).2 = 0) :=
  windingDichotomy_of_boundsDiskW D.essential
    (boundsDiskInComplementW_of_innermostDisc_of_disjoint D hdisj)

end

end Work.Drive
