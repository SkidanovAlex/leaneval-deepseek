import Mathlib
import Submission.Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData
import Submission.Work.Drive.Final.dentOut_resolvedCond
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Mono.eventValue_mem_window
import Submission.Work.Drive.Final.nojump_dent
import Submission.Work.Drive.Final.dentOut_resolvedDisc
import Submission.Work.Drive.Final.dentOut_hgen
import Submission.Work.Drive.Final.exists_dentOut_trace_family
import Submission.Work.Drive.Final.dentOut_sweep_subset

/-!
# The no-jump condition at every event, from the trace data

`Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData` proves the same conclusion from a strictly
stronger hypothesis bundle (it additionally carries `hwin`, the counting data `d`, the level count
`hS` and the sliced-sphere hypothesis `hslice`).  `hwin` is the only one of those that the proof body
consumes, and at a `GoodDataPackage3` datum it is available from the tilt data: the level of any event
lies in the exceptional set `exc`, which `TiltData` keeps strictly inside the window
(`Work.Drive.Mono.eventValue_mem_window`).  So the conclusion holds from the trace data alone.
-/

open scoped Topology

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

noncomputable section

theorem noJumpAtAnyEventCond_of_eventTraceData_proved
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (hdata : Work.Drive.Final.EventTraceData ψ K s c σ u v h R ℓ) :
    Work.Drive.Final.NoJumpAtAnyEventCond ψ K s c σ u v h R ℓ := by
  classical
  intro p₀ hp₀ U₀ hU₀
  -- ## 0. the tilt data and the descent direction
  obtain ⟨-, hv1, hℓne, hℓv, -⟩ := hDP.1.tilt
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 :=
    Work.Drive.Final.exists_descend_of_inner_eq_zero hv0 hℓne hℓv
  have hG3 : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1 := hDP.2.1
  have hcarr : Work.BoxShrink.Pinch.par ψ p₀ ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
    Work.BoxShrink.Pinch.par_mem_carrier ψ p₀
  -- ## 1. the local inessentiality radius at the event's image
  obtain ⟨ε₁, hε₁pos, hε₁bot⟩ :=
    windingSpan_carrier_inter_ball_eq_bot (Work.Drive.EpsSphere.torusOf ψ) hcarr
  -- ## 2. the localised gates at radius `ε₁ / 2`
  have hgates := Work.Drive.Final.gates_local hG3 hp₀ (ρ := ε₁ / 2) (by positivity)
  obtain ⟨E, U₁, U₂, hEopen, hEinner, hEsmall, hU₁pc, hU₂pc, hU₁E, hU₂E, hgate⟩ := hgates
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := hEinner
  -- ## 3. the datum, at a neighbourhood inside both balls
  set ε₃ : ℝ := min ε₂ (ε₁ / 2) with hε₃def
  have hε₃pos : 0 < ε₃ := lt_min hε₂pos (by linarith)
  set U : Set R3 := U₀ ∩ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) ε₃ with hUdef
  have hU : U ∈ nhds (Work.BoxShrink.Pinch.par ψ p₀) :=
    Filter.inter_mem hU₀ (Metric.ball_mem_nhds _ hε₃pos)
  obtain ⟨D, hDp, hr4, ha', m, Ss, hsph, hfront, hdisj, htame⟩ := hdata p₀ hp₀ U hU
  -- ## 4. the trace family of the deformed level
  have hlev : ℓ D.centre ∈ Set.Icc lam0 lam1 := by
    rw [D.centre_eq, hDp]
    exact Work.Drive.Mono.eventValue_mem_window hDP hp₀
  have hcnt := hDP.2.2 (ℓ D.centre) hlev
  obtain ⟨n, cs, hsimple, hess, hdisjcs, hcsZ⟩ :=
    Work.Drive.Final.exists_dentOut_trace_family (ψ := ψ) (K := K) p q hp hq hc himg hcl D ha'
      hsph hdisj hfront hcnt htame
  have hUsub : U ⊆ U₀ := fun z hz => hz.1
  have hsub_cover : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ := le_of_eq hcsZ
  have hdisjΩ : Disjoint (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D)
      (⋃ i, Set.range (cs i).γ) := by
    rw [← hcsZ, Set.disjoint_left]
    intro z hzΩ hzT
    exact Set.disjoint_left.mp disjoint_interior_frontier hzΩ.2 hzT.2
  have hgen : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v z| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ := by
    intro z hzc hzbox hzslab hzℓ
    exact Work.Drive.Final.dentOut_hgen_of_trace hG3 D (le_of_eq hcsZ) hzc hzbox hzslab hzℓ
  have hspan : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre)) = ⊥ →
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) = ⊥ := by

    intro hXbot
    set X : Set R3 := Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
      s c σ u v h ℓ (ℓ D.centre) with hXdef
    set Ω : Set R3 := Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D with hΩdef
    have hXc : X ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := fun z hz => hz.1
    have hXopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) X :=
      Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion
    have hE'open : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
        (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
      rw [Work.SurgeryInvariance.IsOpenInCarrier] at hEopen ⊢
      have heq : (Subtype.val ⁻¹' (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) :
          Set (Work.Drive.EpsSphere.torusOf ψ).carrier) = Subtype.val ⁻¹' E := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
      rw [heq]
      exact hEopen
    have hE'bot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) = ⊥ := by
      rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hε₁bot
      rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
      rintro ⟨γ, hγess, hγ⟩
      refine hε₁bot ⟨γ, hγess, fun t => ⟨γ.mem t, ?_⟩⟩
      have h1 : γ.γ t ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) (ε₁ / 2) :=
        hEsmall (hγ t).1
      rw [Metric.mem_ball] at h1 ⊢
      linarith
    have hcoverΩ : Ω ⊆ X ∪ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
      intro z hz
      rcases Work.Drive.Final.dentOutRegion_subset_sweepRegion_union_ball D hdesc hz with hh | hh
      · exact Or.inl hh
      · refine Or.inr ⟨?_, Work.Drive.Final.dentOutRegion_subset_carrier D hz⟩
        have h1 : z ∈ U := D.ball_sub z (by
          have hb : ‖z - D.centre‖ ≤ D.r := by
            rw [Metric.mem_closedBall, dist_eq_norm] at hh
            exact hh
          linarith [hb, D.δ_pos])
        have h2 : z ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) ε₃ := h1.2
        have h3 : z ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) ε₂ := by
          rw [Metric.mem_ball] at h2 ⊢
          have := min_le_left ε₂ (ε₁ / 2)
          linarith
        exact hε₂ ⟨h3, Work.Drive.Final.dentOutRegion_subset_carrier D hz⟩
    -- the gate decomposition of `X ∩ E`
    have hU₁c : U₁ ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      intro w hw
      have h1 : w ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
          s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p₀) ∩ E := by
        rw [hgate]
        exact Or.inl hw
      exact h1.1.1
    have hU₂c : U₂ ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      intro w hw
      have h1 : w ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
          s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p₀) ∩ E := by
        rw [hgate]
        exact Or.inr hw
      exact h1.1.1
    have hEV : Work.Drive.Final.eventValue ψ ℓ p₀ = ℓ D.centre := by
      rw [Work.Drive.Final.eventValue, ← hDp, ← D.centre_eq]
    have hAE : X ∩ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) = U₁ ∪ U₂ := by
      rw [hXdef, ← Set.inter_assoc, ← hEV, hgate, Set.union_inter_distrib_right,
        Set.inter_eq_left.mpr hU₁c, Set.inter_eq_left.mpr hU₂c]
    -- the rank bound
    have hfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
        (Work.Drive.EpsSphere.torusOf ψ) (X ∪ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))) ≤ 1 := by
      by_cases hne : (X ∩ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)).Nonempty
      · refine Work.Drive.Final.finrank_union_le_one_of_two_gates_nonconn hXc
          Set.inter_subset_right hXopen hE'open hXbot hE'bot ?_
        exact two_gates_cond hXc Set.inter_subset_right hXopen hE'open hAE hU₁pc hU₂pc
          (fun w hw => ⟨hU₁E hw, hU₁c hw⟩) (fun w hw => ⟨hU₂E hw, hU₂c hw⟩) hne
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        have hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (X ∪ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) = ⊥ := by
          refine windingSpan_union_eq_bot_of_disjoint ?_ hXopen hE'open hXbot hE'bot
          rw [hne]
        rw [hbot]
        simp
    -- the dichotomy for `Ω₁` and the conclusion
    have hdich : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) Ω = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) Ω = ⊤ := by
      have hnoF : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
          (frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
        Work.Drive.Final.dentOut_trace_noEssential_of_sphereCover (ψ := ψ) (K := K) p q hp hq hc
          himg hcl D ha' hsph hdisj hfront hcnt htame
      have hno : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
        fun hcon => hnoF (Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _
          Set.inter_subset_right hcon)
      exact Work.Drive.Final.windingSpan_dentOutRegion_bot_or_top D ha' hsph hfront hdisj htame hno
    rcases hdich with hbot | htop
    · exact hbot
    · exfalso
      have hle := Work.SurgeryInvariance.WindingSpan_mono (Work.Drive.EpsSphere.torusOf ψ) hcoverΩ
      have h2 := le_trans (Submodule.finrank_mono hle) hfin
      rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self] at h2
      norm_num at h2

  refine ⟨{ D with ball_sub := fun z hz => hUsub (D.ball_sub z hz) }, hDp, ?_⟩
  exact ⟨⟨n, cs, hsimple, hess, hdisjcs, hsub_cover, hdisjΩ, hgen⟩, hspan⟩

end

end Work.Drive.Final
