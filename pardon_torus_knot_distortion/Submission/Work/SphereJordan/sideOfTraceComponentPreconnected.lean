import Mathlib
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.SphereJordan.exteriorGermSetup
import Submission.Work.Smooth.SphereJordan.crosscutComponents
import Submission.Work.SphereJordan.sideChamberUComponent

namespace Work.SphereJordan

open Set Metric

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- If `A` and `B` are preconnected and `B` meets the closure of `A`, then `A ∪ B` is
preconnected. -/
theorem isPreconnected_union_of_closure_inter {A B : Set ℂ} (hA : IsPreconnected A)
    (hB : IsPreconnected B) (h : (closure A ∩ B).Nonempty) : IsPreconnected (A ∪ B) := by
  intro u v hu hv huv hAu hBv
  obtain ⟨z₀, hz₀cl, hz₀B⟩ := h
  have hAuv : A ⊆ u ∪ v := Set.subset_union_left.trans huv
  have hBuv : B ⊆ u ∪ v := Set.subset_union_right.trans huv
  by_cases hAuint : (A ∩ u).Nonempty
  · by_cases hAvint : (A ∩ v).Nonempty
    · obtain ⟨x, hx⟩ := hA u v hu hv hAuv hAuint hAvint
      exact ⟨x, Or.inl hx.1, hx.2.1, hx.2.2⟩
    · have hAsub : A ⊆ u := fun x hx =>
        (hAuv hx).resolve_right (fun hxv => hAvint ⟨x, hx, hxv⟩)
      by_cases hBvint : (B ∩ v).Nonempty
      · by_cases hBuint : (B ∩ u).Nonempty
        · obtain ⟨x, hx⟩ := hB u v hu hv hBuv hBuint hBvint
          exact ⟨x, Or.inr hx.1, hx.2.1, hx.2.2⟩
        · have hBsub : B ⊆ v := fun x hx =>
            (hBuv hx).resolve_left (fun hxu => hBuint ⟨x, hx, hxu⟩)
          obtain ⟨x, hxv, hxA⟩ := mem_closure_iff_nhds.mp hz₀cl v (hv.mem_nhds (hBsub hz₀B))
          exact ⟨x, Or.inl hxA, hAsub hxA, hxv⟩
      · exfalso
        have hBsub : B ⊆ u := fun x hx =>
          (hBuv hx).resolve_right (fun hxv => hBvint ⟨x, hx, hxv⟩)
        obtain ⟨x, hxAB, hxv⟩ := hBv
        rcases hxAB with hx | hx
        · exact hAvint ⟨x, hx, hxv⟩
        · exact hBvint ⟨x, hx, hxv⟩
  · have hAsub : A ⊆ v := fun x hx =>
      (hAuv hx).resolve_left (fun hxu => hAuint ⟨x, hx, hxu⟩)
    by_cases hBuint : (B ∩ u).Nonempty
    · by_cases hBvint : (B ∩ v).Nonempty
      · obtain ⟨x, hx⟩ := hB u v hu hv hBuv hBuint hBvint
        exact ⟨x, Or.inr hx.1, hx.2.1, hx.2.2⟩
      · have hBsub : B ⊆ u := fun x hx =>
          (hBuv hx).resolve_right (fun hxv => hBvint ⟨x, hx, hxv⟩)
        obtain ⟨x, hxu, hxA⟩ := mem_closure_iff_nhds.mp hz₀cl u (hu.mem_nhds (hBsub hz₀B))
        exact ⟨x, Or.inl hxA, hxu, hAsub hxA⟩
    · exfalso
      have hBsub : B ⊆ v := fun x hx =>
        (hBuv hx).resolve_left (fun hxu => hBuint ⟨x, hx, hxu⟩)
      obtain ⟨x, hxAB, hxu⟩ := hAu
      rcases hxAB with hx | hx
      · exact hAuint ⟨x, hx, hxu⟩
      · exact hBuint ⟨x, hx, hxu⟩

section

variable {p : ℂ} {ε : ℝ} {a : ℂ}

/-- A preconnected piece of the ball off the trace whose closure meets the trace component of `a`
lies in the chamber of `a`. -/
theorem subset_sideChamber_of_preconnected (ha : a ∈ γ.trace ∩ Metric.ball p ε) {W : Set ℂ}
    (hWpre : IsPreconnected W) (hWT : W ⊆ γ.traceᶜ) (hWball : W ⊆ Metric.ball p ε)
    (hcl : (closure W ∩ traceComponent γ p ε a).Nonempty) :
    W ⊆ connectedComponentIn (sideChamber γ p ε a) a := by
  obtain ⟨z, hz1, hz2⟩ := hcl
  have hpre : IsPreconnected (W ∪ traceComponent γ p ε a) :=
    isPreconnected_union_of_closure_inter hWpre isPreconnected_connectedComponentIn
      ⟨z, hz1, hz2⟩
  have hsub : W ∪ traceComponent γ p ε a ⊆ sideChamber γ p ε a := by
    intro x hx
    rcases hx with hx | hx
    · rw [sideChamber_eq]; exact Or.inl ⟨hWball hx, hWT hx⟩
    · rw [sideChamber_eq]; exact Or.inr hx
  intro x hx
  exact hpre.subset_connectedComponentIn (Or.inr (mem_traceComponent ha)) hsub (Or.inl hx)

/-- A component of the ball off the trace that lies in the chamber of `a` has closure meeting the
trace component of `a`. -/
theorem closure_inter_traceComponent_nonempty (ha : a ∈ γ.trace ∩ Metric.ball p ε) {w : ℂ}
    (hw : w ∈ Metric.ball p ε \ γ.trace)
    (hΩ : connectedComponentIn (Metric.ball p ε \ γ.trace) w ⊆
      connectedComponentIn (sideChamber γ p ε a) a) :
    (closure (connectedComponentIn (Metric.ball p ε \ γ.trace) w) ∩
      traceComponent γ p ε a).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hDopen : IsOpen (Metric.ball p ε \ γ.trace) :=
    Metric.isOpen_ball.sdiff γ.isClosed_trace
  have hΩopen : IsOpen (connectedComponentIn (Metric.ball p ε \ γ.trace) w) :=
    hDopen.connectedComponentIn
  have hΩmem : w ∈ connectedComponentIn (Metric.ball p ε \ γ.trace) w :=
    mem_connectedComponentIn hw
  have hΩpre : IsPreconnected (connectedComponentIn (Metric.ball p ε \ γ.trace) w) :=
    isPreconnected_connectedComponentIn
  -- every point of the chamber outside `Ω` avoids the closure of `Ω`
  have hkey : connectedComponentIn (sideChamber γ p ε a) a \
      connectedComponentIn (Metric.ball p ε \ γ.trace) w ⊆
      (closure (connectedComponentIn (Metric.ball p ε \ γ.trace) w))ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff]
    intro hxcl
    have hxX : x ∈ sideChamber γ p ε a := (connectedComponentIn_subset _ _) hx.1
    have hxD : x ∈ Metric.ball p ε \ γ.trace := by
      rw [sideChamber_eq] at hxX
      rcases hxX with hxD | hxC
      · exact hxD
      · exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hcon) x ⟨hxcl, hxC⟩)
    have hxmem : x ∈ connectedComponentIn (Metric.ball p ε \ γ.trace) x :=
      mem_connectedComponentIn hxD
    have hterm :
        IsPreconnected (connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪
          connectedComponentIn (Metric.ball p ε \ γ.trace) x) :=
      isPreconnected_union_of_closure_inter hΩpre isPreconnected_connectedComponentIn
        ⟨x, hxcl, hxmem⟩
    have hsub : connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪
        connectedComponentIn (Metric.ball p ε \ γ.trace) x ⊆
        connectedComponentIn (Metric.ball p ε \ γ.trace) w :=
      hterm.subset_connectedComponentIn (Or.inl hΩmem) (by
        intro y hy
        rcases hy with hy | hy
        · exact connectedComponentIn_subset _ _ hy
        · exact connectedComponentIn_subset _ _ hy)
    exact hx.2 (hsub (Or.inr hxmem))
  have hΞpre : IsPreconnected (connectedComponentIn (sideChamber γ p ε a) a) :=
    isPreconnected_connectedComponentIn
  have hsub2 : connectedComponentIn (sideChamber γ p ε a) a ⊆
      connectedComponentIn (Metric.ball p ε \ γ.trace) w ∪
        (closure (connectedComponentIn (Metric.ball p ε \ γ.trace) w))ᶜ := by
    intro x hx
    by_cases hxΩ : x ∈ connectedComponentIn (Metric.ball p ε \ γ.trace) w
    · exact Or.inl hxΩ
    · exact Or.inr (hkey ⟨hx, hxΩ⟩)
  have hdisj : Disjoint (connectedComponentIn (Metric.ball p ε \ γ.trace) w)
      (closure (connectedComponentIn (Metric.ball p ε \ γ.trace) w))ᶜ :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => hx2 (subset_closure hx1))
  rcases hΞpre.subset_or_subset hΩopen isClosed_closure.isOpen_compl hdisj hsub2 with h | h
  · have haΞ : a ∈ connectedComponentIn (sideChamber γ p ε a) a :=
      mem_connectedComponentIn (by rw [sideChamber_eq]; exact Or.inr (mem_traceComponent ha))
    have : a ∈ connectedComponentIn (Metric.ball p ε \ γ.trace) w := h haΞ
    exact (connectedComponentIn_subset _ _ this).2 ha.1
  · have : w ∈ (closure (connectedComponentIn (Metric.ball p ε \ γ.trace) w))ᶜ :=
      h (hΩ hΩmem)
    exact this (subset_closure hΩmem)

/-- **Pardon's local chamber lemma.**  If the trace inside the small closed ball around `p` is
contained in a single component `C` of the trace inside the ball `ball p ε`, then the part of the
unbounded side in the chamber of `a` is preconnected. -/
theorem sideOfTraceComponentPreconnected {γ : Work.Smooth.Jordan.PlaneCurve}
    (hs : γ.IsSimple) (S : Work.Smooth.Jordan.PlaneSeparation γ)
    {p : ℂ} {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρlt : ρ < ε) {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε)
    (hconf : γ.trace ∩ Metric.closedBall p ρ ⊆ connectedComponentIn (γ.trace ∩ Metric.ball p ε) a) :
    IsPreconnected (connectedComponentIn (Metric.ball p ε \ ((γ.trace ∩ Metric.ball p ε) \ connectedComponentIn (γ.trace ∩ Metric.ball p ε) a)) a ∩ S.U) := by
  obtain ⟨w, _hw, heq⟩ := sideChamberUComponent (γ := γ) hs S hε hρ hρlt ha hconf
  show IsPreconnected (connectedComponentIn (sideChamber γ p ε a) a ∩ S.U)
  rw [heq]
  exact isPreconnected_connectedComponentIn

end

end

end Work.SphereJordan
