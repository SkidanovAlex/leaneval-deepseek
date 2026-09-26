import Mathlib
import Submission.Work.Smooth.SphereJordan.jsepDefs
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.SphereJordan.boundedComponentWinding
import Submission.Work.Smooth.SphereJordan.boundedComponentExists
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range

/-!
# Jordan separation for a continuous simple closed plane curve

A copy of the proof of `Work.Smooth.SphereJordan.exists_jsep` in which the only winding-number input
(the existence of a point of non-zero winding number, `exists_windNumber_ne_zero`, which is
`sorry`-backed in this workspace) is replaced by the *hypothesis* that the component of a point off
the trace being bounded forces the winding number to be non-zero -- the crux, proved in
`Submission/Work/Smooth/SphereJordan/boundedComponentWinding.lean` from the "trap property" of
`Submission/Work/Smooth/SphereJordan/unbounded_component_of_curve_and_reflection.lean`.

The point of the parameterisation: the resulting separation datum `JSep γ` is `sorryAx`-free as soon
as the crux is available, because the remaining inputs (`exists_bounded_complementary_component`,
`compl_jordan_atMostTwo`, `frontier_component_eq_range`, `windNumber_eq_zero_of_mem_U`,
`windNumber_eq_of_preconnected`, `isPreconnected_far`) are all `sorry`-free.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

theorem exists_jsep_of_wind_dict
    (hB : ∀ {γ : ℝ → ℂ} (hγ : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
      (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {z : ℂ}, z ∉ Set.range γ →
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z) →
      windNumber γ hγ z ≠ 0)
    (γ : Work.Smooth.Jordan.PlaneCurve) (hγ : γ.IsSimple) :
    Nonempty (JSep γ) := by
  classical
  have hcont : Continuous γ.γ := γ.cont
  have hper : Function.Periodic γ.γ (2 * Real.pi) := γ.periodic
  have hinj : Set.InjOn γ.γ (Set.Ico 0 (2 * Real.pi)) := hγ
  have htrace : γ.trace = Set.range γ.γ := rfl
  have hcomp : IsCompact γ.trace :=
    Work.Topology.PlaneCurve.isCompact_range_of_periodic hcont hper
  obtain ⟨R₀, hR₀⟩ := hcomp.isBounded.exists_norm_le
  set R : ℝ := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRbound : ∀ t : ℝ, ‖γ.γ t‖ ≤ R := fun t =>
    le_trans (hR₀ _ ⟨t, rfl⟩) (le_max_left _ _)
  obtain ⟨z₁, hz₁t, hz₁bdd⟩ :=
    Work.Smooth.SphereJordan.exists_bounded_complementary_component hcont hper hinj
  have hz₁ne : ∀ t : ℝ, γ.γ t ≠ z₁ := fun t ht => hz₁t ⟨t, ht⟩
  have hz₁w : windNumber γ.γ hcont z₁ ≠ 0 := hB hcont hper hinj hz₁t hz₁bdd
  set p₀ : ℂ := -((R + 1 : ℝ)) with hp₀def
  have hp₀norm : ‖p₀‖ = R + 1 := by
    rw [hp₀def, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hp₀t : p₀ ∉ γ.trace := by
    rintro ⟨t, ht⟩
    have h1 := hRbound t
    rw [ht, hp₀norm] at h1
    linarith
  have hp₀w : windNumber γ.γ hcont p₀ = 0 :=
    windNumber_eq_zero_of_norm_gt hcont hper hRbound (by rw [hp₀norm]; linarith)
  set U : Set ℂ := connectedComponentIn γ.traceᶜ p₀ with hUdef
  set V : Set ℂ := connectedComponentIn γ.traceᶜ z₁ with hVdef
  have memU_iff : ∀ w : ℂ, w ∈ U ↔ w ∈ connectedComponentIn γ.traceᶜ p₀ :=
    fun w => by rw [hUdef]
  have memV_iff : ∀ w : ℂ, w ∈ V ↔ w ∈ connectedComponentIn γ.traceᶜ z₁ :=
    fun w => by rw [hVdef]
  have hUt : U ⊆ γ.traceᶜ := connectedComponentIn_subset _ _
  have hVt : V ⊆ γ.traceᶜ := connectedComponentIn_subset _ _
  have hp₀U : p₀ ∈ U := mem_connectedComponentIn hp₀t
  have hz₁V : z₁ ∈ V := mem_connectedComponentIn hz₁t
  have hUV : U ≠ V := by
    intro hcon
    have hp₀V : p₀ ∈ V := hcon ▸ hp₀U
    have h1 : windNumber γ.γ hcont p₀ = windNumber γ.γ hcont z₁ :=
      windNumber_eq_of_preconnected γ (isPreconnected_connectedComponentIn)
        (connectedComponentIn_subset _ _) hp₀V hz₁V
    rw [hp₀w] at h1
    exact hz₁w h1.symm
  have hdis : ¬ IsPreconnected γ.traceᶜ := by
    intro hpre
    have hUeq : U = γ.traceᶜ :=
      Set.Subset.antisymm hUt (hpre.subset_connectedComponentIn hp₀t (subset_refl γ.traceᶜ))
    have hVeq : V = γ.traceᶜ :=
      Set.Subset.antisymm hVt (hpre.subset_connectedComponentIn hz₁t (subset_refl γ.traceᶜ))
    exact hUV (hUeq.trans hVeq.symm)
  have hfrU : frontier U = γ.trace := by
    simpa [hUdef, htrace] using
      (Work.Topology.PlaneCurve.frontier_component_eq_range hcont hper hinj hdis p₀ hp₀t :
        frontier (connectedComponentIn (Set.range γ.γ)ᶜ p₀) = Set.range γ.γ)
  have hfrV : frontier V = γ.trace := by
    simpa [hVdef, htrace] using
      (Work.Topology.PlaneCurve.frontier_component_eq_range hcont hper hinj hdis z₁ hz₁t :
        frontier (connectedComponentIn (Set.range γ.γ)ᶜ z₁) = Set.range γ.γ)
  have hunion : U ∪ V = γ.traceᶜ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset hUt hVt
    · intro w hw
      rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo hcont hper hinj hw hp₀t hz₁t with
        h | h | h
      · exact Or.inl ((memU_iff w).mpr (h ▸ mem_connectedComponentIn hw))
      · exact Or.inr ((memV_iff w).mpr (h ▸ mem_connectedComponentIn hw))
      · exact absurd h hUV
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxU, hxV⟩
    exact hUV ((connectedComponentIn_eq hxU).trans (connectedComponentIn_eq hxV).symm)
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyc : y ∈ connectedComponentIn γ.traceᶜ p₀ := (memU_iff y).mp hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcomp.isClosed.isOpen_compl y (hUt hy)
    have hsub : Metric.ball y ε ⊆ U := by
      refine (Metric.isPreconnected_ball.subset_connectedComponentIn
        (Metric.mem_ball_self hε) hball).trans ?_
      rw [show connectedComponentIn γ.traceᶜ y = U from
        (connectedComponentIn_eq (F := γ.traceᶜ) hyc).symm.trans hUdef.symm]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hε) hsub
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyc : y ∈ connectedComponentIn γ.traceᶜ z₁ := (memV_iff y).mp hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcomp.isClosed.isOpen_compl y (hVt hy)
    have hsub : Metric.ball y ε ⊆ V := by
      refine (Metric.isPreconnected_ball.subset_connectedComponentIn
        (Metric.mem_ball_self hε) hball).trans ?_
      rw [show connectedComponentIn γ.traceᶜ y = V from
        (connectedComponentIn_eq (F := γ.traceᶜ) hyc).symm.trans hVdef.symm]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hε) hsub
  have hfar_aux : {w : ℂ | R < ‖w‖} ⊆ U := by
    refine (isPreconnected_far hRpos).subset_connectedComponentIn ?_ ?_
    · rw [Set.mem_ofPred_eq, hp₀norm]; linarith
    · intro w hw hwt
      obtain ⟨t, rfl⟩ := hwt
      exact absurd (hRbound t) (not_le.mpr hw)
  have hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ U := fun z hz => hfar_aux hz
  have hVbdd : Bornology.IsBounded V := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) ?_
    intro z hz
    by_contra hcon
    rw [Metric.mem_closedBall, not_le, dist_zero_right] at hcon
    exact (Set.disjoint_left.mp hdisj) (hfar z hcon) hz
  have hwind : ∀ x : ℂ, x ∉ γ.trace → (windNumber γ.γ hcont x = 0 ↔ x ∈ U) := by
    intro x hx
    constructor
    · intro h0
      have hxUV : x ∈ U ∪ V := by rw [hunion]; exact hx
      rcases hxUV with h | h
      · exact h
      · have h2 : windNumber γ.γ hcont x = windNumber γ.γ hcont z₁ :=
          windNumber_eq_of_preconnected γ (isPreconnected_connectedComponentIn)
            (connectedComponentIn_subset _ _) ((memV_iff x).mp h) hz₁V
        rw [h2] at h0
        exact absurd h0 hz₁w
    · intro hxU
      exact (windNumber_eq_of_preconnected γ (isPreconnected_connectedComponentIn)
        (connectedComponentIn_subset _ _) ((memU_iff x).mp hxU) hp₀U).trans hp₀w
  exact ⟨U, V, hUo, hVo, isPreconnected_connectedComponentIn,
    isPreconnected_connectedComponentIn, ⟨p₀, hp₀U⟩, ⟨z₁, hz₁V⟩,
    hdisj, hunion, hVbdd, hfrU, hfrV, hwind⟩

end

end Work.Smooth.SphereJordan
