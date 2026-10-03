import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.PerronOn
import Submission.Lib.Unif2.DirichletRegion
import Submission.Lib.Unif2.HarmonicReplacement
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue

/-!
# The Dirichlet problem on an open set, with restriction to the open set

`Submission.dirichletFamily` consists of functions which are subharmonic on *all* of `X`.  For the
classical exhaustion construction of the Green function one needs the corresponding Perron family
whose members are subharmonic only on the open set `Ω` (so that the harmonic functions on `Ω` with
data on `∂Ω` are competitors), while the data is prescribed *outside* `Ω`:

`dirichletFamilyOn Ω f M = {v | v subharmonic on Ω, v ≤ f off Ω, v ≤ M}`.

This requires the harmonic replacement of a function that is subharmonic only on `Ω` to be again
subharmonic on `Ω` (`replaceOnDisc_subharmonicOn`) and the glued replacement to be continuous on
`Ω` (`continuousOn_replaceOnDisc`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Continuity

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The harmonic replacement is continuous on the open set `U`, provided the chart disc is
contained in `U` and `f` is continuous on `U`. -/
theorem continuousOn_replaceOnDisc {U : Set X} (hU : IsOpen U)
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    {u : ℂ → ℝ} {f : X → ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target)
    (hΔU : c.symm '' Metric.closedBall a ρ ⊆ U) (hf : ContinuousOn f U)
    (hu : ContinuousOn u (Metric.ball a ρ))
    (hG : ContinuousOn (gluedBall u (fun w => f (c.symm w)) a ρ) (Metric.closedBall a ρ)) :
    ContinuousOn (replaceOnDisc c a ρ u f) U := by
  intro x₀ hx₀U
  by_cases hx₀ : x₀ ∈ c.source
  · have hGeq : gluedBall u (fun w => f (c.symm w)) a ρ ∘ c
        =ᶠ[𝓝 x₀] replaceOnDisc c a ρ u f := by
      filter_upwards [c.open_source.mem_nhds hx₀] with x hx
      exact (replaceOnDisc_eq_glued hx).symm
    have hfAt : ContinuousAt (fun w => f (c.symm w)) (c x₀) := by
      have h1 : c.symm (c x₀) = x₀ := c.left_inv hx₀
      have hfx : ContinuousAt f (c.symm (c x₀)) := by
        rw [h1]
        exact hf.continuousAt (IsOpen.mem_nhds hU hx₀U)
      exact hfx.comp (c.continuousAt_symm (c.map_source hx₀))
    have hGA : ContinuousAt (gluedBall u (fun w => f (c.symm w)) a ρ) (c x₀) :=
      continuousAt_gluedBall hG hu hfAt
    exact ((hGA.comp (c.continuousAt hx₀)).congr hGeq).continuousWithinAt
  · have hxcompl : x₀ ∈ (chartClosedBall c a ρ)ᶜ :=
      fun hc => hx₀ (chartClosedBall_subset_source c a ρ hc)
    have hnb : (chartBall c a ρ)ᶜ ∈ 𝓝 x₀ :=
      Filter.mem_of_superset ((isClosed_chartClosedBall hsub).isOpen_compl.mem_nhds hxcompl)
        (compl_subset_compl.mpr (chartBall_subset_chartClosedBall c a ρ))
    have heq : f =ᶠ[𝓝 x₀] replaceOnDisc c a ρ u f := by
      filter_upwards [hnb] with x hx
      exact (replaceOnDisc_of_not_mem_chartBall hx).symm
    exact ((hf.continuousAt (IsOpen.mem_nhds hU hx₀U)).congr heq).continuousWithinAt

end Continuity

section ReplacementSubharmonicOn

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem replaceOnDisc_subharmonicOn {U : Set X} (hU : IsOpen U) {z₀ : X} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ (chartAt ℂ z₀).target)
    (hΔU : (chartAt ℂ z₀).symm '' Metric.closedBall a ρ ⊆ U) {f : X → ℝ}
    (hf : SubharmonicOnX f U) {u : ℂ → ℝ}
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z)
    (hG : ContinuousOn (gluedBall u (fun w => f ((chartAt ℂ z₀).symm w)) a ρ)
      (Metric.closedBall a ρ)) :
    SubharmonicOnX (replaceOnDisc (chartAt ℂ z₀) a ρ u f) U := by
  have hball : Metric.ball a ρ ⊆ (chartAt ℂ z₀).target :=
    fun z hz => hsub (Metric.ball_subset_closedBall hz)
  have hucont : ContinuousOn u (Metric.ball a ρ) :=
    continuousOn_of_forall_continuousAt fun z hz =>
      (hu z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)).1.continuousAt
  have hgcont : ContinuousOn (replaceOnDisc (chartAt ℂ z₀) a ρ u f) U :=
    continuousOn_replaceOnDisc hU hsub hΔU hf.1 hucont hG
  have hge : ∀ y ∈ U, f y ≤ replaceOnDisc (chartAt ℂ z₀) a ρ u f y :=
    le_replaceOnDiscOn hU hf hρ hsub hΔU hu hG
  refine ⟨hgcont, ?_⟩
  intro x hxU
  by_cases hxc : x ∈ chartClosedBall (chartAt ℂ z₀) a ρ
  · -- near the disc: measure everything in the chart at `z₀`
    have hxs : x ∈ (chartAt ℂ z₀).source := chartClosedBall_subset_source _ _ _ hxc
    refine (SubharmonicOnXAt_iff_chartAt hxs).mpr ?_
    have hfchart : SubharmonicAtChart f (chartAt ℂ z₀) x :=
      SubharmonicOnX.subharmonicAtChart hf hxU hxs
    rw [SubharmonicAtChart] at hfchart
    obtain ⟨-, ρf, hρf, htf, hcf, hmf⟩ := hfchart
    -- shrink the radius so that the chart ball lies in `U`
    have hnbhd : (chartAt ℂ z₀).symm ⁻¹' U ∈ 𝓝 ((chartAt ℂ z₀) x) := by
      refine ((chartAt ℂ z₀).continuousAt_symm (htf (Metric.mem_ball_self hρf))).preimage_mem_nhds ?_
      refine hU.mem_nhds ?_
      rw [(chartAt ℂ z₀).left_inv hxs]
      exact hxU
    obtain ⟨ρu, hρu, hρusub⟩ := Metric.mem_nhds_iff.mp hnbhd
    set σ : ℝ := min ρf ρu with hσdef
    have hσ : 0 < σ := lt_min hρf hρu
    have hσf : σ ≤ ρf := min_le_left _ _
    have hσu : σ ≤ ρu := min_le_right _ _
    have htσ : Metric.ball ((chartAt ℂ z₀) x) σ ⊆ (chartAt ℂ z₀).target :=
      (Metric.ball_subset_ball hσf).trans htf
    have hUσ : (chartAt ℂ z₀).symm '' Metric.ball ((chartAt ℂ z₀) x) σ ⊆ U := by
      rintro y ⟨w, hw, rfl⟩
      exact hρusub ((Metric.ball_subset_ball hσu) hw)
    have hcσ : ContinuousOn (fun w => f ((chartAt ℂ z₀).symm w))
        (Metric.ball ((chartAt ℂ z₀) x) σ) :=
      hcf.mono (Metric.ball_subset_ball hσf)
    have hmσ : ∀ p ∈ Metric.ball ((chartAt ℂ z₀) x) σ, ∀ r : ℝ, 0 < r →
        Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ z₀) x) σ →
        (fun w => f ((chartAt ℂ z₀).symm w)) p ≤
          Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) p r :=
      fun p hp r hr hpr => hmf p ((Metric.ball_subset_ball hσf) hp) r hr
        (hpr.trans (Metric.ball_subset_ball hσf))
    have hcontg : ContinuousOn
        (fun w : ℂ => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w))
        (Metric.ball ((chartAt ℂ z₀) x) σ) :=
      hgcont.comp ((chartAt ℂ z₀).continuousOn_symm.mono htσ) (fun z hz => hUσ ⟨z, hz, rfl⟩)
    refine ⟨hxs, σ, hσ, htσ, hcontg, ?_⟩
    refine Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue
      Metric.isOpen_ball hcontg ?_
    intro q hq
    have hqt : q ∈ (chartAt ℂ z₀).target := htσ hq
    have hqd : dist q ((chartAt ℂ z₀) x) < σ := Metric.mem_ball.mp hq
    by_cases hqball : q ∈ Metric.ball a ρ
    · -- inside the replacement disc the replacement is harmonic
      have hqa : dist q a < ρ := Metric.mem_ball.mp hqball
      refine ⟨min (ρ - dist q a) (σ - dist q ((chartAt ℂ z₀) x)),
        lt_min (by linarith) (by linarith),
        (Metric.ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball_of_mem hq), ?_⟩
      intro r hr hpr
      have h1 : Metric.closedBall q r ⊆ Metric.ball a ρ :=
        (hpr.trans (Metric.ball_subset_ball (min_le_left _ _))).trans (ball_subset_ball_of_mem hqball)
      have h2 : Metric.closedBall q r ⊆ Metric.ball ((chartAt ℂ z₀) x) σ :=
        (hpr.trans (Metric.ball_subset_ball (min_le_right _ _))).trans (ball_subset_ball_of_mem hq)
      have heqOn : ∀ z ∈ Metric.closedBall q r,
          replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm z) = u z :=
        fun z hz => replaceOnDisc_pullback_of_mem hball (h1 hz)
      have hqeq : replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) = u q :=
        heqOn q (Metric.mem_closedBall_self (le_of_lt hr))
      have havg : Real.circleAverage
          (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
          = Real.circleAverage u q r :=
        Real.circleAverage_congr_sphere (fun z hz => heqOn z (Metric.sphere_subset_closedBall
          (by simpa [abs_of_pos hr] using hz)))
      change replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) ≤
        Real.circleAverage
          (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
      rw [hqeq, havg]
      exact (InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by
        rw [abs_of_pos hr]
        intro z hz
        exact hu z (by simpa [Metric.mem_ball, dist_eq_norm] using h1 hz))).ge
    · by_cases hqsph : q ∈ Metric.sphere a ρ
      · -- on the boundary circle: the replacement dominates `f` and agrees with it at `q`
        refine ⟨σ - dist q ((chartAt ℂ z₀) x), by linarith, ball_subset_ball_of_mem hq, ?_⟩
        intro r hr hpr
        have h2 : Metric.closedBall q r ⊆ Metric.ball ((chartAt ℂ z₀) x) σ :=
          hpr.trans (ball_subset_ball_of_mem hq)
        have hqmem : replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q)
            = f ((chartAt ℂ z₀).symm q) := by
          refine replaceOnDisc_of_not_mem_chartBall ?_
          intro hmem
          exact hqball (by simpa [(chartAt ℂ z₀).right_inv hqt] using hmem.2)
        have hfmvp : (fun w => f ((chartAt ℂ z₀).symm w)) q
            ≤ Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) q r := hmσ q hq r hr h2
        have hsphere' : Metric.sphere q r ⊆ Metric.ball ((chartAt ℂ z₀) x) σ :=
          fun z hz => h2 (Metric.sphere_subset_closedBall hz)
        have hsphere'' : Metric.sphere q |r| ⊆ Metric.ball ((chartAt ℂ z₀) x) σ :=
          fun z hz => h2 (Metric.sphere_subset_closedBall (by simpa [abs_of_pos hr] using hz))
        have hIf : CircleIntegrable (fun w => f ((chartAt ℂ z₀).symm w)) q r :=
          (hcσ.mono hsphere').circleIntegrable (le_of_lt hr)
        have hIg : CircleIntegrable
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r :=
          (hcontg.mono hsphere').circleIntegrable (le_of_lt hr)
        have hm := Real.circleAverage_mono hIf hIg
          (fun z hz => hge _ (hUσ ⟨z, hsphere'' hz, rfl⟩))
        change replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) ≤
          Real.circleAverage
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
        calc replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q)
            = f ((chartAt ℂ z₀).symm q) := hqmem
          _ ≤ Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) q r := hfmvp
          _ ≤ Real.circleAverage
              (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r := hm
      · -- outside the closed disc the replacement agrees with `f` near `q`
        have hqcl : q ∉ Metric.closedBall a ρ := by
          intro h
          rcases (Metric.mem_closedBall.mp h).lt_or_eq with hlt | heq
          · exact hqball (Metric.mem_ball.mpr hlt)
          · exact hqsph (Metric.mem_sphere.mpr heq)
        have hnbhd : (Metric.closedBall a ρ)ᶜ ∈ 𝓝 q :=
          (isOpen_compl_iff.mpr (Metric.isClosed_closedBall (x := a) (ε := ρ))).mem_nhds hqcl
        obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hnbhd
        refine ⟨min ε₁ (σ - dist q ((chartAt ℂ z₀) x)), lt_min hε₁ (by linarith),
          (Metric.ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball_of_mem hq), ?_⟩
        intro r hr hpr
        have h2 : Metric.closedBall q r ⊆ Metric.ball ((chartAt ℂ z₀) x) σ :=
          (hpr.trans (Metric.ball_subset_ball (min_le_right _ _))).trans (ball_subset_ball_of_mem hq)
        have hout : Metric.closedBall q r ⊆ (Metric.closedBall a ρ)ᶜ :=
          (hpr.trans (Metric.ball_subset_ball (min_le_left _ _))).trans hε₁sub
        have heqOn : ∀ z ∈ Metric.closedBall q r,
            replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm z)
              = f ((chartAt ℂ z₀).symm z) := by
          intro z hz
          have hzt : z ∈ (chartAt ℂ z₀).target := htσ (h2 hz)
          refine replaceOnDisc_of_not_mem_chartBall ?_
          intro hmem
          refine hout hz ?_
          have h1 : z ∈ Metric.ball a ρ := by
            have h2' := hmem.2
            simp only [Set.mem_preimage] at h2'
            rwa [(chartAt ℂ z₀).right_inv hzt] at h2'
          exact Metric.ball_subset_closedBall h1
        have hqeq : replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q)
            = f ((chartAt ℂ z₀).symm q) := heqOn q (Metric.mem_closedBall_self (le_of_lt hr))
        have havg : Real.circleAverage
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
            = Real.circleAverage (fun w => f ((chartAt ℂ z₀).symm w)) q r :=
          Real.circleAverage_congr_sphere (fun z hz => heqOn z (Metric.sphere_subset_closedBall
            (by simpa [abs_of_pos hr] using hz)))
        change replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm q) ≤
          Real.circleAverage
            (fun w => replaceOnDisc (chartAt ℂ z₀) a ρ u f ((chartAt ℂ z₀).symm w)) q r
        rw [hqeq, havg]
        exact hmσ q hq r hr h2
  · -- far from the disc: the replacement equals `f` on a neighbourhood of `x`
    have hne : (chartClosedBall (chartAt ℂ z₀) a ρ)ᶜ ∈ 𝓝 x :=
      (isClosed_chartClosedBall hsub).isOpen_compl.mem_nhds hxc
    have heq : f =ᶠ[𝓝 x] replaceOnDisc (chartAt ℂ z₀) a ρ u f := by
      filter_upwards [hne] with y hy
      exact (replaceOnDisc_of_not_mem_chartBall
        (fun hmem => hy (chartBall_subset_chartClosedBall _ _ _ hmem))).symm
    exact SubharmonicOnXAt.congr (hf.2 x hxU) heq

end ReplacementSubharmonicOn


section DirichletOn

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The Perron family of the Dirichlet problem on `Ω`, whose members are required to be subharmonic
only on `Ω` (and `≤ f` outside `Ω`, `≤ M` everywhere). -/
def dirichletFamilyOn (Ω : Set X) (f : X → ℝ) (M : ℝ) : Set (X → ℝ) :=
  {v | SubharmonicOnX v Ω ∧ (∀ x : X, x ∉ Ω → v x ≤ f x) ∧ ∀ x : X, v x ≤ M}

theorem dirichletFamilyOn_subharmonic {Ω : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ dirichletFamilyOn Ω f M) : SubharmonicOnX v Ω := hv.1

theorem dirichletFamilyOn_le_off {Ω : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ dirichletFamilyOn Ω f M) {x : X} (hx : x ∉ Ω) : v x ≤ f x := hv.2.1 x hx

theorem dirichletFamilyOn_le_bound {Ω : Set X} {f : X → ℝ} {M : ℝ} {v : X → ℝ}
    (hv : v ∈ dirichletFamilyOn Ω f M) (x : X) : v x ≤ M := hv.2.2 x

/-- **The region-Dirichlet family is a Perron family with restricted replacement.** -/
theorem dirichletFamilyOn_isPerronOn {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamilyOn Ω f M).Nonempty) :
    IsPerronOn (dirichletFamilyOn Ω f M) (fun _ => M) Ω := by
  refine ⟨hne, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact dirichletFamilyOn_subharmonic hv
  · intro v hv x _
    exact dirichletFamilyOn_le_bound hv x
  · intro v hv w hw
    exact ⟨(dirichletFamilyOn_subharmonic hv).sup (dirichletFamilyOn_subharmonic hw),
      fun x hx => max_le (dirichletFamilyOn_le_off hv hx) (dirichletFamilyOn_le_off hw hx),
      fun x => max_le (dirichletFamilyOn_le_bound hv x) (dirichletFamilyOn_le_bound hw x)⟩
  · intro z hz
    have hsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hmemtgt : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hsrc
    have hsymm : (chartAt ℂ z).symm ((chartAt ℂ z) z) = z := (chartAt ℂ z).left_inv hsrc
    obtain ⟨ε₁, hε₁, hε₁sub⟩ :=
      Metric.mem_nhds_iff.mp ((chartAt ℂ z).open_target.mem_nhds hmemtgt)
    obtain ⟨ε₂, hε₂, hε₂Ω⟩ := Metric.mem_nhds_iff.mp
      (((chartAt ℂ z).continuousAt_symm hmemtgt).preimage_mem_nhds
        (hΩ.mem_nhds (by rw [hsymm]; exact hz)))
    refine ⟨min (ε₁ / 2) (ε₂ / 2), lt_min (half_pos hε₁) (half_pos hε₂), ?_⟩
    intro v hv ρ hρ hρle hsub u hu hglued
    have hρ1 : ρ < ε₁ := by linarith [hρle, min_le_left (ε₁ / 2) (ε₂ / 2), hε₁]
    have hρ2 : ρ < ε₂ := by linarith [hρle, min_le_right (ε₁ / 2) (ε₂ / 2), hε₂]
    have hsubU : Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target := hsub
    have hΩcl : chartClosedBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ ⊆ Ω := by
      rintro y ⟨hy1, hy2⟩
      have h1 : (chartAt ℂ z) y ∈ Metric.ball ((chartAt ℂ z) z) ε₂ :=
        (Metric.closedBall_subset_ball hρ2) hy2
      have h2 := hε₂Ω h1
      rw [Set.mem_preimage] at h2
      rwa [(chartAt ℂ z).left_inv hy1] at h2
    have hΔU : (chartAt ℂ z).symm '' Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ Ω := by
      rw [← chartClosedBall_eq_image hsubU]
      exact hΩcl
    have hΩball : chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ ⊆ Ω :=
      (chartBall_subset_chartClosedBall _ _ _).trans hΩcl
    refine ⟨replaceOnDisc_subharmonicOn hΩ hρ hsubU hΔU
      (dirichletFamilyOn_subharmonic hv) hu hglued, ?_, ?_⟩
    · intro x hx
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ
      · exact absurd (hΩball hxb) hx
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact dirichletFamilyOn_le_off hv hx
    · intro x
      by_cases hxb : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ
      · have hxball : (chartAt ℂ z) x ∈ Metric.ball ((chartAt ℂ z) z) ρ := hxb.2
        have hcontM : ContinuousOn
            (gluedBall (fun _ : ℂ => M) (fun _ : ℂ => M) ((chartAt ℂ z) z) ρ)
            (Metric.closedBall ((chartAt ℂ z) z) ρ) := by
          rw [gluedBall_const]
          exact continuousOn_const
        have hle := harmonic_le_of_gluedBall_le hρ hu
          (fun w _ => InnerProductSpace.harmonicAt_const M) hglued hcontM
          (fun w _ => dirichletFamilyOn_le_bound hv _)
        rw [replaceOnDisc_of_mem_chartBall hxb]
        exact hle _ (by simpa [Metric.mem_ball, dist_eq_norm] using hxball)
      · rw [replaceOnDisc_of_not_mem_chartBall hxb]
        exact dirichletFamilyOn_le_bound hv x

/-- The Perron solution of the Dirichlet problem on the region `Ω` (members subharmonic only on
`Ω`). -/
def dirichletOnRegionOn (Ω : Set X) (f : X → ℝ) (M : ℝ) : X → ℝ :=
  upperEnvelope (dirichletFamilyOn Ω f M)

/-- **The region-Dirichlet problem**: the Perron solution is harmonic on `Ω`. -/
theorem harmonicOnX_dirichletOnRegionOn {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamilyOn Ω f M).Nonempty) :
    HarmonicOnX (dirichletOnRegionOn Ω f M) Ω :=
  IsPerronOn.upperEnvelope_harmonic hΩ (dirichletFamilyOn_isPerronOn hΩ hne)

theorem dirichletOnRegionOn_le_off {Ω : Set X} {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamilyOn Ω f M).Nonempty) {x : X} (hx : x ∉ Ω) :
    dirichletOnRegionOn Ω f M x ≤ f x := by
  rw [dirichletOnRegionOn, upperEnvelope]
  exact csSup_le (hne.image _) (by rintro y ⟨v, hv, rfl⟩; exact dirichletFamilyOn_le_off hv hx)

theorem dirichletOnRegionOn_le_bound {Ω : Set X} {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamilyOn Ω f M).Nonempty) (x : X) : dirichletOnRegionOn Ω f M x ≤ M := by
  rw [dirichletOnRegionOn, upperEnvelope]
  exact csSup_le (hne.image _) (by rintro y ⟨v, hv, rfl⟩; exact dirichletFamilyOn_le_bound hv x)

/-- **Maximality of the region-Dirichlet solution**: it dominates every subharmonic function on `Ω`
with the same bounds (in particular every *harmonic* function on `Ω` which is `≤ f` on `∂Ω` and
extended by values `≤ f` outside `Ω`). -/
theorem le_dirichletOnRegionOn {Ω : Set X} (hΩ : IsOpen Ω) {f : X → ℝ} {M : ℝ}
    (hne : (dirichletFamilyOn Ω f M).Nonempty) {v : X → ℝ} (hv : v ∈ dirichletFamilyOn Ω f M) :
    ∀ x ∈ Ω, v x ≤ dirichletOnRegionOn Ω f M x :=
  fun x hx => IsPerronOn.mem_le_upperEnvelope (dirichletFamilyOn_isPerronOn hΩ hne) hv hx

end DirichletOn

end Submission
