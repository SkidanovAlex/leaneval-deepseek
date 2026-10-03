import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero

open Set Metric Filter
open scoped Topology Manifold

set_option linter.style.haveILetI false

namespace Work.BasinSC.StepOneCrit

/-- Plain-language form of the workspace degree-one result for proper maps into the disc: a
holomorphic map of a connected plane domain into the unit disc, proper into the disc, with exactly
one (simple) zero, is a homeomorphism onto the disc.  Use
`Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero` (module
`Submission.Lib.Unif2.Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero`),
which gives injectivity and surjectivity of `fun z : ↥V' => (⟨Ψ z, _⟩ : Metric.ball (0:ℂ) 1)`;
set up `ChartedSpace ℂ ↥V'` as in
`Submission/Lib/Unif2/Work/Analysis/Complex/hull_simplyConnected_of_isCompact.lean` (via
`let U : TopologicalSpace.Opens ℂ := ⟨V', hV'o⟩`, whose chart at `x` is the identity, so the
chart-derivative hypotheses of the library result become exactly `deriv Ψ z₀ ≠ 0` here); the map is
then a closed map (properness; cf. the private `isClosedMap_toBall` in
`Submission/Lib/Unif2/Commons/Analysis/Complex/ProperIntoBall/bijective_of_isProperMap_into_ball_single_zero.lean`),
so the continuous bijection is a homeomorphism. -/
theorem homeomorph_ball_single_zero {V' : Set ℂ} (hV'o : IsOpen V') (hV'c : IsConnected V')
    {Ψ : ℂ → ℂ} (hΨ : DifferentiableOn ℂ Ψ V')
    (hmaps : ∀ z ∈ V', Ψ z ∈ Metric.ball (0 : ℂ) 1)
    (hprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → IsCompact (V' ∩ Ψ ⁻¹' K))
    {z₀ : ℂ} (hz₀ : z₀ ∈ V') (hfib : ∀ z ∈ V', Ψ z = 0 ↔ z = z₀) (hloc : deriv Ψ z₀ ≠ 0) :
    Nonempty (↥V' ≃ₜ ↥(Metric.ball (0 : ℂ) 1)) := by
  classical
  let U : TopologicalSpace.Opens ℂ := ⟨V', hV'o⟩
  haveI hconn : ConnectedSpace ↥U := isConnected_iff_connectedSpace.mp hV'c
  let Φ : ↥U → ℂ := fun z => Ψ z
  let zU : ↥U := ⟨z₀, hz₀⟩
  -- The chart of the `Opens` charted structure at `x` is the identity inclusion.
  have hchart : ∀ x : ↥U, (chartAt ℂ x) x = (x : ℂ) := by
    intro x
    show (chartAt ℂ x : OpenPartialHomeomorph ↥U ℂ) x = (x : ℂ)
    rw [TopologicalSpace.Opens.chartAt_eq]
    rfl
  -- Hence `Φ ∘ (chartAt ℂ x).symm` agrees near the base point with `Ψ`.
  have hev : ∀ x : ↥U, (Φ ∘ (chartAt ℂ x).symm : ℂ → ℂ) =ᶠ[𝓝 ((chartAt ℂ x) x)] Ψ := by
    intro x
    have h1 : (Subtype.val ∘ (chartAt ℂ x).symm : ℂ → ℂ)
        =ᶠ[𝓝 ((chartAt ℂ x) x)] (id : ℂ → ℂ) := by
      rw [hchart x]
      have h := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) U (x := x)
      rw [chartAt_self_eq] at h
      simpa using h.symm
    have h2 : (Φ ∘ (chartAt ℂ x).symm : ℂ → ℂ)
        = Ψ ∘ (Subtype.val ∘ (chartAt ℂ x).symm : ℂ → ℂ) := rfl
    rw [h2]
    exact h1.fun_comp Ψ |>.trans (by simp)
  have hmapsU : ∀ z : ↥U, Φ z ∈ Metric.ball (0 : ℂ) 1 := fun z => hmaps z z.2
  have hpropU : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 →
      IsCompact (Φ ⁻¹' K) := by
    intro K hK hKB
    have hset : Φ ⁻¹' K = (Subtype.val : ↥U → ℂ) ⁻¹' (V' ∩ Ψ ⁻¹' K) := by
      ext z; constructor
      · intro hz; exact ⟨z.2, hz⟩
      · intro hz; exact hz.2
    rw [hset]
    exact (Topology.IsInducing.isCompact_preimage_iff (Topology.IsInducing.subtypeVal)
      (K := V' ∩ Ψ ⁻¹' K) (by rintro z ⟨hzV, -⟩; exact ⟨⟨z, hzV⟩, rfl⟩)).2 (hprop K hK hKB)
  have hΦan : ∀ x : ↥U, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    intro x
    have h1 : AnalyticAt ℂ Ψ ((chartAt ℂ x) x) := by
      rw [hchart x]
      exact hΨ.analyticAt (hV'o.mem_nhds x.2)
    exact h1.congr (hev x).symm
  have hfibU : Φ ⁻¹' {0} = {zU} := by
    ext z; constructor
    · intro hz; exact Subtype.ext ((hfib z z.2).mp hz)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (hfib z₀ hz₀).mpr rfl
  have hlocU : deriv (Φ ∘ (chartAt ℂ zU).symm) ((chartAt ℂ zU) zU) ≠ 0 := by
    rw [(hev zU).deriv_eq, hchart zU]
    exact hloc
  have hbij := Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
    hmapsU hpropU hΦan hfibU hlocU
  -- Now turn the continuous bijection into a homeomorphism via properness.
  let f : ↥U → Metric.ball (0 : ℂ) 1 := fun z => ⟨Φ z, hmapsU z⟩
  have hcontΦ : Continuous Φ :=
    hΨ.continuousOn.comp_continuous continuous_subtype_val (fun z => z.2)
  have hcontf : Continuous f := hcontΦ.subtype_mk _
  have hproper : IsProperMap f := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hcontf, ?_⟩
    intro K hK
    have hset : f ⁻¹' K = Φ ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) '' K) := by
      ext z; constructor
      · intro hz; exact ⟨f z, hz, rfl⟩
      · rintro ⟨w, hwK, hw⟩
        have hzw : f z = w := Subtype.ext hw.symm
        show f z ∈ K
        rw [hzw]
        exact hwK
    rw [hset]
    exact hpropU _ (hK.image continuous_subtype_val)
      (by rintro w ⟨w', -, rfl⟩; exact w'.2)
  exact ⟨(Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed
    hproper.continuous hproper.isClosedMap⟩

end Work.BasinSC.StepOneCrit
