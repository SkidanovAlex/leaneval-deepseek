import Mathlib
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# Sections of holomorphic coverings (Lemma 6.2 support)

If `X ⊆ ℂ` is open, `p : ℂ → ℂ` is holomorphic on `X` and `(fun z : X => p z)` is a covering map
on an open simply connected `Y ⊆ ℂ`, then the covering admits a global holomorphic section through
any prescribed point `x₀ ∈ X` above `y₀ ∈ Y`.

The proof has two parts:

* `IsCoveringMapOn.existsUnique_continuousMap_lifts` produces the continuous section `F : Y → X`
  (using `SimplyConnectedSpace Y` and `LocallyPathConnectedSpace Y`, the latter from
  `IsOpen.locallyPathConnectedSpace`).
* The section is holomorphic.  A covering map is a local homeomorphism, so on a small ball around
  `s y` the map `p` is injective; hence `deriv p (s y) ≠ 0`
  (`Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`) and `analyticAt_comp_iff_of_deriv_ne_zero`
  transfers analyticity of `id =ᶠ s ∘ p` to analyticity of `s`.
-/

namespace Work.L62

open Complex Set Metric Filter Topology

/-- If `p` is analytic at `x` with nonvanishing derivative, and `s` is a local right inverse of
`p` near `x`, then `s` is analytic at `p x`. -/
theorem analyticAt_of_comp_eventuallyEq_id {p s : ℂ → ℂ} {x : ℂ}
    (hp : AnalyticAt ℂ p x) (hd : deriv p x ≠ 0) (h : ∀ᶠ z in 𝓝 x, s (p z) = z) :
    AnalyticAt ℂ s (p x) :=
  (analyticAt_comp_iff_of_deriv_ne_zero hp hd).mp
    (analyticAt_id.congr (h.mono fun _ hz => hz.symm))

/-- A covering map of an open subset of `ℂ` is injective near every point of its domain. -/
theorem injOn_ball_of_covering {X Y : Set ℂ} (hXo : IsOpen X) {p : ℂ → ℂ}
    (hcov : IsCoveringMapOn (fun z : X => p z) Y) {x : ℂ} (hx : x ∈ X) (hpxY : p x ∈ Y) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ X ∧ Set.InjOn p (Metric.ball x r) := by
  obtain ⟨e, hxe, he⟩ := hcov.isLocalHomeomorphOn (⟨x, hx⟩ : X) (by simpa using hpxY)
  have hSopen : IsOpen (Subtype.val '' e.source) :=
    (hXo.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen).mp e.open_source
  have hxS : x ∈ Subtype.val '' e.source := ⟨⟨x, hx⟩, hxe, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds hxS)
  refine ⟨r, hr, fun z hz => ?_, ?_⟩
  · obtain ⟨w, -, hwz⟩ := hball hz
    exact hwz ▸ w.2
  · intro z₁ hz₁ z₂ hz₂ hpz
    obtain ⟨w₁, hw₁, hwz₁⟩ := hball hz₁
    obtain ⟨w₂, hw₂, hwz₂⟩ := hball hz₂
    have he1 : e w₁ = p (w₁ : ℂ) := (congr_fun he w₁).symm
    have he2 : e w₂ = p (w₂ : ℂ) := (congr_fun he w₂).symm
    have h1 : e w₁ = e w₂ := by rw [he1, he2, hwz₁, hwz₂, hpz]
    have h2 : w₁ = w₂ := e.injOn hw₁ hw₂ h1
    rw [← hwz₁, ← hwz₂, h2]

/-- **Sections of holomorphic coverings.**  Let `X ⊆ ℂ` be open, `p : ℂ → ℂ` holomorphic on `X`,
and let `(fun z : X => p z)` be a covering map on an open simply connected `Y ⊆ ℂ`.  Then for any
`x₀ ∈ X` above `y₀ ∈ Y` there is a holomorphic section `s` of `p` over `Y` with `s y₀ = x₀`. -/
theorem lift_section {X : Set ℂ} (hXo : IsOpen X)
    {p : ℂ → ℂ} (hp : DifferentiableOn ℂ p X)
    {Y : Set ℂ} (hYo : IsOpen Y) (hYsc : SimplyConnectedSpace Y)
    (hcov : IsCoveringMapOn (fun z : X => p z) Y)
    {y₀ : ℂ} (hy₀ : y₀ ∈ Y) {x₀ : ℂ} (hx₀ : x₀ ∈ X) (hp₀ : p x₀ = y₀) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s Y ∧ s y₀ = x₀ ∧ ∀ y ∈ Y, s y ∈ X ∧ p (s y) = y := by
  classical
  let : SimplyConnectedSpace Y := hYsc
  let : LocallyPathConnectedSpace Y := hYo.locallyPathConnectedSpace
  obtain ⟨F, hF⟩ := (hcov.existsUnique_continuousMap_lifts
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Y, ℂ))
      (a₀ := (⟨y₀, hy₀⟩ : Y)) (e₀ := (⟨x₀, hx₀⟩ : X))
      (by simpa using hp₀) (fun a => a.2)).exists
  let s : ℂ → ℂ := fun y => if h : y ∈ Y then (F ⟨y, h⟩ : ℂ) else 0
  have hsval : ∀ (y : ℂ) (hy : y ∈ Y), s y = (F ⟨y, hy⟩ : ℂ) := by
    intro y hy
    dsimp only [s]
    exact dite_eq_left hy
  have hsp : ∀ (y : ℂ) (hy : y ∈ Y), p (s y) = y := by
    intro y hy
    rw [hsval y hy]
    simpa using congr_fun hF.2 (⟨y, hy⟩ : Y)
  have hsmem : ∀ (y : ℂ) (hy : y ∈ Y), s y ∈ X := by
    intro y hy
    rw [hsval y hy]
    exact (F ⟨y, hy⟩).2
  refine ⟨s, ?_, ?_, fun y hy => ⟨hsmem y hy, hsp y hy⟩⟩
  · intro y hy
    set x : ℂ := s y with hxdef
    have hxX : x ∈ X := hsmem y hy
    have hpx : p x = y := hsp y hy
    obtain ⟨r, hr, -, hinj⟩ := injOn_ball_of_covering hXo hcov hxX (by rw [hpx]; exact hy)
    have hana : AnalyticAt ℂ p x := hp.analyticAt (hXo.mem_nhds hxX)
    have hd : deriv p x ≠ 0 :=
      Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr hana hinj
    have hcX : X ∈ 𝓝 x := hXo.mem_nhds hxX
    have hcp : ContinuousAt p x := hp.continuousOn.continuousAt hcX
    have hYnhds : Y ∈ 𝓝 (p x) := by rw [hpx]; exact hYo.mem_nhds hy
    have hpy : ∀ᶠ z in 𝓝 x, p z ∈ Y := hcp.preimage_mem_nhds hYnhds
    have hbx : ∀ᶠ z in 𝓝 x, z ∈ Metric.ball x r := Metric.ball_mem_nhds x hr
    have hHball : Subtype.val ⁻¹' Metric.ball x r ∈ 𝓝 (⟨x, hxX⟩ : X) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds x hr)
    have hFy : F ⟨y, hy⟩ = (⟨x, hxX⟩ : X) := by
      apply Subtype.ext
      exact ((hsval y hy).symm.trans hxdef.symm)
    have hFballT : (F ⁻¹' (Subtype.val ⁻¹' Metric.ball x r)) ∈ 𝓝 (⟨y, hy⟩ : Y) := by
      have h1 : ContinuousAt (⇑F) (⟨y, hy⟩ : Y) := F.continuous.continuousAt
      have hHball' : Subtype.val ⁻¹' Metric.ball x r ∈ 𝓝 (F ⟨y, hy⟩) := by rwa [hFy]
      exact h1.preimage_mem_nhds hHball'
    have hFball' : Subtype.val '' (F ⁻¹' (Subtype.val ⁻¹' Metric.ball x r)) ∈ 𝓝 (p x) := by
      have h2 : Subtype.val '' (F ⁻¹' (Subtype.val ⁻¹' Metric.ball x r)) ∈ 𝓝 y :=
        hYo.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hFballT
      rwa [hpx]
    have h3 : ∀ᶠ z in 𝓝 x, p z ∈ Subtype.val '' (F ⁻¹' (Subtype.val ⁻¹' Metric.ball x r)) :=
      hcp.preimage_mem_nhds hFball'
    have hev : ∀ᶠ z in 𝓝 x, s (p z) = z := by
      filter_upwards [hpy, h3, hbx] with z hzY hzF hzball
      obtain ⟨w, hwF, hwz⟩ := hzF
      rw [hsval (p z) hzY, ← (Subtype.ext hwz : w = (⟨p z, hzY⟩ : Y))]
      have hwF' : p (F w : ℂ) = p z := by
        rw [show p (↑(F w) : ℂ) = (↑w : ℂ) from by simpa using congr_fun hF.2 w, hwz]
      exact (hinj hzball hwF hwF'.symm).symm
    have hfin : AnalyticAt ℂ s y := by
      rw [← hpx]
      exact analyticAt_of_comp_eventuallyEq_id hana hd hev
    exact hfin.differentiableAt.differentiableWithinAt
  · simp [hsval y₀ hy₀, hF.1]

end Work.L62
