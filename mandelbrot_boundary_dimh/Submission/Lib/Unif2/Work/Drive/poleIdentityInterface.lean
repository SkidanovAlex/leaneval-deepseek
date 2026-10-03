import Mathlib
import Submission.Lib.Unif2.Work.Drive.greenPoleValue
import Submission.Lib.Unif2.Work.Kernel.pairing_pole_smooth
import Submission.Lib.Unif2.Work.Kernel.pairingPoleTools
import Submission.Lib.Unif2.Work.Drive.greenCoverSwap
import Submission.Lib.Unif2.Work.Drive.chartDiff_update_of_notMem

/-!
# The pole identity for a Green function, with the expansion produced from `IsGreenOn`

`Work.Kernel.pairing_pole_smooth` is the pole identity

`pairing E.y E.ρ E.σ E.ψ gA Ψ = 2π Ψ a`

for a chart-`C¹` test function `Ψ` with `tsupport Ψ ⊆ K`, under the hypotheses that `gA` is the Green
function of `Ω` at `a`, that its chart representative in the cover's pole chart has the logarithmic
expansion `-log ‖· - p‖ + H` on a ball, and the `C¹` facts of the cover weights.

This file removes the *expansion* hypothesis: it is produced from `IsGreenOn` by
`Work.Kernel.exists_logExpansion_poleChart`, and the only remaining technicality is that the expansion
is an equality *off* the pole, while `pairing_pole_smooth` asks for it at every point of the ball
(where, at the centre, it pins the value of `gA` at its own pole).  That value is free: we pass to
`Function.update gA a (H p)`, which is again a Green function at `a` (`IsGreenOn.update` below) and
whose pairing equals that of `gA` (`Work.Drive.pairing_update_eq`).

With `Work.Kernel.GreenCover.swap` this gives the pole identity at *both* poles of the same cover:
apply it to `E` with `gA`, and to `E.swap` with `gB`.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **The value of a Green function at its own pole is free.**  `IsGreenOn` never mentions the value
at the pole, so it may be replaced by any real number. -/
theorem IsGreenOn.update [DecidableEq X] {Ω : Set X} {a : X} (haΩ : a ∈ Ω) {G : X → ℝ} (M : ℝ)
    (hG : IsGreenOn Ω a G) : IsGreenOn Ω a (Function.update G a M) := by
  obtain ⟨hpos, hharm, hdec, hpole⟩ := hG
  have hEq : ∀ x ∈ Ω, x ≠ a → Function.update G a M x = G x := fun x _ hx =>
    Function.update_of_ne hx M G
  refine ⟨fun x hx hxa => ?_, ?_, ?_, ?_⟩
  · rw [hEq x hx hxa]; exact hpos x hx hxa
  · intro x hx
    have hxa : x ≠ a := fun h => hx.2 (by simpa [h])
    have hsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hU : (chartAt ℂ x).source \ {a} ∈ 𝓝 x :=
      ((chartAt ℂ x).open_source.sdiff isClosed_singleton).mem_nhds
        ⟨hsrc, by simpa using hxa⟩
    have himg : (chartAt ℂ x) '' ((chartAt ℂ x).source \ {a}) ∈ 𝓝 ((chartAt ℂ x) x) :=
      (chartAt ℂ x).image_mem_nhds hsrc hU
    have hev : ((Function.update G a M) ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝 ((chartAt ℂ x) x)] (G ∘ (chartAt ℂ x).symm) := by
      filter_upwards [himg] with z hz
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).left_inv hy.1]
      exact Function.update_of_ne (by simpa [Set.mem_singleton_iff] using hy.2) M G
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr (hharm x hx)
  · intro ε hε
    obtain ⟨K, hKc, hKΩ, hKlt⟩ := hdec ε hε
    refine ⟨K ∪ {a}, hKc.union isCompact_singleton, ?_, ?_⟩
    · rintro x (hx | hx)
      · exact hKΩ hx
      · rw [Set.mem_singleton_iff] at hx; exact hx ▸ haΩ
    · intro x hxΩ hxK
      have hxa : x ≠ a := fun h => hxK (Or.inr (by simpa [h]))
      rw [hEq x hxΩ hxa]
      exact hKlt x hxΩ fun hxK' => hxK (Or.inl hxK')
  · obtain ⟨C, V, hV, hb⟩ := hpole
    refine ⟨C, V, hV, fun x hxV hxΩ hxa => ?_⟩
    rw [hEq x hxΩ hxa]
    exact hb x hxV hxΩ hxa

end Work.SimplyConnected.ABS

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The pole identity, with the logarithmic expansion produced from `IsGreenOn`.** -/
theorem pairing_pole_of_isGreenOn {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) (hya : E.y E.ia = a) (hKc : IsCompact K) (haK : a ∈ K)
    (hΩo : IsOpen Ω) (hKΩ : K ⊆ Ω) {gA : X → ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA) (haΩ : a ∈ Ω)
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hβc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.β i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {Ψ : X → ℝ}
    (hΨdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) Ψ Ω)
    (hΨc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hΨK : tsupport Ψ ⊆ K) (hΨΩ : tsupport Ψ ⊆ Ω) :
    Work.Drive.pairing E.y E.ρ E.σ E.ψ gA Ψ = 2 * Real.pi * Ψ a := by
  classical
  -- cover data
  have hρpos : 0 < E.ρ E.ia := lt_trans (lt_trans (E.hspos E.ia) (E.hsσ E.ia)) (E.hσρ E.ia)
  have htgt : Metric.ball ((chartAt ℂ (E.y E.ia)) (E.y E.ia)) (E.ρ E.ia)
      ⊆ (chartAt ℂ (E.y E.ia)).target := E.htgt E.ia
  have hpmem : (chartAt ℂ (E.y E.ia)) a ∈
      Metric.ball ((chartAt ℂ (E.y E.ia)) (E.y E.ia)) (E.ρ E.ia) := by
    have hs : dist ((chartAt ℂ (E.y E.ia)) a) ((chartAt ℂ (E.y E.ia)) (E.y E.ia))
        < E.s E.ia := Metric.mem_ball.mp E.ha_mem.2
    rw [Metric.mem_ball]
    exact lt_trans (lt_trans hs (E.hsσ E.ia)) (E.hσρ E.ia)
  -- the logarithmic expansion of `gA` at its pole, in the cover's pole chart
  obtain ⟨r₀, hr₀, H, hH₀, hexp₀⟩ :=
    exists_logExpansion_poleChart (x := a) hΩo haΩ hgA.2.1 hgA.2.2.2
  -- the ball on which (P) is applied
  set r : ℝ := min r₀ (E.ρ E.ia) with hrdef
  have hrpos : 0 < r := lt_min hr₀ hρpos
  have hrρ : r ≤ E.ρ E.ia := min_le_right _ _
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  -- the two centres agree, so the cover's pole ball is the expansion's ball
  have hsub : Metric.ball ((chartAt ℂ (E.y E.ia)) a) r
      ⊆ Metric.ball ((chartAt ℂ (E.y E.ia)) (E.y E.ia)) (E.ρ E.ia) := by
    rw [hya]
    exact Metric.ball_subset_ball hrρ
  -- the expansion, in the cover's pole chart
  have hexp : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ia)) a) r₀, z ≠ (chartAt ℂ (E.y E.ia)) a →
      gA ((chartAt ℂ (E.y E.ia)).symm z) = -Real.log ‖z - (chartAt ℂ (E.y E.ia)) a‖ + H z := by
    rw [hya]
    exact hexp₀
  have hH : InnerProductSpace.HarmonicOnNhd H
      (Metric.ball ((chartAt ℂ (E.y E.ia)) a) r) := by
    rw [hya]
    exact fun z hz => hH₀ z (Metric.ball_subset_ball hrr₀ hz)
  -- the value of `gA` at its pole, adjusted so that the expansion holds there too
  have hsrc : a ∈ (chartAt ℂ (E.y E.ia)).source := by rw [hya]; exact mem_chart_source ℂ a
  have hleft : (chartAt ℂ (E.y E.ia)).symm ((chartAt ℂ (E.y E.ia)) a) = a := by
    rw [hya]; exact (chartAt ℂ a).left_inv (mem_chart_source ℂ a)
  set M : ℝ := H ((chartAt ℂ (E.y E.ia)) a) with hMdef
  have hupd : Work.SimplyConnected.ABS.IsGreenOn Ω a (Function.update gA a M) :=
    Work.SimplyConnected.ABS.IsGreenOn.update haΩ M hgA
  have hueq : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ia)) a) r,
      Function.update gA a M ((chartAt ℂ (E.y E.ia)).symm z)
        = -Real.log ‖z - (chartAt ℂ (E.y E.ia)) a‖ + H z := by
    intro z hz
    by_cases hzc : z = (chartAt ℂ (E.y E.ia)) a
    · subst hzc
      rw [hleft]
      simp [Function.update, hMdef]
    · have hyne : (chartAt ℂ (E.y E.ia)).symm z ≠ a := by
        intro hcon
        have h1 : (chartAt ℂ (E.y E.ia)) ((chartAt ℂ (E.y E.ia)).symm z)
            = (chartAt ℂ (E.y E.ia)) a := congrArg _ hcon
        rw [(chartAt ℂ (E.y E.ia)).right_inv (htgt (hsub hz))] at h1
        exact hzc h1
      rw [Function.update_of_ne hyne M gA]
      exact hexp z (Metric.ball_subset_ball hrr₀ hz) hzc
  -- the chart differentiability of `gA` on `Ω ∖ {a,b}`, for the adjusted function
  have hgAdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k))
      (Function.update gA a M) (Ω \ ({a, b} : Set X)) :=
    fun k => Work.Drive.chartDiff_update_of_notMem (by simp) (chartDiff_of_isGreenOn hgA (E.y k))
  -- (P) for the adjusted function
  have hP := Work.Kernel.pairing_pole_smooth (E := E) (hKc := hKc) (haK := haK) (hΩo := hΩo)
    (hKΩ := hKΩ) (hgA := hupd) (hgAdiff := hgAdiff) (hrpos := hrpos) (hrρ := hrρ)
    (hpmem := hpmem) (hH := hH) (hueq := hueq) (hψc1 := hψc1) (hβc1 := hβc1)
    (hΨdiff := hΨdiff) (hΨc1 := hΨc1) (hΨK := hΨK) (hΨΩ := hΨΩ)
  rw [← Work.Drive.pairing_update_eq (y := E.y) (ρ := E.ρ) (σ := E.σ) (ψ := E.ψ)
    (u := gA) (q := a) (c := M) (χ := Ψ) E.htgt]
  exact hP

end Work.Kernel
