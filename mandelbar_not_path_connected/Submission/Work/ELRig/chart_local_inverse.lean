import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic
import Submission.Work.ELRig.analyticOnNhd_invFunOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set Metric
open scoped Topology

variable {c : ℂ}

/-- Off the filled Julia set, the dynamical Böttcher coordinate `dynPhi c φ` is analytic: there it
agrees with the Böttcher coordinate `φ`, which is analytic on the escape set
(`Work.ELRig.analyticOnNhd_dynBottcher`). -/
theorem analyticAt_dynPhi_of_notMem_K {φ : ℂ → ℂ} (hb : Work.ParamRays.IsDynBottcher c φ)
    {z : ℂ} (hz : z ∉ Work.EL.K c) : AnalyticAt ℂ (Work.EL.dynPhi c φ) z := by
  have hφ : AnalyticAt ℂ φ z :=
    analyticOnNhd_dynBottcher hb z (mem_EscapeSet_iff_notMem_K.mpr hz)
  refine hφ.congr ?_
  filter_upwards [(Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hz] with w hw
  exact (Work.EL.dynPhi_of_notMem hw).symm

variable {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
variable {L : Work.ELRig.RayCylLift d fl}
variable {s₀ : ℝ}

/-- The straightening chart of the ray `R(α₁)` is analytic at the point `p = L.γ₁ s₀` of the lift:
there `Ψ p` lies outside the filled Julia set, so `dynPhi c d.φ` agrees with the analytic Böttcher
coordinate `d.φ` on a neighbourhood of `Ψ p`.  (No hypothesis on `p` beyond being on the lift is
needed.) -/
theorem analyticAt_sideFlipChart (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (s₀ : ℝ) :
    AnalyticAt ℂ (sideFlipChart c d fl L s₀) (L.γ₁ s₀) := by
  have hq : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]
    exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  have h1 : AnalyticAt ℂ (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s₀)) :=
    analyticAt_dynPhi_of_notMem_K d.bottcher hq
  have h2 : AnalyticAt ℂ (fun w => Work.EL.dynPhi c d.φ (fl.Ψ w)) (L.γ₁ s₀) :=
    h1.comp (fl.Ψ_diff.analyticAt (L.γ₁ s₀))
  exact h2.div_const (c := Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀))

/-- **The analytic inverse function theorem at a point, with both inverse identities.**

If `f` is analytic at `x` and injective on some ball around `x`, then there are radii `δ₁, δ₂ > 0`
and a function `σ`, analytic on the ball `ball (f x) δ₂`, which is a *two-sided* local inverse of
`f` there: `f (σ z) = z` on `ball (f x) δ₂` and `σ (f w) = w` on `ball x δ₁`; moreover
`deriv σ (f x) ≠ 0`.

The analyticity comes from `Work.ELRig.exists_analytic_localInverse_of_injOn` applied to a ball on
which `f` is analytic and injective (`AnalyticAt.exists_ball_analyticOnNhd`); the second inverse
identity is then a consequence of the injectivity of `f` on that ball. -/
theorem exists_localInverse_of_analyticAt {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hinj : ∃ ρ > 0, Set.InjOn f (Metric.ball x ρ)) :
    ∃ δ₁ > 0, ∃ δ₂ > 0, ∃ σ : ℂ → ℂ,
      AnalyticOnNhd ℂ σ (Metric.ball (f x) δ₂) ∧
      (∀ z ∈ Metric.ball (f x) δ₂, f (σ z) = z) ∧
      (∀ w ∈ Metric.ball x δ₁, σ (f w) = w) ∧
      deriv σ (f x) ≠ 0 := by
  obtain ⟨ρ, hρpos, hinjρ⟩ := hinj
  obtain ⟨r, hrpos, hran⟩ := hf.exists_ball_analyticOnNhd
  have hminpos : 0 < min ρ r := lt_min hρpos hrpos
  have hUopen : IsOpen (Metric.ball x (min ρ r)) := Metric.isOpen_ball
  have hxU : x ∈ Metric.ball x (min ρ r) := Metric.mem_ball_self hminpos
  have hUan : AnalyticOnNhd ℂ f (Metric.ball x (min ρ r)) :=
    hran.mono (Metric.ball_subset_ball (min_le_right ρ r))
  have hUinj : Set.InjOn f (Metric.ball x (min ρ r)) :=
    hinjρ.mono (Metric.ball_subset_ball (min_le_left ρ r))
  obtain ⟨δ₂, hδ₂pos, σ, hσan, hσright, hσmem, hσderiv⟩ :=
    exists_analytic_localInverse_of_injOn hUopen hUan hUinj hxU
  have hpre : f ⁻¹' Metric.ball (f x) δ₂ ∈ 𝓝 x :=
    hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (f x) hδ₂pos)
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hpre (hUopen.mem_nhds hxU))
  refine ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, σ, hσan, hσright, ?_, hσderiv⟩
  intro w hw
  have h1 : w ∈ Metric.ball x (min ρ r) := (hδ₁sub hw).2
  have h2 : f w ∈ Metric.ball (f x) δ₂ := (hδ₁sub hw).1
  exact hUinj (hσmem _ h2) h1 (hσright _ h2)

theorem chart_local_inverse {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ δ₁ > 0, ∃ δ₂ > 0, ∃ k : ℂ → ℂ,
      AnalyticOnNhd ℂ k (Metric.ball 1 δ₂) ∧
      (∀ z ∈ Metric.ball 1 δ₂, Work.ELRig.sideFlipChart c d fl L s₀ (k z) = z) ∧
      (∀ w ∈ Metric.ball (L.γ₁ s₀) δ₁, k (Work.ELRig.sideFlipChart c d fl L s₀ w) = w) ∧
      deriv k 1 ≠ 0 := by
  have han : AnalyticAt ℂ (sideFlipChart c d fl L s₀) (L.γ₁ s₀) :=
    analyticAt_sideFlipChart d fl L s₀
  obtain ⟨ρ, hρpos, hρsub⟩ :=
    exists_ball_sideFlip (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) hre
  have hinj : Set.InjOn (sideFlipChart c d fl L s₀) (Metric.ball (L.γ₁ s₀) ρ) :=
    fun a ha b hb hab => sideFlipChart_injOn (hρsub ha) (hρsub hb) hab
  obtain ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, k, hkan, hkright, hkleft, hkderiv⟩ :=
    exists_localInverse_of_analyticAt han ⟨ρ, hρpos, hinj⟩
  have hp : sideFlipChart c d fl L s₀ (L.γ₁ s₀) = 1 := sideFlipChart_at_p
  exact ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, k, by simpa only [hp] using hkan,
    by simpa only [hp] using hkright, hkleft, by simpa only [hp] using hkderiv⟩

end Work.ELRig
