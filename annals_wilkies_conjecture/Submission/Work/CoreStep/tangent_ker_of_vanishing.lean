import Mathlib
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange

namespace Work.CoreStep

open scoped Topology
open Filter

/-- The level-set chart `γ` of `F` at `z` (from `analyticLevelSetChartRange`) parametrises the
fibre of `F` through `z` by the kernel of `F'(z)`.  Along any curve `t ↦ γ (t • w)` lying in the
fibre, `P` holds near `t = 0`, hence `G` vanishes there, so the derivative of `G` along the curve
vanishes.  Taking `w` with `γ'(0) w = v` gives `G' v = 0` for every `v ∈ ker F'(z)`. -/
theorem tangent_ker_of_vanishing {m c d : ℕ}
    (F : (Fin m → ℝ) → (Fin c → ℝ)) (z : Fin m → ℝ)
    (hFan : ∀ p, AnalyticAt ℝ F p) (hsurj : (fderiv ℝ F z).range = ⊤)
    (P : (Fin m → ℝ) → Prop)
    (hP : Filter.Eventually (fun y => F y = F z → P y) (nhds z))
    (G : (Fin m → ℝ) → (Fin d → ℝ)) (G' : (Fin m → ℝ) →L[ℝ] (Fin d → ℝ))
    (hG : HasFDerivAt G G' z) (hGvanish : ∀ y, P y → G y = 0) :
    ∀ v : Fin m → ℝ, (fderiv ℝ F z) v = 0 → G' v = 0 := by
  intro v hv
  -- A local chart of the level set `F = F z` through `z`, parametrised by `ker F'(z)`.
  obtain ⟨γ, V, U, χ, hVopen, hUopen, h0V, hzU, hγ0, hγan, hγVU, hγF, hcover, hinj,
    hγrange, hχan, hχprop⟩ :=
    Work.WilE7.Nondrop.analyticLevelSetChartRange F z hFan hsurj
  have hvker : v ∈ (fderiv ℝ F z).ker := by
    rw [LinearMap.mem_ker]; exact hv
  -- `v` is in the range of the chart's derivative, so it is the velocity of a curve in the fibre.
  have hvrange : v ∈ (fderiv ℝ γ 0).range := by
    rw [hγrange]; exact hvker
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hvrange
  have hw' : (fderiv ℝ γ 0) w = v := hw
  -- The parameter curve `t ↦ t • w` in `ker F'(z)`.
  set S : ℝ →L[ℝ] (fderiv ℝ F z).ker :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w with hS
  have hσ : HasFDerivAt (fun t : ℝ => t • w) S 0 := by
    have h := S.hasFDerivAt (x := (0 : ℝ))
    have hfun : (⇑S : ℝ → (fderiv ℝ F z).ker) = fun t => t • w := by
      funext t; simp [hS, ContinuousLinearMap.smulRight_apply]
    simpa [hfun] using h
  have hS1 : S 1 = w := by simp [hS]
  have hγ' : HasFDerivAt γ (fderiv ℝ γ 0) 0 := hγan.differentiableAt.hasFDerivAt
  have hγ'at : HasFDerivAt γ (fderiv ℝ γ 0) ((fun t : ℝ => t • w) 0) := by
    simpa using hγ'
  have hηγ : HasFDerivAt (fun t : ℝ => γ (t • w)) ((fderiv ℝ γ 0) ∘SL S) 0 := by
    have h := hγ'at.comp 0 hσ
    simpa only [Function.comp_def] using h
  have hη1 : (fderiv ℝ (fun t : ℝ => γ (t • w)) 0) 1 = v := by
    rw [hηγ.fderiv, ContinuousLinearMap.comp_apply, hS1]
    exact hw'
  -- The curve stays in the fibre near `0`, so `P` and then `G = 0` hold there.
  have hσcont : Continuous (fun t : ℝ => t • w) := continuous_id.smul continuous_const
  have htend0 : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
    have := hσcont.continuousAt (x := (0 : ℝ))
    simpa using this.tendsto
  have hγtend : Tendsto γ (𝓝 0) (𝓝 z) := by
    have := hγan.continuousAt (x := (0 : (fderiv ℝ F z).ker))
    simpa [hγ0] using this.tendsto
  have hηtend : Tendsto (fun t : ℝ => γ (t • w)) (𝓝 0) (𝓝 z) := by
    have := hγtend.comp htend0
    simpa only [Function.comp_def] using this
  have hσV : ∀ᶠ t in 𝓝 (0 : ℝ), t • w ∈ V :=
    htend0.eventually (hVopen.mem_nhds h0V)
  have hFzev : ∀ᶠ t in 𝓝 (0 : ℝ), F (γ (t • w)) = F z :=
    hσV.mono (fun t ht => hγF (t • w) ht)
  have hPev : ∀ᶠ t in 𝓝 (0 : ℝ), P (γ (t • w)) := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), (F (γ (t • w)) = F z → P (γ (t • w))) :=
      hηtend.eventually hP
    exact (h1.and hFzev).mono (fun t ht => ht.1 ht.2)
  have hGev : ∀ᶠ t in 𝓝 (0 : ℝ), G (γ (t • w)) = 0 :=
    hPev.mono (fun t ht => hGvanish _ ht)
  have hkeq : (fun t : ℝ => G (γ (t • w))) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : Fin d → ℝ)) := hGev
  have hk0 : fderiv ℝ (fun t : ℝ => G (γ (t • w))) 0 = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hkeq]
    exact congr_fun (fderiv_const (𝕜 := ℝ) (0 : Fin d → ℝ)) 0
  -- Chain rule: the derivative of `G` along the curve at `t = 0` is `G' v`.
  have hGat : HasFDerivAt G G' ((fun t : ℝ => γ (t • w)) 0) := by
    simpa [hγ0] using hG
  have hηγ' : HasFDerivAt (fun t : ℝ => γ (t • w))
      (fderiv ℝ (fun t : ℝ => γ (t • w)) 0) 0 := by
    rw [hηγ.fderiv]; exact hηγ
  have hkcomp : HasFDerivAt (fun t : ℝ => G (γ (t • w)))
      (G' ∘SL fderiv ℝ (fun t : ℝ => γ (t • w)) 0) 0 := by
    have h := hGat.comp 0 hηγ'
    simpa only [Function.comp_def] using h
  have hkfderiv : fderiv ℝ (fun t : ℝ => G (γ (t • w))) 0
      = G' ∘SL fderiv ℝ (fun t : ℝ => γ (t • w)) 0 := hkcomp.fderiv
  have hone : (G' ∘SL fderiv ℝ (fun t : ℝ => γ (t • w)) 0) 1 = G' v := by
    rw [ContinuousLinearMap.comp_apply, hη1]
  calc G' v = (G' ∘SL fderiv ℝ (fun t : ℝ => γ (t • w)) 0) 1 := hone.symm
    _ = (fderiv ℝ (fun t : ℝ => G (γ (t • w))) 0) 1 := by rw [hkfderiv]
    _ = 0 := by rw [hk0]; rfl

end Work.CoreStep
