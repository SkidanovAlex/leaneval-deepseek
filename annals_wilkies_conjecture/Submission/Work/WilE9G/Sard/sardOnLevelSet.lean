import Mathlib
import Submission.Work.WilE9G.Sard.levelSetChartParam
import Submission.Work.WilE9G.Sard.sardAnalyticGeneral

namespace Work.WilE9G.Sard

open MeasureTheory
open scoped Topology

/-- For a linear map `S` onto a subspace `K` and a second linear map `T` defined on the big space,
`T ∘ S` is onto exactly when the restriction of `T` to `K` is onto. -/
lemma surjective_comp_iff {r Q n : ℕ} (S : (Fin r → ℝ) →L[ℝ] (Fin Q → ℝ))
    (T : (Fin Q → ℝ) →L[ℝ] (Fin n → ℝ)) (K : Submodule ℝ (Fin Q → ℝ)) (hS : S.range = K) :
    Function.Surjective (T.comp S) ↔ (∀ w : Fin n → ℝ, ∃ v ∈ K, T v = w) := by
  constructor
  · intro hs w
    obtain ⟨u, hu⟩ := hs w
    exact ⟨S u, by rw [← hS]; exact LinearMap.mem_range.mpr ⟨u, rfl⟩, hu⟩
  · intro hs w
    obtain ⟨v, hv, hTv⟩ := hs w
    rw [← hS] at hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    exact ⟨u, hTv⟩

theorem sardOnLevelSet {Q n j : ℕ} (h : (Fin Q → ℝ) → (Fin j → ℝ)) (F : (Fin Q → ℝ) → (Fin n → ℝ))
    (hh : ∀ x, AnalyticAt ℝ h x) (hF : ∀ x, AnalyticAt ℝ F x)
    (z₀ : Fin Q → ℝ) (hsurj : Function.Surjective (fderiv ℝ h z₀)) :
    ∃ (N : Set (Fin n → ℝ)) (U : Set (Fin Q → ℝ)), MeasureTheory.volume N = 0 ∧ U ∈ 𝓝 z₀ ∧
      ∀ z ∈ U, h z = h z₀ →
        (¬ ∀ w : Fin n → ℝ, ∃ v : Fin Q → ℝ, fderiv ℝ h z v = 0 ∧ fderiv ℝ F z v = w) →
        F z ∈ N := by
  classical
  -- Local analytic parametrisation `γ` of the level set `{h = h z₀}` near `z₀`, whose
  -- differential realises the tangent space `ker (fderiv ℝ h (γ t))` at every `t`.
  obtain ⟨r, γ, C, V, Uc, hVopen, hUcopen, h0V, hz₀U, hγ0, hγan, hγU, hγlvl, hCprop, hγker⟩ :=
    levelSetChartParam h z₀ hh hsurj
  -- A ball around `0` on which `γ` is analytic throughout.
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hγan.eventually_analyticAt
  set B : Set (Fin r → ℝ) := Metric.ball (0 : Fin r → ℝ) ρ ∩ V with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball.inter hVopen
  have h0B : (0 : Fin r → ℝ) ∈ B := ⟨Metric.mem_ball_self hρpos, h0V⟩
  have hBan : ∀ t ∈ B, AnalyticAt ℝ γ t := fun t ht => hρsub ht.1
  -- The restricted parametrisation, with its critical values.
  let f : (Fin r → ℝ) → (Fin n → ℝ) := F ∘ γ
  have hf_an : AnalyticOn ℝ f B := by
    intro t ht
    exact ((hF (γ t)).comp (hBan t ht)).analyticWithinAt
  have hvol : MeasureTheory.volume (f '' ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ B)) = 0 :=
    sardAnalyticGeneral f hBopen hf_an
  refine ⟨f '' ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ B),
    Uc ∩ {y | C (y - z₀) ∈ B}, hvol, ?_, ?_⟩
  · -- `U` is a neighbourhood of `z₀`.
    refine IsOpen.mem_nhds ?_ ?_
    · exact hUcopen.inter (hBopen.preimage (C.continuous.comp (continuous_id.sub continuous_const)))
    · refine ⟨hz₀U, ?_⟩
      simpa using h0B
  · intro z hzU hzlvl hbad
    obtain ⟨hzUc, hzB⟩ := hzU
    -- `z` is recovered from the chart as `γ (C (z - z₀))`.
    obtain ⟨htV, hγt⟩ := hCprop z hzUc hzlvl
    have ht_an : AnalyticAt ℝ γ (C (z - z₀)) := hBan _ hzB
    -- Chain rule along the parametrisation.
    have hchain : fderiv ℝ f (C (z - z₀))
        = (fderiv ℝ F (γ (C (z - z₀)))).comp (fderiv ℝ γ (C (z - z₀))) := by
      have h1 : HasFDerivAt (fun s : Fin r → ℝ => F (γ s))
          ((fderiv ℝ F (γ (C (z - z₀)))).comp (fderiv ℝ γ (C (z - z₀)))) (C (z - z₀)) :=
        ((hF (γ (C (z - z₀)))).differentiableAt.hasFDerivAt).comp (C (z - z₀))
          (ht_an.differentiableAt.hasFDerivAt)
      exact h1.fderiv
    have hbad' : ¬ ∀ w : Fin n → ℝ, ∃ v : Fin Q → ℝ,
        fderiv ℝ h (γ (C (z - z₀))) v = 0 ∧ fderiv ℝ F (γ (C (z - z₀))) v = w := by
      rw [hγt]; exact hbad
    -- Badness of `z` is exactly criticality of the parametrised map at `C (z - z₀)`.
    have hequiv : Function.Surjective (fderiv ℝ f (C (z - z₀))) ↔
        (∀ w : Fin n → ℝ, ∃ v : Fin Q → ℝ,
          fderiv ℝ h (γ (C (z - z₀))) v = 0 ∧ fderiv ℝ F (γ (C (z - z₀))) v = w) := by
      rw [hchain]
      rw [surjective_comp_iff (fderiv ℝ γ (C (z - z₀))) (fderiv ℝ F (γ (C (z - z₀))))
        ((fderiv ℝ h (γ (C (z - z₀)))).ker) (hγker (C (z - z₀)) htV)]
      constructor
      · rintro hb w
        obtain ⟨v, hv, hTv⟩ := hb w
        exact ⟨v, LinearMap.mem_ker.mp hv, hTv⟩
      · rintro hb w
        obtain ⟨v, hv, hTv⟩ := hb w
        exact ⟨v, LinearMap.mem_ker.mpr hv, hTv⟩
    have hnot : ¬ Function.Surjective (fderiv ℝ f (C (z - z₀))) := fun hs => hbad' (hequiv.mp hs)
    have hfz : f (C (z - z₀)) = F z := by
      show (F ∘ γ) (C (z - z₀)) = F z
      rw [Function.comp_apply, hγt]
    rw [← hfz]
    exact ⟨C (z - z₀), ⟨hnot, hzB⟩, rfl⟩

end Work.WilE9G.Sard
