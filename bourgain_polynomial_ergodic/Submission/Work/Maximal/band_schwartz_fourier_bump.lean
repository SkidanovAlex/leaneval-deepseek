import Mathlib

/-!
# A band-limited Schwartz bump for the Fourier transform

For `0 < c0 < 1/2` there is a Schwartz function `ψ` whose Fourier transform equals `1` on the
band `[-c0, c0]` and vanishes outside the larger band `[-1/2, 1/2]`.

The construction is the standard one: take a smooth compactly supported bump function `χ`
which is identically `1` on `[-c0, c0]` and vanishes outside `[-1/2, 1/2]`, and let `ψ` be its
*inverse* Fourier transform.  Since `χ` is compactly supported and smooth, `ψ` is Schwartz
(Paley–Wiener), and Fourier inversion (`FourierInvPair.fourier_fourierInv_eq`) gives back
`𝓕 ψ = χ`, so `𝓕 ψ` has exactly the required pointwise values.
-/

namespace Work.Maximal

open scoped FourierTransform ContDiff
open MeasureTheory

/-- There is a Schwartz function on `ℝ` which is identically `1` on `[-c0, c0]` and vanishes
outside `[-1/2, 1/2]` (as soon as `0 < c0 < 1/2`).  The witness is the smooth bump of inner
radius `(c0 + 1/2)/2` and outer radius `1/2`. -/
lemma exists_schwartzMap_eq_one_band {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 < 1 / 2) :
    ∃ χ : SchwartzMap ℝ ℂ,
      (∀ ξ : ℝ, ξ ∈ Set.Icc (-c0) c0 → (χ : ℝ → ℂ) ξ = 1) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2 : ℝ)) (1/2) → (χ : ℝ → ℂ) ξ = 0) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨(c0 + 1/2)/2, 1/2, by linarith, by linarith⟩
  let χ : ℝ → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hχ_diff : ContDiff ℝ ∞ χ :=
    (Complex.ofRealCLM.contDiff (n := ∞)).comp (bump.contDiff (n := ⊤))
  have hχ_cs : HasCompactSupport χ :=
    bump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨hχ_cs.toSchwartzMap hχ_diff, ?_, ?_⟩
  · intro ξ hξ
    rw [HasCompactSupport.toSchwartzMap_toFun]
    change ((bump ξ : ℝ) : ℂ) = 1
    have hmem : ξ ∈ Metric.closedBall (0 : ℝ) bump.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have hr : bump.rIn = (c0 + 1/2)/2 := rfl
      rw [hr, sub_zero, abs_le]
      exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
    rw [bump.one_of_mem_closedBall hmem]
    norm_num
  · intro ξ hξ
    rw [HasCompactSupport.toSchwartzMap_toFun]
    change ((bump ξ : ℝ) : ℂ) = 0
    have hd : bump.rOut ≤ dist ξ 0 := by
      have hr : bump.rOut = 1/2 := rfl
      rw [hr, Real.dist_eq, sub_zero]
      by_contra h
      push Not at h
      rw [abs_lt] at h
      exact hξ ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [bump.zero_of_le_dist hd]
    norm_num

theorem band_schwartz_fourier_bump {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 < 1 / 2) :
    ∃ ψ : SchwartzMap ℝ ℂ,
      (∀ ξ ∈ Set.Icc (-c0) c0, FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 1) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2 : ℝ)) (1/2) → FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 0) := by
  obtain ⟨χ, hχ1, hχ0⟩ := exists_schwartzMap_eq_one_band hc0 hc01
  let ψ : SchwartzMap ℝ ℂ := 𝓕⁻ χ
  have hψeq : (𝓕 ψ : SchwartzMap ℝ ℂ) = χ := FourierInvPair.fourier_fourierInv_eq χ
  have hfun : FourierTransform.fourier (ψ : ℝ → ℂ) = ⇑χ := by
    have h' := congrArg (fun f : SchwartzMap ℝ ℂ => (f : ℝ → ℂ)) hψeq
    simpa only [SchwartzMap.fourier_coe] using h'
  refine ⟨ψ, ?_, ?_⟩
  · intro ξ hξ
    rw [congr_fun hfun ξ]
    exact hχ1 ξ hξ
  · intro ξ hξ
    rw [congr_fun hfun ξ]
    exact hχ0 ξ hξ

end Work.Maximal
