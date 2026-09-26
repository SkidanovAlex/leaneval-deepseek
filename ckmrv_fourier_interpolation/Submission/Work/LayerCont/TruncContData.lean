import Mathlib
import Submission.Work.LayerCont.TruncFromContour
import Submission.Work.LayerCont.ExistsContourStrong

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter

/-- **Cleanliness of the retained trunc axis, from the *web* classification of the orbit.**

If every orbit point `σ • (i t)` that comes within `rw₀` of `1 + i s₀` has `Re = 1` and height
`t` or `t⁻¹` (the `hweb` clause of `Work.LayerCont.ECS.exists_contour_left_data`), then on the
retained set `E = Ici 1 \ Ioo (s₀-A₁)(s₀+A₁)` the contour point `i s` is clean for every `τ` of
the ball — *no* condition on the second interval `I₂` is needed:

* the branch `τ.im = s` puts `s` inside the removed interval `I₁` (height bound `3 s₀ ε < A₁`),
* the branch `τ.im = s⁻¹` puts `τ.im ≤ 1`, while `τ.im > s₀ - A₁ > 1`.

This is what makes the trunc capstone `truncContData` unconditional (the `hI₂low` route through
`hclean` only works for `s₀ < 7`). -/
theorem clean_axis_of_web {s₀ A₁ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hA₁ : 0 < A₁)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεw : ε ≤ rw₀) (hhi : 1 < s₀ - A₁)
    (hhgt : 3 * s₀ * ε < A₁)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (s : ℝ) (hs : 0 < s), s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
  intro s hs hsE τ hτ hjeq
  have hs1 : (1 : ℝ) ≤ s := Set.mem_Ici.mp hsE.1
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  -- `hσ : σ • (i s) = τ`
  have hd : dist (σ • Work.Kernels.imagAxis s hs) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, him⟩ := hweb σ s hs hd
  rw [hσ] at him
  obtain ⟨-, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hε hε1 hτ
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  have himb : |τ.im - s₀| < A₁ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have himgt : 1 < τ.im := by linarith
  rcases him with him | him
  · -- `τ.im = s`: then `s ∈ I₁`, contradicting `s ∈ E`
    have hsb : |s - s₀| < A₁ := by rw [← him]; exact himb
    obtain ⟨ha, hb⟩ := abs_lt.mp hsb
    exact absurd ⟨by linarith, by linarith⟩ hsE.2
  · -- `τ.im = s⁻¹`: then `τ.im ≤ 1 < s₀ - A₁ < τ.im`
    have hinv1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
    rw [him] at himgt
    linarith

/-- **The trunc-piece holomorphy from the web data.** -/
theorem mdifferentiableOn_layerTruncCont_of_web (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ A₁ ξ₁ A₂ ξ₂ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hA₁ : 0 < A₁)
    (hξ₁ : 0 < ξ₁) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεw : ε ≤ rw₀) (hhi : 1 < s₀ - A₁)
    (hhgt : 3 * s₀ * ε < A₁)
    (hedge₀ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)
        ∨ (-ξ₂ < u ∧ u < 0 ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂)) →
      ε ≤ dist (γ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀))
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerTruncCont ℓ d s₀ A₁ ξ₁ r τ)
      (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε) := by
  have hcleanAxis := clean_axis_of_web (s₀ := s₀) (A₁ := A₁) hs₀ hA₁ hε hε1 hεw hhi hhgt hweb
  have hedge : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd hτ (not_lt.mpr hge)
  exact fun r => TruncHolomorphy ℓ d hd hs₀ hA₁ hξ₁ hε hhi hedge hcleanAxis

/-- **The trunc piece of the CKMRV layer, continued across `Re τ = 1`, with the geometry of
`exists_contour_left` fed in and no extra hypothesis.**

The mirror of `Work.LayerCont.lowContData` for the truncated piece `[1,∞)`: for every `s₀ > 0`
there are a half-width `A` and a width `ξ` such that, in the *trunc* case `1 < s₀ - A`, there is a
ball `B(1 + i s₀, ε)` on which

* `τ ↦ layerTruncCont ℓ d s₀ A ξ r τ` is holomorphic for every `r`, and
* it agrees with the paper's trunc layer `layerTrunc (Gcusp ℓ d) ℓ d · r` on `{Re τ < 1} ∩ 𝒟`.

The agreement uses `Work.LayerCont.TruncAgreement` (with `hcl`/`hpole`/`hdeg` derived from the
geometry as in the low case, and the axis cleanliness from `hclean` + `hclass` for `s ∈ I₂`);
the holomorphy uses the **web** classification (`clean_axis_of_web`), which avoids the `hI₂low`
condition `s₀⁻¹ + A₂ < 1` (true only for `s₀ < 7`). -/
theorem truncContData (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ A ξ : ℝ, 0 < A ∧ 0 < ξ ∧ 0 < s₀ - A ∧
      (1 < s₀ - A → ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => layerTruncCont ℓ d s₀ A ξ r τ)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            layerTruncCont ℓ d s₀ A ξ r τ
              = Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)) := by
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ :=
    Work.LayerCont.ECS.exists_contour_left_data s₀ hs₀
  refine ⟨A₁, ξ₁, hA₁, hξ₁, by linarith, fun hhi => ?_⟩
  -- the agreement, at radius `εa`
  obtain ⟨εa, hεapos, hεaε, hagree⟩ :=
    layerTruncCont_eq_layerTrunc_of_contourLeft ℓ d hd hs₀ hA₁ hA₁s hξ₁ hA₂ hξ₂ hεpos h4sεA h4sεξ
      hclean hclass hhi
  -- the holomorphy, at radius `εb = min ε (1/4)`
  set εb : ℝ := min ε (1 / 4) with hεbdef
  have hεbpos : 0 < εb := lt_min hεpos (by norm_num)
  have hεbε : εb ≤ ε := min_le_left _ _
  have hεb1 : εb ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hεbw : εb ≤ rw₀ := le_trans hεbε hεw
  have h4sεb : 4 * s₀ * εb ≤ A₁ := le_trans (mul_le_mul_of_nonneg_left hεbε (by positivity)) h4sεA
  have hgt : 3 * s₀ * εb < A₁ := by linarith
  have hholo : ∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerTruncCont ℓ d s₀ A₁ ξ₁ r τ)
      (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) := fun r =>
    mdifferentiableOn_layerTruncCont_of_web ℓ d hd (A₂ := A₂) (ξ₂ := ξ₂) hs₀ hA₁ hξ₁ hεbpos
      hεb1 hεbw hhi hgt
      (fun γ u v hv hc => le_trans hεbε (hedge₀ γ u v hv hc)) hweb r
  refine ⟨min εa εb, lt_min hεapos hεbpos, fun r => ?_, fun τ r hτ hτre hD => ?_⟩
  · exact (hholo r).mono (Metric.ball_subset_ball (min_le_right _ _))
  · exact hagree τ r (lt_of_lt_of_le hτ (min_le_left _ _)) hτre hD

end Work.LayerCont
