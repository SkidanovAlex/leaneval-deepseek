import Submission.Work.VolterraLong.Weighted.Basic

/-!
# The two elementary estimates of the weighted Volterra argument

* `norm_defect_le`: the defect `Ξ̃` is `O(ε)`;
* `qrem_lipschitz`: the Taylor remainder `Q̃` is Lipschitz with constant
  `Cg * R + ε` on the ball of radius `R`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The defect `Ξ̃(s) = Ξ s - G s (Z₀ s) + ∫_s^b Θ s σ (Z₀ σ)` is bounded by
`(2 + (b-a)) ε` when the perturbed data is `ε`-close to the base data and `Z₀`
solves the base identity. -/
theorem norm_defect_le {a b : ℝ} (hab : a ≤ b)
    {G0 G : ℝ → E → E} {Θ0 Θ : ℝ → ℝ → E → E} {Ξ0 Ξ : ℝ → E} {Z₀ : ℝ → E} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hZ₀ : ContinuousOn Z₀ (Set.Icc a b))
    (hΘ : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΘ0 : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hG_close : ∀ s ∈ Set.Icc a b, dist (G s (Z₀ s)) (G0 s (Z₀ s)) < ε)
    (hΘ_close : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      dist (Θ s σ (Z₀ σ)) (Θ0 s σ (Z₀ σ)) < ε)
    (hΞ_close : ∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) :
    ∀ s ∈ Set.Icc a b,
      ‖defect G Θ Ξ Z₀ b s‖ ≤ (2 + (b - a)) * ε := by
  intro s hs
  have hsb : s ≤ b := hs.2
  -- continuity of the two integrands on `[s,b]`, hence integrability
  have hsub : Set.Icc s b ⊆ Set.Icc a b := fun x hx => ⟨le_trans hs.1 hx.1, hx.2⟩
  have hZsub : Continuous fun σ : Set.Icc s b => Z₀ (σ : ℝ) :=
    continuousOn_iff_continuous_domRestrict.mp (hZ₀.mono hsub)
  have hcont : ∀ f : ℝ → ℝ → E → E,
      Continuous (fun p : ℝ × ℝ × E => f p.1 p.2.1 p.2.2) →
      ContinuousOn (fun σ : ℝ => f s σ (Z₀ σ)) (Set.Icc s b) := by
    intro f hf
    rw [continuousOn_iff_continuous_domRestrict]
    exact hf.comp (continuous_const.prodMk (continuous_subtype_val.prodMk hZsub))
  have hint1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hsb (hcont Θ hΘ)
  have hint0 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hsb (hcont Θ0 hΘ0)
  have hI : (∫ σ in s..b, Θ s σ (Z₀ σ)) - (∫ σ in s..b, Θ0 s σ (Z₀ σ)) =
      ∫ σ in s..b, (Θ s σ (Z₀ σ) - Θ0 s σ (Z₀ σ)) :=
    (intervalIntegral.integral_sub hint1 hint0).symm
  have hdecomp : defect G Θ Ξ Z₀ b s =
      (Ξ s - Ξ0 s) - (G s (Z₀ s) - G0 s (Z₀ s)) +
        ((∫ σ in s..b, Θ s σ (Z₀ σ)) - (∫ σ in s..b, Θ0 s σ (Z₀ σ))) := by
    rw [defect, hbase s hs]
    abel
  have hGnorm : ‖G s (Z₀ s) - G0 s (Z₀ s)‖ < ε := by
    have := hG_close s hs
    rwa [dist_eq_norm] at this
  have hΞnorm : ‖Ξ s - Ξ0 s‖ < ε := by
    have := hΞ_close s hs
    rwa [dist_eq_norm] at this
  have hInorm : ‖∫ σ in s..b, (Θ s σ (Z₀ σ) - Θ0 s σ (Z₀ σ))‖ ≤ ε * (b - s) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := b)
      (f := fun σ => Θ s σ (Z₀ σ) - Θ0 s σ (Z₀ σ)) (C := ε) (fun σ hσ => by
        rw [Set.uIoc_of_le hsb] at hσ
        have hσab : σ ∈ Set.Icc a b := ⟨le_trans hs.1 (le_of_lt hσ.1), hσ.2⟩
        have hcl := hΘ_close s hs σ hσab
        rw [dist_eq_norm] at hcl
        exact le_of_lt hcl)
    rwa [abs_of_nonneg (sub_nonneg.mpr hsb)] at h
  rw [hdecomp, hI]
  calc ‖(Ξ s - Ξ0 s) - (G s (Z₀ s) - G0 s (Z₀ s)) +
        ∫ σ in s..b, (Θ s σ (Z₀ σ) - Θ0 s σ (Z₀ σ))‖
      ≤ ‖(Ξ s - Ξ0 s) - (G s (Z₀ s) - G0 s (Z₀ s))‖ +
        ‖∫ σ in s..b, (Θ s σ (Z₀ σ) - Θ0 s σ (Z₀ σ))‖ := norm_add_le _ _
    _ ≤ (‖Ξ s - Ξ0 s‖ + ‖G s (Z₀ s) - G0 s (Z₀ s)‖) + ε * (b - s) := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (2 + (b - a)) * ε := by
        nlinarith [hGnorm, hΞnorm, hInorm, hε, hs.1, hs.2]

/-- The Taylor remainder is Lipschitz with constant `Cg * R + ε` on the ball of
radius `R` (with `R ≤ 1`), assuming `G` is differentiable in `z` on the unit
ball around `Z₀ s` with `‖fderiv G - A‖ ≤ Cg ‖z - Z₀ s‖ + ε` there. -/
theorem qrem_lipschitz {G : ℝ → E → E} (A : E ≃L[ℝ] E) (Z₀ : ℝ → E) (s : ℝ)
    {Cg ε R : ℝ} (hCg : 0 ≤ Cg) (hε : 0 ≤ ε) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hdiff : ∀ z ∈ Metric.closedBall (Z₀ s) 1, DifferentiableAt ℝ (fun w => G s w) z)
    (hderiv : ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε) :
    ∀ w w' : E, ‖w‖ ≤ R → ‖w'‖ ≤ R →
      ‖qrem G A Z₀ s w - qrem G A Z₀ s w'‖ ≤ (Cg * R + ε) * ‖w - w'‖ := by
  intro w w' hw hw'
  have hmem : ∀ v : E, ‖v‖ ≤ R → Z₀ s + v ∈ Metric.closedBall (Z₀ s) 1 := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : Z₀ s + v - Z₀ s = v := by abel
    rw [hsub]
    linarith
  have hFderiv : ∀ v ∈ Metric.closedBall (0 : E) R,
      HasFDerivAt (fun v : E => G s (Z₀ s + v) - G s (Z₀ s) - A v)
        (fderiv ℝ (fun z => G s z) (Z₀ s + v) - (A : E →L[ℝ] E)) v := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    have h1 : HasFDerivAt (fun z => G s z) (fderiv ℝ (fun z => G s z) (Z₀ s + v))
        (Z₀ s + v) := (hdiff _ (hmem v hv)).hasFDerivAt
    have hinner : HasFDerivAt (fun v : E => Z₀ s + v) (ContinuousLinearMap.id ℝ E) v := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) v).const_add (Z₀ s)
    have h2 := h1.comp v hinner
    have h3 : HasFDerivAt (fun v : E => G s (Z₀ s + v))
        (fderiv ℝ (fun z => G s z) (Z₀ s + v)) v := by
      simpa [ContinuousLinearMap.comp_id, Function.comp_def] using h2
    exact (h3.sub_const (G s (Z₀ s))).sub
      ((A : E →L[ℝ] E).hasFDerivAt (x := v))
  have hbound : ∀ v ∈ Metric.closedBall (0 : E) R,
      ‖fderiv ℝ (fun z => G s z) (Z₀ s + v) - (A : E →L[ℝ] E)‖ ≤ Cg * R + ε := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    have h := hderiv _ (hmem v hv)
    have hsub : Z₀ s + v - Z₀ s = v := by abel
    rw [hsub] at h
    nlinarith [h, hCg, hv, hε]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun v : E => G s (Z₀ s + v) - G s (Z₀ s) - A v)
    (f' := fun v : E => fderiv ℝ (fun z => G s z) (Z₀ s + v) - (A : E →L[ℝ] E))
    (s := Metric.closedBall (0 : E) R) (C := Cg * R + ε) (x := w) (y := w')
    (fun v hv => (hFderiv v hv).hasFDerivWithinAt) hbound (convex_closedBall 0 R)
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw)
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw')
  simpa [qrem, norm_sub_rev] using hmvt

end Work.VolterraLong
