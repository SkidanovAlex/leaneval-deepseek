import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.log_one_sub_jump

/-!
# `Work.A14D.D_ray_value`

The jump `D = HU - HL` across the real ray `(1, ∞)`: with `ℓ z = log (1 - z)`, a function which
equals `e₀ + e₁ ℓ + e₂ ℓ²` on the upper half-plane and on the lower half-plane restricts on `(1,∞)`
to a difference of boundary values.  Approaching a point `t > 1` from above resp. below gives

`ℓ (t + ε i) → log (t-1) - π i`,  `ℓ (t - ε i) → log (t-1) + π i`

(`Work.A14D.log_one_sub_jump`), so that

`D t = (e₀ + e₁ (L - π i) + e₂ (L - π i)²) - (e₀ + e₁ (L + π i) + e₂ (L + π i)²)
     = -2 π i e₁ t - 4 π i L e₂ t`,  `L = log (t-1)`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

private lemma mem_SU_of_one_le_re {z : ℂ} (hre : 1 ≤ z.re) (him : 0 < z.im) : z ∈ SU := by
  change (1 - z.re) / 8 < z.im
  linarith

private lemma mem_SL_of_one_le_re {z : ℂ} (hre : 1 ≤ z.re) (him : z.im < 0) : z ∈ SL := by
  change z.im < (z.re - 1) / 8
  linarith

theorem D_ray_value {δ : ℝ} (hδ : 0 < δ)
    {e0 e1 e2 : ℂ → ℂ}
    (he0 : DifferentiableOn ℂ e0 (Metric.ball 1 δ))
    (he1 : DifferentiableOn ℂ e1 (Metric.ball 1 δ))
    (he2 : DifferentiableOn ℂ e2 (Metric.ball 1 δ))
    {HU HL D : ℂ → ℂ}
    (hHUd : DifferentiableOn ℂ HU SU) (hHLd : DifferentiableOn ℂ HL SL)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (hU : ∀ z ∈ SU ∩ Metric.ball 1 δ ∩ {z : ℂ | 0 < z.im},
      HU z = e0 z + e1 z * ell z + e2 z * ell z ^ 2)
    (hL : ∀ z ∈ SL ∩ Metric.ball 1 δ ∩ {z : ℂ | z.im < 0},
      HL z = e0 z + e1 z * ell z + e2 z * ell z ^ 2)
    {t : ℝ} (ht1 : 1 < t) (htδ : t - 1 < δ) :
    D (t : ℂ) = -2 * (Real.pi : ℂ) * Complex.I * e1 (t : ℂ)
      - 4 * (Real.pi : ℂ) * Complex.I * ((Real.log (t - 1) : ℝ) : ℂ) * e2 (t : ℂ) := by
  have htball : (t : ℂ) ∈ Metric.ball 1 δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h : (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t - 1)]
    exact htδ
  have hSUopen : IsOpen SU := by
    change IsOpen {z : ℂ | (1 - z.re) / 8 < z.im}
    exact isOpen_lt (by continuity) (by continuity)
  have hSLopen : IsOpen SL := by
    change IsOpen {z : ℂ | z.im < (z.re - 1) / 8}
    exact isOpen_lt (by continuity) (by continuity)
  have htSU : (t : ℂ) ∈ SU := by
    change (1 - (t : ℂ).re) / 8 < (t : ℂ).im
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have htSL : (t : ℂ) ∈ SL := by
    change (t : ℂ).im < ((t : ℂ).re - 1) / 8
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have hHUct : ContinuousAt HU (t : ℂ) :=
    (hHUd.differentiableAt (hSUopen.mem_nhds htSU)).continuousAt
  have hHLct : ContinuousAt HL (t : ℂ) :=
    (hHLd.differentiableAt (hSLopen.mem_nhds htSL)).continuousAt
  have he0ct : ContinuousAt e0 (t : ℂ) :=
    (he0.differentiableAt (Metric.isOpen_ball.mem_nhds htball)).continuousAt
  have he1ct : ContinuousAt e1 (t : ℂ) :=
    (he1.differentiableAt (Metric.isOpen_ball.mem_nhds htball)).continuousAt
  have he2ct : ContinuousAt e2 (t : ℂ) :=
    (he2.differentiableAt (Metric.isOpen_ball.mem_nhds htball)).continuousAt
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hεI : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    simpa using Tendsto.mul_const Complex.I hε
  have hmap : Tendsto (fun ε : ℝ => (t : ℂ) + (ε : ℂ) * I) (𝓝[>] (0:ℝ)) (𝓝 (t : ℂ)) := by
    have h3 := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (t:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (t:ℂ))).add hεI
    simpa using h3
  have hmapL : Tendsto (fun ε : ℝ => (t : ℂ) - (ε : ℂ) * I) (𝓝[>] (0:ℝ)) (𝓝 (t : ℂ)) := by
    have h3 := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (t:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (t:ℂ))).sub hεI
    simpa using h3
  have hlogU : Tendsto (fun ε : ℝ => ell ((t : ℂ) + (ε : ℂ) * I)) (𝓝[>] (0:ℝ))
      (𝓝 (((Real.log (t - 1) : ℝ) : ℂ) - (Real.pi : ℂ) * I)) := by
    simpa [ell] using (log_one_sub_jump t ht1).1
  have hlogL : Tendsto (fun ε : ℝ => ell ((t : ℂ) - (ε : ℂ) * I)) (𝓝[>] (0:ℝ))
      (𝓝 (((Real.log (t - 1) : ℝ) : ℂ) + (Real.pi : ℂ) * I)) := by
    simpa [ell] using (log_one_sub_jump t ht1).2
  have hball_ev : ∀ᶠ (ε : ℝ) in 𝓝[>](0:ℝ), (t:ℂ) + (ε:ℂ)*I ∈ Metric.ball 1 δ := by
    have hcont : Continuous (fun ε : ℝ => ‖(t:ℂ) + (ε:ℂ)*I - 1‖) := by continuity
    have h0 : ‖(t:ℂ) + ((0:ℝ):ℂ)*I - 1‖ < δ := by
      have h : (t:ℂ) + ((0:ℝ):ℂ)*I - 1 = ((t-1:ℝ):ℂ) := by push_cast; ring
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t - 1)]
      exact htδ
    have hmem : ∀ᶠ (ε : ℝ) in 𝓝 (0:ℝ), (t:ℂ) + (ε:ℂ)*I ∈ Metric.ball 1 δ := by
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0)] with ε hε
      rw [Metric.mem_ball, Complex.dist_eq]
      exact hε
    refine hmem.filter_mono ?_
    exact nhdsWithin_le_nhds
  have hball_evL : ∀ᶠ (ε : ℝ) in 𝓝[>](0:ℝ), (t:ℂ) - (ε:ℂ)*I ∈ Metric.ball 1 δ := by
    have hcont : Continuous (fun ε : ℝ => ‖(t:ℂ) - (ε:ℂ)*I - 1‖) := by continuity
    have h0 : ‖(t:ℂ) - ((0:ℝ):ℂ)*I - 1‖ < δ := by
      have h : (t:ℂ) - ((0:ℝ):ℂ)*I - 1 = ((t-1:ℝ):ℂ) := by push_cast; ring
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t - 1)]
      exact htδ
    have hmem : ∀ᶠ (ε : ℝ) in 𝓝 (0:ℝ), (t:ℂ) - (ε:ℂ)*I ∈ Metric.ball 1 δ := by
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0)] with ε hε
      rw [Metric.mem_ball, Complex.dist_eq]
      exact hε
    refine hmem.filter_mono ?_
    exact nhdsWithin_le_nhds
  have hA : Tendsto (fun ε : ℝ => e0 ((t:ℂ) + (ε:ℂ)*I) + e1 ((t:ℂ) + (ε:ℂ)*I) * ell ((t:ℂ) + (ε:ℂ)*I)
        + e2 ((t:ℂ) + (ε:ℂ)*I) * ell ((t:ℂ) + (ε:ℂ)*I)^2) (𝓝[>] (0:ℝ))
      (𝓝 (e0 (t:ℂ) + e1 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) - (Real.pi:ℂ)*I)
        + e2 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) - (Real.pi:ℂ)*I)^2)) :=
    ((he0ct.tendsto.comp hmap).add ((he1ct.tendsto.comp hmap).mul hlogU)).add
      ((he2ct.tendsto.comp hmap).mul (hlogU.pow 2))
  have hB : Tendsto (fun ε : ℝ => e0 ((t:ℂ) - (ε:ℂ)*I) + e1 ((t:ℂ) - (ε:ℂ)*I) * ell ((t:ℂ) - (ε:ℂ)*I)
        + e2 ((t:ℂ) - (ε:ℂ)*I) * ell ((t:ℂ) - (ε:ℂ)*I)^2) (𝓝[>] (0:ℝ))
      (𝓝 (e0 (t:ℂ) + e1 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) + (Real.pi:ℂ)*I)
        + e2 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) + (Real.pi:ℂ)*I)^2)) :=
    ((he0ct.tendsto.comp hmapL).add ((he1ct.tendsto.comp hmapL).mul hlogL)).add
      ((he2ct.tendsto.comp hmapL).mul (hlogL.pow 2))
  have hevU : (fun ε : ℝ => HU ((t:ℂ) + (ε:ℂ)*I)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun ε : ℝ => e0 ((t:ℂ) + (ε:ℂ)*I) + e1 ((t:ℂ) + (ε:ℂ)*I) * ell ((t:ℂ) + (ε:ℂ)*I)
        + e2 ((t:ℂ) + (ε:ℂ)*I) * ell ((t:ℂ) + (ε:ℂ)*I)^2) := by
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)), hball_ev] with ε hε hball
    have hεpos : (0:ℝ) < ε := hε
    have hre : (1:ℝ) ≤ ((t:ℂ) + (ε:ℂ)*I).re := by
      have h : ((t:ℂ) + (ε:ℂ)*I).re = t := by simp
      rw [h]; linarith
    have him : 0 < ((t:ℂ) + (ε:ℂ)*I).im := by
      have h : ((t:ℂ) + (ε:ℂ)*I).im = ε := by simp
      rw [h]; exact hεpos
    exact hU _ ⟨⟨mem_SU_of_one_le_re hre him, hball⟩, him⟩
  have hevL : (fun ε : ℝ => HL ((t:ℂ) - (ε:ℂ)*I)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun ε : ℝ => e0 ((t:ℂ) - (ε:ℂ)*I) + e1 ((t:ℂ) - (ε:ℂ)*I) * ell ((t:ℂ) - (ε:ℂ)*I)
        + e2 ((t:ℂ) - (ε:ℂ)*I) * ell ((t:ℂ) - (ε:ℂ)*I)^2) := by
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)), hball_evL] with ε hε hball
    have hεpos : (0:ℝ) < ε := hε
    have hre : (1:ℝ) ≤ ((t:ℂ) - (ε:ℂ)*I).re := by
      have h : ((t:ℂ) - (ε:ℂ)*I).re = t := by simp
      rw [h]; linarith
    have him : ((t:ℂ) - (ε:ℂ)*I).im < 0 := by
      have h : ((t:ℂ) - (ε:ℂ)*I).im = -ε := by simp
      rw [h]; linarith
    exact hL _ ⟨⟨mem_SL_of_one_le_re hre him, hball⟩, him⟩
  have hHUval : HU (t:ℂ) = e0 (t:ℂ) + e1 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) - (Real.pi:ℂ)*I)
      + e2 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) - (Real.pi:ℂ)*I)^2 :=
    tendsto_nhds_unique (Filter.Tendsto.congr' hevU (hHUct.tendsto.comp hmap)) hA
  have hHLval : HL (t:ℂ) = e0 (t:ℂ) + e1 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) + (Real.pi:ℂ)*I)
      + e2 (t:ℂ) * (((Real.log (t-1):ℝ):ℂ) + (Real.pi:ℂ)*I)^2 :=
    tendsto_nhds_unique (Filter.Tendsto.congr' hevL (hHLct.tendsto.comp hmapL)) hB
  have hDt : D (t:ℂ) = HU (t:ℂ) - HL (t:ℂ) := hDj (t:ℂ) ⟨htSU, htSL⟩
  rw [hDt, hHUval, hHLval]
  ring

end Work.A14D
