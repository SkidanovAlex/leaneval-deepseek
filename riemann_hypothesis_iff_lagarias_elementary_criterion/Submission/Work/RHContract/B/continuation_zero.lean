import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.Phi_secondDeriv
import Submission.Work.RHContract.B.div_removable_analyticAt

/-!
# `B.continuation_zero`: `Φ` continues analytically across the origin

`Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt` is holomorphic on the right half-plane `Re s > 0`
(`B.Phi_analyticOn`) and its second derivative there is the closed form `h₂ − h₂′`
(`B.Phi_secondDeriv`), where

`h₂(s) = −ζ′(s+1)/ζ(s+1)/(s+1) − 2^{−s}/s`.

The apparent singularities of that closed form at `s = 0` cancel: writing
`logDeriv ζ₁(1+s) = (ζ′/ζ)(1+s) + 1/s` (the corpus lemma `deriv_zeta_div_zeta_eq`, transported
from `ζ₁ = (s−1)·ζ`), the combination

`(−(ζ′/ζ)(s+1) − (s+1)/s)/(s+1) = (−logDeriv ζ₁(1+s) − 1)/(1+s)`

is holomorphic at `0`, and the remaining `(1 − 2^{−s})/s` has a removable singularity
(`B.div_removable_analyticAt` applied to `N s = 1 − 2^{−s}`, whose derivative at `0` is
`log 2 ≠ 0`).  Hence there is a function `G`, holomorphic at `0`, agreeing with `h₂` off `0`.

Since `G − G′` is holomorphic at `0` and equals `Φ″` on the right half-plane, the general
double-primitive lemma below (applied to `f = G − G′`) provides an analytic continuation of `Φ`
to a ball around `0`, agreeing with `Φ` on the intersection with the right half-plane.  Gluing
it with `H` outside the ball gives the statement.
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.RHContract.B

noncomputable section

/-! ## The extension of the closed form `h₂` at `0` -/

private lemma log_two_complex : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
  simpa using (Complex.natCast_log (n := 2)).symm

private lemma cpow_two_eq_exp (s : ℂ) :
    (2 : ℂ) ^ (-s) = Complex.exp (-s * ((Real.log 2 : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), log_two_complex]
  congr 1
  ring

/-- Off `0`, the closed form `h₂` of `LandauDefs` equals the manifestly regular expression
`(−logDeriv ζ₁(1+s) − 1)/(1+s) + A s`, where `A` is any analytic extension of
`(1 − 2^{−s})/s`. -/
private lemma h2Closed_eq_aux (A : ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) (hz : riemannZeta₁ (1 + s) ≠ 0)
    (hA : A s = (1 - (2 : ℂ) ^ (-s)) / s) :
    Work.RHContract.Landau.h2Closed s =
      (-logDeriv riemannZeta₁ (1 + s) - 1) / (1 + s) + A s := by
  have hne : (1 + s : ℂ) ≠ 1 := by
    intro h
    exact hs (by linear_combination h)
  have hD := Commons.NumberTheory.Zeta.deriv_zeta_div_zeta_eq (1 + s) hne hz
  rw [show ((1 + s : ℂ) - 1)⁻¹ = s⁻¹ by ring_nf] at hD
  have hld : logDeriv riemannZeta₁ (1 + s)
      = deriv riemannZeta₁ (1 + s) / riemannZeta₁ (1 + s) := rfl
  have hnum : (-(deriv riemannZeta (1 + s))) / riemannZeta (1 + s) - (1 + s) / s
      = -logDeriv riemannZeta₁ (1 + s) - 1 := by
    rw [neg_div, hld, hD]
    field_simp
    ring
  rw [Work.RHContract.Landau.h2Closed]
  rw [show s + 1 = (1 + s : ℂ) by ring]
  rw [hnum, hA]

/-- **The closed form `h₂` continues analytically through `0`.** -/
private theorem h2Closed_extension_aux :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      Filter.EventuallyEq (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) G Work.RHContract.Landau.h2Closed := by
  have hfun : (fun s : ℂ => 1 - (2 : ℂ) ^ (-s))
      = fun s : ℂ => 1 - Complex.exp (-s * ((Real.log 2 : ℝ) : ℂ)) := by
    funext s
    rw [cpow_two_eq_exp]
  have hN_an : AnalyticAt ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (-s)) 0 := by
    rw [hfun]
    exact AnalyticAt.sub analyticAt_const
      (AnalyticAt.cexp (AnalyticAt.mul (AnalyticAt.neg analyticAt_id) analyticAt_const))
  have hN0 : (fun s : ℂ => 1 - (2 : ℂ) ^ (-s)) 0 = 0 := by
    simp [Complex.cpow_zero]
  have hN' : deriv (fun s : ℂ => 1 - (2 : ℂ) ^ (-s)) 0 ≠ 0 := by
    rw [hfun]
    have hd : HasDerivAt (fun s : ℂ => 1 - Complex.exp (-s * ((Real.log 2 : ℝ) : ℂ)))
        (((Real.log 2 : ℝ) : ℂ)) 0 := by
      have h1 : HasDerivAt (fun s : ℂ => -s * ((Real.log 2 : ℝ) : ℂ))
          (-((Real.log 2 : ℝ) : ℂ)) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).neg.mul_const (((Real.log 2 : ℝ) : ℂ))
      have h2 := h1.cexp
      have h3 : HasDerivAt (fun s : ℂ => 1 - Complex.exp (-s * ((Real.log 2 : ℝ) : ℂ)))
          (0 - Complex.exp (-0 * ((Real.log 2 : ℝ) : ℂ)) * (-((Real.log 2 : ℝ) : ℂ))) 0 :=
        (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub h2
      simpa using h3
    rw [hd.deriv]
    exact_mod_cast (ne_of_gt (Real.log_pos (by norm_num)))
  obtain ⟨A, hAan, hAev⟩ :=
    div_removable_analyticAt (fun s : ℂ => 1 - (2 : ℂ) ^ (-s)) hN_an hN0 hN'
  refine ⟨fun s => (-logDeriv riemannZeta₁ (1 + s) - 1) / (1 + s) + A s, ?_, ?_⟩
  · have hld : AnalyticAt ℂ (logDeriv riemannZeta₁) 1 := by
      change AnalyticAt ℂ (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s) 1
      exact AnalyticAt.div (differentiable_riemannZeta₁.analyticAt 1).deriv
        (differentiable_riemannZeta₁.analyticAt 1) (by rw [riemannZeta₁_one]; norm_num)
    have hshift : AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) + s) 0 :=
      (analyticAt_const (v := (1 : ℂ)) (x := (0 : ℂ))).add (analyticAt_id (z := (0 : ℂ)))
    have hld' : AnalyticAt ℂ (logDeriv riemannZeta₁) ((1 : ℂ) + 0) := by simpa using hld
    have hcomp : AnalyticAt ℂ (fun s : ℂ => logDeriv riemannZeta₁ (1 + s)) 0 := hld'.comp hshift
    refine AnalyticAt.add (AnalyticAt.div
      (AnalyticAt.sub (show AnalyticAt ℂ (fun s : ℂ => -logDeriv riemannZeta₁ (1 + s)) 0 from
        hcomp.neg) analyticAt_const) hshift (by norm_num)) hAan
  · change ∀ᶠ s in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      (fun s => (-logDeriv riemannZeta₁ (1 + s) - 1) / (1 + s) + A s) s
        = Work.RHContract.Landau.h2Closed s
    rw [eventually_nhdsWithin_iff]
    have hA' : ∀ᶠ s in 𝓝 (0 : ℂ), s ∈ {(0 : ℂ)}ᶜ → A s = (1 - (2 : ℂ) ^ (-s)) / s :=
      eventually_nhdsWithin_iff.mp hAev
    have hz₁ : ∀ᶠ s in 𝓝 (0 : ℂ), riemannZeta₁ (1 + s) ≠ 0 := by
      have ht : Tendsto (fun s : ℂ => (1 : ℂ) + s) (𝓝 0) (𝓝 ((1 : ℂ) + 0)) :=
        (continuousAt_const.add continuousAt_id).tendsto
      have ht' : Tendsto (fun s : ℂ => (1 : ℂ) + s) (𝓝 0) (𝓝 1) := by simpa using ht
      exact ht'.eventually riemannZeta₁_ne_zero_of_near_one
    filter_upwards [hA', hz₁] with s hAs hzs hs0
    exact (h2Closed_eq_aux A s hs0 hzs (hAs (by simpa using hs0))).symm

/-! ## The double-primitive lemma

(This is a private copy of the general continuation lemma for a function whose second
derivative is known on a half-disk: the carrier `f` has a double primitive on the ball, and the
difference `g − F₂` has vanishing second derivative on the open convex set
`ball 0 R ∩ {0 < s.re}`, hence is affine there.) -/

private theorem continuation_of_secondDeriv_aux {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOn ℂ f (Metric.ball 0 R))
    (hg : AnalyticOn ℂ g {s : ℂ | 0 < s.re})
    (h2deriv : ∀ s : ℂ, s ∈ Metric.ball 0 R → 0 < s.re → deriv (deriv g) s = f s) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, AnalyticOn ℂ F (Metric.ball 0 r) ∧
      ∀ s : ℂ, s ∈ Metric.ball 0 r → 0 < s.re → F s = g s := by
  obtain ⟨F1, hF1⟩ := hf.differentiableOn.isExactOn_ball
  have hF1diff : DifferentiableOn ℂ F1 (Metric.ball 0 R) :=
    fun z hz => (hF1 z hz).differentiableAt.differentiableWithinAt
  obtain ⟨F2, hF2⟩ := hF1diff.isExactOn_ball
  have hF2diff : DifferentiableOn ℂ F2 (Metric.ball 0 R) :=
    fun z hz => (hF2 z hz).differentiableAt.differentiableWithinAt
  have hhalf_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderivg : DifferentiableOn ℂ (deriv g) {s : ℂ | 0 < s.re} :=
    hg.differentiableOn.deriv hhalf_open
  set U : Set ℂ := Metric.ball 0 R ∩ {s : ℂ | 0 < s.re} with hU
  have hsub : U ⊆ {s : ℂ | 0 < s.re} := fun z hz => hz.2
  have hUopen : IsOpen U := (Metric.isOpen_ball).inter hhalf_open
  have hUpre : IsPreconnected U :=
    ((convex_ball 0 R).inter (convex_halfSpace_re_gt 0)).isPreconnected
  obtain ⟨a, ha⟩ := hUopen.exists_eq_add_of_deriv_eq hUpre
    (hderivg.mono hsub) (hF1diff.mono (fun z hz => hz.1))
    (fun z hz => by rw [h2deriv z hz.1 hz.2, (hF1 z hz.1).deriv])
  have hGdiff : DifferentiableOn ℂ (fun z : ℂ => F2 z + a * z) U := by
    intro z hz
    exact ((hF2 z hz.1).differentiableAt.add
      (hasDerivAt_const_mul a).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc⟩ := hUopen.exists_eq_add_of_deriv_eq hUpre
    (hg.differentiableOn.mono hsub) hGdiff
    (fun z hz => by
      have hdz : HasDerivAt (fun w : ℂ => F2 w + a * w) (F1 z + a) z := by
        refine (((hF2 z hz.1).add (hasDerivAt_const_mul a))).congr_of_eventuallyEq ?_
        exact Filter.Eventually.of_forall (fun w => rfl)
      rw [ha hz]
      exact hdz.deriv.symm)
  let F : ℂ → ℂ := fun z => F2 z + a * z + c
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 R) := by
    intro z hz
    have hdz : HasDerivAt (fun w : ℂ => F2 w + a * w + c) (F1 z + a) z := by
      refine (((hF2 z hz).add (hasDerivAt_const_mul a)).add_const c).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall (fun w => rfl)
    exact hdz.differentiableAt.differentiableWithinAt
  refine ⟨R, hR, F, hFdiff.analyticOn Metric.isOpen_ball, ?_⟩
  intro s hs hspos
  exact (hc ⟨hs, hspos⟩).symm

/-! ## The target -/

theorem continuation_zero
    (H : ℂ → ℂ) (hH : AnalyticOn ℂ H {s : ℂ | 0 < s.re})
    (hHΦ : ∀ s : ℂ, 0 < s.re → H s = Work.RHContract.Landau.Phi s) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φtilde : ℂ → ℂ,
      AnalyticOn ℂ Φtilde (Metric.ball 0 r) ∧
      ∀ s : ℂ, 0 < s.re → Φtilde s = H s := by
  classical
  obtain ⟨G, hGan, hGev⟩ := h2Closed_extension_aux
  -- a ball around `0` on which `G` is analytic
  obtain ⟨R₁, hR₁pos, hR₁an⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, z ∈ Metric.ball 0 R →
      AnalyticAt ℂ G z := by
    have h : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ G z := hGan.eventually_analyticAt
    rcases Metric.mem_nhds_iff.mp h with ⟨R, hR, hsub⟩
    exact ⟨R, hR, fun z hz => hsub hz⟩
  -- a punctured ball around `0` where `h₂` agrees with `G`
  obtain ⟨R₂, hR₂pos, hR₂⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ s : ℂ, s ∈ Metric.ball 0 R → s ≠ 0 → Work.RHContract.Landau.h2Closed s = G s := by
    have h : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ {(0 : ℂ)}ᶜ → Work.RHContract.Landau.h2Closed z = G z :=
      eventually_nhdsWithin_iff.mp hGev.symm
    rcases Metric.mem_nhds_iff.mp h with ⟨R, hR, hsub⟩
    exact ⟨R, hR, fun z hz hz0 => hsub hz (by simpa using hz0)⟩
  set R : ℝ := min R₁ R₂ with hRdef
  have hRpos : 0 < R := lt_min hR₁pos hR₂pos
  have hRR₁ : R ≤ R₁ := min_le_left _ _
  have hRR₂ : R ≤ R₂ := min_le_right _ _
  -- the carrier `f = G − G′` of the second derivative is analytic on the ball
  have hf : AnalyticOn ℂ (fun s => G s - deriv G s) (Metric.ball 0 R) := by
    refine AnalyticOnNhd.analyticOn ?_
    intro s hs
    have hs₁ : s ∈ Metric.ball 0 R₁ := Metric.ball_subset_ball hRR₁ hs
    exact (hR₁an s hs₁).sub (hR₁an s hs₁).deriv
  -- it computes the second derivative of `Φ` on the right half-plane
  have h2deriv : ∀ s : ℂ, s ∈ Metric.ball 0 R → 0 < s.re →
      deriv (deriv Work.RHContract.Landau.Phi) s = G s - deriv G s := by
    intro s hs hsre
    have hsne : s ≠ 0 := by
      intro h0
      rw [h0] at hsre
      simp at hsre
    have hs₂ : s ∈ Metric.ball 0 R₂ := Metric.ball_subset_ball hRR₂ hs
    have h1 : Work.RHContract.Landau.h2Closed s = G s := hR₂ s hs₂ hsne
    have hmem : Metric.ball 0 R₂ ∩ {z : ℂ | z ≠ 0} ∈ 𝓝 s :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hs₂) (isOpen_ne.mem_nhds hsne)
    have hev : Work.RHContract.Landau.h2Closed =ᶠ[𝓝 s] G := by
      filter_upwards [hmem] with z hz
      exact hR₂ z hz.1 hz.2
    have h2 : deriv Work.RHContract.Landau.h2Closed s = deriv G s := hev.deriv_eq
    rw [Phi_secondDeriv s hsre, Work.RHContract.Landau.h2Minus, h1, h2]
  -- the double primitive of `f` matching `Φ`
  obtain ⟨r, hrpos, F, hFan, hFeq⟩ :=
    continuation_of_secondDeriv_aux hRpos hf
      (fun s hs => (Phi_analyticOn s hs).analyticWithinAt) h2deriv
  refine ⟨r, hrpos, fun s => if s ∈ Metric.ball 0 r then F s else H s, ?_, ?_⟩
  · intro x hx
    have hxF : AnalyticAt ℂ F x := hFan.analyticAt (Metric.isOpen_ball.mem_nhds hx)
    have hev : F =ᶠ[𝓝 x] (fun s => if s ∈ Metric.ball 0 r then F s else H s) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      simp only [hy, if_true]
    exact (hxF.congr hev).analyticWithinAt
  · intro s hs
    by_cases hmem : s ∈ Metric.ball 0 r
    · simp only [if_pos hmem]
      exact (hFeq s hmem hs).trans (hHΦ s hs).symm
    · simp only [if_neg hmem]

end

end Work.RHContract.B
