import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.amoM_strip
import Submission.Work.TMComp.MAnalytic.amoM_section
import Submission.Work.TMComp.MAnalytic.section_unique_real
import Submission.Work.TMComp.MAnalytic.fourierCoeff_holomorphic
import Submission.Work.TMComp.MAnalytic.fourierCoeff_decay
import Submission.Work.TMComp.MAnalytic.fourier_series_eq
import Submission.Work.TMComp.MAnalytic.fourier_series_analytic
import Submission.Work.TMComp.MAnalytic.addCircle_fourier_expansion
import Submission.Work.TMComp.MAnalytic.strip_section
import Submission.Work.TMComp.MAnalytic.summable_int_exp_neg_abs
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.MAnalytic.propagate_smallness
import Submission.Work.TMComp.MAnalytic.amoM_strip_cayley
import Submission.Work.TMComp.MAnalytic.separately_holomorphic_real_analytic
open MeasureTheory Filter Topology Set
open scoped Topology

set_option maxHeartbeats 4000000

namespace Work.TMComp.MAnalytic

open Work.TMContract

noncomputable section

/-- Cayley transform of the section `M`. -/
def aks_amf (M : ℂ → ℝ → ℂ) : ℂ → ℝ → ℂ := fun z x => Kotani.cayley (M z x)

/-- The `k`-th Fourier coefficient of `x ↦ aks_amf M z x`. -/
def aks_amce (M : ℂ → ℝ → ℂ) (k : ℤ) : ℂ → ℂ :=
  fun z => ∫ x in (0 : ℝ)..1, aks_amf M z x * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))

/-- The two-variable Fourier series. -/
def aks_amF (M : ℂ → ℝ → ℂ) (z x : ℂ) : ℂ :=
  ∑' k : ℤ, aks_amce M k z * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * x)

theorem aks_kotaniDomain_isOpen (a b : ℝ) : IsOpen (kotaniDomain a b) := by
  have h : kotaniDomain a b =
      (Complex.im ⁻¹' {(0 : ℝ)})ᶜ ∪ Complex.re ⁻¹' (Ioo a b) := by
    ext z
    simp only [kotaniDomain, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ioo, ne_eq]
    tauto
  rw [h]
  have hc : IsClosed (Complex.im ⁻¹' {(0 : ℝ)}) :=
    isClosed_singleton.preimage Complex.continuous_im
  exact IsOpen.union hc.isOpen_compl (isOpen_Ioo.preimage Complex.continuous_re)

theorem aks_mem_kotaniDomain_of_ball {a b E ρ : ℝ}
    (hρ : ρ ≤ min (E - a) (b - E)) :
    Metric.ball (E : ℂ) ρ ⊆ kotaniDomain a b := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hlt : ‖z - (E : ℂ)‖ < min (E - a) (b - E) := lt_of_lt_of_le hz hρ
  have habs : |z.re - E| ≤ ‖z - (E : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z - (E : ℂ))
  rcases eq_or_ne z.im 0 with him | him
  · right
    refine ⟨him, ?_, ?_⟩
    · have h2 : |z.re - E| < E - a :=
        lt_of_le_of_lt habs (lt_of_lt_of_le hlt (min_le_left _ _))
      linarith [(abs_lt.mp h2).1]
    · have h2 : |z.re - E| < b - E :=
        lt_of_le_of_lt habs (lt_of_lt_of_le hlt (min_le_right _ _))
      linarith [(abs_lt.mp h2).2]
  · left; exact him

theorem aks_isOpen_halfPlane_union_ball (E ρ : ℝ) :
    IsOpen ({z : ℂ | 0 < z.im} ∪ Metric.ball (E : ℂ) ρ) :=
  IsOpen.union (isOpen_lt continuous_const Complex.continuous_im) Metric.isOpen_ball

theorem aks_isPreconnected_halfPlane_union_ball {E ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected ({z : ℂ | 0 < z.im} ∪ Metric.ball (E : ℂ) ρ) := by
  have h1 : IsPreconnected ({z : ℂ | 0 < z.im}) := by
    have hc : Convex ℝ (Complex.imCLM ⁻¹' (Ioi (0 : ℝ))) :=
      (convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap
    have he : ({z : ℂ | 0 < z.im} : Set ℂ) = Complex.imCLM ⁻¹' (Ioi (0 : ℝ)) := by
      ext z; simp [Complex.imCLM_apply]
    rw [he]; exact hc.isPreconnected
  have h2 : IsPreconnected (Metric.ball (E : ℂ) ρ) := Metric.isPreconnected_ball
  have hmem : (E : ℂ) + ((ρ / 2 : ℝ) : ℂ) * Complex.I ∈
      ({z : ℂ | 0 < z.im}) ∩ Metric.ball (E : ℂ) ρ := by
    constructor
    · simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      positivity
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
  exact IsPreconnected.union _ hmem.1 hmem.2 h1 h2

theorem aks_closedBall_imag_ge {T r : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall ((T : ℂ) * Complex.I) r) : T - r ≤ z.im := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 : |z.im - T| ≤ ‖z - (T : ℂ) * Complex.I‖ := by
    have := Complex.abs_im_le_norm (z - (T : ℂ) * Complex.I)
    simpa using this
  have := (abs_le.mp (le_trans h1 hz)).1
  linarith

theorem aks_two_div_mono {t : ℝ} (ht : 5 ≤ t) : (5:ℝ)/2 - 2/5 ≤ t/2 - 2/t := by
  have hpos : (0:ℝ) < t := by linarith
  have hkey : t/2 - 2/t - (5/2 - 2/5) = (t - 5)/2 + (t - 5) * (2/(5*t)) := by
    field_simp; ring
  have hnn : 0 ≤ (t - 5)/2 + (t - 5) * (2/(5*t)) := by
    apply add_nonneg (by linarith)
    exact mul_nonneg (by linarith) (by positivity)
  linarith [hkey, hnn]


theorem aks_norm_exp_two_pi_I_mul_le {k : ℤ} {w : ℂ} {ρ : ℝ} (hw : |w.im| ≤ ρ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖
      ≤ Real.exp (2 * Real.pi * |(k : ℝ)| * ρ) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (2 * Real.pi * Complex.I * (k : ℂ) * w).re = -(2 * Real.pi * (k : ℝ) * w.im) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  have h4 : |(k : ℝ) * w.im| = |(k : ℝ)| * |w.im| := abs_mul _ _
  have h5 : |2 * Real.pi * (k : ℝ) * w.im| = 2 * Real.pi * (|(k : ℝ)| * |w.im|) := by
    rw [show (2:ℝ) * Real.pi * (k:ℝ) * w.im = (2 * Real.pi) * ((k:ℝ) * w.im) by ring, abs_mul, h4,
        abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  calc -(2 * Real.pi * (k : ℝ) * w.im) ≤ |2 * Real.pi * (k : ℝ) * w.im| := neg_le_abs _
    _ = 2 * Real.pi * (|(k : ℝ)| * |w.im|) := h5
    _ ≤ 2 * Real.pi * (|(k : ℝ)| * ρ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (abs_nonneg _)) (by positivity)
    _ = 2 * Real.pi * |(k : ℝ)| * ρ := by ring



/-! ## The main argument -/

theorem aks_analyticAt_of_mem {α lam a b : ℝ} (h0 : 0 < lam) (hab : a < b) {M : ℂ → ℝ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (kotaniDomain a b))
    (him : ∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im)
    (hamoM : ∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = amoM α lam z x)
    (hper : ∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x)
    {E₀ : ℝ} (hE₀ : E₀ ∈ Ioo a b) (x₀ : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => M p.1 p.2) (E₀, x₀) := by
  have hWo : IsOpen (kotaniDomain a b) := aks_kotaniDomain_isOpen a b
  set ρ₀ : ℝ := min (E₀ - a) (b - E₀) / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀def]
    have : 0 < min (E₀ - a) (b - E₀) := by
      rw [lt_min_iff]; exact ⟨by linarith [hE₀.1], by linarith [hE₀.2]⟩
    linarith
  have hρ₀le : ρ₀ ≤ min (E₀ - a) (b - E₀) := by rw [hρ₀def]; linarith
  have hballρ₀ : Metric.ball (E₀ : ℂ) ρ₀ ⊆ kotaniDomain a b := aks_mem_kotaniDomain_of_ball hρ₀le
  set W' : Set ℂ := {z : ℂ | 0 < z.im} ∪ Metric.ball (E₀ : ℂ) ρ₀ with hW'def
  have hW'o : IsOpen W' := aks_isOpen_halfPlane_union_ball E₀ ρ₀
  have hW'c : IsPreconnected W' := aks_isPreconnected_halfPlane_union_ball hρ₀pos
  have hW'sub : W' ⊆ kotaniDomain a b := by
    intro z hz
    rcases hz with h | h
    · exact Or.inl (ne_of_gt h)
    · exact hballρ₀ h
  have hden_ne : ∀ p ∈ kotaniDomain a b ×ˢ univ, M p.1 p.2 + Complex.I ≠ 0 := by
    rintro ⟨z, x⟩ ⟨hz, -⟩ h
    have h1 : (M z x).im + 1 = 0 := by simpa using congrArg Complex.im h
    have := him z hz x
    linarith
  have hfcont : ContinuousOn (fun p : ℂ × ℝ => aks_amf M p.1 p.2) (kotaniDomain a b ×ˢ univ) := by
    have hnum : ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2 - Complex.I) (kotaniDomain a b ×ˢ univ) :=
      hcont.sub continuousOn_const
    have hden : ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2 + Complex.I) (kotaniDomain a b ×ˢ univ) :=
      hcont.add continuousOn_const
    have h := hnum.div hden hden_ne
    have hfun : ((fun p : ℂ × ℝ => M p.1 p.2 - Complex.I) / fun p : ℂ × ℝ => M p.1 p.2 + Complex.I)
        = fun p : ℂ × ℝ => aks_amf M p.1 p.2 := by
      funext p; simp only [Pi.div_apply, aks_amf, Kotani.cayley]
    rw [hfun] at h
    exact h
  have hfhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => aks_amf M z x) (kotaniDomain a b) := by
    intro x
    have hne : ∀ z ∈ kotaniDomain a b, M z x + Complex.I ≠ 0 := by
      intro z hz h
      have h1 : (M z x).im + 1 = 0 := by simpa using congrArg Complex.im h
      have := him z hz x
      linarith
    have h1 : DifferentiableOn ℂ (fun z : ℂ => M z x + Complex.I) (kotaniDomain a b) :=
      (hhol x).add_const Complex.I
    have h2 : DifferentiableOn ℂ (fun z : ℂ => M z x - Complex.I) (kotaniDomain a b) :=
      (hhol x).sub_const Complex.I
    have hinv : DifferentiableOn ℂ (fun z : ℂ => (M z x + Complex.I)⁻¹) (kotaniDomain a b) :=
      h1.inv hne
    have hmul := h2.mul hinv
    have hgoal : (fun z : ℂ => aks_amf M z x)
        = fun z : ℂ => (M z x - Complex.I) * (M z x + Complex.I)⁻¹ := by
      funext z; simp only [aks_amf, Kotani.cayley, div_eq_mul_inv]
    rw [hgoal]; exact hmul
  have hce_hol : ∀ k, AnalyticOnNhd ℂ (aks_amce M k) (kotaniDomain a b) := by
    intro k
    exact (fourierCoeff_holomorphic (W := kotaniDomain a b) (f := aks_amf M) hWo hfcont hfhol k).analyticOnNhd hWo
  have hce_le1 : ∀ k z, z ∈ kotaniDomain a b → ‖aks_amce M k z‖ ≤ 1 := by
    intro k z hz
    have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖aks_amf M z t * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)))‖ ≤ 1 := by
      intro t ht
      rw [norm_mul]
      have h1 : ‖aks_amf M z t‖ ≤ 1 := le_of_lt (Kotani.norm_cayley_lt_one (him z hz t))
      have h2 : ‖Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        have : (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        rw [this, Real.exp_zero]
      rw [h2, mul_one]; exact h1
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    simpa [aks_amce] using this
  obtain ⟨σ, hσpos, hσle⟩ := strip_sigma_exists (lam := lam) h0 (by norm_num : (4:ℝ) ≤ 5)
  set σ' : ℝ := σ / 2 with hσ'def
  have hσ'pos : 0 < σ' := by rw [hσ'def]; linarith
  have hσ'lt : σ' < σ := by rw [hσ'def]; linarith
  have hdecay : ∀ k z, z ∈ Metric.closedBall ((6 : ℂ) * Complex.I) 1 →
      ‖aks_amce M k z‖ ≤ Real.exp (-(2 * Real.pi * σ' * |(k : ℝ)|)) := by
    intro k z hz
    have hzim : (5 : ℝ) ≤ z.im := by
      have h := aks_closedBall_imag_ge (T := (6 : ℝ)) (r := 1) hz
      norm_num at h; exact h
    have hz4 : 4 ≤ z.im := by linarith
    have hzpos : 0 < z.im := by linarith
    have hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im :=
      le_trans hσle (aks_two_div_mono hzim)
    obtain ⟨G, hGan, hGB, hGper, hGval⟩ := amoM_strip_cayley (α := α) h0 hz4 hσpos hσz
    have hB : ∀ x : ℂ, |x.im| < σ → ‖G x‖ ≤ 1 := fun x hx => le_of_lt (hGB x hx)
    have hdec := fourierCoeff_decay (δ := σ) hσpos hGan hGper hB hσ'pos hσ'lt k
    have hcongr : (∫ t in (0 : ℝ)..1,
          G (t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)))) = aks_amce M k z := by
      rw [aks_amce]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have h1 : G (t : ℂ) = aks_amf M z t := by
        rw [hGval t]
        simp only [aks_amf, Kotani.cayley]
        rw [hamoM z hzpos t]
      rw [h1]
    rw [hcongr] at hdec
    have heq : (1 : ℝ) * Real.exp (-(2 * Real.pi * |(k : ℝ)| * σ'))
        = Real.exp (-(2 * Real.pi * σ' * |(k : ℝ)|)) := by
      rw [one_mul]; congr 1; ring
    rw [heq] at hdec
    exact hdec
  set K : Set ℂ := Metric.closedBall (E₀ : ℂ) (ρ₀ / 2) with hKdef
  have hD0W' : Metric.closedBall ((6 : ℂ) * Complex.I) 1 ⊆ W' := by
    intro z hz
    left
    have h := aks_closedBall_imag_ge (T := (6 : ℝ)) (r := 1) hz
    show (0:ℝ) < z.im
    linarith
  have hKW' : K ⊆ W' := by
    intro z hz
    right
    simp only [hKdef, Metric.mem_closedBall, Metric.mem_ball] at hz ⊢
    linarith
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨c, hcpos, hc⟩ := propagate_smallness hW'o hW'c (a := (6 : ℂ) * Complex.I) (r := 1)
    (by norm_num) hD0W' K hKW' hKc
  have hdecayK : ∀ k z, z ∈ K →
      ‖aks_amce M k z‖ ≤ Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|)) := by
    intro k z hz
    have h1 : AnalyticOnNhd ℂ (aks_amce M k) W' := (hce_hol k).mono hW'sub
    have h2 : ∀ w ∈ W', ‖aks_amce M k w‖ ≤ 1 := fun w hw => hce_le1 k w (hW'sub hw)
    have h3 : ∀ w ∈ Metric.closedBall ((6 : ℂ) * Complex.I) 1,
        ‖aks_amce M k w‖ ≤ Real.exp (-(2 * Real.pi * σ' * |(k : ℝ)|)) := hdecay k
    have h4 := hc (aks_amce M k) (2 * Real.pi * σ' * |(k : ℝ)|) (by positivity) h1 h2 h3 z hz
    have heq : c * (2 * Real.pi * σ' * |(k : ℝ)|) = 2 * Real.pi * c * σ' * |(k : ℝ)| := by ring
    rwa [heq] at h4
  set U : Set ℂ := Metric.ball (E₀ : ℂ) (ρ₀ / 2) with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUK : U ⊆ K := Metric.ball_subset_closedBall
  have hUW' : U ⊆ W' := fun z hz => Or.inr (Metric.ball_subset_ball (by linarith) hz)
  have hUdom : U ⊆ kotaniDomain a b := fun z hz => hW'sub (hUW' hz)
  have hdecayU : ∀ k z, z ∈ U → ‖aks_amce M k z‖ ≤ Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|)) :=
    fun k z hz => hdecayK k z (hUK hz)
  have hcσ'pos : 0 < c * σ' := mul_pos hcpos hσ'pos
  set V : Set ℂ := {x : ℂ | |x.im| < c * σ' / 2} with hVdef
  have hVo : IsOpen V := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hFz : ∀ z ∈ U, DifferentiableOn ℂ (aks_amF M z) V := by
    intro z hz
    have hdec : ∀ k : ℤ, ‖aks_amce M k z‖ ≤ (1 : ℝ) * Real.exp (-(2 * Real.pi * |(k : ℝ)| * (c * σ'))) := by
      intro k
      rw [one_mul]
      have := hdecayU k z hz
      convert this using 1
      ring
    have h := fourier_series_analytic (c := fun k => aks_amce M k z) (B := 1) (ρ := c * σ')
      (by norm_num) hcσ'pos hdec
    refine (h.mono ?_).differentiableOn
    intro x hx
    rw [hVdef] at hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    linarith
  have hFw : ∀ w ∈ V, DifferentiableOn ℂ (fun z => aks_amF M z w) U := by
    intro w hw
    rw [hVdef] at hw
    have hwabs : |w.im| < c * σ' / 2 := hw
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun k z => aks_amce M k z * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
      (u := fun k : ℤ => Real.exp (-(Real.pi * c * σ' * |(k : ℝ)|))) ?_ ?_ hUo ?_
    · have := summable_int_exp_neg_abs 1 (Real.pi * c * σ') (by positivity)
      simpa [one_mul] using this
    · intro k
      exact (((hce_hol k).mono hUdom).differentiableOn).mul_const _
    · intro k z hz
      have h1 : ‖aks_amce M k z‖ ≤ Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|)) := hdecayU k z hz
      have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖
          ≤ Real.exp (2 * Real.pi * |(k : ℝ)| * (c * σ' / 2)) :=
        aks_norm_exp_two_pi_I_mul_le (le_of_lt hwabs)
      calc ‖aks_amce M k z * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖
          = ‖aks_amce M k z‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)‖ := norm_mul _ _
        _ ≤ Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|))
              * Real.exp (2 * Real.pi * |(k : ℝ)| * (c * σ' / 2)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (-(Real.pi * c * σ' * |(k : ℝ)|)) := by
            rw [← Real.exp_add]; congr 1; ring
  have hFcont : ContinuousOn (fun p : ℂ × ℂ => aks_amF M p.1 p.2) (U ×ˢ V) := by
    refine continuousOn_tsum
      (f := fun k (p : ℂ × ℂ) => aks_amce M k p.1 * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * p.2))
      (u := fun k : ℤ => Real.exp (-(Real.pi * c * σ' * |(k : ℝ)|))) ?_ ?_ ?_
    · intro k
      have h1 : ContinuousOn (fun p : ℂ × ℂ => aks_amce M k p.1) (U ×ˢ V) :=
        ((hce_hol k).mono hUdom).continuousOn.comp continuous_fst.continuousOn
          (fun p hp => hp.1)
      have h2 : ContinuousOn (fun p : ℂ × ℂ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * p.2))
          (U ×ˢ V) := by fun_prop
      exact h1.mul h2
    · have := summable_int_exp_neg_abs 1 (Real.pi * c * σ') (by positivity)
      simpa [one_mul] using this
    · intro k p hp
      rw [Set.mem_prod] at hp
      have h1 : ‖aks_amce M k p.1‖ ≤ Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|)) := hdecayU k p.1 hp.1
      rw [hVdef] at hp
      have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * p.2)‖
          ≤ Real.exp (2 * Real.pi * |(k : ℝ)| * (c * σ' / 2)) :=
        aks_norm_exp_two_pi_I_mul_le (le_of_lt hp.2)
      calc ‖aks_amce M k p.1 * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * p.2)‖
          = ‖aks_amce M k p.1‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * p.2)‖ := norm_mul _ _
        _ ≤ Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|))
              * Real.exp (2 * Real.pi * |(k : ℝ)| * (c * σ' / 2)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (-(Real.pi * c * σ' * |(k : ℝ)|)) := by
            rw [← Real.exp_add]; congr 1; ring
  have hFOn : AnalyticOnNhd ℝ (fun p : ℂ × ℂ => aks_amF M p.1 p.2) (U ×ˢ V) :=
    separately_holomorphic_real_analytic hUo hVo hFcont hFz hFw
  have hfourier : ∀ E : ℝ, (E : ℂ) ∈ U → ∀ x : ℝ, aks_amF M (E : ℂ) (x : ℂ) = aks_amf M E x := by
    intro E hE x
    have hEdom : (E : ℂ) ∈ kotaniDomain a b := hUdom hE
    have hcontg : Continuous (fun t : ℝ => aks_amf M E t) := by
      have h1 : Continuous (fun t : ℝ => M (E : ℂ) t) :=
        hcont.comp_continuous (continuous_const.prodMk continuous_id)
          (fun t => ⟨hEdom, Set.mem_univ t⟩)
      have h2 : Continuous (fun t : ℝ => M (E : ℂ) t + Complex.I) := h1.add continuous_const
      have h3 : ∀ t : ℝ, M (E : ℂ) t + Complex.I ≠ 0 := by
        intro t h
        have h4 : (M (E : ℂ) t).im + 1 = 0 := by simpa using congrArg Complex.im h
        have := him (E : ℂ) hEdom t
        linarith
      have h4 : Continuous (((fun t : ℝ => M (E : ℂ) t) - (fun _ : ℝ => Complex.I)) /
          ((fun t : ℝ => M (E : ℂ) t) + (fun _ : ℝ => Complex.I))) :=
        (h1.sub continuous_const).div h2 h3
      have hfun : (((fun t : ℝ => M (E : ℂ) t) - (fun _ : ℝ => Complex.I)) /
          ((fun t : ℝ => M (E : ℂ) t) + (fun _ : ℝ => Complex.I))) = fun t : ℝ => aks_amf M E t := by
        funext t; simp only [Pi.sub_apply, Pi.add_apply, Pi.div_apply, aks_amf, Kotani.cayley]
      rw [hfun] at h4
      exact h4
    have hperg : ∀ t : ℝ, (fun s : ℝ => aks_amf M E s) (t + 1) = (fun s : ℝ => aks_amf M E s) t := by
      intro t
      simp only [aks_amf]
      rw [hper (E : ℂ) t]
    have hsum : Summable (fun k : ℤ => ∫ s in (0 : ℝ)..1,
        aks_amf M E s * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)))) := by
      refine Summable.of_norm ?_
      have hs : Summable (fun k : ℤ => Real.exp (-(2 * Real.pi * c * σ' * |(k : ℝ)|))) := by
        have := summable_int_exp_neg_abs 1 (2 * Real.pi * c * σ') (by positivity)
        simpa [one_mul] using this
      exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hdecayU k (E : ℂ) hE) hs
    have h := addCircle_fourier_expansion hcontg hperg hsum x
    simpa [aks_amF, aks_amce] using h.symm
  have hmU : (E₀ : ℂ) ∈ U := by
    rw [hUdef, Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; linarith
  have hmV : (x₀ : ℂ) ∈ V := by
    rw [hVdef]; simp only [Set.mem_ofPred_eq, Complex.ofReal_im, abs_zero]; positivity
  have hFAt : AnalyticAt ℝ (fun p : ℂ × ℂ => aks_amF M p.1 p.2) ((E₀ : ℂ), (x₀ : ℂ)) :=
    hFOn _ ⟨hmU, hmV⟩
  have hmap : AnalyticAt ℝ (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) (E₀, x₀) :=
    ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))).analyticAt (E₀, x₀)
  have hFAtR : AnalyticAt ℝ (fun p : ℝ × ℝ => aks_amF M (p.1 : ℂ) (p.2 : ℂ)) (E₀, x₀) := by
    refine AnalyticAt.comp (f := fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))) hFAt hmap
  have hcay : AnalyticAt ℝ (fun u : ℂ => Kotani.cayleyInv u) (aks_amF M (E₀ : ℂ) (x₀ : ℂ)) := by
    have hana : AnalyticOnNhd ℂ Kotani.cayleyInv (Metric.ball (0 : ℂ) 1) := by
      rw [Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
      unfold Kotani.cayleyInv
      refine DifferentiableOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro u hu h
        have : u = 1 := by linear_combination -h
        rw [this] at hu; simp at hu
    have hval : aks_amF M (E₀ : ℂ) (x₀ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      have h1 : ‖aks_amf M E₀ x₀‖ < 1 := Kotani.norm_cayley_lt_one (him (E₀ : ℂ) (hUdom hmU) x₀)
      rw [Metric.mem_ball, dist_zero_right, hfourier E₀ hmU x₀]
      exact h1
    exact ((hana _ hval).restrictScalars (𝕜 := ℝ))
  have hcomp : AnalyticAt ℝ (fun p : ℝ × ℝ => Kotani.cayleyInv (aks_amF M (p.1 : ℂ) (p.2 : ℂ)))
      (E₀, x₀) := by
    refine AnalyticAt.comp (f := fun p : ℝ × ℝ => aks_amF M (p.1 : ℂ) (p.2 : ℂ))
      (g := fun u : ℂ => Kotani.cayleyInv u) (x := (E₀, x₀)) hcay hFAtR
  refine hcomp.congr ?_
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨{p : ℝ × ℝ | (p.1 : ℂ) ∈ U}, ?_, ?_⟩
  · have hop : IsOpen {p : ℝ × ℝ | (p.1 : ℂ) ∈ U} :=
      hUo.preimage (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous
    exact hop.mem_nhds (by simp [hmU])
  · intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    have hpdom : (p.1 : ℂ) ∈ kotaniDomain a b := hUdom hp
    show Kotani.cayleyInv (aks_amF M (p.1 : ℂ) (p.2 : ℂ)) = M p.1 p.2
    rw [hfourier p.1 hp p.2]
    exact Kotani.cayleyInv_cayley (him (p.1 : ℂ) hpdom p.2)


/-- **Kotani's analyticity of the section.**  Given a continuous `ℍ`-valued section `M` of the
almost Mathieu cocycle on the domain `kotaniDomain a b`, holomorphic in the energy variable and
agreeing with the `m`-function on the upper half plane, `M` is jointly real analytic on
`(a,b) × ℝ`. -/
theorem analytic_kotani_section {α lam a b : ℝ} (h0 : 0 < lam) (hab : a < b) {M : ℂ → ℝ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (Work.TMContract.kotaniDomain a b ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (Work.TMContract.kotaniDomain a b))
    (him : ∀ z ∈ Work.TMContract.kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im)
    (hamoM : ∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = Work.TMContract.amoM α lam z x)
    (hper : ∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x)
    (hsec : ∀ z ∈ Work.TMContract.kotaniDomain a b, ∀ x : ℝ,
      M z (x + α) = Work.TMContract.mob (Work.TMContract.tmC lam z x) (M z x)) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => M p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) := by
  intro p hp
  rw [Set.mem_prod] at hp
  exact aks_analyticAt_of_mem h0 hab hcont hhol him hamoM hper hp.1 p.2

end

end Work.TMComp.MAnalytic
