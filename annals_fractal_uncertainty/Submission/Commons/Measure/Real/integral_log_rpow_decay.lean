import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Commons.Measure.Real

/-- Auxiliary: derivative facts for the antiderivative `t ↦ (log t)^(1-β)/(1-β)` of
`t ↦ t⁻¹ (log t)^{-β}`, valid for `t > 1`. -/
private lemma log_rpow_antideriv (β : ℝ) (hβ : 1 < β) {c : ℝ} (hc : 1 < c) :
    (∀ x ∈ Set.Ici c, HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β))
        (x⁻¹ / (Real.log x) ^ β) x) ∧
    (∀ x ∈ Set.Ioi c, 0 ≤ x⁻¹ / (Real.log x) ^ β) ∧
    Tendsto (fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β)) atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le hc hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have h1 : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - β))
        (x⁻¹ * (1 - β) * (Real.log x) ^ ((1 - β) - 1)) x :=
      h1.rpow_const (Or.inl (ne_of_gt hlog))
    have h3 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β))
        ((x⁻¹ * (1 - β) * (Real.log x) ^ ((1 - β) - 1)) / (1 - β)) x :=
      h2.div_const (1 - β)
    convert h3 using 1
    rw [show (1 : ℝ) - β - 1 = -β by ring, Real.rpow_neg (le_of_lt hlog)]
    have hne : (1 - β) ≠ 0 := by linarith
    have hne2 : (Real.log x) ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlog β)
    field_simp
  · intro x hx
    have hx1 : 1 < x := lt_trans hc hx
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    exact div_nonneg (inv_pos.mpr hx0).le (Real.rpow_pos_of_pos hlog β).le
  · have h1 : Tendsto (fun t : ℝ => (Real.log t) ^ (1 - β)) atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop (show (0 : ℝ) < β - 1 by linarith)).comp
        Real.tendsto_log_atTop using 1
      ext t
      simp [Function.comp_apply, neg_sub]
    simpa using h1.div_const (1 - β)

/-- Auxiliary integral computation: `∫_c^∞ t⁻¹ (log t)^{-β} = (log c)^{1-β}/(β-1)`
for `β > 1` and `c > 1`. -/
private lemma integral_inv_div_log_rpow_Ioi (β : ℝ) (hβ : 1 < β) {c : ℝ} (hc : 1 < c) :
    ∫ t in Set.Ioi c, t⁻¹ / (Real.log t) ^ β = (Real.log c) ^ (1 - β) / (β - 1) := by
  obtain ⟨hd, hpos, hlim⟩ := log_rpow_antideriv β hβ hc
  have hmain := integral_Ioi_of_hasDerivAt_of_nonneg' (a := c)
    (g := fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β))
    (g' := fun x => x⁻¹ / (Real.log x) ^ β) (l := 0) hd hpos hlim
  rw [hmain, show (1 : ℝ) - β = -(β - 1) by ring, div_neg]
  ring

/-- Auxiliary integrability: `t ↦ t⁻¹ (log t)^{-β}` is integrable on `(c, ∞)` for
`β > 1`, `c > 1`. -/
private lemma integrableOn_inv_div_log_rpow_Ioi (β : ℝ) (hβ : 1 < β) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (Real.log t) ^ β) (Set.Ioi c) := by
  obtain ⟨hd, hpos, hlim⟩ := log_rpow_antideriv β hβ hc
  exact integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim

/-- The dominating function `r ↦ r/(log (2+r))^β/(1+r²)`. -/
private noncomputable def psi (β : ℝ) : ℝ → ℝ :=
  fun r => r / (Real.log (2 + r)) ^ β / (1 + r ^ 2)

private lemma lintegral_psi_Ioc (β : ℝ) (hβ : 1 < β) :
    ∫⁻ r in Set.Ioc (0 : ℝ) 2, ENNReal.ofReal (psi β r) ≤
      ENNReal.ofReal (4 / (Real.log 2) ^ β) := by
  have hβ0 : 0 < β := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : ∀ r ∈ Set.Ioc (0 : ℝ) 2,
      ENNReal.ofReal (psi β r) ≤ ENNReal.ofReal (2 / (Real.log 2) ^ β) := by
    intro r hr
    obtain ⟨hr0, hr2⟩ := hr
    apply ENNReal.ofReal_le_ofReal
    have hlog_pos : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
    have hlog_mono : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
    have hpow : (Real.log 2) ^ β ≤ (Real.log (2 + r)) ^ β :=
      Real.rpow_le_rpow hlog2.le hlog_mono hβ0.le
    have hnum : 0 ≤ r / (Real.log (2 + r)) ^ β :=
      div_nonneg hr0.le (Real.rpow_pos_of_pos hlog_pos β).le
    have step1 : psi β r ≤ r / (Real.log (2 + r)) ^ β := by
      have := div_le_div_of_nonneg_left hnum (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ 1 + r ^ 2 by nlinarith [sq_nonneg r])
      simpa only [psi, div_one] using this
    have step2 : r / (Real.log (2 + r)) ^ β ≤ 2 / (Real.log (2 + r)) ^ β :=
      div_le_div_of_nonneg_right hr2 (Real.rpow_pos_of_pos hlog_pos β).le
    have step3 : 2 / (Real.log (2 + r)) ^ β ≤ 2 / (Real.log 2) ^ β :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hlog2 β) hpow
    exact step1.trans (step2.trans step3)
  calc ∫⁻ r in Set.Ioc (0 : ℝ) 2, ENNReal.ofReal (psi β r)
      ≤ ∫⁻ r in Set.Ioc (0 : ℝ) 2, ENNReal.ofReal (2 / (Real.log 2) ^ β) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal (2 / (Real.log 2) ^ β) * volume (Set.Ioc (0 : ℝ) 2) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (2 / (Real.log 2) ^ β) * ENNReal.ofReal 2 := by
        rw [Real.volume_Ioc]; norm_num
    _ = ENNReal.ofReal (4 / (Real.log 2) ^ β) := by
        rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) (Real.rpow_pos_of_pos hlog2 β).le)]
        congr 1
        ring

private lemma lintegral_psi_Ioi (β : ℝ) (hβ : 1 < β) :
    ∫⁻ r in Set.Ioi (2 : ℝ), ENNReal.ofReal (psi β r) ≤
      ENNReal.ofReal ((Real.log 2) ^ (1 - β) / (β - 1)) := by
  have hβ0 : 0 < β := by linarith
  have hint : IntegrableOn (fun t : ℝ => t⁻¹ / (Real.log t) ^ β) (Set.Ioi 2) :=
    integrableOn_inv_div_log_rpow_Ioi β hβ (by norm_num)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (2 : ℝ))]
      (fun t : ℝ => t⁻¹ / (Real.log t) ^ β) := by
    change ∀ᵐ t ∂(volume.restrict (Set.Ioi (2 : ℝ))), 0 ≤ t⁻¹ / (Real.log t) ^ β
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht2 : (2 : ℝ) < t := ht
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have ht0 : 0 < t := by linarith
    exact div_nonneg (inv_pos.mpr ht0).le (Real.rpow_pos_of_pos hlog β).le
  have hpt : ∀ r ∈ Set.Ioi (2 : ℝ),
      ENNReal.ofReal (psi β r) ≤ ENNReal.ofReal (r⁻¹ / (Real.log r) ^ β) := by
    intro r hr
    apply ENNReal.ofReal_le_ofReal
    have hr2 : (2 : ℝ) < r := hr
    have hr0 : 0 < r := by linarith
    have hr1 : 1 < r := by linarith
    have hlogr : 0 < Real.log r := Real.log_pos hr1
    have hlog_mono : Real.log r ≤ Real.log (2 + r) := Real.log_le_log hr0 (by linarith)
    have hpow : (Real.log r) ^ β ≤ (Real.log (2 + r)) ^ β :=
      Real.rpow_le_rpow hlogr.le hlog_mono hβ0.le
    have step1 : r / (Real.log (2 + r)) ^ β ≤ r / (Real.log r) ^ β :=
      div_le_div_of_nonneg_left hr0.le (Real.rpow_pos_of_pos hlogr β) hpow
    have step12 : psi β r ≤ r / (Real.log r) ^ β / (1 + r ^ 2) := by
      have := div_le_div_of_nonneg_right step1 (by positivity : (0 : ℝ) ≤ 1 + r ^ 2)
      simpa only [psi] using this
    have hden : r ^ 2 ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
    have hnum : 0 ≤ r / (Real.log r) ^ β :=
      div_nonneg hr0.le (Real.rpow_pos_of_pos hlogr β).le
    have step2 : r / (Real.log r) ^ β / (1 + r ^ 2) ≤ r / (Real.log r) ^ β / r ^ 2 :=
      div_le_div_of_nonneg_left hnum (by positivity : (0 : ℝ) < r ^ 2) hden
    have step3 : r / (Real.log r) ^ β / r ^ 2 = r⁻¹ / (Real.log r) ^ β := by
      field_simp
    exact step12.trans (step2.trans (le_of_eq step3))
  calc ∫⁻ r in Set.Ioi (2 : ℝ), ENNReal.ofReal (psi β r)
      ≤ ∫⁻ r in Set.Ioi (2 : ℝ), ENNReal.ofReal (r⁻¹ / (Real.log r) ^ β) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (∫ r in Set.Ioi (2 : ℝ), r⁻¹ / (Real.log r) ^ β) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    _ = ENNReal.ofReal ((Real.log 2) ^ (1 - β) / (β - 1)) := by
        rw [integral_inv_div_log_rpow_Ioi β hβ (by norm_num : (1 : ℝ) < 2)]

/-- The growth-condition integral of §6.1: if `G` is dominated by `r/(log (2+r))^β` on `(0,∞)`
with `β > 1`, then `∫_0^∞ G(r)/(1+r^2) dr` is bounded by a constant depending only on `β`. -/
theorem integral_log_rpow_decay (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ → ℝ,
      (∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ G r) →
      (∀ r ∈ Set.Ioi (0 : ℝ), G r ≤ r / (Real.log (2 + r)) ^ β) →
      (∫ r in Set.Ioi (0 : ℝ), G r / (1 + r ^ 2)) ≤ C := by
  have hβ0 : 0 < β := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 / (Real.log 2) ^ β + (Real.log 2) ^ (1 - β) / (β - 1) + 1,
    by positivity, ?_⟩
  intro G hGnn hGbd
  have hle : ∀ r ∈ Set.Ioi (0 : ℝ), G r / (1 + r ^ 2) ≤ psi β r := by
    intro r hr
    have h2 : 0 ≤ 1 + r ^ 2 := by positivity
    have := div_le_div_of_nonneg_right (hGbd r hr) h2
    simpa only [psi] using this
  have hφnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun r => G r / (1 + r ^ 2)) := by
    change ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ G r / (1 + r ^ 2)
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    exact div_nonneg (hGnn r hr) (by positivity)
  by_cases hmeas : AEStronglyMeasurable (fun r => G r / (1 + r ^ 2))
      (volume.restrict (Set.Ioi (0 : ℝ)))
  · rw [integral_eq_lintegral_of_nonneg_ae hφnn hmeas]
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_)
      (le_of_eq (ENNReal.toReal_ofReal (by positivity)))
    calc ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (G r / (1 + r ^ 2))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (psi β r) :=
          setLIntegral_mono' measurableSet_Ioi
            (fun r hr => ENNReal.ofReal_le_ofReal (hle r hr))
      _ = (∫⁻ r in Set.Ioc (0 : ℝ) 2, ENNReal.ofReal (psi β r))
            + (∫⁻ r in Set.Ioi (2 : ℝ), ENNReal.ofReal (psi β r)) := by
          rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num),
            lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
      _ ≤ ENNReal.ofReal (4 / (Real.log 2) ^ β)
            + ENNReal.ofReal ((Real.log 2) ^ (1 - β) / (β - 1)) :=
          add_le_add (lintegral_psi_Ioc β hβ) (lintegral_psi_Ioi β hβ)
      _ = ENNReal.ofReal (4 / (Real.log 2) ^ β + (Real.log 2) ^ (1 - β) / (β - 1)) := by
          rw [ENNReal.ofReal_add
            (div_nonneg (by norm_num) (Real.rpow_pos_of_pos hlog2 β).le)
            (div_nonneg (Real.rpow_pos_of_pos hlog2 (1 - β)).le (by linarith))]
      _ ≤ ENNReal.ofReal (4 / (Real.log 2) ^ β + (Real.log 2) ^ (1 - β) / (β - 1) + 1) :=
          ENNReal.ofReal_le_ofReal (by norm_num)
  · rw [integral_non_aestronglyMeasurable hmeas]
    positivity

end Commons.Measure.Real