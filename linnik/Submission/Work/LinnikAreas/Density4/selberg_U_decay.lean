import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selberg_U_aux
import Submission.Work.LinnikAreas.Density4.Udecay.step_integral
import Submission.Work.LinnikAreas.Density4.Udecay.recip_bound
import Submission.Work.LinnikAreas.Density4.Udecay.exp_sqrtlog_ioi
import Submission.Work.LinnikAreas.Density4.Udecay.exp_sqrtlog_integrable
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_identity
import Submission.Work.LinnikAreas.Density4.Udecay.mu_series_zeta_inv
import Submission.Work.LinnikAreas.Density4.Udecay.zeta_pole_limit

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open MeasureTheory Filter

/-!
## Decay of Selberg's `U`-function

`selU x = Σ_{m ≤ x} μ(m) log (x/m) / m` is the (logarithmically weighted) Möbius reciprocal
sum appearing in Selberg's sieve.  Its limit is `1`: writing `A(t) = Σ_{m ≤ ⌊t⌋} μ(m)/m`
(so that `selU x = ∫_1^x A(t) dt/t`, a summation-by-parts identity) the constant is pinned by
the Mellin transform identity

  `∫_1^∞ A(t) t^{-1-s} dt = (1/s) Σ_n μ(n) n^{-1-s} = (1/s) ζ(1+s)^{-1}  (s > 0)`,

whose `s → 0⁺` limit is `1` because ζ has a simple pole with residue one at `s = 1`.  Since
`A(t) = O(exp (-c √(log t)))`, the tail of the integral is then of size
`(2/c) (√(log x) + 1/c) exp (-c √(log x))`, which gives the stated bound.

The analytic inputs are proved in `Submission/Work/LinnikAreas/Density4/Udecay/`:
`step_integral`, `recip_bound`, `exp_sqrtlog_ioi`, `exp_sqrtlog_integrable`, `mellin_identity`,
`mu_series_zeta_inv` and `zeta_pole_limit`.
-/

theorem selberg_U_decay : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |Work.LinnikAreas.Density4.selU x - 1| ≤ C * (1 + Real.sqrt (Real.log x)) * Real.exp (-(c * Real.sqrt (Real.log x))) := by
  -- the seven analytic inputs
  have h_recip_bound := Udecay.recip_bound
  have h_step : ∀ x : ℝ, 1 ≤ x →
      selU x = ∫ t in (1:ℝ)..x, muRecip t / t := Udecay.step_integral
  have h_ioi : ∀ {c' : ℝ}, 0 < c' → ∀ {x : ℝ}, 1 ≤ x →
      ∫ t in Set.Ioi x, Real.exp (-(c' * Real.sqrt (Real.log t))) / t
        = (2 / c') * (Real.sqrt (Real.log x) + 1 / c') * Real.exp (-(c' * Real.sqrt (Real.log x))) :=
    fun {c'} hc' {x} hx => Udecay.exp_sqrtlog_ioi hc' hx
  have h_integrable : ∀ {c' : ℝ}, 0 < c' →
      IntegrableOn (fun t : ℝ => Real.exp (-(c' * Real.sqrt (Real.log t))) / t) (Set.Ioi 1) ∧
      IntegrableOn (fun t : ℝ => Real.exp (-(c' * Real.sqrt (Real.log t))) * Real.log t / t)
        (Set.Ioi 1) := fun {c'} hc' => Udecay.exp_sqrtlog_integrable hc'
  have h_mellin : ∀ s : ℝ, 0 < s →
      ∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ)
        = (1 / s) * (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ)) :=
    fun s hs => Udecay.mellin_identity s hs
  have h_series : ∀ s : ℝ, 0 < s →
      (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ))
        = ((riemannZeta ((1 + s : ℝ) : ℂ))⁻¹).re := fun s hs => Udecay.mu_series_zeta_inv s hs
  have h_pole : Tendsto (fun s : ℝ => (1 / s) * ((riemannZeta ((1 + s : ℝ) : ℂ))⁻¹).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := Udecay.zeta_pole_limit
  -- the main argument
  obtain ⟨c, C, hc, hC, hbound⟩ := h_recip_bound
  obtain ⟨hint1, hint2⟩ := h_integrable hc
  have hmeasM : Measurable (fun t : ℝ => muRecip t) :=
    (measurable_of_countable Commons.NumberTheory.Moebius.muRecipSum).comp Nat.measurable_floor
  have hCint1 : Integrable (fun t => C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t))
      (volume.restrict (Set.Ioi 1)) := (hint1 : Integrable _ _).const_mul C
  have hAint : IntegrableOn (fun t => muRecip t / t) (Set.Ioi 1) := by
    change Integrable (fun t => muRecip t / t) (volume.restrict (Set.Ioi 1))
    refine hCint1.mono' (hmeasM.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) ≤ t := by have h : (1:ℝ) < t := ht; linarith
    have ht0 : (0:ℝ) < t := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |muRecip t| / t ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) / t :=
          div_le_div_of_nonneg_right (hbound t ht1) (le_of_lt ht0)
      _ = C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t) := by ring
  have hAint_s : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => muRecip t / t ^ (1 + s : ℝ)) (Set.Ioi 1) := by
    intro s hs
    change Integrable (fun t => muRecip t / t ^ (1 + s : ℝ)) (volume.restrict (Set.Ioi 1))
    refine hCint1.mono'
      (hmeasM.div ((Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ 1 + s)).measurable)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) ≤ t := by have h : (1:ℝ) < t := ht; linarith
    have ht0 : (0:ℝ) < t := by linarith
    have hpowpos : (0:ℝ) < t ^ (1 + s : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hpowge : t ≤ t ^ (1 + s : ℝ) := by
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ (1 + s : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpowpos]
    have hnn : (0:ℝ) ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) := by positivity
    calc |muRecip t| / t ^ (1 + s : ℝ)
          ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) / t ^ (1 + s : ℝ) :=
          div_le_div_of_nonneg_right (hbound t ht1) (le_of_lt hpowpos)
      _ ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) / t :=
          div_le_div_of_nonneg_left hnn ht0 hpowge
      _ = C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t) := by ring
  -- pointwise comparison of `A(t)/t` with `A(t)/t^{1+s}`
  have key_pt : ∀ {s t : ℝ}, 0 < s → 1 ≤ t →
      |muRecip t / t - muRecip t / t ^ (1 + s : ℝ)|
        ≤ s * C * (Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t) := by
    intro s t hs ht1
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hts : (0:ℝ) < t ^ s := Real.rpow_pos_of_pos ht0 s
    have hpow : t ^ (1 + s : ℝ) = t * t ^ s := by rw [Real.rpow_add ht0, Real.rpow_one]
    have hkey : 1 - 1 / t ^ s ≤ s * Real.log t := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hts)
      rw [Real.log_inv, Real.log_rpow ht0] at h
      rw [one_div]
      linarith
    have hgen : |1/t - 1/t^(1+s:ℝ)| ≤ s * Real.log t / t := by
      have hdiff : 1 / t - 1 / t ^ (1 + s : ℝ) = (1/t) * (1 - 1 / t ^ s) := by
        rw [hpow]; field_simp
      have hnn : 0 ≤ 1 - 1 / t ^ s := by
        have : 1 / t ^ s ≤ 1 := by
          rw [div_le_one hts]; exact Real.one_le_rpow ht1 hs.le
        linarith
      rw [hdiff, abs_of_nonneg (mul_nonneg (by positivity) hnn)]
      calc (1/t) * (1 - 1 / t ^ s) ≤ (1/t) * (s * Real.log t) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = s * Real.log t / t := by ring
    have hsplit : muRecip t / t - muRecip t / t ^ (1 + s : ℝ)
        = muRecip t * (1/t - 1/t^(1+s:ℝ)) := by ring
    rw [hsplit, abs_mul]
    calc |muRecip t| * |1/t - 1/t^(1+s:ℝ)|
        ≤ (C * Real.exp (-(c * Real.sqrt (Real.log t)))) * (s * Real.log t / t) :=
          mul_le_mul (hbound t ht1) hgen (abs_nonneg _) (by positivity)
      _ = s * C * (Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t) := by ring
  -- the Mellin bound: `|L - Φ(s)| ≤ s · C · K`
  have hmellin_bound : ∀ s : ℝ, 0 < s →
      |selULimit - (∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ))| ≤
        s * (C * (∫ t in Set.Ioi 1, Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t)) := by
    intro s hs
    have h2int := hAint_s s hs
    have hdiff : ∫ t in Set.Ioi 1, (muRecip t / t - muRecip t / t ^ (1 + s : ℝ))
        = (∫ t in Set.Ioi 1, muRecip t / t)
          - (∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ)) :=
      integral_sub (hAint : Integrable _ _) (h2int : Integrable _ _)
    have habs : |∫ t in Set.Ioi 1, (muRecip t / t - muRecip t / t ^ (1 + s : ℝ))|
        ≤ ∫ t in Set.Ioi 1, |muRecip t / t - muRecip t / t ^ (1 + s : ℝ)| := by
      simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi 1))
        (fun t => muRecip t / t - muRecip t / t ^ (1 + s : ℝ))
    have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioi 1)),
        |muRecip t / t - muRecip t / t ^ (1 + s : ℝ)|
          ≤ s * C * (Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact key_pt hs (le_of_lt ht)
    have hintabs : Integrable (fun t => |muRecip t / t - muRecip t / t ^ (1 + s : ℝ)|)
        (volume.restrict (Set.Ioi 1)) := ((hAint : Integrable _ _).sub (h2int : Integrable _ _)).abs
    have hintg : Integrable
        (fun t => s * C * (Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t))
        (volume.restrict (Set.Ioi 1)) := (hint2 : Integrable _ _).const_mul (s * C)
    have hmono := integral_mono_ae hintabs hintg hpt
    have hval : ∫ t in Set.Ioi 1, s * C * (Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t)
        = s * C * (∫ t in Set.Ioi 1, Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t) :=
      MeasureTheory.integral_const_mul _ _
    calc |selULimit - (∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ))|
        = |∫ t in Set.Ioi 1, (muRecip t / t - muRecip t / t ^ (1 + s : ℝ))| := by rw [hdiff]; rfl
      _ ≤ ∫ t in Set.Ioi 1, |muRecip t / t - muRecip t / t ^ (1 + s : ℝ)| := habs
      _ ≤ ∫ t in Set.Ioi 1, s * C * (Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t) :=
            hmono
      _ = s * (C * (∫ t in Set.Ioi 1, Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t)) := by
            rw [hval]; ring
  -- `Φ(s) → 1` as `s → 0⁺`
  have hPsi_tendsto : Tendsto (fun s : ℝ => ∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have heq : (fun s : ℝ => (1 / s) * ((riemannZeta ((1 + s : ℝ) : ℂ))⁻¹).re)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun s : ℝ => ∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [h_mellin s hs, h_series s hs]
    exact Filter.Tendsto.congr' heq h_pole
  -- hence the limit of `selU` is `1`
  have hL1 : selULimit = 1 := by
    have hineq : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), |selULimit - 1| ≤
        s * (C * (∫ t in Set.Ioi 1, Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t))
        + |(∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ)) - 1| := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact le_trans (abs_sub_le _ _ _) (add_le_add (hmellin_bound s hs) le_rfl)
    have hlim : Tendsto (fun s : ℝ =>
          s * (C * (∫ t in Set.Ioi 1, Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t))
          + |(∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ)) - 1|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hid : Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        Filter.tendsto_id.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun s : ℝ =>
            s * (C * (∫ t in Set.Ioi 1, Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hid.mul tendsto_const_nhds
      have h2 : Tendsto (fun s : ℝ => |(∫ t in Set.Ioi 1, muRecip t / t ^ (1 + s : ℝ)) - 1|)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using (hPsi_tendsto.sub_const 1).abs
      simpa using h1.add h2
    have hle : |selULimit - 1| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hineq
    have h0 : |selULimit - 1| = 0 := le_antisymm hle (abs_nonneg _)
    linarith [abs_eq_zero.mp h0]
  -- the tail estimate
  refine ⟨c, C * max (2/c) (2/c^2), hc, ?_, ?_⟩
  · have h2c : (0:ℝ) < max (2/c) (2/c^2) := lt_max_of_lt_left (by positivity)
    positivity
  · intro x hx
    have hx1 : (1:ℝ) ≤ x := by linarith
    have hsel : selU x = selULimit - ∫ t in Set.Ioi x, muRecip t / t := by
      rw [h_step x hx1]
      exact (intervalIntegral.integral_Ioi_sub_Ioi hAint hx1).symm
    have hxint : IntegrableOn (fun t => muRecip t / t) (Set.Ioi x) :=
      hAint.mono_set (Set.Ioi_subset_Ioi hx1)
    have hCintx : Integrable (fun t => C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t))
        (volume.restrict (Set.Ioi x)) :=
      (((hint1 : Integrable _ _).mono_set (Set.Ioi_subset_Ioi hx1))).const_mul C
    have hptx : ∀ᵐ t ∂(volume.restrict (Set.Ioi x)),
        |muRecip t / t| ≤ C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hxt : x < t := ht
      have ht1 : (1:ℝ) ≤ t := by linarith
      have ht0 : (0:ℝ) < t := by linarith
      rw [abs_div, abs_of_pos ht0]
      calc |muRecip t| / t ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) / t :=
            div_le_div_of_nonneg_right (hbound t ht1) (le_of_lt ht0)
        _ = C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t) := by ring
    have htail : |∫ t in Set.Ioi x, muRecip t / t| ≤
        C * ((2/c) * (Real.sqrt (Real.log x) + 1/c) * Real.exp (-(c * Real.sqrt (Real.log x)))) := by
      have hnorm : |∫ t in Set.Ioi x, muRecip t / t| ≤ ∫ t in Set.Ioi x, |muRecip t / t| := by
        simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Set.Ioi x)) (fun t => muRecip t / t)
      have hmono := integral_mono_ae ((hxint : Integrable _ _).abs) hCintx hptx
      calc |∫ t in Set.Ioi x, muRecip t / t| ≤ ∫ t in Set.Ioi x, |muRecip t / t| := hnorm
        _ ≤ ∫ t in Set.Ioi x, C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t) := hmono
        _ = C * (∫ t in Set.Ioi x, Real.exp (-(c * Real.sqrt (Real.log t))) / t) :=
              MeasureTheory.integral_const_mul _ _
        _ = C * ((2/c) * (Real.sqrt (Real.log x) + 1/c) * Real.exp (-(c * Real.sqrt (Real.log x)))) := by
              rw [h_ioi hc hx1]
    have hkey : (2/c) * (Real.sqrt (Real.log x) + 1/c)
        ≤ max (2/c) (2/c^2) * (1 + Real.sqrt (Real.log x)) := by
      have hmax1 : 2/c ≤ max (2/c) (2/c^2) := le_max_left _ _
      have hmax2 : 2/c^2 ≤ max (2/c) (2/c^2) := le_max_right _ _
      have hsqrtL : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
      have h1 : (2/c) * Real.sqrt (Real.log x) ≤ max (2/c) (2/c^2) * Real.sqrt (Real.log x) :=
        mul_le_mul_of_nonneg_right hmax1 hsqrtL
      have h2 : (2/c) * (1/c) ≤ max (2/c) (2/c^2) := by
        have he : (2/c) * (1/c) = 2/c^2 := by field_simp
        rw [he]; exact hmax2
      calc (2/c) * (Real.sqrt (Real.log x) + 1/c)
          = (2/c)*Real.sqrt (Real.log x) + (2/c)*(1/c) := by ring
        _ ≤ max (2/c) (2/c^2) * Real.sqrt (Real.log x) + max (2/c) (2/c^2) * 1 := by
            exact add_le_add h1 (by simpa using h2)
        _ = max (2/c) (2/c^2) * (1 + Real.sqrt (Real.log x)) := by ring
    have hred : selU x - 1 = -(∫ t in Set.Ioi x, muRecip t / t) := by rw [hsel, hL1]; ring
    rw [hred, abs_neg]
    calc |∫ t in Set.Ioi x, muRecip t / t|
        ≤ C * ((2/c) * (Real.sqrt (Real.log x) + 1/c)
            * Real.exp (-(c * Real.sqrt (Real.log x)))) := htail
      _ ≤ C * (max (2/c) (2/c^2) * (1 + Real.sqrt (Real.log x))
            * Real.exp (-(c * Real.sqrt (Real.log x)))) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
            exact mul_le_mul_of_nonneg_right hkey (Real.exp_nonneg _)
      _ = (C * max (2/c) (2/c^2)) * (1 + Real.sqrt (Real.log x))
            * Real.exp (-(c * Real.sqrt (Real.log x))) := by
            ring

end Work.LinnikAreas.Density4
