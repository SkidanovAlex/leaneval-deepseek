import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.deriv_kW_eq
import Submission.Work.RHContract.A.kernel_antideriv
import Submission.Work.RHContract.A.ibp_psi

/-!
# The linear-kernel identity

For `a c x : ℝ` with `1 < x`,

`(-a x + c) k(x) - ∫_x^∞ (-a t + c) (-k'(t)) dt = a/(x log x)`

where `k = kW`.  This is improper integration by parts for the primitive
`H(t) = (a t - c) k(t) + a/(t log t)`, whose derivative is `(-a t + c)(-k'(t))`, together with
the limit `H(t) → 0`.
-/

namespace Work.RHContract.A

open MeasureTheory

/-- `kW t → 0` as `t → ∞`. -/
private lemma tendsto_kW_zero :
    Filter.Tendsto Work.RHContract.kW Filter.atTop (nhds 0) := by
  refine squeeze_zero' (g := fun s : ℝ => 2/s) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with s hs
    have hs0 : (0:ℝ) < s := by linarith
    have hl : 0 < Real.log s := Real.log_pos hs
    rw [Work.RHContract.kW]
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))] with s hs hlog
    have hs0 : (0:ℝ) < s := by linarith
    have hL : (0:ℝ) ≤ Real.log s := by linarith
    have hsL : (1:ℝ) ≤ s * Real.log s := by
      have h := mul_le_mul hlog (le_of_lt hs) (zero_le_one) hL
      simpa [mul_comm] using h
    have key : Real.log s + 1 ≤ 2 * s * (Real.log s)^2 := by
      calc Real.log s + 1 ≤ 2 * Real.log s := by linarith
        _ = (2 * Real.log s) * 1 := by ring
        _ ≤ (2 * Real.log s) * (s * Real.log s) := mul_le_mul_of_nonneg_left hsL (by linarith)
        _ = 2 * s * (Real.log s)^2 := by ring
    rw [Work.RHContract.kW, div_le_iff₀ (by positivity : (0:ℝ) < s^2 * (Real.log s)^2)]
    field_simp
    linarith [key]
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id

/-- `t * kW t → 0` as `t → ∞`. -/
private lemma tendsto_mul_kW_zero :
    Filter.Tendsto (fun s : ℝ => s * Work.RHContract.kW s) Filter.atTop (nhds 0) := by
  refine squeeze_zero' (g := fun s : ℝ => 2/s) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with s hs
    have hs0 : (0:ℝ) < s := by linarith
    have hl : 0 < Real.log s := Real.log_pos hs
    rw [Work.RHContract.kW]
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))] with s hs hlog
    have hs0 : (0:ℝ) < s := by linarith
    have hL : (0:ℝ) ≤ Real.log s := by linarith
    have hkey : Real.log s + 1 ≤ 2 * (Real.log s)^2 := by
      nlinarith [hlog, hL, sq_nonneg (Real.log s - 1)]
    have h1 : s * ((Real.log s + 1)/(s^2*(Real.log s)^2))
        = (Real.log s + 1)/(s*(Real.log s)^2) := by
      field_simp
    rw [Work.RHContract.kW, h1, div_le_iff₀ (by positivity : (0:ℝ) < s*(Real.log s)^2)]
    field_simp
    linarith [hkey]
  · exact Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id

/-- The boundary term `H(t) = (a t - c) kW t + a/(t log t)` vanishes at `+∞`. -/
private lemma tendsto_pad (a c : ℝ) :
    Filter.Tendsto (fun t : ℝ => (a*t - c) * Work.RHContract.kW t + a/(t*Real.log t))
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => (a * t - c) * Work.RHContract.kW t) Filter.atTop (nhds 0) := by
    have ha := tendsto_mul_kW_zero.const_mul a
    have hc := tendsto_kW_zero.const_mul c
    have h := ha.sub hc
    simpa [sub_mul, mul_assoc] using h
  have h2 : Filter.Tendsto (fun t : ℝ => a / (t * Real.log t)) Filter.atTop (nhds 0) := by
    have h := one_div_mul_log_tendsto.const_mul a
    simpa [div_eq_mul_inv] using h
  have h := h1.add h2
  simpa using h

/-- `H' = (-a t + c)·(-kW')`. -/
private lemma hasDerivAt_pad (a c : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => (a*s - c)*Work.RHContract.kW s + a/(s*Real.log s))
      ((-a * t + c) * (-deriv Work.RHContract.kW t)) t := by
  have htI : t ∈ Set.Ioi (1:ℝ) := ht
  have hlin : HasDerivAt (fun s : ℝ => a * s - c) a t := by
    have h1 : HasDerivAt (fun s : ℝ => a * s) a t := by
      have h := (hasDerivAt_pow 1 t).const_mul a
      simpa using h
    simpa using h1.sub_const c
  have hkW : HasDerivAt Work.RHContract.kW (deriv Work.RHContract.kW t) t := by
    have hd : DifferentiableOn ℝ Work.RHContract.kW (Set.Ioi 1) :=
      contDiffOn_kW.differentiableOn (by norm_num)
    exact ((hd t htI).differentiableAt (isOpen_Ioi.mem_nhds htI)).hasDerivAt
  have hprod := hlin.mul hkW
  have hG := kW_hasDerivAt_antideriv ht
  have hpad2 : HasDerivAt (fun s : ℝ => -a * (-1/(s*Real.log s))) (-a * (Work.RHContract.kW t)) t :=
    hG.const_mul (-a)
  have hsum := hprod.add hpad2
  convert hsum using 1 <;> try rfl
  all_goals first
    | (funext s; simp only [Pi.add_apply, Pi.mul_apply]; ring)
    | ring

/-- Pointwise bound for the explicit representative of the integrand. -/
private lemma abs_h'_le (a c x : ℝ) (hx : 1 < x) {t : ℝ} (ht : t ∈ Set.Ioi x) :
    ‖(-a*t + c) * ((2*(Real.log t)^2 + 3*Real.log t + 2)/(t^3*(Real.log t)^3))‖
      ≤ (2 + 3/Real.log x + 2/(Real.log x)^2) * (|a| + |c|) * Work.RHContract.kW t := by
  have ht1 : 1 < t := lt_trans hx ht
  have ht0 : (0:ℝ) < t := by linarith
  have ht1le : (1:ℝ) ≤ t := le_of_lt ht1
  set L := Real.log t with hLdef
  set L0 := Real.log x with hL0def
  have hL : 0 < L := by rw [hLdef]; exact Real.log_pos ht1
  have hL0 : 0 < L0 := by rw [hL0def]; exact Real.log_pos hx
  have hL0L : L0 ≤ L := by
    rw [hLdef, hL0def]; exact Real.log_le_log (by linarith) (le_of_lt ht)
  have h3 : 3*L ≤ 3*L^2/L0 := by rw [le_div_iff₀ hL0]; nlinarith [hL0L, hL0]
  have h2 : (2:ℝ) ≤ 2*L^2/L0^2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < L0^2)]; nlinarith [hL0L, hL0]
  have hkey : 2*L^2 + 3*L + 2 ≤ (2 + 3/L0 + 2/L0^2) * L^2 := by
    have e1 : (3/L0)*L^2 = 3*L^2/L0 := by ring
    have e2 : (2/L0^2)*L^2 = 2*L^2/L0^2 := by ring
    nlinarith [h3, h2, e1, e2]
  have hkey2 : 2*L^2 + 3*L + 2 ≤ (2 + 3/L0 + 2/L0^2) * (L*(L+1)) := by nlinarith [hkey, hL]
  have hApos : (0:ℝ) < 2*L^2 + 3*L + 2 := by positivity
  have hdenpos : (0:ℝ) < t^3*L^3 := by positivity
  have habs : |a*t - c| ≤ (|a| + |c|)*t := by
    have h1 : |a*t - c| ≤ |a*t| + |c| := by
      refine (abs_sub_le_iff).mpr ⟨?_, ?_⟩
      · linarith [le_abs_self (a*t), neg_le_abs c]
      · linarith [neg_le_abs (a*t), le_abs_self c]
    rw [abs_mul, abs_of_pos ht0] at h1
    nlinarith [h1, abs_nonneg a, abs_nonneg c, ht1le]
  have habs2 : |(-a*t + c)| = |a*t - c| := by
    rw [show -a*t + c = -(a*t - c) by ring, abs_neg]
  have hLHS : ‖(-a*t + c) * ((2*L^2 + 3*L + 2)/(t^3*L^3))‖
      = |a*t - c| * ((2*L^2 + 3*L + 2)/(t^3*L^3)) := by
    rw [Real.norm_eq_abs, abs_mul, habs2, abs_div, abs_of_pos hApos, abs_of_pos hdenpos]
  have hkWval : Work.RHContract.kW t = (L + 1)/(t^2*L^2) := by
    rw [Work.RHContract.kW, ← hLdef]
  rw [hLHS, hkWval]
  have hdiv : |a*t - c| * ((2*L^2 + 3*L + 2)/(t^3*L^3))
      = (|a*t - c| * (2*L^2 + 3*L + 2))/(t^3*L^3) := by rw [← mul_div_assoc]
  rw [hdiv, div_le_iff₀ hdenpos]
  have hR : (2 + 3/L0 + 2/L0^2) * (|a| + |c|) * ((L+1)/(t^2*L^2)) * (t^3*L^3)
      = (2 + 3/L0 + 2/L0^2) * (|a| + |c|) * (L + 1) * L * t := by
    field_simp
  rw [hR]
  calc |a*t - c| * (2*L^2 + 3*L + 2)
      ≤ ((|a| + |c|)*t) * (2*L^2 + 3*L + 2) :=
        mul_le_mul_of_nonneg_right habs (le_of_lt hApos)
    _ ≤ ((|a| + |c|)*t) * ((2 + 3/L0 + 2/L0^2) * (L*(L+1))) :=
        mul_le_mul_of_nonneg_left hkey2 (by positivity)
    _ = (2 + 3/L0 + 2/L0^2) * (|a| + |c|) * (L + 1) * L * t := by ring

/-- The integrand is integrable on `(x, ∞)` for `x > 1`. -/
private lemma integrableOn_h (a c x : ℝ) (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => (-a * t + c) * (-deriv Work.RHContract.kW t)) (Set.Ioi x) := by
  set K : ℝ := 2 + 3/Real.log x + 2/(Real.log x)^2 with hK
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hdom : Integrable (fun t : ℝ => K * (|a| + |c|) * Work.RHContract.kW t)
      (volume.restrict (Set.Ioi x)) := by
    have h := MeasureTheory.Integrable.const_mul (integrableOn_kW x hx) (K * (|a| + |c|))
    simpa [mul_assoc] using h
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi x)),
      ‖(-a*t + c) * ((2*(Real.log t)^2 + 3*Real.log t + 2)/(t^3*(Real.log t)^3))‖
        ≤ K * (|a| + |c|) * Work.RHContract.kW t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hK]
    exact abs_h'_le a c x hx ht
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (-a*t + c) * ((2*(Real.log t)^2 + 3*Real.log t + 2)/(t^3*(Real.log t)^3)))
      (volume.restrict (Set.Ioi x)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hint' : IntegrableOn
      (fun t : ℝ => (-a*t + c) * ((2*(Real.log t)^2 + 3*Real.log t + 2)/(t^3*(Real.log t)^3)))
      (Set.Ioi x) := hdom.mono' hmeas hbound
  refine hint'.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht1 : 1 < t := lt_trans hx ht
  change (-a*t + c) * ((2*(Real.log t)^2 + 3*Real.log t + 2)/(t^3*(Real.log t)^3))
      = (-a*t + c) * (-deriv Work.RHContract.kW t)
  rw [deriv_kW_eq ht1]
  ring

/-- The main identity. -/
theorem lin_kernel_identity (a c x : ℝ) (hx : 1 < x) :
    (-a * x + c) * Work.RHContract.kW x
        - ∫ t in Set.Ioi x, (-a * t + c) * (-deriv Work.RHContract.kW t)
      = a / (x * Real.log x) := by
  have hderiv : ∀ t ∈ Set.Ici x,
      HasDerivAt (fun s : ℝ => (a*s - c)*Work.RHContract.kW s + a/(s*Real.log s))
        ((-a * t + c) * (-deriv Work.RHContract.kW t)) t := by
    intro t ht
    rw [Set.mem_Ici] at ht
    exact hasDerivAt_pad a c (by linarith)
  have hint := integrableOn_h a c x hx
  have hlim := tendsto_pad a c
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := x) (f := fun s : ℝ => (a*s - c)*Work.RHContract.kW s + a/(s*Real.log s))
    (f' := fun t : ℝ => (-a * t + c) * (-deriv Work.RHContract.kW t)) (m := 0)
    hderiv hint hlim
  rw [hFTC]
  have hx0 : x ≠ 0 := by linarith
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  ring

end Work.RHContract.A
