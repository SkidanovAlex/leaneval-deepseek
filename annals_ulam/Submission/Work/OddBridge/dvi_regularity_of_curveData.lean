import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddBridge.Kden_radicand_pos_of_curve
import Submission.Work.OddBridge.dvi_of_volterra_regular
import Submission.Work.OddBridge.KvecM_eq_Kvec
import Submission.Work.OddBridge.KvecM_contDiffOn_box
import Submission.Work.OddBridge.kvecMAverage_differentiableAt_of_contDiffOn
import Submission.Work.OddVolterra.Kernel.G2Deriv
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Existence.hquot_contDiff
import Submission.Work.OddVolterra.KernelExt.Kden_pos_of_curve
import Submission.Work.OddBridge.theta_row_integrable

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra
open Commons.Geometry.Ulam

noncomputable section

/-! ## Positivity of the Abel denominator on the whole triangle `0 < a ≤ σ`

`Work.OddBridge.Kden_radicand_pos_of_curve` covers the slope window `0 < s, σ ≤ 1`.  Here the
upper bound on `σ` is removed: for `σ > 1` the tail hypotheses of `CurveData` give
`x σ = y σ = profileX σ` exactly and `h σ = 0`, so the two factors of the radicand
`(t + H(a,σ)) (L_σ(t) + L_a(t))` reduce to `profileX σ + hquot h a σ` and
`(σ + a) profileX σ + h a`, both of which are positive because `|hquot| ≤ 1/100/(σ - 9/10)`
(the support of `h` is `[4/5, 9/10]`) is dominated by `profileX σ ≈ 1/σ`. -/

theorem Kden_pos_all (n : ℕ) {h x y : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    (∀ a σ : ℝ, 0 < a → a ≤ σ →
      0 < (y σ + Work.OddVolterra.hquot h a σ) *
        (Work.OddVolterra.line h σ (y σ) + Work.OddVolterra.line h a (y σ))) ∧
    (∀ a σ : ℝ, 0 < a → a ≤ σ →
      0 < (-(x σ) + Work.OddVolterra.hquot h a σ) *
        (Work.OddVolterra.line h σ (-(x σ)) + Work.OddVolterra.line h a (-(x σ)))) := by
  have htau_lo : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  have htau_hi : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hzero_hi : ∀ z : ℝ, 9 / 10 < z → h z = 0 := by
    intro z hz
    by_contra hne
    have hmem := hhsupp hne
    rw [htau_lo, htau_hi] at hmem
    linarith [hmem.2]
  have hev_zero : ∀ z : ℝ, 9 / 10 < z → h =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact hzero_hi w hw
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  /- `hquot` is small in the tail region: since `support h ⊆ [4/5, 9/10]`, the divided
  difference `(h σ - h a)/(σ - a)` is bounded by `1/100/(σ - 9/10)`. -/
  have hq_bound : ∀ a σ : ℝ, 0 < a → a ≤ σ → 9 / 10 < σ →
      |hquot h a σ| ≤ (1 / 100) / (σ - 9 / 10) := by
    intro a σ ha haσ hσ9
    have h3 : 0 < σ - 9 / 10 := by linarith
    rcases eq_or_lt_of_le haσ with heq | hlt
    · have hder0 : deriv h σ = 0 := by
        rw [(hev_zero σ hσ9).deriv_eq]; simp
      rw [heq, hquot_self, hder0, abs_zero]
      positivity
    · have hsub : h σ - h a = (σ - a) * hquot h a σ := sub_mul_hquot hh1 a σ
      have hσ0 : h σ = 0 := hzero_hi σ hσ9
      have h4 : (σ - a) ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
      by_cases ha9 : a ≤ 9 / 10
      · have hq_eq : hquot h a σ * (σ - a) = -h a := by
          rw [mul_comm, ← hsub, hσ0, zero_sub]
        have h1 : |hquot h a σ| = |h a| / (σ - a) := by
          rw [eq_div_iff h4, ← abs_of_pos (sub_pos.mpr hlt), ← abs_mul, hq_eq, abs_neg]
        calc |hquot h a σ| = |h a| / (σ - a) := h1
          _ ≤ (1 / 100) / (σ - a) :=
              div_le_div_of_nonneg_right (hdata.close_h a).1
                (le_of_lt (sub_pos.mpr hlt))
          _ ≤ (1 / 100) / (σ - 9 / 10) :=
              div_le_div_of_nonneg_left (by norm_num) h3 (by linarith)
      · have ha9' : 9 / 10 < a := not_le.mp ha9
        have ha0 : h a = 0 := hzero_hi a ha9'
        have h5 : hquot h a σ = 0 := by
          have h6 : (σ - a) * hquot h a σ = 0 := by rw [← hsub, hσ0, ha0, sub_zero]
          exact (mul_eq_zero.mp h6).resolve_left h4
        rw [h5, abs_zero]
        positivity
  /- `1/100/(σ - 9/10) < profileX σ` for `σ > 1`. -/
  have hCq_lt : ∀ σ : ℝ, 1 < σ → (1 / 100) / (σ - 9 / 10) < profileX σ := by
    intro σ hσ
    have h3 : 0 < σ - 9 / 10 := by linarith
    have hspos : 0 < Real.sqrt (1 + σ ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have hsq : Real.sqrt (1 + σ ^ 2) < 100 * (σ - 9 / 10) := by
      rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < 100 * (σ - 9 / 10))]
      nlinarith
    have hgoal : (1 / Real.sqrt (1 + σ ^ 2)) * (σ - 9 / 10)
        = (σ - 9 / 10) / Real.sqrt (1 + σ ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [div_lt_iff₀ h3, profileX, hgoal, lt_div_iff₀ hspos]
    linarith
  /- `σ * profileX σ ≥ 1/√2` for `σ > 1`. -/
  have hp2 : ∀ σ : ℝ, 1 < σ → (1 : ℝ) / Real.sqrt 2 ≤ σ * profileX σ := by
    intro σ hσ
    have hsp : 0 < Real.sqrt (1 + σ ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h1 : (1 : ℝ) + σ ^ 2 ≤ 2 * σ ^ 2 := by nlinarith
    have h2 : Real.sqrt (1 + σ ^ 2) ≤ σ * Real.sqrt 2 := by
      calc Real.sqrt (1 + σ ^ 2) ≤ Real.sqrt (2 * σ ^ 2) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 2 * Real.sqrt (σ ^ 2) := Real.sqrt_mul (by norm_num) _
        _ = Real.sqrt 2 * σ := by rw [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ σ)]
        _ = σ * Real.sqrt 2 := by ring
    have hgoal : σ * profileX σ = σ / Real.sqrt (1 + σ ^ 2) := by
      rw [profileX, mul_one_div]
    rw [hgoal, le_div_iff₀ hsp]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs2]
    linarith
  have hquot_lt : ∀ a σ : ℝ, 0 < a → a ≤ σ → 1 < σ → |hquot h a σ| < profileX σ := by
    intro a σ ha haσ hσ
    exact lt_of_le_of_lt (hq_bound a σ ha haσ (by linarith)) (hCq_lt σ hσ)
  have hsmall : (1 : ℝ) / 100 < 1 / Real.sqrt 2 := by
    refine one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr (by norm_num)) ?_
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  constructor
  · intro a σ ha haσ
    rcases le_or_gt σ 1 with hσ1 | hσ1
    · exact (Kden_radicand_pos_of_curve n hh hhsupp hdata).1 a σ ha
        (lt_of_lt_of_le ha haσ) (le_trans haσ hσ1) hσ1
    · -- `σ > 1`: `x σ = y σ = profileX σ` and `h σ = 0`
      have hσ9 : 9 / 10 < σ := by linarith
      have hyσ : y σ = profileX σ := hdata.tail_y σ (by rw [htau_hi]; linarith)
      have hσ0 : h σ = 0 := hzero_hi σ hσ9
      have hpd : 0 < profileX σ := profileX_pos σ (by linarith)
      have hlt := hquot_lt a σ ha haσ hσ1
      refine mul_pos ?_ ?_
      · rw [hyσ]
        have h1 : -profileX σ < hquot h a σ := (abs_lt.mp hlt).1
        linarith
      · rw [line, line, hyσ, hσ0]
        have hha : -(1 / 100) ≤ h a := (abs_le.mp (hdata.close_h a).1).1
        have h1 : (1 : ℝ) / Real.sqrt 2 ≤ (σ + a) * profileX σ :=
          le_trans (hp2 σ hσ1) (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hpd))
        linarith
  · intro a σ ha haσ
    rcases le_or_gt σ 1 with hσ1 | hσ1
    · exact (Kden_radicand_pos_of_curve n hh hhsupp hdata).2 a σ ha
        (lt_of_lt_of_le ha haσ) (le_trans haσ hσ1) hσ1
    · have hσ9 : 9 / 10 < σ := by linarith
      have hxσ : x σ = profileX σ := hdata.tail_x σ (by rw [htau_hi]; linarith)
      have hσ0 : h σ = 0 := hzero_hi σ hσ9
      have hpd : 0 < profileX σ := profileX_pos σ (by linarith)
      have hlt := hquot_lt a σ ha haσ hσ1
      refine mul_pos_of_neg_of_neg ?_ ?_
      · rw [hxσ]
        have h1 : hquot h a σ < profileX σ := (abs_lt.mp hlt).2
        linarith
      · rw [line, line, hxσ, hσ0]
        have hha : h a ≤ 1 / 100 := (abs_le.mp (hdata.close_h a).1).2
        have h1 : (1 : ℝ) / Real.sqrt 2 ≤ (σ + a) * profileX σ :=
          le_trans (hp2 σ hσ1) (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hpd))
        linarith

/-! ## Continuity and measurability of the manifest kernel in its first slot -/

/-- `Kden h · σ t` is continuous (it is `√((t + H(a,σ))(L_σ(t) + L_a(t)))`). -/
lemma continuous_Kden_fst {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Continuous (fun a : ℝ => Kden h a σ t) := by
  have hq : Continuous (fun a : ℝ => hquot h a σ) :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp
      (continuous_id.prodMk continuous_const)
  have h1 : Continuous (fun a : ℝ => t + hquot h a σ) := continuous_const.add hq
  have h2 : Continuous (fun a : ℝ => line h σ t + line h a t) := by
    have h3 : Continuous (fun a : ℝ => line h σ t) := continuous_const
    have h4 : Continuous (fun a : ℝ => line h a t) := by
      have he : (fun a : ℝ => line h a t) = fun a : ℝ => a * t + h a := by
        funext a; rfl
      rw [he]
      exact (continuous_id.mul continuous_const).add hh.continuous
    exact h3.add h4
  exact Real.continuous_sqrt.comp (h1.mul h2)

lemma continuous_J1M_fst (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Continuous (fun a : ℝ => J1M n h a σ t) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => J1M n h p.1 p.2 t) := by
    rw [← contDiffOn_univ]
    exact contDiffOn_J1M_comp n hh (B := Set.univ) (t := fun _ : ℝ × ℝ => t) contDiffOn_const
  exact hcd.continuous.comp (continuous_id.prodMk continuous_const)

lemma continuous_J2M_fst (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Continuous (fun a : ℝ => J2M n h a σ t) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => J2M n h p.1 p.2 t) := by
    rw [← contDiffOn_univ]
    exact contDiffOn_J2M_comp n hh (B := Set.univ) (t := fun _ : ℝ × ℝ => t) contDiffOn_const
  exact hcd.continuous.comp (continuous_id.prodMk continuous_const)

lemma measurable_K1M_fst (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Measurable (fun a : ℝ => K1M n h a σ t) :=
  (continuous_J1M_fst n hh σ t).measurable.div (continuous_Kden_fst hh σ t).measurable

lemma measurable_K2M_fst (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Measurable (fun a : ℝ => K2M n h a σ t) :=
  (continuous_J2M_fst n hh σ t).measurable.div (continuous_Kden_fst hh σ t).measurable

lemma measurable_KvecM_fst (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (σ x y x' y' : ℝ) :
    Measurable (fun a : ℝ => KvecM n h a σ x y x' y') := by
  rw [show (fun a : ℝ => KvecM n h a σ x y x' y') = fun a : ℝ =>
      ![- (K1M n h a σ (-x) * x' + K1M n h a σ y * y'),
        - (K2M n h a σ (-x) * x' + K2M n h a σ y * y')] from by
      funext a i; fin_cases i <;> rfl]
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · exact (((measurable_K1M_fst n hh σ (-x)).mul measurable_const).add
      ((measurable_K1M_fst n hh σ y).mul measurable_const)).neg
  · exact (((measurable_K2M_fst n hh σ (-x)).mul measurable_const).add
      ((measurable_K2M_fst n hh σ y).mul measurable_const)).neg

/-- Continuity of `a ↦ KvecM n h a σ x y x' y'` on a segment on which `Kden` does not
vanish at the two chord endpoints. -/
lemma continuousOn_KvecM_fst (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {σ x y x' y' u : ℝ}
    (hposy : ∀ a ∈ Set.Icc u σ, 0 < Kden h a σ y)
    (hposx : ∀ a ∈ Set.Icc u σ, 0 < Kden h a σ (-x)) :
    ContinuousOn (fun a : ℝ => KvecM n h a σ x y x' y') (Set.Icc u σ) := by
  have hKy : ContinuousOn (fun a : ℝ => K1M n h a σ y) (Set.Icc u σ) :=
    (continuous_J1M_fst n hh σ y).continuousOn.div (continuous_Kden_fst hh σ y).continuousOn
      (fun a ha => ne_of_gt (hposy a ha))
  have hKx : ContinuousOn (fun a : ℝ => K1M n h a σ (-x)) (Set.Icc u σ) :=
    (continuous_J1M_fst n hh σ (-x)).continuousOn.div
      (continuous_Kden_fst hh σ (-x)).continuousOn (fun a ha => ne_of_gt (hposx a ha))
  have hLy : ContinuousOn (fun a : ℝ => K2M n h a σ y) (Set.Icc u σ) :=
    (continuous_J2M_fst n hh σ y).continuousOn.div (continuous_Kden_fst hh σ y).continuousOn
      (fun a ha => ne_of_gt (hposy a ha))
  have hLx : ContinuousOn (fun a : ℝ => K2M n h a σ (-x)) (Set.Icc u σ) :=
    (continuous_J2M_fst n hh σ (-x)).continuousOn.div
      (continuous_Kden_fst hh σ (-x)).continuousOn (fun a ha => ne_of_gt (hposx a ha))
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · show ContinuousOn (fun a : ℝ => -((K1M n h a σ (-x)) * x' + (K1M n h a σ y) * y'))
      (Set.Icc u σ)
    exact ((hKx.mul continuousOn_const).add (hKy.mul continuousOn_const)).neg
  · show ContinuousOn (fun a : ℝ => -((K2M n h a σ (-x)) * x' + (K2M n h a σ y) * y'))
      (Set.Icc u σ)
    exact ((hLx.mul continuousOn_const).add ((hLy).mul continuousOn_const)).neg

/-! ## `KvecM` agrees with `Kvec` on the whole triangle -/

/-- On the triangle `0 < a ≤ σ` the manifest kernel agrees with the paper's. -/
lemma KvecM_eq_Kvec_of_le (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ) :
    KvecM n h a σ (x σ) (y σ) (deriv x σ) (deriv y σ)
      = Kvec n h a σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
  obtain ⟨h1, h2⟩ := Kden_pos_all n hh hhsupp hdata
  exact KvecM_eq_Kvec n hn hh haσ _ _ _ _ (h1 a σ ha haσ) (h2 a σ ha haσ)

/-! ## The first conjunct: integrability of the Abel average of `KvecM` -/

/-- For `0 < a ≤ σ` and `u ∈ (a,σ)` the `τ`-integrand of the Abel average of the manifest
kernel is interval integrable on `(0,1)`: the moving point stays in the compact segment
`[u,σ]` on which `KvecM` is continuous, so the integrand is bounded by a constant times the
integrable Abel weight `(√(τ(1-τ)))⁻¹`. -/
theorem intervalIntegrable_KvecM_abel (n : ℕ) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    ∀ σ : ℝ, ∀ u ∈ Set.Ioo a σ, IntervalIntegrable (fun τ : ℝ =>
      (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
        KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ))
      volume (0 : ℝ) 1 := by
  intro σ u hu
  have hu0 : 0 < u := lt_trans ha hu.1
  have huσ : u < σ := hu.2
  obtain ⟨hp1, hp2⟩ := Kden_pos_all n hh hhsupp hdata
  have hpos : ∀ a' ∈ Set.Icc u σ, 0 < Kden h a' σ (y σ) ∧ 0 < Kden h a' σ (-(x σ)) := by
    intro a' ha'
    have h0 : 0 < a' := lt_of_lt_of_le hu0 ha'.1
    exact ⟨Real.sqrt_pos.mpr (hp1 a' σ h0 ha'.2), Real.sqrt_pos.mpr (hp2 a' σ h0 ha'.2)⟩
  have hcont := continuousOn_KvecM_fst n hh (σ := σ) (x := x σ) (y := y σ)
    (x' := deriv x σ) (y' := deriv y σ) (u := u)
    (fun a' ha' => (hpos a' ha').1) (fun a' ha' => (hpos a' ha').2)
  have hsub : 0 ≤ σ - u := le_of_lt (sub_pos.mpr huσ)
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, u + τ * (σ - u) ∈ Set.Icc u σ := by
    intro τ hτ
    constructor
    · have : 0 ≤ τ * (σ - u) := mul_nonneg hτ.1 hsub
      linarith
    · have : τ * (σ - u) ≤ 1 * (σ - u) := mul_le_mul_of_nonneg_right hτ.2 hsub
      linarith
  have hmap : Continuous fun τ : ℝ => u + τ * (σ - u) := by fun_prop
  have hgc : ContinuousOn (fun τ : ℝ => KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
      (deriv x σ) (deriv y σ)) (Set.Icc 0 1) :=
    hcont.comp hmap.continuousOn (fun τ hτ => hmem τ hτ)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  have hmeas : Measurable (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
      KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) := by
    have hw : Measurable (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹) :=
      (Real.continuous_sqrt.measurable.comp
        (measurable_id.mul (measurable_const.sub measurable_id))).inv
    have hK : Measurable (fun τ : ℝ => KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
        (deriv x σ) (deriv y σ)) :=
      (measurable_KvecM_fst n hh σ (x σ) (y σ) (deriv x σ) (deriv y σ)).comp (by fun_prop)
    exact hw.smul hK
  refine (abelWeight_intervalIntegrable.mul_const C).mono_fun' hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
  have hτI : τ ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
    exact ⟨le_of_lt hτ.1, hτ.2⟩
  have hw_nonneg : 0 ≤ (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc ‖(Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
        (deriv x σ) (deriv y σ)‖
      = (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ * ‖KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
        (deriv x σ) (deriv y σ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
    _ ≤ (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hC τ hτI) hw_nonneg

/-! ## `G₂M` as a vector-valued integral -/

/-- `G₂M` is the componentwise form of the vector-valued Abel average. -/
lemma G2M_eq_integral_smul (n : ℕ) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a σ u : ℝ} (ha : 0 < a)
    (hu : u ∈ Set.Ioo a σ) :
    G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)
      = ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
  funext i
  rw [intervalIntegral_apply_fin2 (i := i)
    (h := intervalIntegrable_KvecM_abel n hh hhsupp hdata ha σ u hu)]
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  simp only [Pi.smul_apply, div_eq_mul_inv]
  ring

/-! ## The second conjunct: differentiability of `G₂` in its first slot -/

/-- On the region `u ∈ (a,σ)`, `σ ≤ 1`, the paper's kernel `Kvec` equals the manifest one, so
the Abel average `G₂` is the manifest average `G₂M`, which is differentiable by
`Work.OddBridge.kvecMAverage_differentiableAt_of_contDiffOn`. -/
theorem differentiableAt_G2_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    ∀ s ∈ Set.Ioo a 1, ∀ σ ∈ Set.Ioo s 1,
      DifferentiableAt ℝ (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s := by
  intro s hs σ hσ
  have hEq : (fun u : ℝ => Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
      =ᶠ[𝓝 s] (fun u : ℝ =>
        G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hs.1, hσ.1⟩] with u hu
    funext i
    simp only [Work.OddVolterra.G2, G2M, div_eq_mul_inv]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
    have ha' : 0 < u + τ * (σ - u) := by
      have h1 : 0 ≤ τ * (σ - u) := mul_nonneg hτ.1 (by linarith [hu.2])
      linarith [hu.1]
    have hle : u + τ * (σ - u) ≤ σ := by
      have h1 : τ * (σ - u) ≤ 1 * (σ - u) :=
        mul_le_mul_of_nonneg_right hτ.2 (by linarith [hu.2])
      linarith
    rw [KvecM_eq_Kvec_of_le n hn hh hhsupp hdata ha' hle]
  have hEq2 : (fun u : ℝ => G2M n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
      =ᶠ[𝓝 s] (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hs.1, hσ.1⟩] with u hu
    exact G2M_eq_integral_smul n hh hhsupp hdata ha hu
  rw [Filter.EventuallyEq.differentiableAt_iff hEq,
    Filter.EventuallyEq.differentiableAt_iff hEq2]
  have hbox := KvecM_contDiffOn_box n hh hdata.smooth_x hdata.smooth_y ha le_rfl
    (fun s' σ' hs' hσ' => Real.sqrt_pos.mpr
      ((Kden_radicand_pos_of_curve n hh hhsupp hdata).1 s' σ'
        (lt_of_lt_of_le ha hs'.1) (lt_of_lt_of_le ha hσ'.1) hs'.2 hσ'.2))
    (fun s' σ' hs' hσ' => Real.sqrt_pos.mpr
      ((Kden_radicand_pos_of_curve n hh hhsupp hdata).2 s' σ'
        (lt_of_lt_of_le ha hs'.1) (lt_of_lt_of_le ha hσ'.1) hs'.2 hσ'.2))
  exact kvecMAverage_differentiableAt_of_contDiffOn n hs.1 hσ.1 (le_of_lt hσ.2) hbox

/-! ## The fourth conjunct: integrability of the Volterra kernel `Θ` -/

/-- The `Fin 4`-valued Volterra kernel `Θ n h s σ (stateOf x y σ)` is interval integrable in
`σ ∈ (s,1)`.  Its first two components are `-deriv x σ`, `-deriv y σ` (continuous on `(0,1)`),
and its last two are (up to sign) the two components of the `Fin 2`-valued derivative of `G₂`,
whose interval integrability is the third conjunct. -/
theorem theta_intervalIntegrable_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a : ℝ} (ha : 0 < a)
    (hDint : ∀ s ∈ Set.Ioo a 1, IntervalIntegrable (fun σ : ℝ =>
        deriv (fun u : ℝ =>
          Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) volume s 1) :
    ∀ s ∈ Set.Ioo a 1, IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1 := by
  intro s hs
  have hs1 : 0 ≤ s := le_of_lt (lt_trans ha hs.1)
  have hxcont : ContinuousOn (fun σ : ℝ => deriv x σ) (Set.Icc s 1) :=
    (contDiffOn_deriv_Ioi hdata.smooth_x).continuousOn.mono
      (fun σ hσ => lt_of_lt_of_le (lt_trans ha hs.1) hσ.1)
  have hycont : ContinuousOn (fun σ : ℝ => deriv y σ) (Set.Icc s 1) :=
    (contDiffOn_deriv_Ioi hdata.smooth_y).continuousOn.mono
      (fun σ hσ => lt_of_lt_of_le (lt_trans ha hs.1) hσ.1)
  have hcomp : ∀ i : Fin 4, IntervalIntegrable (fun σ : ℝ =>
      Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ) i) volume s 1 := by
    intro i
    fin_cases i
    · have hxc : ContinuousOn (fun σ : ℝ => -deriv x σ) (Set.uIcc s 1) := by
        rw [Set.uIcc_of_le (le_of_lt hs.2)]
        exact hxcont.neg
      refine IntervalIntegrable.congr_uIoo hxc.intervalIntegrable ?_
      intro σ _
      simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
    · have hyc : ContinuousOn (fun σ : ℝ => -deriv y σ) (Set.uIcc s 1) := by
        rw [Set.uIcc_of_le (le_of_lt hs.2)]
        exact hycont.neg
      refine IntervalIntegrable.congr_uIoo hyc.intervalIntegrable ?_
      intro σ _
      simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
    · -- third component: `-deriv_u ((G₂) 0)`
      have h1 : IntervalIntegrable (fun σ : ℝ =>
          deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s 0)
          volume s 1 := intervalIntegrable_iff.mpr (Integrable.eval ((hDint s hs).def') 0)
      refine IntervalIntegrable.congr_uIoo h1.neg ?_
      intro σ hσ
      rw [Set.uIoo_of_le (le_of_lt hs.2)] at hσ
      have hd := differentiableAt_G2_of_curveData n hn hh hhsupp hdata ha s hs σ hσ
      have hder := deriv_pi (𝕜 := ℝ) (x := s) (ι := Fin 2) (E' := fun _ : Fin 2 => ℝ)
        (φ := fun u : ℝ =>
          Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
        (fun j => (differentiableAt_pi.mp hd) j)
      have h2 : deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s 0
          = deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ) 0) s :=
        congrFun hder 0
      simp only [Pi.neg_apply]
      rw [h2]
      simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
    · have h1 : IntervalIntegrable (fun σ : ℝ =>
          deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s 1)
          volume s 1 := intervalIntegrable_iff.mpr (Integrable.eval ((hDint s hs).def') 1)
      refine IntervalIntegrable.congr_uIoo h1.neg ?_
      intro σ hσ
      rw [Set.uIoo_of_le (le_of_lt hs.2)] at hσ
      have hd := differentiableAt_G2_of_curveData n hn hh hhsupp hdata ha s hs σ hσ
      have hder := deriv_pi (𝕜 := ℝ) (x := s) (ι := Fin 2) (E' := fun _ : Fin 2 => ℝ)
        (φ := fun u : ℝ =>
          Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
        (fun j => (differentiableAt_pi.mp hd) j)
      have h2 : deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s 1
          = deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ) 1) s :=
        congrFun hder 1
      simp only [Pi.neg_apply]
      rw [h2]
      simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  refine intervalIntegrable_iff.mpr ⟨?_, ?_⟩
  · exact (aemeasurable_pi_iff.mpr (fun i => ((hcomp i).def').aemeasurable)).aestronglyMeasurable
  · exact (integrable_pi_iff.mpr (fun i => (hcomp i).def')).2


/-! ## The third conjunct: integrability of the first-slot derivative of `G₂` -/

/-- The `Fin 2`-valued derivative in the first slot of `G₂(·,σ,stateOf x y σ)` is interval
integrable in `σ ∈ (s,1)`.  The componentwise statement `intervalIntegrable_G2_row` is the
scalar derivative of each component, and the two agree a.e. on `(s,1]` because each component of
`G₂` is differentiable in its first slot (`deriv_pi`). -/
theorem deriv_G2_intervalIntegrable (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    ∀ s ∈ Set.Ioo a 1, IntervalIntegrable (fun σ : ℝ =>
        deriv (fun u : ℝ =>
          Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
        volume s 1 := by
  intro s hs
  have hs1 : s < 1 := hs.2
  have hrow : ∀ i : Fin 2, IntervalIntegrable (fun σ : ℝ =>
      deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      volume s 1 := by
    intro i
    refine (intervalIntegrable_G2_row n hn hh hhsupp hdata ha hs i).congr_uIoo ?_
    intro σ _
    simp [Work.OddVolterra.stateOf]
  have hrestrict : volume.restrict (Set.uIoo s 1) = volume.restrict (Set.uIoc s 1) := by
    rw [Set.uIoo_of_le (le_of_lt hs1), Set.uIoc_of_le (le_of_lt hs1)]
    exact MeasureTheory.Measure.restrict_congr_set
      (Work.OddVolterra.Existence.Ioo_ae_eq_Ioc_volume s 1)
  have hDint : ∀ i : Fin 2, Integrable (fun σ : ℝ =>
      deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      (volume.restrict (Set.uIoo s 1)) := by
    intro i
    rw [hrestrict]
    exact (hrow i).def'
  have hcongr : ∀ i : Fin 2, (fun σ : ℝ => deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      =ᵐ[volume.restrict (Set.uIoo s 1)]
      (fun σ : ℝ => (deriv (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) i) := by
    intro i
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with σ hσ
    rw [Set.uIoo_of_le (le_of_lt hs1)] at hσ
    have hd := differentiableAt_G2_of_curveData n hn hh hhsupp hdata ha s hs σ ⟨hσ.1, hσ.2⟩
    have hder := deriv_pi (𝕜 := ℝ) (x := s) (ι := Fin 2) (E' := fun _ : Fin 2 => ℝ)
      (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
      (fun j => (differentiableAt_pi.mp hd) j)
    exact (congrFun hder i).symm
  have hIntVec : Integrable (fun σ : ℝ => deriv (fun u : ℝ =>
      Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
      (volume.restrict (Set.uIoo s 1)) := by
    refine ⟨?_, ?_⟩
    · refine (aemeasurable_pi_iff.mpr ?_).aestronglyMeasurable
      intro i
      exact ((hDint i).aemeasurable).congr (hcongr i)
    · exact (integrable_pi_iff.mpr (fun i => (hDint i).congr (hcongr i))).2
  rw [intervalIntegrable_iff]
  show Integrable (fun σ : ℝ => deriv (fun u : ℝ =>
      Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
      (volume.restrict (Set.uIoc s 1))
  rw [← hrestrict]
  exact hIntVec

/-! ## The target theorem -/


theorem dvi_regularity_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    (∀ σ : ℝ, ∀ u ∈ Set.Ioo a σ, IntervalIntegrable (fun τ : ℝ =>
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
            (deriv x σ) (deriv y σ)) volume (0 : ℝ) 1) ∧
    (∀ s ∈ Set.Ioo a 1, ∀ σ ∈ Set.Ioo s 1,
      DifferentiableAt ℝ (fun u : ℝ =>
        Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) ∧
    (∀ s ∈ Set.Ioo a 1, IntervalIntegrable (fun σ : ℝ =>
        deriv (fun u : ℝ => Work.OddVolterra.G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
        volume s 1) ∧
    (∀ s ∈ Set.Ioo a 1, IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) volume s 1) := by
  exact ⟨intervalIntegrable_KvecM_abel n hh hsupp hdata ha,
    differentiableAt_G2_of_curveData n hn hh hsupp hdata ha,
    deriv_G2_intervalIntegrable n hn hh hsupp hdata ha,
    theta_row_integrable n hn hh hsupp hdata ha⟩

end

end Work.OddBridge
