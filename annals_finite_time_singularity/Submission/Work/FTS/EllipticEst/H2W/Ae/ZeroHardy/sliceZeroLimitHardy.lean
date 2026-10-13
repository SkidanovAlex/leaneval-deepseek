import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae.ZeroHardy

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# The two-derivative weighted Hardy inequality for slices with vanishing endpoint limits

For `g` of class `C²` on `(0, π/2)` whose one-sided limits at `0` and `π/2` both vanish and whose
second derivative is square-integrable against the weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`),
we prove

  `∫⁻_θ ofReal (g θ² σ θ) ≤ ofReal C · ∫⁻_θ ofReal (g'' θ² σ θ)`.

This is the analytic core of the slice part of Elgindi's Step 1/2 in the `AeData` class
(`Work.FTS.EllipticEst.H2W.Ae`).

The proof is the one recorded in
`Submission/Work/FTS/EllipticEst/H2W/Ae/SliceTwo/NOTES_greenSliceBound.md`:

* for `a < θ < b` inside the interval, the *interior Green identity* expresses `g θ` as the
  weighted average `c₁ g a + c₂ g b` minus the two second-derivative integrals against the
  Green kernel `ψ₁ t = c₁ (t - a)`, `ψ₂ t = c₂ (b - t)`, and `|ψᵢ| ≤ (b-a)/4`;
* the two endpoint limits remove `|g a|`, `|g b|`;
* Cauchy–Schwarz turns `(∫ |g''|)²` into `(∫ g''² σ)(∫ σ^{-1})`.
-/

/-! ## Elementary helpers -/

/-- AM–GM: `x y ≤ (x+y)²/4` for `x, y ≥ 0`. -/
private lemma mul_le_sq_div_four {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ (x + y) ^ 2 / 4 := by
  nlinarith [sq_nonneg (x - y)]

private lemma sEta_nonneg_sl {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _

private lemma sEta_zero_left : Work.FTS.EllipticEst.sEta 0 = 0 := by
  simp only [Work.FTS.EllipticEst.sEta, mul_zero, Real.sin_zero]
  rw [Real.zero_rpow (by
    rw [Work.Spaces.eta]; norm_num)]

private lemma sEta_zero_right : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  simp only [Work.FTS.EllipticEst.sEta]
  rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  rw [Real.zero_rpow (by
    rw [Work.Spaces.eta]; norm_num)]

/-! ## The interior Green identity -/

/-- **The interior Green identity.**  For `a < θ < b` inside `(0, π/2)` and `g` of class `C²`
there, the value `g θ` is the weighted average `c₁ g a + c₂ g b` minus the second-derivative
integrals against the Green kernel. -/
private theorem green_identity {g : ℝ → ℝ} {a θ b : ℝ} (haθ : a < θ) (hθb : θ < b)
    (hsm : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (ha : 0 < a) (hb : b < Real.pi / 2) :
    g θ = ((b - θ) / (b - a)) * g a + ((θ - a) / (b - a)) * g b
      - (∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
          * deriv (fun s => deriv g s) t)
      - (∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
          * deriv (fun s => deriv g s) t) := by
  have hπ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hba : (0 : ℝ) < b - a := by linarith
  set c₁ : ℝ := (b - θ) / (b - a) with hc₁
  set c₂ : ℝ := (θ - a) / (b - a) with hc₂
  have hsub1 : Set.uIcc a θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hsub2 : Set.uIcc θ b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  -- differentiability
  have hdg : DifferentiableOn ℝ g (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.differentiableOn (by norm_num)
  have hdg1c : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdg1 : DifferentiableOn ℝ (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
    hdg1c.differentiableOn (by norm_num)
  have hdg2c : ContDiffOn ℝ 0 (deriv (fun s => deriv g s)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdg1c.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (fun s => deriv g s)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdg2c.continuousOn
  have hg_at1 : ∀ x ∈ Set.uIcc a θ, HasDerivAt g (deriv g x) x := fun x hx =>
    hdg.hasDerivAt (isOpen_Ioo.mem_nhds (hsub1 hx))
  have hv_at1 : ∀ x ∈ Set.uIcc a θ, HasDerivAt (deriv g) (deriv (fun s => deriv g s) x) x :=
    fun x hx => hdg1.hasDerivAt (isOpen_Ioo.mem_nhds (hsub1 hx))
  have hg_at2 : ∀ x ∈ Set.uIcc θ b, HasDerivAt g (deriv g x) x := fun x hx =>
    hdg.hasDerivAt (isOpen_Ioo.mem_nhds (hsub2 hx))
  have hv_at2 : ∀ x ∈ Set.uIcc θ b, HasDerivAt (deriv g) (deriv (fun s => deriv g s) x) x :=
    fun x hx => hdg1.hasDerivAt (isOpen_Ioo.mem_nhds (hsub2 hx))
  -- the kernels
  have hker1 : ∀ x ∈ Set.uIcc a θ, HasDerivAt (fun t : ℝ => c₁ * (t - a)) c₁ x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => t - a) 1 x := (hasDerivAt_id x).sub_const a
    simpa using h.const_mul c₁
  have hker2 : ∀ x ∈ Set.uIcc θ b, HasDerivAt (fun t : ℝ => c₂ * (b - t)) (-c₂) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => b - t) (-1) x :=
      (hasDerivAt_id x).const_sub b
    simpa using h1.const_mul c₂
  have hker1' : IntervalIntegrable (fun _ : ℝ => c₁) MeasureTheory.volume a θ :=
    intervalIntegrable_const
  have hker2' : IntervalIntegrable (fun _ : ℝ => -c₂) MeasureTheory.volume θ b :=
    intervalIntegrable_const
  have hint1 : IntervalIntegrable (deriv g) MeasureTheory.volume a θ :=
    (hdg1.continuousOn.mono hsub1).intervalIntegrable
  have hint2 : IntervalIntegrable (deriv g) MeasureTheory.volume θ b :=
    (hdg1.continuousOn.mono hsub2).intervalIntegrable
  have hinv1 : IntervalIntegrable (deriv (fun s => deriv g s)) MeasureTheory.volume a θ :=
    (hcont2.mono hsub1).intervalIntegrable
  have hinv2 : IntervalIntegrable (deriv (fun s => deriv g s)) MeasureTheory.volume θ b :=
    (hcont2.mono hsub2).intervalIntegrable
  -- the two integrations by parts
  have hIBP1 : (∫ x in a..θ, (c₁ * (x - a)) * deriv (fun s => deriv g s) x)
      = (c₁ * (θ - a)) * deriv g θ - (c₁ * (a - a)) * deriv g a
        - ∫ x in a..θ, c₁ * deriv g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hker1 hv_at1 hker1' hinv1
  have hIBP2 : (∫ x in θ..b, (c₂ * (b - x)) * deriv (fun s => deriv g s) x)
      = (c₂ * (b - b)) * deriv g b - (c₂ * (b - θ)) * deriv g θ
        - ∫ x in θ..b, (-c₂) * deriv g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hker2 hv_at2 hker2' hinv2
  -- the fundamental theorem of calculus
  have hFTC1 : (∫ x in a..θ, deriv g x) = g θ - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg_at1 hint1
  have hFTC2 : (∫ x in θ..b, deriv g x) = g b - g θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg_at2 hint2
  -- the combination
  have hkey : (∫ x in a..θ, (c₁ * (x - a)) * deriv (fun s => deriv g s) x)
        + (∫ x in θ..b, (c₂ * (b - x)) * deriv (fun s => deriv g s) x)
      = -g θ + c₁ * g a + c₂ * g b := by
    rw [hIBP1, hIBP2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hFTC1, hFTC2]
    have h1 : c₁ * (θ - a) = c₂ * (b - θ) := by
      rw [hc₁, hc₂]; field_simp
    have h2 : c₁ + c₂ = 1 := by rw [hc₁, hc₂]; field_simp; ring
    have haa : c₁ * (a - a) = 0 := by ring
    rw [h1, haa, hc₁, hc₂]
    field_simp
    ring
  calc g θ = c₁ * g a + c₂ * g b
        - ((∫ x in a..θ, (c₁ * (x - a)) * deriv (fun s => deriv g s) x)
            + (∫ x in θ..b, (c₂ * (b - x)) * deriv (fun s => deriv g s) x)) := by
        linarith [hkey]
    _ = ((b - θ) / (b - a)) * g a + ((θ - a) / (b - a)) * g b
        - (∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t)
        - (∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t) := by
        rw [hc₁, hc₂]
        ring_nf

/-! ## Two elementary absolute-value helpers -/

private lemma abs_add_three (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
  calc |x + y + z| ≤ |x + y| + |z| := abs_add_le _ _
    _ ≤ (|x| + |y|) + |z| := by linarith [abs_add_le x y]
    _ = |x| + |y| + |z| := by ring

private lemma abs_sum_four_sub (x y z w : ℝ) : |x + y - z - w| ≤ |x| + |y| + |z| + |w| := by
  have h1 : x + y - z - w = x + y + -z + -w := by ring
  rw [h1]
  calc |x + y + -z + -w| ≤ |x + y| + |-z| + |-w| := abs_add_three _ _ _
    _ ≤ (|x| + |y|) + |-z| + |-w| := by linarith [abs_add_le x y]
    _ = |x| + |y| + |z| + |w| := by rw [abs_neg, abs_neg]

/-! ## The pointwise Green bound -/

/-- **Pointwise bound of a slice by its second derivative.**  If both one-sided limits of `g`
vanish and `|g''|` is integrable on `(0, π/2)`, then
`|g θ| ≤ (π/4) ∫_{Ioc 0 (π/2)} |g''|` on the interval. -/
private theorem greenBound {g : ℝ → ℝ} (hsm : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun t => |deriv (fun s => deriv g s) t|)
      (Set.Ioc 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hL : Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |g θ| ≤ (Real.pi / 4) * ∫ t in Set.Ioc 0 (Real.pi / 2),
        |deriv (fun s => deriv g s) t| := by
  intro θ hθ
  obtain ⟨hθ0, hθL⟩ := hθ
  set L : ℝ := Real.pi / 2 with hLdef
  have hLpi : L = Real.pi / 2 := hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith [Real.pi_pos]
  set M : ℝ := ∫ t in Set.Ioc 0 L, |deriv (fun s => deriv g s) t| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg _)
  -- continuity of the second derivative on the sub-intervals
  have hdg1c : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 L) := by
    rw [hLpi]; exact hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (fun s => deriv g s)) (Set.Ioo 0 L) := by
    have h2 : ContDiffOn ℝ 0 (deriv (fun s => deriv g s)) (Set.Ioo 0 L) :=
      hdg1c.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h2.continuousOn
  -- the two-boundary estimate
  have hstep : ∀ a b : ℝ, 0 < a → a < θ → θ < b → b < L →
      |g θ| ≤ |g a| + |g b| + (L / 2) * M := by
    intro a b ha haθ hθb hb
    have hsub1 : Set.uIcc a θ ⊆ Set.Ioo 0 L := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    have hsub2 : Set.uIcc θ b ⊆ Set.Ioo 0 L := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    have hid := green_identity haθ hθb hsm ha (by linarith [hb, hLpi])
    have hba : 0 < b - a := by linarith
    -- the two Green kernels are bounded by `(b-a)/4 ≤ L/4`
    have hψ1 : ∀ t ∈ Set.uIcc a θ, |(((b - θ) / (b - a)) * (t - a))| ≤ (b - a) / 4 := by
      intro t ht
      have ht' : a ≤ t ∧ t ≤ θ := by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exfalso; linarith
      have hc0 : 0 ≤ (b - θ) / (b - a) := div_nonneg (by linarith) (le_of_lt hba)
      have ht0 : 0 ≤ t - a := by linarith [ht'.1]
      rw [abs_of_nonneg (mul_nonneg hc0 ht0)]
      have hAM := mul_le_sq_div_four (x := b - θ) (y := θ - a) (by linarith) (by linarith)
      have h1 : (b - θ) / (b - a) * (t - a) ≤ (b - θ) / (b - a) * (θ - a) :=
        mul_le_mul_of_nonneg_left (by linarith [ht'.2]) hc0
      have h2 : (b - θ) / (b - a) * (θ - a) ≤ (b - a) / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hba]
        nlinarith [hAM]
      linarith
    have hψ2 : ∀ t ∈ Set.uIcc θ b, |(((θ - a) / (b - a)) * (b - t))| ≤ (b - a) / 4 := by
      intro t ht
      have ht' : θ ≤ t ∧ t ≤ b := by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exfalso; linarith
      have hc0 : 0 ≤ (θ - a) / (b - a) := div_nonneg (by linarith) (le_of_lt hba)
      have ht0 : 0 ≤ b - t := by linarith [ht'.2]
      rw [abs_of_nonneg (mul_nonneg hc0 ht0)]
      have hAM := mul_le_sq_div_four (x := b - θ) (y := θ - a) (by linarith) (by linarith)
      have h1 : (θ - a) / (b - a) * (b - t) ≤ (θ - a) / (b - a) * (b - θ) :=
        mul_le_mul_of_nonneg_left (by linarith [ht'.1]) hc0
      have h2 : (θ - a) / (b - a) * (b - θ) ≤ (b - a) / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hba]
        nlinarith [hAM]
      linarith
    -- integrability of the pieces
    have hIp1 : IntervalIntegrable
        (fun t => |(((b - θ) / (b - a)) * (t - a)) * deriv (fun s => deriv g s) t|)
        MeasureTheory.volume a θ := ((continuousOn_const.mul
          (continuousOn_id.sub continuousOn_const)).mul (hcont2.mono hsub1)).abs.intervalIntegrable
    have hIp2 : IntervalIntegrable
        (fun t => |(((θ - a) / (b - a)) * (b - t)) * deriv (fun s => deriv g s) t|)
        MeasureTheory.volume θ b := ((continuousOn_const.mul
          (continuousOn_const.sub continuousOn_id)).mul (hcont2.mono hsub2)).abs.intervalIntegrable
    have hIg1 : IntervalIntegrable (fun t => |deriv (fun s => deriv g s) t|)
        MeasureTheory.volume a θ := (hcont2.mono hsub1).abs.intervalIntegrable
    have hIg2 : IntervalIntegrable (fun t => |deriv (fun s => deriv g s) t|)
        MeasureTheory.volume θ b := (hcont2.mono hsub2).abs.intervalIntegrable
    -- the two integral bounds
    have hI1 : |∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
        * deriv (fun s => deriv g s) t| ≤ (L / 4) * M := by
      have h1 : |∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
          * deriv (fun s => deriv g s) t|
          ≤ ∫ t in a..θ, |(((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t| :=
        intervalIntegral.abs_integral_le_integral_abs (le_of_lt haθ)
      have h2 : (∫ t in a..θ, |(((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t|)
          ≤ ∫ t in a..θ, (L / 4) * |deriv (fun s => deriv g s) t| := by
        refine intervalIntegral.integral_mono_on (le_of_lt haθ) hIp1
          (hIg1.const_mul (L / 4)) (fun t ht => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact le_trans (hψ1 t (Set.Icc_subset_uIcc ht)) (by linarith)
      have h3 : (∫ t in a..θ, (L / 4) * |deriv (fun s => deriv g s) t|)
          = (L / 4) * ∫ t in a..θ, |deriv (fun s => deriv g s) t| :=
        intervalIntegral.integral_const_mul _ _
      have h4 : (∫ t in a..θ, |deriv (fun s => deriv g s) t|) ≤ M := by
        rw [hMdef, intervalIntegral.integral_of_le (le_of_lt haθ)]
        refine MeasureTheory.setIntegral_mono_set hint
          (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_
        exact Filter.Eventually.of_forall fun t ht =>
          ⟨by linarith [ht.1, ha], by linarith [ht.2, hθL]⟩
      calc |∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t|
          ≤ ∫ t in a..θ, |(((b - θ) / (b - a)) * (t - a))
              * deriv (fun s => deriv g s) t| := h1
        _ ≤ ∫ t in a..θ, (L / 4) * |deriv (fun s => deriv g s) t| := h2
        _ = (L / 4) * ∫ t in a..θ, |deriv (fun s => deriv g s) t| := h3
        _ ≤ (L / 4) * M := mul_le_mul_of_nonneg_left h4 (by linarith)
    have hI2 : |∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
        * deriv (fun s => deriv g s) t| ≤ (L / 4) * M := by
      have h1 : |∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
          * deriv (fun s => deriv g s) t|
          ≤ ∫ t in θ..b, |(((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t| :=
        intervalIntegral.abs_integral_le_integral_abs (le_of_lt hθb)
      have h2 : (∫ t in θ..b, |(((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t|)
          ≤ ∫ t in θ..b, (L / 4) * |deriv (fun s => deriv g s) t| := by
        refine intervalIntegral.integral_mono_on (le_of_lt hθb) hIp2
          (hIg2.const_mul (L / 4)) (fun t ht => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact le_trans (hψ2 t (Set.Icc_subset_uIcc ht)) (by linarith)
      have h3 : (∫ t in θ..b, (L / 4) * |deriv (fun s => deriv g s) t|)
          = (L / 4) * ∫ t in θ..b, |deriv (fun s => deriv g s) t| :=
        intervalIntegral.integral_const_mul _ _
      have h4 : (∫ t in θ..b, |deriv (fun s => deriv g s) t|) ≤ M := by
        rw [hMdef, intervalIntegral.integral_of_le (le_of_lt hθb)]
        refine MeasureTheory.setIntegral_mono_set hint
          (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_
        exact Filter.Eventually.of_forall fun t ht =>
          ⟨by linarith [ht.1, hθ0], by linarith [ht.2, hb, hLpi]⟩
      calc |∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t|
          ≤ ∫ t in θ..b, |(((θ - a) / (b - a)) * (b - t))
              * deriv (fun s => deriv g s) t| := h1
        _ ≤ ∫ t in θ..b, (L / 4) * |deriv (fun s => deriv g s) t| := h2
        _ = (L / 4) * ∫ t in θ..b, |deriv (fun s => deriv g s) t| := h3
        _ ≤ (L / 4) * M := mul_le_mul_of_nonneg_left h4 (by linarith)
    -- the coefficients are at most `1`
    have hcoe1 : |((b - θ) / (b - a)) * g a| ≤ |g a| := by
      rw [abs_mul]
      have hc : |(b - θ) / (b - a)| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hba)), div_le_one hba]
        linarith
      calc |(b - θ) / (b - a)| * |g a| ≤ 1 * |g a| := by gcongr
        _ = |g a| := one_mul _
    have hcoe2 : |((θ - a) / (b - a)) * g b| ≤ |g b| := by
      rw [abs_mul]
      have hc : |(θ - a) / (b - a)| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hba)), div_le_one hba]
        linarith
      calc |(θ - a) / (b - a)| * |g b| ≤ 1 * |g b| := by gcongr
        _ = |g b| := one_mul _
    rw [hid]
    have htri := abs_sum_four_sub (((b - θ) / (b - a)) * g a) (((θ - a) / (b - a)) * g b)
      (∫ t in a..θ, (((b - θ) / (b - a)) * (t - a)) * deriv (fun s => deriv g s) t)
      (∫ t in θ..b, (((θ - a) / (b - a)) * (b - t)) * deriv (fun s => deriv g s) t)
    linarith [htri, hcoe1, hcoe2, hI1, hI2]
  -- pass to the limit at the two endpoints
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ₁, hδ1pos, hδ1⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ t ∈ Set.Ioo 0 δ₁, |g t| < ε / 2 := by
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), g t ∈ Metric.ball (0 : ℝ) (ε / 2) :=
      h0.eventually (Metric.ball_mem_nhds (0 : ℝ) hε2)
    have hmem : {t : ℝ | g t ∈ Metric.ball (0 : ℝ) (ε / 2)}
        ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := hev
    rw [Metric.mem_nhdsWithin_iff] at hmem
    obtain ⟨δ, hδ, hsub⟩ := hmem
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have ht' : t ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi 0 := by
      refine ⟨?_, ht.1⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2
    have hgt : g t ∈ Metric.ball (0 : ℝ) (ε / 2) := hsub ht'
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hgt
  obtain ⟨δ₂, hδ2pos, hδ2⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ t ∈ Set.Ioo (L - δ₂) L, |g t| < ε / 2 := by
    have hev : ∀ᶠ t in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        g t ∈ Metric.ball (0 : ℝ) (ε / 2) :=
      hL.eventually (Metric.ball_mem_nhds (0 : ℝ) hε2)
    have hmem : {t : ℝ | g t ∈ Metric.ball (0 : ℝ) (ε / 2)}
        ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := hev
    rw [Metric.mem_nhdsWithin_iff] at hmem
    obtain ⟨δ, hδ, hsub⟩ := hmem
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have htd : dist t (Real.pi / 2) < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [ht.2]), neg_sub]
      linarith [ht.1]
    have ht' : t ∈ Metric.ball (Real.pi / 2) δ ∩ Set.Iio (Real.pi / 2) :=
      ⟨by rwa [Metric.mem_ball], ht.2⟩
    have hgt : g t ∈ Metric.ball (0 : ℝ) (ε / 2) := hsub ht'
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hgt
  set a : ℝ := min (θ / 2) (δ₁ / 2) with hadef
  set b : ℝ := L - min (δ₂ / 2) ((L - θ) / 2) with hbdef
  have ha_pos : 0 < a := by
    rw [hadef]; exact lt_min (by linarith) (by linarith)
  have haθ : a < θ := by
    rw [hadef]
    calc min (θ / 2) (δ₁ / 2) ≤ θ / 2 := min_le_left _ _
      _ < θ := by linarith
  have ha_δ : a < δ₁ := by
    rw [hadef]
    calc min (θ / 2) (δ₁ / 2) ≤ δ₁ / 2 := min_le_right _ _
      _ < δ₁ := by linarith
  have hb_L : b < L := by
    rw [hbdef]
    have : 0 < min (δ₂ / 2) ((L - θ) / 2) := lt_min (by linarith) (by linarith)
    linarith
  have hθb : θ < b := by
    rw [hbdef]
    have : min (δ₂ / 2) ((L - θ) / 2) ≤ (L - θ) / 2 := min_le_right _ _
    linarith
  have hb_δ : L - b < δ₂ := by
    rw [hbdef]
    have : min (δ₂ / 2) ((L - θ) / 2) ≤ δ₂ / 2 := min_le_left _ _
    linarith
  have hga : |g a| < ε / 2 := hδ1 a ⟨ha_pos, ha_δ⟩
  have hgb : |g b| < ε / 2 := hδ2 b ⟨by linarith, hb_L⟩
  have hmain := hstep a b ha_pos haθ hθb hb_L
  have hLM : (L / 2) * M
      = (Real.pi / 4) * ∫ t in Set.Ioc 0 (Real.pi / 2), |deriv (fun s => deriv g s) t| := by
    rw [hMdef, hLpi]
    ring
  linarith [hmain, hLM, hga, hgb]

/-- Conversion between the interval integral `∫_0^{π/2}` and the set integral over `Iθ`. -/
private lemma interval_eq_Iθ {f : ℝ → ℝ} :
    (∫ x in (0 : ℝ)..Real.pi / 2, f x) = ∫ x in Work.Spaces.Iθ, f x := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  show (∫ x in Set.Ioc 0 (Real.pi / 2), f x) = ∫ x in Set.Icc 0 (Real.pi / 2), f x
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))]

/-! ## The target: the two-derivative weighted Hardy inequality -/

theorem sliceZeroLimitHardy : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
    ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal C * ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro g hsm hint h0 hL
  set L : ℝ := Real.pi / 2 with hLdef
  have hLpi : L = Real.pi / 2 := hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith [Real.pi_pos]
  set G2 : ℝ → ℝ := fun θ => deriv (fun t => deriv g t) θ with hG2def
  -- ## integrability of the two weights on `Ioc 0 L`
  have hsinpos : ∀ θ ∈ Set.Ioo 0 L, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    rw [hLpi] at hθ
    linarith [hθ.2]
  have hA : MeasureTheory.IntegrableOn
      (fun θ => (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioc 0 L) := by
    rw [hLpi]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  have hB : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sEta θ)⁻¹)
      (Set.Ioc 0 L) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Real.sin (2 * θ) ^ (Work.Spaces.eta)) (Set.Ioc 0 L) := by
      rw [hLpi]
      exact (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := Work.Spaces.eta)
        (by norm_num [Work.Spaces.eta])).1.mono_set Set.Ioc_subset_Icc_self
    refine h1.congr_fun (fun θ hθ => ?_) measurableSet_Ioc
    show Real.sin (2 * θ) ^ (Work.Spaces.eta) = (Work.FTS.EllipticEst.sEta θ)⁻¹
    rw [Work.FTS.EllipticEst.sEta]
    have h2θ0 : 0 ≤ 2 * θ := by rw [Set.mem_Ioc] at hθ; linarith [hθ.1]
    have h2θπ : 2 * θ ≤ Real.pi := by
      rw [Set.mem_Ioc] at hθ
      rw [hLpi] at hθ
      linarith [hθ.2]
    rw [Real.rpow_neg (Real.sin_nonneg_of_nonneg_of_le_pi h2θ0 h2θπ), inv_inv]
  -- ## `|G2|` is integrable on `Ioc 0 L`
  have hL1 : MeasureTheory.IntegrableOn (fun θ => |G2 θ|) (Set.Ioc 0 L) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => (1 / 2) * ((G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + (Work.FTS.EllipticEst.sEta θ)⁻¹)) (Set.Ioc 0 L) := (hA.add hB).const_mul (1 / 2)
    refine MeasureTheory.Integrable.mono' hdom
      ((measurable_deriv (fun t : ℝ => deriv g t)).abs.aestronglyMeasurable) ?_
    have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc 0 L)), θ ∈ Set.Ioo 0 L := by
      rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := 0) (b := L)).symm]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with θ hθ
    have hs : 0 < Work.FTS.EllipticEst.sEta θ := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_abs]
    have hAM := two_mul_le_add_sq (|G2 θ| * Work.FTS.EllipticEst.sEta θ) (1 : ℝ)
    rw [mul_one, one_pow, mul_pow, sq_abs] at hAM
    have hkey : 2 * |G2 θ| ≤ (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (Work.FTS.EllipticEst.sEta θ)⁻¹ := by
      refine (mul_le_mul_iff_of_pos_right hs).mp ?_
      have hspos : Work.FTS.EllipticEst.sEta θ ≠ 0 := ne_of_gt hs
      have e : ((G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (Work.FTS.EllipticEst.sEta θ)⁻¹)
          * Work.FTS.EllipticEst.sEta θ
          = (G2 θ) ^ 2 * (Work.FTS.EllipticEst.sEta θ) ^ 2 + 1 := by
        rw [add_mul, inv_mul_cancel₀ hspos]
        ring
      rw [e]
      linarith [hAM]
    linarith [hkey]
  -- ## the three integrals
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sEta θ)⁻¹ with hBdef
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, |G2 θ| with hMdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_sl hθ))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => inv_nonneg.mpr (sEta_nonneg_sl hθ))
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => abs_nonneg _)
  have hBpi : B ≤ Real.pi / 2 := by
    rw [hBdef]
    have h2 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := Work.Spaces.eta)
      (by norm_num [Work.Spaces.eta])).2
    refine le_trans (le_of_eq ?_) h2
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.sEta,
      Real.rpow_neg (Work.FTS.EllipticEst.sin_two_nonneg hθ), inv_inv]
  -- ## Cauchy–Schwarz for `M`
  have hA' : MeasureTheory.IntegrableOn
      (fun s => |G2 s| ^ 2 * Work.FTS.EllipticEst.sEta s) (Set.Ioc 0 (Real.pi / 2)) := by
    have hh := hA
    rw [hLpi] at hh
    exact hh.congr_fun (fun t _ => by rw [sq_abs]) measurableSet_Ioc
  have hB' : MeasureTheory.IntegrableOn
      (fun s => (Work.FTS.EllipticEst.sEta s)⁻¹) (Set.Ioc 0 (Real.pi / 2)) := by
    have hh := hB
    rw [hLpi] at hh
    exact hh
  have hCS : M ^ 2 ≤ A * B := by
    have h := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
      (f := fun t => |G2 t|) (σ := Work.FTS.EllipticEst.sEta) (a := 0) (b := Real.pi / 2)
      (le_of_lt (by linarith [Real.pi_pos]))
      (fun t ht => Real.rpow_pos_of_pos
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])) _)
      hA' hB'
    rw [interval_eq_Iθ (f := fun t => |G2 t|), interval_eq_Iθ
        (f := fun t => |G2 t| ^ 2 * Work.FTS.EllipticEst.sEta t),
      interval_eq_Iθ (f := fun t => (Work.FTS.EllipticEst.sEta t)⁻¹)] at h
    rw [hMdef, hAdef, hBdef]
    simpa only [sq_abs] using h
  -- ## the pointwise bound and the lintegral chain
  have hbd := greenBound hsm hL1 h0 hL
  have hMconv : (∫ t in Set.Ioc 0 (Real.pi / 2), |G2 t|) = M := by
    rw [hMdef]
    show (∫ t in Set.Ioc 0 (Real.pi / 2), |G2 t|) = ∫ t in Work.Spaces.Iθ, |G2 t|
    rw [Work.Spaces.Iθ]
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)).symm]
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) := by
    intro θ hθ
    obtain ⟨hθ0, hθL⟩ := Set.mem_Icc.mp hθ
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_lt_of_le hθ0 with h0θ | h0θ
    · rw [← h0θ, sEta_zero_left]
      simp
    rcases eq_or_lt_of_le hθL with hπθ | hπθ
    · have hz : Work.FTS.EllipticEst.sEta L = 0 := by
        rw [hLpi]; exact sEta_zero_right
      rw [hπθ, hz]
      simp
    · have hb := hbd θ ⟨h0θ, by linarith [hπθ, hLpi]⟩
      rw [hMconv] at hb
      have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_sl hθ
      have hsq : (g θ) ^ 2 ≤ ((Real.pi / 4) * M) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      calc (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ ((Real.pi / 4) * M) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
            mul_le_mul_of_nonneg_right hsq hs
        _ = ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ := by ring
  have hintnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (by positivity) (sEta_nonneg_sl hθ))
  have hintIθ : MeasureTheory.IntegrableOn
      (fun θ => ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have := Work.FTS.EllipticEst.integrableOn_thEta.1
    exact this.const_mul _
  have hintnneg : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_sl hθ))
  calc ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
        MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintIθ hintnn).symm
    _ = ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2)
          * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2) * 10000) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left Work.FTS.EllipticEst.integrableOn_thEta.2 (by positivity)
    _ ≤ ENNReal.ofReal (10 ^ 6) * ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hintnneg]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10 ^ 6)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hgoal : ((Real.pi / 4) ^ 2 * M ^ 2) * 10000 ≤ 10 ^ 6 * A := by
          have hpi4 : (Real.pi / 4) ^ 2 ≤ 1 := by nlinarith [Real.pi_pos, Real.pi_le_four]
          have hB2 : B ≤ 2 := by linarith [hBpi, Real.pi_le_four]
          have hM2' : M ^ 2 ≤ A * 2 := le_trans hCS (mul_le_mul_of_nonneg_left hB2 hA0)
          have h1 : (Real.pi / 4) ^ 2 * M ^ 2 ≤ A * 2 := by
            calc (Real.pi / 4) ^ 2 * M ^ 2 ≤ 1 * M ^ 2 :=
                  mul_le_mul_of_nonneg_right hpi4 (sq_nonneg M)
              _ = M ^ 2 := one_mul _
              _ ≤ A * 2 := hM2'
          calc ((Real.pi / 4) ^ 2 * M ^ 2) * 10000 ≤ (A * 2) * 10000 :=
                mul_le_mul_of_nonneg_right h1 (by norm_num)
            _ ≤ 10 ^ 6 * A := by nlinarith [hA0]
        simpa only [← hAdef] using hgoal

end

end Work.FTS.EllipticEst.H2W.Ae.ZeroHardy