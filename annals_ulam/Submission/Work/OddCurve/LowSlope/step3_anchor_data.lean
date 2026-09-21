import Mathlib
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddCurve.LowSlope.anchorPhiData_eq_ballData
import Submission.Work.OddCurve.LowSlope.anchorPsiData_eq_zero
import Submission.Work.OddCurve.LowSlope.exists_radialFunction_of_strictConcaveProfile
import Submission.Work.OddCurve.Strong
import Submission.Work.OddEnvelope.Main

/-!
# Step 3, the anchor side: the radial function of the anchor and the junction in the
`c = cos α` variable

Anchor-side inputs of the Radon step (paper Step 3):

* `Work.OddCurve.LowSlope.anchorRadialFunction` — the radial function `ρ_a` of the anchor
  profile `f_a = envelopeProfile h X Y`;
* `anchorPhiData_junction` / `anchorPsiData_junction` — the two junction identities of
  `anchorPhiData_eq_ballData` / `anchorPsiData_eq_zero`, rewritten in the variable
  `c = (√(1+s²))⁻¹` (the variable in which the glued datum `gluedPhi` is stated);
* `anchorData_junction_near` — the junction identities on a *neighbourhood* of a point `c₀` in
  the interior of the agreement interval (the form required by `contDiffOn_gluedPhi`).

## Why the junction point is `c = 4/5`

The anchor's data agree with the ball's on the *slope* range `(1-3τ, 1-2τ) = (7/10, 4/5)` (there
the bump vanishes, so the cutting lines are central and the anchor's moment equations are the
ball's central-section conditions).  In the `c` variable this is the interval
`(1/√(1+(4/5)²), 1/√(1+(7/10)²)) ≈ (0.7809, 0.8192)`, whose interior contains `4/5 = 0.8` — which
is why `gluedPhi`/`gluedPsi` glue at `4/5`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

lemma tauEnvelope_eq : Work.OddEnvelope.tau = tau := rfl

/-- The bump of the anchor vanishes strictly outside the closed transition window. -/
lemma anchor_h_eq_zero_of_not_mem {h X Y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    {s : ℝ} (hs : s < 1 - 2 * tau ∨ 1 - tau < s) : h s = 0 := by
  by_contra hne
  have hmem := H.h_support (Function.mem_support.mpr hne)
  rw [Set.mem_Icc, tauEnvelope_eq] at hmem
  rcases hs with hs | hs
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- **The radial function of the anchor profile.**  For the envelope profile `f_a` of a chord
curve `(X, Y)` there is a radial function `ρ_a` on `(-1,1)`: positive, `C^∞`, `u ↦ ρ_a u * u`
strictly increasing, satisfying the radial-graph identity `ρ_a u * √(1-u²) = f_a (ρ_a u * u)`, and
normalised by `ρ_a 0 = 1`. -/
theorem anchorRadialFunction {h X Y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) :
    ∃ ρ : ℝ → ℝ,
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1) ∧
      StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) ∧
      ρ 0 = 1 :=
  exists_radialFunction_of_strictConcaveProfile (Work.OddEnvelope.envelopeProfile h X Y)
    Work.OddEnvelope.envelopeProfile_zero (Work.OddEnvelope.continuousOn_envelopeProfile' H)
    Work.OddEnvelope.envelopeProfile_left_end Work.OddEnvelope.envelopeProfile_right_end
    (fun t ht => Work.OddEnvelope.envelopeProfile_pos H ht)
    ((Work.OddEnvelope.strictConcaveOn_envelopeProfile H).subset Set.Ioo_subset_Icc_self
      (convex_Ioo _ _))
    (Work.OddEnvelope.envelopeProfile_contDiffOn H)

/-! ## The junction in the `c` variable -/

/-- `(√(1+s²))⁻¹ = c` whenever `s² c² = 1 - c²` and `c > 0`. -/
lemma inv_sqrt_one_add_sq_eq {c s : ℝ} (hc : 0 < c) (hs : s ^ 2 * c ^ 2 = 1 - c ^ 2) :
    (Real.sqrt (1 + s ^ 2))⁻¹ = c := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
  have h1 : 1 + s ^ 2 = (1 / c) ^ 2 := by
    rw [div_pow, one_pow, eq_div_iff hc2]
    nlinarith [hs]
  rw [h1, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hc), one_div, inv_inv]

/-- The slope associated with `c`: `√(1-c²)/c` satisfies `s² c² = 1 - c²`. -/
lemma sqrt_one_sub_sq_div_sq_mul {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (Real.sqrt (1 - c ^ 2) / c) ^ 2 * c ^ 2 = 1 - c ^ 2 := by
  have hone : (0 : ℝ) ≤ 1 - c ^ 2 := by nlinarith
  have hs2 : (Real.sqrt (1 - c ^ 2) / c) ^ 2 = (1 - c ^ 2) / c ^ 2 := by
    rw [div_pow, Real.sq_sqrt hone]
  rw [hs2]
  field_simp

/-- The slope `√(1-c²)/c` lies in `(a,b)` as soon as the two squared inequalities hold. -/
lemma sqrt_one_sub_sq_div_mem {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcb : 1 < c ^ 2 * (1 + b ^ 2)) (hca : c ^ 2 * (1 + a ^ 2) < 1) :
    Real.sqrt (1 - c ^ 2) / c ∈ Set.Ioo a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsb : 1 - c ^ 2 < (b * c) ^ 2 := by nlinarith [hcb]
  have hsa : (a * c) ^ 2 < 1 - c ^ 2 := by nlinarith [hca]
  have hone : (0 : ℝ) ≤ 1 - c ^ 2 := by nlinarith
  constructor
  · rw [lt_div_iff₀ hc]
    exact (Real.lt_sqrt (by positivity : (0 : ℝ) ≤ a * c)).mpr hsa
  · rw [div_lt_iff₀ hc]
    exact (Real.sqrt_lt hone (by positivity : (0 : ℝ) ≤ b * c)).mpr hsb

/-- `c > (√(1+b²))⁻¹` implies the squared inequality `1 < c²(1+b²)`. -/
lemma sq_cond_of_gt_inv_sqrt {b c : ℝ} (hb : 0 < b)
    (hc : (Real.sqrt (1 + b ^ 2))⁻¹ < c) : 1 < c ^ 2 * (1 + b ^ 2) := by
  have hspos : 0 < Real.sqrt (1 + b ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have ht2 : ((Real.sqrt (1 + b ^ 2))⁻¹) ^ 2 * (1 + b ^ 2) = 1 := by
    rw [inv_pow]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  have hlt : ((Real.sqrt (1 + b ^ 2))⁻¹) ^ 2 < c ^ 2 :=
    pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  have := mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < 1 + b ^ 2)
  rw [ht2] at this
  exact this

/-- `c < (√(1+a²))⁻¹` (with `c ≥ 0`) implies the squared inequality `c²(1+a²) < 1`. -/
lemma sq_cond_of_lt_inv_sqrt {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hc1 : c < (Real.sqrt (1 + a ^ 2))⁻¹) : c ^ 2 * (1 + a ^ 2) < 1 := by
  have ht2 : ((Real.sqrt (1 + a ^ 2))⁻¹) ^ 2 * (1 + a ^ 2) = 1 := by
    rw [inv_pow]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  have hlt : c ^ 2 < ((Real.sqrt (1 + a ^ 2))⁻¹) ^ 2 :=
    pow_lt_pow_left₀ hc1 hc (by norm_num)
  have := mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < 1 + a ^ 2)
  rw [ht2] at this
  exact this

/-- **The first junction identity in the `c` variable.**  On the slope interval `[a,b]` (where the
bump and its derivative vanish and the anchor satisfies the first moment equation), the anchor's
first Radon datum equals the ball's at every `c` with `1 < c²(1+b²)` and `c²(1+a²) < 1`. -/
theorem anchorPhiData_junction (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hc1 : c ≤ 1)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hA : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hcb : 1 < c ^ 2 * (1 + b ^ 2)) (hca : c ^ 2 * (1 + a ^ 2) < 1) :
    radonPhi n ρ c = ballPhiData n c := by
  set s : ℝ := Real.sqrt (1 - c ^ 2) / c with hsdef
  have hs : s ∈ Set.Ioo a b := sqrt_one_sub_sq_div_mem ha hab hc hc1 hcb hca
  have hsq : s ^ 2 * c ^ 2 = 1 - c ^ 2 := sqrt_one_sub_sq_div_sq_mul hc hc1
  have h := anchorPhiData_eq_ballData n hn H hρpos hρsm hρmono hgraph ha hab hzero hder0 hA hB
    s hs
  rw [inv_sqrt_one_add_sq_eq hc hsq] at h
  exact h

/-- **The second junction identity in the `c` variable.**  Same statement for the anchor's second
Radon datum, which vanishes on the junction range. -/
theorem anchorPsiData_junction (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hc1 : c ≤ 1)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hcb : 1 < c ^ 2 * (1 + b ^ 2)) (hca : c ^ 2 * (1 + a ^ 2) < 1) :
    radonPsi n ρ c = 0 := by
  set s : ℝ := Real.sqrt (1 - c ^ 2) / c with hsdef
  have hs : s ∈ Set.Ioo a b := sqrt_one_sub_sq_div_mem ha hab hc hc1 hcb hca
  have hsq : s ^ 2 * c ^ 2 = 1 - c ^ 2 := sqrt_one_sub_sq_div_sq_mul hc hc1
  have h := anchorPsiData_eq_zero n hn H hρpos hρsm hρmono hgraph ha hab hzero hder0 hB s hs
  rw [inv_sqrt_one_add_sq_eq hc hsq] at h
  exact h

/-- **The junction identities on a neighbourhood of `c₀`**: the form needed by
`contDiffOn_gluedPhi` / `contDiffOn_gluedPsi`. -/
theorem anchorData_junction_near (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    {a b c₀ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc₀ : 0 < c₀) (hc₀1 : c₀ < 1)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0) (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hA : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hcb : 1 < c₀ ^ 2 * (1 + b ^ 2)) (hca : c₀ ^ 2 * (1 + a ^ 2) < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c ∈ Set.Ioo (c₀ - δ) (c₀ + δ),
      radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0 := by
  have h1 : ∀ᶠ c in 𝓝 c₀, 1 < c ^ 2 * (1 + b ^ 2) :=
    (isOpen_lt continuous_const (by fun_prop : Continuous fun c : ℝ => c ^ 2 * (1 + b ^ 2))).mem_nhds hcb
  have h2 : ∀ᶠ c in 𝓝 c₀, c ^ 2 * (1 + a ^ 2) < 1 :=
    (isOpen_lt (by fun_prop : Continuous fun c : ℝ => c ^ 2 * (1 + a ^ 2)) continuous_const).mem_nhds hca
  have h3 : ∀ᶠ c in 𝓝 c₀, 0 < c := isOpen_Ioi.mem_nhds hc₀
  have h4 : ∀ᶠ c in 𝓝 c₀, c < 1 := isOpen_Iio.mem_nhds hc₀1
  have hall : ∀ᶠ c in 𝓝 c₀,
      0 < c ∧ c < 1 ∧ 1 < c ^ 2 * (1 + b ^ 2) ∧ c ^ 2 * (1 + a ^ 2) < 1 := by
    filter_upwards [h3, h4, h1, h2] with c hc1 hc2 hc3 hc4
    exact ⟨hc1, hc2, hc3, hc4⟩
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨δ, hδ, hδ'⟩ := hall
  refine ⟨δ, hδ, fun c hc => ?_⟩
  have hdist : dist c c₀ < δ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [hc.2], by linarith [hc.1]⟩
  obtain ⟨hcpos, hclt, hcb', hca'⟩ := hδ' hdist
  exact ⟨anchorPhiData_junction n hn H hρpos hρsm hρmono hgraph ha hab hcpos (le_of_lt hclt)
      hzero hder0 hA hB hcb' hca',
    anchorPsiData_junction n hn H hρpos hρsm hρmono hgraph ha hab hcpos (le_of_lt hclt)
      hzero hder0 hB hcb' hca'⟩

end

end Work.OddCurve.LowSlope

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- `deriv h s = 0` when `h` vanishes on an open interval around `s`. -/
lemma deriv_eq_zero_of_eqOn_Ioo {h : ℝ → ℝ} {s a b : ℝ} (ha : a < s) (hb : s < b)
    (hh : ∀ x ∈ Set.Ioo a b, h x = 0) : deriv h s = 0 := by
  have hev : h =ᶠ[𝓝 s] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩] with x hx using hh x hx
  rw [hev.deriv_eq, deriv_const]

/-- The comparison `√(1-c²)/c < x` in squared form. -/
lemma sqrt_one_sub_sq_div_lt_iff {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hc1 : c ≤ 1) :
    Real.sqrt (1 - c ^ 2) / c < x ↔ 1 < c ^ 2 * (1 + x ^ 2) := by
  have hone : (0 : ℝ) ≤ 1 - c ^ 2 := by nlinarith
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have key : (Real.sqrt (1 - c ^ 2) / c) ^ 2 = (1 - c ^ 2) / c ^ 2 := by
    rw [div_pow, Real.sq_sqrt hone]
  have step : (Real.sqrt (1 - c ^ 2) / c < x) ↔ ((Real.sqrt (1 - c ^ 2) / c) ^ 2 < x ^ 2) := by
    constructor
    · intro h
      exact pow_lt_pow_left₀ h (div_nonneg (Real.sqrt_nonneg _) hc.le) (by norm_num)
    · intro h
      have h1 : (0 : ℝ) ≤ Real.sqrt (1 - c ^ 2) / c :=
        div_nonneg (Real.sqrt_nonneg _) hc.le
      have := (sq_lt_sq (a := Real.sqrt (1 - c ^ 2) / c) (b := x)).mp h
      rwa [abs_of_nonneg h1, abs_of_pos hx] at this
  rw [step, key, div_lt_iff₀ hc2]
  constructor <;> intro h <;> nlinarith

/-- **The two junction identities on the cap.**  For `c` between `1/√(1+(4/5)²) ≈ 0.7809` and
`1/√(1+(7/10)²) ≈ 0.8192` (the `c`-image of the slope window `(7/10, 4/5)`, where the bump
vanishes and the anchor's moment equations coincide with the ball's central-section conditions)
the anchor's two Radon data are the ball's. -/
theorem anchorData_junction_cap (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    (hA : ∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    {c : ℝ}
    (hc : c ∈ Set.Ioo ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹)
      ((Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹)) :
    radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0 := by
  have hL : (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ < c := hc.1
  have hR : c < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ := hc.2
  have hcpos : 0 < c := by
    have : 0 < (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ :=
      inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
    linarith
  have hc1 : c ≤ 1 := by
    have h1 : c < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ := hR
    have h2 : (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by norm_num))
    linarith
  have hcLt1 : c < 1 := by
    have h2 : (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹ < 1 := by
      refine inv_lt_one_of_one_lt₀ ?_
      rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
      norm_num
    linarith
  have hslt0 : Real.sqrt (1 - c ^ 2) / c < 4 / 5 :=
    (sqrt_one_sub_sq_div_lt_iff hcpos (by norm_num) hc1).mpr
      (sq_cond_of_gt_inv_sqrt (by norm_num) hL)
  have hsgt0 : 7 / 10 < Real.sqrt (1 - c ^ 2) / c := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : (0 : ℝ) ≤ Real.sqrt (1 - c ^ 2) / c :=
      div_nonneg (Real.sqrt_nonneg _) hcpos.le
    have hsq : (Real.sqrt (1 - c ^ 2) / c) ^ 2 * c ^ 2 = 1 - c ^ 2 :=
      sqrt_one_sub_sq_div_sq_mul hcpos hc1
    have hcs : c ^ 2 * (1 + (Real.sqrt (1 - c ^ 2) / c) ^ 2) = 1 := by nlinarith [hsq]
    have hlt : c ^ 2 * (1 + (7 / 10 : ℝ) ^ 2) < 1 :=
      sq_cond_of_lt_inv_sqrt (by norm_num) hcpos.le hR
    have hle : (Real.sqrt (1 - c ^ 2) / c) ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by
      nlinarith [hcon, h1]
    nlinarith [hcs, hlt, hle]
  set s : ℝ := Real.sqrt (1 - c ^ 2) / c with hsdef
  have hs2c : s ^ 2 * c ^ 2 = 1 - c ^ 2 := sqrt_one_sub_sq_div_sq_mul hcpos hc1
  have hcs : c ^ 2 * (1 + s ^ 2) = 1 := by nlinarith [hs2c]
  have hspos : 0 < s := by rw [hsdef]; exact div_pos (Real.sqrt_pos.mpr (by nlinarith)) hcpos
  have hslt : s < 4 / 5 := by rw [hsdef]; exact hslt0
  have hsgt : 7 / 10 < s := by rw [hsdef]; exact hsgt0
  set a : ℝ := (7 / 10 + s) / 2 with hadef
  set b : ℝ := (s + 4 / 5) / 2 with hbdef
  have ha_pos : 0 < a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha_lt_s : a < s := by rw [hadef]; linarith
  have hs_lt_b : s < b := by rw [hbdef]; linarith
  have hb_lt : b < 4 / 5 := by rw [hbdef]; linarith
  have hcb : 1 < c ^ 2 * (1 + b ^ 2) := by
    have : 0 < c ^ 2 * (b ^ 2 - s ^ 2) := by
      have h1 : 0 < b - s := by linarith
      have h2 : 0 < b + s := by linarith
      nlinarith
    nlinarith [hcs, this]
  have hca : c ^ 2 * (1 + a ^ 2) < 1 := by
    have : 0 < c ^ 2 * (s ^ 2 - a ^ 2) := by
      have h1 : 0 < s - a := by linarith
      have h2 : 0 < s + a := by linarith
      nlinarith
    nlinarith [hcs, this]
  have hzero : ∀ u ∈ Set.Icc a b, h u = 0 := by
    intro u hu
    refine anchor_h_eq_zero_of_not_mem H (Or.inl ?_)
    have : (1 : ℝ) - 2 * tau = 4 / 5 := by norm_num [tau]
    rw [this]
    linarith [hu.2, hb_lt]
  have hder0 : ∀ u ∈ Set.Icc a b, deriv h u = 0 := by
    intro u hu
    refine deriv_eq_zero_of_eqOn_Ioo (show (7 / 10 : ℝ) < u by linarith [hu.1, ha_pos])
      (show u < 4 / 5 by linarith [hu.2, hb_lt]) ?_
    intro x hx
    refine anchor_h_eq_zero_of_not_mem H (Or.inl ?_)
    have : (1 : ℝ) - 2 * tau = 4 / 5 := by norm_num [tau]
    rw [this]
    exact hx.2
  have h3t : (1 : ℝ) - 3 * tau = 7 / 10 := by norm_num [tau]
  have hAb : ∀ u ∈ Set.Icc a b,
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) u =
        Work.OddCurve.refConst n / Real.sqrt (1 + u ^ 2) := by
    intro u hu
    exact hA u (by linarith [hu.1, ha_pos, h3t]) (by linarith [hu.2, hb_lt])
  have hBb : ∀ u ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) u = 0 := by
    intro u hu
    exact hB u (by linarith [hu.1, ha_pos, h3t]) (by linarith [hu.2, hb_lt])
  refine ⟨anchorPhiData_junction n hn H hρpos hρsm hρmono hgraph ha_pos hab hcpos hc1
      hzero hder0 hAb hBb hcb hca,
    anchorPsiData_junction n hn H hρpos hρsm hρmono hgraph ha_pos hab hcpos hc1
      hzero hder0 hBb hcb hca⟩

/-- On the cap `(0, 1/√(1+(7/10)²))` the glued datum is the anchor's: below `4/5` by the glue,
and above it because the anchor's datum is the ball's there (`anchorData_junction_cap`). -/
theorem gluedPhi_eq_anchorPhi_on_cap (n : ℕ) (hn : 1 ≤ n) {φa ψa : ℝ → ℝ} {c : ℝ}
    (hc0 : 0 < c) (hcc : c < (Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹)
    (hagree : ∀ x ∈ Set.Ioo ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹)
      ((Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹), φa x = ballPhiData n x ∧ ψa x = 0) :
    gluedPhi n φa c = φa c ∧ gluedPsi ψa c = ψa c := by
  have h45 : (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ < 4 / 5 := by
    rw [inv_lt_comm₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num : (0:ℝ) < 4 / 5)]
    rw [show ((4 : ℝ) / 5)⁻¹ = 5 / 4 by norm_num,
      Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 5 / 4)]
    norm_num
  rcases lt_or_ge c (4 / 5) with hc | hc
  · exact ⟨gluedPhi_of_lt hc0.le hc, gluedPsi_of_lt hc0.le hc⟩
  · have hmem : c ∈ Set.Ioo ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹)
        ((Real.sqrt (1 + (7 / 10 : ℝ) ^ 2))⁻¹) := ⟨lt_of_lt_of_le h45 hc, hcc⟩
    exact ⟨by rw [gluedPhi_of_ge hc0.le hc]; exact (hagree c hmem).1.symm,
      by rw [gluedPsi_of_ge hc0.le hc]; exact (hagree c hmem).2.symm⟩

end

end Work.OddCurve.LowSlope
