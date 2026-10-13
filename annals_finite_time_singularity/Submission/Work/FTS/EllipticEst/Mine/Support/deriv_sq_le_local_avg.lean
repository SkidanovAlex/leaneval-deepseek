import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.Support

open MeasureTheory intervalIntegral Set

/-- **Cauchy–Schwarz for interval integrals.**  If `f` is interval-integrable on `[a,b]` together
with `f²`, then `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`.  Proof: the quadratic polynomial
`λ ↦ ∫_a^b (λ - f)²` is nonnegative, and at `λ = (∫_a^b f)/(b-a)` its value is
`∫_a^b f² - (∫_a^b f)²/(b-a)`. -/
private lemma sq_integral_le_mul_integral_sq {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun y => f y ^ 2) volume a b) :
    (∫ y in a..b, f y) ^ 2 ≤ (b - a) * ∫ y in a..b, f y ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have hb : 0 < b - a := sub_pos.mpr h
  have hnonneg : ∀ lam : ℝ, 0 ≤ ∫ y in a..b, (lam - f y) ^ 2 :=
    fun lam => intervalIntegral.integral_nonneg hab (fun y _ => sq_nonneg _)
  have hexp : ∀ lam : ℝ, ∫ y in a..b, (lam - f y) ^ 2
      = lam ^ 2 * (b - a) - 2 * lam * (∫ y in a..b, f y) + (∫ y in a..b, f y ^ 2) := by
    intro lam
    have h1 : (fun y => (lam - f y) ^ 2) = fun y => lam ^ 2 - 2 * lam * f y + f y ^ 2 := by
      funext y; ring
    have hint1 : IntervalIntegrable (fun y : ℝ => lam ^ 2 - 2 * lam * f y) volume a b :=
      intervalIntegrable_const.sub (hf.const_mul (2 * lam))
    rw [h1, intervalIntegral.integral_add hint1 hf2,
      intervalIntegral.integral_sub intervalIntegrable_const (hf.const_mul (2 * lam)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    ring
  set A := ∫ y in a..b, f y
  set B := ∫ y in a..b, f y ^ 2
  have hmain := hnonneg (A / (b - a))
  rw [hexp] at hmain
  have e1 : (A / (b - a)) ^ 2 * (b - a) = A ^ 2 / (b - a) := by field_simp
  have e2 : 2 * (A / (b - a)) * A = 2 * (A ^ 2 / (b - a)) := by field_simp
  rw [e1, e2] at hmain
  have h4 : A ^ 2 / (b - a) ≤ B := by linarith
  rw [div_le_iff₀ hb] at h4
  have : A ^ 2 ≤ (b - a) * B := by linarith
  exact this

/-- **Oscillation bound for `g'` by the `L²` mass of `g''`.**  For `g` of class `C²` on `(p,r)`
and `p < a ≤ b < r`, one has `(g'(b) - g'(a))² ≤ (r-p) ∫_p^r (g'')²`.  Proof: the fundamental
theorem of calculus gives `g'(b) - g'(a) = ∫_a^b g''`, Cauchy–Schwarz gives
`(∫_a^b g'')² ≤ (b-a) ∫_a^b (g'')²`, and `∫_a^b (g'')² ≤ ∫_p^r (g'')²` since `(g'')² ≥ 0` and
`[a,b] ⊆ (p,r)`; finally `b - a ≤ r - p`. -/
private lemma deriv_sub_sq_le {g : ℝ → ℝ} {p r a b : ℝ} (hpa : p < a) (hbr : b < r) (hab : a ≤ b)
    (hg : ContDiffOn ℝ 2 g (Ioo p r))
    (hint : IntervalIntegrable (fun y => (deriv (deriv g) y) ^ 2) volume p r) :
    (deriv g b - deriv g a) ^ 2 ≤ (r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2) := by
  have hCd : ContinuousOn (deriv g) (Ioo p r) :=
    hg.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h1 : ContDiffOn ℝ 1 (deriv g) (Ioo p r) := hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDd : DifferentiableOn ℝ (deriv g) (Ioo p r) := h1.differentiableOn (by norm_num)
  have hCdd : ContinuousOn (deriv (deriv g)) (Ioo p r) := by
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) (f := deriv g) isOpen_Ioo).mp h1
    exact contDiffOn_zero.mp h2.2.2
  have hsub : Icc a b ⊆ Ioo p r := fun y hy => ⟨lt_of_lt_of_le hpa hy.1, lt_of_le_of_lt hy.2 hbr⟩
  have hsub' : Ioo a b ⊆ Ioo p r :=
    fun y hy => ⟨lt_of_lt_of_le hpa hy.1.le, lt_of_le_of_lt hy.2.le hbr⟩
  have hi1 : IntervalIntegrable (deriv (deriv g)) volume a b :=
    (hCdd.mono hsub).intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun y => (deriv (deriv g) y) ^ 2) volume a b :=
    ((hCdd.mono hsub).pow 2).intervalIntegrable_of_Icc hab
  have hFTC : ∫ y in a..b, deriv (deriv g) y = deriv g b - deriv g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hCd.mono hsub)
      (fun y hy => hDd.hasDerivAt (Ioo_mem_nhds (hsub' hy).1 (hsub' hy).2)) hi1
  have hCS : (∫ y in a..b, deriv (deriv g) y) ^ 2
      ≤ (b - a) * ∫ y in a..b, (deriv (deriv g) y) ^ 2 :=
    sq_integral_le_mul_integral_sq hab hi1 hi2
  have hmono : ∫ y in a..b, (deriv (deriv g) y) ^ 2 ≤ ∫ y in p..r, (deriv (deriv g) y) ^ 2 :=
    intervalIntegral.integral_mono_interval (le_of_lt hpa) hab (le_of_lt hbr)
      (ae_of_all _ (fun y => sq_nonneg _)) hint
  have hnonneg : 0 ≤ ∫ y in p..r, (deriv (deriv g) y) ^ 2 :=
    intervalIntegral.integral_nonneg (le_of_lt (lt_trans hpa (lt_of_le_of_lt hab hbr)))
      (fun y _ => sq_nonneg _)
  have hlen : b - a ≤ r - p := by linarith
  calc (deriv g b - deriv g a) ^ 2 = (∫ y in a..b, deriv (deriv g) y) ^ 2 := by rw [hFTC]
    _ ≤ (b - a) * ∫ y in a..b, (deriv (deriv g) y) ^ 2 := hCS
    _ ≤ (b - a) * ∫ y in p..r, (deriv (deriv g) y) ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
    _ ≤ (r - p) * ∫ y in p..r, (deriv (deriv g) y) ^ 2 :=
        mul_le_mul_of_nonneg_right hlen hnonneg

/-- **Averaging bound for `(g')²` from a local `L²` average and the global `(g'')²` mass.**
For `g` of class `C²` on the open interval `(p,r)`, with `p < x₁ < x₂ < r` and `(g'')²`
interval-integrable on `(p,r)`, every `θ ∈ (p,r)` satisfies
`(g'(θ))² ≤ (2/(x₂-x₁)) ∫_{x₁}^{x₂}(g')² + 2(r-p) ∫_p^r (g'')²`.  Route: pick (mean value property
for integrals, applied to the continuous function `(g')²` on `[x₁,x₂]`) a point `ȳ ∈ [x₁,x₂]` with
`(g'(ȳ))² = (∫_{x₁}^{x₂}(g')²)/(x₂-x₁)`.  Then `(g'(θ))² ≤ 2(g'(ȳ))² + 2(g'(θ)-g'(ȳ))²`, and
`|g'(θ)-g'(ȳ)| = |∫_θ^{ȳ} g''| ≤ ∫|g''|`, whose square is at most
`|θ-ȳ| ∫ (g'')² ≤ (r-p)∫_p^r (g'')²` by Cauchy–Schwarz (the sub-interval lies in `(p,r)`, where
`(g'')²` is integrable by hypothesis, hence so is `|g''|`). -/
theorem deriv_sq_le_local_avg {g : ℝ → ℝ} {p x₁ x₂ r : ℝ}
    (hp₁ : p < x₁) (h₁₂ : x₁ < x₂) (h₂r : x₂ < r)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo p r))
    (hint : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) MeasureTheory.volume p r) :
    ∀ θ ∈ Set.Ioo p r, (deriv g θ) ^ 2
      ≤ (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
        + 2 * (r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2) := by
  -- Instead of extracting a mean-value point of `(g')²` on `[x₁,x₂]`, integrate the pointwise
  -- inequality `(g'(θ))² ≤ 2(g'(x))² + 2(g'(θ)-g'(x))²` over `x ∈ [x₁,x₂]`.
  intro θ hθ
  obtain ⟨hθp, hθr⟩ := hθ
  have hxL : x₁ ≤ x₂ := h₁₂.le
  have hL : 0 < x₂ - x₁ := sub_pos.mpr h₁₂
  have hCd : ContinuousOn (deriv g) (Set.Ioo p r) :=
    hg.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsubX : Set.Icc x₁ x₂ ⊆ Set.Ioo p r :=
    fun y hy => ⟨lt_of_lt_of_le hp₁ hy.1, lt_of_le_of_lt hy.2 h₂r⟩
  have hcx : ContinuousOn (deriv g) (Set.Icc x₁ x₂) := hCd.mono hsubX
  have hInt1 : IntervalIntegrable (fun y : ℝ => (deriv g y) ^ 2) volume x₁ x₂ :=
    (hcx.pow 2).intervalIntegrable_of_Icc hxL
  have hInt3 : IntervalIntegrable (fun y : ℝ => (deriv g θ - deriv g y) ^ 2) volume x₁ x₂ := by
    have hc : ContinuousOn (fun y : ℝ => deriv g θ - deriv g y) (Set.Icc x₁ x₂) :=
      continuousOn_const.sub hcx
    exact (hc.pow 2).intervalIntegrable_of_Icc hxL
  have hInt2 : IntervalIntegrable
      (fun y : ℝ => 2 * (deriv g y) ^ 2 + 2 * (deriv g θ - deriv g y) ^ 2) volume x₁ x₂ :=
    (hInt1.const_mul 2).add (hInt3.const_mul 2)
  -- the uniform oscillation bound, for every `x ∈ [x₁,x₂]`
  have hdiff : ∀ x ∈ Set.Icc x₁ x₂,
      (deriv g θ - deriv g x) ^ 2 ≤ (r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2) := by
    intro x hx
    rcases le_total x θ with hxθ | hθx
    · exact deriv_sub_sq_le (lt_of_lt_of_le hp₁ hx.1) hθr hxθ hg hint
    · have h := deriv_sub_sq_le hθp (lt_of_le_of_lt hx.2 h₂r) hθx hg hint
      have h2 : (deriv g x - deriv g θ) ^ 2 = (deriv g θ - deriv g x) ^ 2 := by ring
      linarith [h, h2]
  -- the pointwise splitting `(g'(θ))² ≤ 2(g'(x))² + 2(g'(θ)-g'(x))²`
  have hpoint : ∀ x ∈ Set.Icc x₁ x₂,
      (deriv g θ) ^ 2 ≤ 2 * (deriv g x) ^ 2 + 2 * (deriv g θ - deriv g x) ^ 2 := by
    intro x hx
    nlinarith [sq_nonneg (deriv g θ - 2 * deriv g x)]
  have hmono1 : ∫ x in x₁..x₂, (deriv g θ) ^ 2
      ≤ ∫ x in x₁..x₂, (2 * (deriv g x) ^ 2 + 2 * (deriv g θ - deriv g x) ^ 2) :=
    intervalIntegral.integral_mono_on hxL
      (intervalIntegrable_const (c := (deriv g θ) ^ 2)) hInt2 hpoint
  have hexp1 : ∫ x in x₁..x₂, (2 * (deriv g x) ^ 2 + 2 * (deriv g θ - deriv g x) ^ 2)
      = 2 * (∫ x in x₁..x₂, (deriv g x) ^ 2)
        + 2 * (∫ x in x₁..x₂, (deriv g θ - deriv g x) ^ 2) := by
    rw [intervalIntegral.integral_add (hInt1.const_mul 2) (hInt3.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hmono2 : ∫ x in x₁..x₂, (deriv g θ - deriv g x) ^ 2
      ≤ (x₂ - x₁) * ((r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2)) := by
    calc ∫ x in x₁..x₂, (deriv g θ - deriv g x) ^ 2
        ≤ ∫ x in x₁..x₂, ((r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2)) :=
          intervalIntegral.integral_mono_on hxL hInt3
            (intervalIntegrable_const (c := (r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2)))
            hdiff
      _ = (x₂ - x₁) * ((r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have hconstA : (deriv g θ) ^ 2 * (x₂ - x₁) = ∫ x in x₁..x₂, (deriv g θ) ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hchain : (deriv g θ) ^ 2 * (x₂ - x₁)
      ≤ 2 * (∫ x in x₁..x₂, (deriv g x) ^ 2)
        + 2 * ((x₂ - x₁) * ((r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2))) := by
    rw [hconstA]
    have h := hmono1.trans (le_of_eq hexp1)
    have h3 : 2 * (∫ x in x₁..x₂, (deriv g x) ^ 2)
          + 2 * (∫ x in x₁..x₂, (deriv g θ - deriv g x) ^ 2)
        ≤ 2 * (∫ x in x₁..x₂, (deriv g x) ^ 2)
          + 2 * ((x₂ - x₁) * ((r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2))) := by
      linarith [hmono2]
    exact h.trans h3
  have hgoal : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
        + 2 * (r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2)
      = (2 * (∫ y in x₁..x₂, (deriv g y) ^ 2)
          + 2 * ((x₂ - x₁) * ((r - p) * (∫ y in p..r, (deriv (deriv g) y) ^ 2))))
        / (x₂ - x₁) := by
    field_simp
  rw [hgoal, le_div_iff₀ hL]
  linarith [hchain]

end Work.FTS.EllipticEst.Mine.Support
