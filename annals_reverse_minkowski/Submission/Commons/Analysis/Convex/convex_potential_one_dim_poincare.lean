import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Convex.convex_mollification_exists

/-
One-dimensional Brascamp-Lieb (variance) inequality.

Proof strategy (Hardy-inequality route, avoiding optimal transport):

For a convex potential `V` with `V - π x²` convex and a convex (interval) set `J`, the
inequality `∫_J f² e^{-V} ≤ (1/(2π)) ∫_J (f')² e^{-V}` for mean-zero `f` is equivalent to a
*weighted Hardy inequality* for the weight `1/ρ`, `ρ = e^{-V}`:

  `∫_J R²/ρ ≤ (1/c) ∫_J (R')²/ρ`   for all test functions `R`,

which in turn follows from a completion-of-squares identity together with the elementary
equilibrium inequality for the harmonic oscillator.  The interval case is obtained by
localising to `J ∩ [-n,n]` and passing to the limit.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Real Topology

namespace Commons.Analysis.Convex

noncomputable section

namespace BL1D

/-- **Completion of squares (Hardy form).**  For `u` continuous on `[A,B]`, differentiable in the
interior with derivative `du`, vanishing at the endpoints, and any `c`, `x₁`:
`(c/2)∫u² ≤ ∫du² + (c²/4)∫(x-x₁)²u²`. -/
lemma ho_bound (A B c x₁ : ℝ) (u du : ℝ → ℝ) (hAB : A ≤ B)
    (hu : ContinuousOn u (uIcc A B)) (hdu : ContinuousOn du (uIcc A B))
    (hd : ∀ x ∈ Ioo A B, HasDerivAt u (du x) x)
    (huA : u A = 0) (huB : u B = 0) :
    c / 2 * (∫ x in A..B, u x ^ 2)
      ≤ (∫ x in A..B, du x ^ 2) + c ^ 2 / 4 * (∫ x in A..B, (x - x₁) ^ 2 * u x ^ 2) := by
  set Iu : ℝ := ∫ x in A..B, u x ^ 2 with hIu
  set Idu : ℝ := ∫ x in A..B, du x ^ 2 with hIdu
  set Ixu : ℝ := ∫ x in A..B, (x - x₁) ^ 2 * u x ^ 2 with hIxu
  set J : ℝ := ∫ x in A..B, (x - x₁) * u x * du x with hJ
  have hu2 : IntervalIntegrable (fun x => u x ^ 2) volume A B := (hu.pow 2).intervalIntegrable
  have hdu2 : IntervalIntegrable (fun x => du x ^ 2) volume A B := (hdu.pow 2).intervalIntegrable
  have hJ' : IntervalIntegrable (fun x => (x - x₁) * u x * du x) volume A B :=
    (((continuousOn_id.sub continuousOn_const).mul hu).mul hdu).intervalIntegrable
  have hxu : IntervalIntegrable (fun x => (x - x₁) ^ 2 * u x ^ 2) volume A B :=
    (((continuousOn_id.sub continuousOn_const).pow 2).mul (hu.pow 2)).intervalIntegrable
  have h0 : 0 ≤ ∫ x in A..B, (du x + c/2 * (x - x₁) * u x) ^ 2 :=
    intervalIntegral.integral_nonneg hAB (fun x _ => sq_nonneg _)
  have hexp : ∫ x in A..B, (du x + c/2 * (x - x₁) * u x) ^ 2 = Idu + c * J + c ^ 2 / 4 * Ixu := by
    rw [show (fun x => (du x + c/2 * (x - x₁) * u x) ^ 2)
        = fun x => du x ^ 2 + c * ((x - x₁) * u x * du x) + c^2/4 * ((x - x₁)^2 * u x^2) by
      funext x; ring]
    rw [intervalIntegral.integral_add (hdu2.add (hJ'.const_mul c)) (hxu.const_mul (c^2/4)),
      intervalIntegral.integral_add hdu2 (hJ'.const_mul c),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hIdu, hJ, hIxu]
  have hibp : J = -(1/2) * Iu := by
    have hder2 : ∀ x ∈ Ioo (min A B) (max A B),
        HasDerivAt (fun y => u y ^ 2) (2 * u x * du x) x := by
      intro x hx
      have hx' : x ∈ Ioo A B := by
        rw [min_eq_left hAB, max_eq_right hAB] at hx; exact hx
      have hd2 : HasDerivAt (fun y => u y * u y) (du x * u x + u x * du x) x := by
        have h := (hd x hx').mul (hd x hx')
        have hfun : (u * u) = fun y => u y * u y := rfl
        rwa [hfun] at h
      have heq : (2:ℝ) * u x * du x = du x * u x + u x * du x := by ring
      rw [heq]; simpa [pow_two] using hd2
    have hder1 : ∀ x ∈ Ioo (min A B) (max A B), HasDerivAt (fun y => y - x₁) 1 x := by
      intro x hx; simpa using (hasDerivAt_id x).sub_const x₁
    have hcont1 : ContinuousOn (fun y => y - x₁) (uIcc A B) := by fun_prop
    have hcont2 : ContinuousOn (fun y => u y ^ 2) (uIcc A B) := hu.pow 2
    have h1 : IntervalIntegrable (fun _ => (1:ℝ)) volume A B := intervalIntegrable_const
    have h2 : IntervalIntegrable (fun x => 2 * u x * du x) volume A B :=
      ((hu.const_mul 2).mul hdu).intervalIntegrable
    have key := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcont1 hcont2 hder1 hder2 h1 h2
    have h2u : (fun x => (x - x₁) * (2 * u x * du x)) = fun x => 2 * ((x - x₁) * u x * du x) := by
      funext x; ring
    rw [h2u, intervalIntegral.integral_const_mul] at key
    rw [huB, huA] at key
    simp only [mul_zero, sub_zero, one_mul] at key
    rw [← hIu] at key
    linarith [key]
  have hfin : 0 ≤ Idu + c * J + c ^ 2 / 4 * Ixu := hexp ▸ h0
  rw [hibp] at hfin
  have hres : Idu + c ^ 2 / 4 * Ixu - c/2 * Iu = Idu + c * (-(1/2) * Iu) + c ^ 2 / 4 * Ixu := by ring
  rw [hIu, hIdu, hIxu]
  linarith [hfin, hres]

/-- Slope bound: `V' b - V' a ≥ c (b-a)` for `a < b` when `V'' ≥ c`. -/
lemma slope_bound_le (c : ℝ) (V' V'' : ℝ → ℝ) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : ∀ x, c ≤ V'' x) {a b : ℝ} (hab : a < b) :
    c * (b - a) ≤ V' b - V' a := by
  have hdiff : Differentiable ℝ V' := fun y => (hV' y).differentiableAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope V' hab hdiff.continuous.continuousOn
    hdiff.differentiableOn
  have hder : deriv V' ξ = V'' ξ := (hV' ξ).deriv
  rw [hder] at hξeq
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hle : c ≤ (V' b - V' a) / (b - a) := by rw [← hξeq]; exact hV''c ξ
  have := (le_div_iff₀ hpos).mp hle
  linarith

/-- For `V'` with `V'' ≥ c > 0` there is a point where `V'` vanishes. -/
lemma exists_deriv_eq_zero_of_le (c : ℝ) (V' V'' : ℝ → ℝ) (hc : 0 < c)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x) (hV''c : ∀ x, c ≤ V'' x) :
    ∃ x₁, V' x₁ = 0 := by
  have hdiff : Differentiable ℝ V' := fun y => (hV' y).differentiableAt
  have hbig : ∀ N : ℝ, 0 < N → V' (-N) ≤ V' 0 - c * N := by
    intro N hN
    have h := slope_bound_le c V' V'' hV' hV''c (show -N < 0 by linarith)
    linarith
  have hsmall : ∀ N : ℝ, 0 < N → V' N ≥ V' 0 + c * N := by
    intro N hN
    have h := slope_bound_le c V' V'' hV' hV''c (show (0:ℝ) < N by linarith)
    linarith
  obtain ⟨N, hNpos, hNabs⟩ : ∃ N : ℝ, 0 < N ∧ |V' 0| < c * N := by
    refine ⟨1 + |V' 0| / c, by positivity, ?_⟩
    have h1 : c * (1 + |V' 0| / c) = c + |V' 0| := by field_simp
    have h2 : (0:ℝ) ≤ |V' 0| := abs_nonneg _
    linarith
  have hneg : V' (-N) < 0 := by
    have h := hbig N hNpos
    have hlt : V' 0 < c * N := (abs_lt.mp hNabs).2
    linarith
  have hpos2 : 0 < V' N := by
    have h := hsmall N hNpos
    have hlt : -(c * N) < V' 0 := (abs_lt.mp hNabs).1
    linarith
  have hcont : ContinuousOn V' (uIcc (-N) N) := hdiff.continuous.continuousOn
  have hmem : (0:ℝ) ∈ uIcc (V' (-N)) (V' N) := by
    rw [uIcc_of_le (le_of_lt (lt_trans hneg hpos2))]
    exact ⟨le_of_lt hneg, le_of_lt hpos2⟩
  obtain ⟨x₁, hx₁, hx₁val⟩ := (intermediate_value_uIcc hcont) hmem
  exact ⟨x₁, hx₁val⟩

/-- Pointwise bound `c²(x-x₁)² ≤ (V' x)²` for `V'` with `V'' ≥ c ≥ 0` and `V' x₁ = 0`. -/
lemma deriv_sq_ge (c x₁ : ℝ) (V' V'' : ℝ → ℝ) (hc : 0 ≤ c)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : ∀ x, c ≤ V'' x) (hV'x₁ : V' x₁ = 0) (x : ℝ) :
    c ^ 2 * (x - x₁) ^ 2 ≤ V' x ^ 2 := by
  have hdiff : Differentiable ℝ V' := fun y => (hV' y).differentiableAt
  have slope_bound : ∀ (a b : ℝ), a < b → V' b - V' a ≥ c * (b - a) := by
    intro a b hab
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope V' hab hdiff.continuous.continuousOn
      hdiff.differentiableOn
    have hder : deriv V' ξ = V'' ξ := (hV' ξ).deriv
    rw [hder] at hξeq
    have hpos : 0 < b - a := sub_pos.mpr hab
    have hle : c ≤ (V' b - V' a) / (b - a) := by rw [← hξeq]; exact hV''c ξ
    have := (le_div_iff₀ hpos).mp hle
    linarith
  rcases le_total x₁ x with h | h
  · rcases eq_or_lt_of_le h with heq | hlt
    · rw [← heq, hV'x₁]; ring_nf; positivity
    · have h1 := slope_bound x₁ x hlt
      rw [hV'x₁] at h1
      have h2 : 0 ≤ c * (x - x₁) := mul_nonneg hc (by linarith)
      nlinarith [h1, h2]
  · rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq, hV'x₁]; ring_nf; positivity
    · have h1' : V' x₁ - V' x ≥ c * (x₁ - x) := by
        have := slope_bound x x₁ hlt; linarith
      rw [hV'x₁] at h1'
      have h2 : c * (x₁ - x) ≥ 0 := mul_nonneg hc (by linarith)
      nlinarith [h1', h2]

/-- **One-dimensional Hardy inequality.**  `c ∫ v² ≤ ∫ (v' - (V'/2) v)²` for `v` continuous on
`[A,B]`, `C¹` inside, vanishing at the endpoints, where `V'' ≥ c ≥ 0` and `V'` vanishes at `x₁`. -/
lemma hardy_C2 (A B c x₁ : ℝ) (V' V'' v dv : ℝ → ℝ) (hAB : A ≤ B) (hc : 0 ≤ c)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : ∀ x, c ≤ V'' x) (hV'x₁ : V' x₁ = 0)
    (hV''i : IntervalIntegrable V'' volume A B)
    (hv : ContinuousOn v (uIcc A B)) (hdv : ContinuousOn dv (uIcc A B))
    (hd : ∀ x ∈ Ioo A B, HasDerivAt v (dv x) x)
    (hvA : v A = 0) (hvB : v B = 0) :
    c * (∫ x in A..B, v x ^ 2) ≤ ∫ x in A..B, (dv x - V' x / 2 * v x) ^ 2 := by
  have hV'diff : Differentiable ℝ V' := fun y => (hV' y).differentiableAt
  have hV'c : ContinuousOn V' (uIcc A B) := hV'diff.continuous.continuousOn
  set Iu : ℝ := ∫ x in A..B, v x ^ 2 with hIu
  set Iv : ℝ := ∫ x in A..B, dv x ^ 2 with hIv
  set Ixu : ℝ := ∫ x in A..B, (x - x₁) ^ 2 * v x ^ 2 with hIxu
  set IVu : ℝ := ∫ x in A..B, V' x ^ 2 * v x ^ 2 with hIVu
  set J : ℝ := ∫ x in A..B, V' x * v x * dv x with hJ
  set IWu : ℝ := ∫ x in A..B, V'' x * v x ^ 2 with hIWu
  have hvu : IntervalIntegrable (fun x => v x ^ 2) volume A B := (hv.pow 2).intervalIntegrable
  have ho := ho_bound A B c x₁ v dv hAB hv hdv hd hvA hvB
  rw [← hIu, ← hIv, ← hIxu] at ho
  have hpt : ∀ x ∈ Icc A B, c ^ 2 / 4 * ((x - x₁) ^ 2 * v x ^ 2) ≤ V' x ^ 2 / 4 * v x ^ 2 := by
    intro x hx
    have h := deriv_sq_ge c x₁ V' V'' hc hV' hV''c hV'x₁ x
    nlinarith [sq_nonneg (v x)]
  have hmono : c ^ 2 / 4 * Ixu ≤ IVu / 4 := by
    have h1 : IntervalIntegrable (fun x => V' x ^ 2 / 4 * v x ^ 2) volume A B :=
      (((hV'c.pow 2).div_const 4).mul (hv.pow 2)).intervalIntegrable
    have h2 : IntervalIntegrable (fun x => c^2/4 * ((x - x₁)^2 * v x^2)) volume A B :=
      ((((continuousOn_id.sub continuousOn_const).pow 2).mul (hv.pow 2)).const_mul (c^2/4)).intervalIntegrable
    have hint := intervalIntegral.integral_mono_on hAB h2 h1 hpt
    have heq1 : (∫ x in A..B, c^2/4 * ((x - x₁)^2 * v x^2)) = c^2/4 * Ixu := by
      rw [intervalIntegral.integral_const_mul, hIxu]
    have heq2 : (∫ x in A..B, V' x^2/4 * v x^2) = IVu/4 := by
      rw [show (fun x => V' x^2/4 * v x^2) = fun x => (1/4:ℝ) * (V' x^2 * v x^2) by
        funext x; ring]
      rw [intervalIntegral.integral_const_mul, hIVu]
      ring
    rw [heq1, heq2] at hint
    exact hint
  have hA : c / 2 * Iu ≤ Iv + IVu / 4 := by
    nlinarith [hmono, ho]
  have hibp : J = -(1/2) * IWu := by
    have hcont2 : ContinuousOn (fun y => v y ^ 2) (uIcc A B) := hv.pow 2
    have hder1 : ∀ x ∈ Ioo (min A B) (max A B), HasDerivAt V' (V'' x) x := fun x _ => hV' x
    have hder2 : ∀ x ∈ Ioo (min A B) (max A B),
        HasDerivAt (fun y => v y ^ 2) (2 * v x * dv x) x := by
      intro x hx
      have hx' : x ∈ Ioo A B := by
        rw [min_eq_left hAB, max_eq_right hAB] at hx; exact hx
      have hd2 : HasDerivAt (fun y => v y * v y) (dv x * v x + v x * dv x) x := by
        have h := (hd x hx').mul (hd x hx')
        have hfun : (v * v) = fun y => v y * v y := rfl
        rwa [hfun] at h
      have heq : (2:ℝ) * v x * dv x = dv x * v x + v x * dv x := by ring
      rw [heq]; simpa [pow_two] using hd2
    have h1 : IntervalIntegrable (fun _ => (1:ℝ)) volume A B := intervalIntegrable_const
    have h2 : IntervalIntegrable (fun x => 2 * v x * dv x) volume A B :=
      ((hv.const_mul 2).mul hdv).intervalIntegrable
    have key := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hV'c hcont2 hder1 hder2 hV''i h2
    have h2u : (fun x => V' x * (2 * v x * dv x)) = fun x => 2 * (V' x * v x * dv x) := by
      funext x; ring
    rw [h2u, intervalIntegral.integral_const_mul] at key
    have hsimp : V' B * v B ^ 2 - V' A * v A ^ 2 - (∫ x in A..B, V'' x * v x ^ 2)
        = -(∫ x in A..B, V'' x * v x ^ 2) := by rw [hvB, hvA]; ring
    rw [hsimp] at key
    rw [← hIWu] at key
    rw [hJ]
    linarith [key]
  have hC : c / 2 * Iu ≤ IWu / 2 := by
    have h1 : IntervalIntegrable (fun x => V'' x * v x ^ 2) volume A B :=
      (hV''i.mul_continuousOn (hv.pow 2)).congr (by
        intro x _
        simp only [Pi.pow_apply])
    have h2 : IntervalIntegrable (fun x => c * v x ^ 2) volume A B := hvu.const_mul c
    have hpt2 : ∀ x ∈ Icc A B, c * v x ^ 2 ≤ V'' x * v x ^ 2 := by
      intro x hx
      exact mul_le_mul_of_nonneg_right (hV''c x) (sq_nonneg _)
    have hint := intervalIntegral.integral_mono_on hAB h2 h1 hpt2
    rw [intervalIntegral.integral_const_mul, ← hIu, ← hIWu] at hint
    linarith
  have hexp : ∫ x in A..B, (dv x - V' x / 2 * v x) ^ 2 = Iv - J + IVu / 4 := by
    rw [show (fun x => (dv x - V' x / 2 * v x) ^ 2)
        = fun x => dv x ^ 2 - (V' x * v x * dv x) + 1/4 * (V' x^2 * v x^2) by
      funext x; ring]
    have h1 : IntervalIntegrable (fun x => dv x ^ 2) volume A B := (hdv.pow 2).intervalIntegrable
    have h2 : IntervalIntegrable (fun x => V' x * v x * dv x) volume A B :=
      ((hV'c.mul hv).mul hdv).intervalIntegrable
    have h3 : IntervalIntegrable (fun x => V' x ^ 2 * v x ^ 2) volume A B :=
      ((hV'c.pow 2).mul (hv.pow 2)).intervalIntegrable
    rw [intervalIntegral.integral_add (h1.sub h2) (h3.const_mul (1/4)),
      intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
      hIv, hJ, hIVu]
    ring
  rw [hexp]
  linarith [hA, hibp, hC]

lemma pointwise1 (V R : ℝ → ℝ) (x : ℝ) :
    (R x * Real.exp (V x / 2)) ^ 2 = R x ^ 2 / Real.exp (-(V x)) := by
  have he : Real.exp (V x / 2) * Real.exp (V x / 2) = Real.exp (V x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (V x) = 1 / Real.exp (-(V x)) := by
    rw [Real.exp_neg, one_div, inv_inv]
  rw [show (R x * Real.exp (V x / 2))^2
      = R x^2 * (Real.exp (V x/2) * Real.exp (V x/2)) by ring]
  rw [he, hinv, mul_one_div]

lemma pointwise2 (V V' R dR : ℝ → ℝ) (x : ℝ) :
    ((dR x + V' x / 2 * R x) * Real.exp (V x / 2) - V' x / 2 * (R x * Real.exp (V x / 2))) ^ 2
      = dR x ^ 2 / Real.exp (-(V x)) := by
  have he : Real.exp (V x / 2) * Real.exp (V x / 2) = Real.exp (V x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (V x) = 1 / Real.exp (-(V x)) := by
    rw [Real.exp_neg, one_div, inv_inv]
  rw [show (dR x + V' x / 2 * R x) * Real.exp (V x / 2) - V' x / 2 * (R x * Real.exp (V x/2))
      = dR x * Real.exp (V x / 2) by ring]
  rw [show (dR x * Real.exp (V x / 2))^2 = dR x^2 * (Real.exp (V x/2) * Real.exp (V x/2)) by ring]
  rw [he, hinv, mul_one_div]

lemma hardy_range (A B c x₁ : ℝ) (V V' V'' R dR : ℝ → ℝ) (hAB : A ≤ B) (hc : 0 ≤ c)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : ∀ x, c ≤ V'' x) (hV'x₁ : V' x₁ = 0)
    (hV''i : IntervalIntegrable V'' volume A B)
    (hR : ContinuousOn R (uIcc A B)) (hdR : ContinuousOn dR (uIcc A B))
    (hd : ∀ x ∈ Ioo A B, HasDerivAt R (dR x) x)
    (hRA : R A = 0) (hRB : R B = 0) :
    c * (∫ x in A..B, R x ^ 2 / Real.exp (-(V x)))
      ≤ ∫ x in A..B, dR x ^ 2 / Real.exp (-(V x)) := by
  have hVdiff : Differentiable ℝ V := fun y => (hV y).differentiableAt
  have hV'diff : Differentiable ℝ V' := fun y => (hV' y).differentiableAt
  have hVc : ContinuousOn V (uIcc A B) := hVdiff.continuous.continuousOn
  have hV'c : ContinuousOn V' (uIcc A B) := hV'diff.continuous.continuousOn
  have hexp : ContinuousOn (fun x => Real.exp (V x / 2)) (uIcc A B) :=
    Real.continuous_exp.comp_continuousOn (hVc.div_const 2)
  have hvc : ContinuousOn (fun x => R x * Real.exp (V x / 2)) (uIcc A B) := hR.mul hexp
  have hdvc : ContinuousOn (fun x => (dR x + V' x / 2 * R x) * Real.exp (V x / 2)) (uIcc A B) :=
    (hdR.add ((hV'c.div_const 2).mul hR)).mul hexp
  have hvder : ∀ x ∈ Ioo A B,
      HasDerivAt (fun y => R y * Real.exp (V y / 2))
        ((dR x + V' x / 2 * R x) * Real.exp (V x / 2)) x := by
    intro x hx
    have h1 : HasDerivAt R (dR x) x := hd x hx
    have h2 : HasDerivAt (fun y => Real.exp (V y / 2))
        (Real.exp (V x / 2) * (V' x / 2)) x :=
      ((hV x).div_const 2).exp
    have h3 : HasDerivAt (fun y => R y * Real.exp (V y / 2))
        (dR x * Real.exp (V x / 2) + R x * (Real.exp (V x / 2) * (V' x / 2))) x := h1.mul h2
    have h4 : dR x * Real.exp (V x / 2) + R x * (Real.exp (V x / 2) * (V' x / 2))
        = (dR x + V' x / 2 * R x) * Real.exp (V x / 2) := by ring
    rwa [h4] at h3
  have hvA : (fun y => R y * Real.exp (V y / 2)) A = 0 := by simp [hRA]
  have hvB : (fun y => R y * Real.exp (V y / 2)) B = 0 := by simp [hRB]
  have key := hardy_C2 A B c x₁ V' V'' (fun y => R y * Real.exp (V y / 2))
    (fun y => (dR y + V' y / 2 * R y) * Real.exp (V y / 2))
    hAB hc hV' hV''c hV'x₁ hV''i hvc hdvc hvder hvA hvB
  have h1 : (∫ x in A..B, (R x * Real.exp (V x / 2)) ^ 2)
      = ∫ x in A..B, R x ^ 2 / Real.exp (-(V x)) :=
    intervalIntegral.integral_congr (fun x _ => pointwise1 V R x)
  have h2 : (∫ x in A..B, ((dR x + V' x / 2 * R x) * Real.exp (V x / 2)
        - V' x / 2 * (R x * Real.exp (V x / 2))) ^ 2)
      = ∫ x in A..B, dR x ^ 2 / Real.exp (-(V x)) :=
    intervalIntegral.integral_congr (fun x _ => pointwise2 V V' R dR x)
  rw [h1, h2] at key
  exact key

lemma transfer_interval (A B c x₁ : ℝ) (V V' V'' g dg : ℝ → ℝ) (hAB : A ≤ B) (hc : 0 < c)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : ∀ x, c ≤ V'' x) (hV'x₁ : V' x₁ = 0)
    (hV''i : IntervalIntegrable V'' volume A B)
    (hg : ContinuousOn g (uIcc A B)) (hdg : ContinuousOn dg (uIcc A B))
    (hd : ∀ x ∈ Ioo A B, HasDerivAt g (dg x) x)
    (hmean : ∫ x in A..B, g x * Real.exp (-(V x)) = 0) :
    ∫ x in A..B, g x ^ 2 * Real.exp (-(V x))
      ≤ (1 / c) * ∫ x in A..B, dg x ^ 2 * Real.exp (-(V x)) := by
  have hVdiff : Differentiable ℝ V := fun y => (hV y).differentiableAt
  have hVc : ContinuousOn V (uIcc A B) := hVdiff.continuous.continuousOn
  have hρc : ContinuousOn (fun x => Real.exp (-(V x))) (uIcc A B) :=
    Real.continuous_exp.comp_continuousOn hVc.neg
  have hUI : uIcc A B = Icc A B := uIcc_of_le hAB
  set G : ℝ → ℝ := fun x => g x * Real.exp (-(V x)) with hGdef
  have hGc : ContinuousOn G (uIcc A B) := hg.mul hρc
  have hGint : IntegrableOn G (uIcc A B) volume := hGc.integrableOn_compact isCompact_uIcc
  -- R
  have hRc : ContinuousOn (fun t => ∫ x in t..B, G x) (uIcc A B) :=
    intervalIntegral.continuousOn_primitive_interval_left hGint
  have hGcontOn : ∀ x ∈ Ioo A B, ContinuousAt G x := fun x hx =>
    hGc.continuousAt (by rw [hUI]; exact Icc_mem_nhds hx.1 hx.2)
  have hRd : ∀ t ∈ Ioo A B, HasDerivAt (fun s => ∫ x in s..B, G x) (-(G t)) t := by
    intro t ht
    have htB : t ≤ B := le_of_lt ht.2
    have hsub : uIcc t B ⊆ uIcc A B := by
      rw [hUI, uIcc_of_le htB]
      intro y hy
      exact ⟨le_trans (le_of_lt ht.1) hy.1, hy.2⟩
    have hcont : ContinuousOn G (uIcc t B) := hGc.mono hsub
    have hint : IntervalIntegrable G volume t B := hcont.intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter G (𝓝 t) volume :=
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun x hx => hGcontOn x hx) t ht
    exact integral_hasDerivAt_left hint hmeas (hGcontOn t ht)
  have hRA : (fun s => ∫ x in s..B, G x) A = 0 := by
    rw [hGdef] at hmean ⊢
    exact hmean
  have hRB : (fun s => ∫ x in s..B, G x) B = 0 := by simp
  -- Hardy applied to R
  have hhardy := hardy_range A B c x₁ V V' V'' (fun s => ∫ x in s..B, G x)
    (fun s => -(G s)) hAB hc.le hV hV' hV''c hV'x₁ hV''i hRc (hGc.neg) hRd hRA hRB
  have hRHS_int : (∫ x in A..B, (-(G x)) ^ 2 / Real.exp (-(V x)))
      = ∫ x in A..B, G x ^ 2 / Real.exp (-(V x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hRHS_int] at hhardy
  have hG2 : (∫ x in A..B, G x ^ 2 / Real.exp (-(V x)))
      = ∫ x in A..B, g x ^ 2 * Real.exp (-(V x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hGdef]
    simp only
    rw [show (g x * Real.exp (-(V x)))^2
        = g x^2 * (Real.exp (-(V x)) * Real.exp (-(V x))) by ring]
    field_simp
  rw [hG2] at hhardy
  -- IBP
  have hIBP : (∫ x in A..B, g x * (-(G x)))
      = g B * (∫ x in B..B, G x) - g A * (∫ x in A..B, G x)
        - ∫ x in A..B, dg x * (∫ y in x..B, G y) :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hg hRc
      (fun x hx => hd x (by rwa [min_eq_left hAB, max_eq_right hAB] at hx))
      (fun x hx => hRd x (by rwa [min_eq_left hAB, max_eq_right hAB] at hx))
      hdg.intervalIntegrable (hGc.neg.intervalIntegrable)
  have hkey : (∫ x in A..B, g x ^ 2 * Real.exp (-(V x)))
      = ∫ x in A..B, dg x * (∫ y in x..B, G y) := by
    have h1 : (∫ x in A..B, g x * (-(G x))) = -(∫ x in A..B, g x ^ 2 * Real.exp (-(V x))) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [hGdef]
      simp only
      ring
    have hRA' : (∫ x in A..B, G x) = 0 := hRA
    rw [h1] at hIBP
    rw [hRA'] at hIBP
    rw [intervalIntegral.integral_same, mul_zero, mul_zero, sub_zero, zero_sub] at hIBP
    linarith [hIBP]
  -- AM-GM
  have hcontR : ContinuousOn (fun x => ∫ y in x..B, G y) (uIcc A B) := hRc
  have hpt : ∀ x ∈ Icc A B, dg x * (∫ y in x..B, G y)
      ≤ (1/(2*c)) * (dg x^2 * Real.exp (-(V x)))
        + (c/2) * ((∫ y in x..B, G y)^2 / Real.exp (-(V x))) := by
    intro x hx
    have h1 : 2 * (c * Real.exp (-(V x))) * (dg x * (∫ y in x..B, G y))
        ≤ dg x^2 * (Real.exp (-(V x)))^2 + c^2 * (∫ y in x..B, G y)^2 := by
      nlinarith [sq_nonneg (dg x * Real.exp (-(V x)) - (∫ y in x..B, G y) * c)]
    have h2 : 0 < Real.exp (-(V x)) := Real.exp_pos _
    field_simp
    nlinarith [h1]
  have hHc : ContinuousOn (fun x => (1/(2*c)) * (dg x^2 * Real.exp (-(V x)))
      + (c/2) * ((∫ y in x..B, G y)^2 / Real.exp (-(V x)))) (uIcc A B) := by
    have h1 : ContinuousOn (fun x => dg x^2 * Real.exp (-(V x))) (uIcc A B) :=
      (hdg.pow 2).mul hρc
    have h2 : ContinuousOn (fun x => (∫ y in x..B, G y)^2 / Real.exp (-(V x))) (uIcc A B) :=
      (hcontR.pow 2).div hρc (fun x _ => Real.exp_ne_zero _)
    exact (continuousOn_const.mul h1).add (continuousOn_const.mul h2)
  have hi1 : IntervalIntegrable (fun x => dg x * (∫ y in x..B, G y)) volume A B :=
    (hdg.mul hcontR).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => (1/(2*c)) * (dg x^2 * Real.exp (-(V x)))
      + (c/2) * ((∫ y in x..B, G y)^2 / Real.exp (-(V x)))) volume A B :=
    hHc.intervalIntegrable
  have hAM := intervalIntegral.integral_mono_on hAB hi1 hi2 hpt
  have hsplit : (∫ x in A..B, ((1/(2*c)) * (dg x^2 * Real.exp (-(V x)))
        + (c/2) * ((∫ y in x..B, G y)^2 / Real.exp (-(V x)))))
      = (1/(2*c)) * (∫ x in A..B, dg x^2 * Real.exp (-(V x)))
        + (c/2) * (∫ x in A..B, (∫ y in x..B, G y)^2 / Real.exp (-(V x))) := by
    rw [intervalIntegral.integral_add (by
          have h1 : ContinuousOn (fun x => dg x^2 * Real.exp (-(V x))) (uIcc A B) :=
            (hdg.pow 2).mul hρc
          exact (continuousOn_const.mul h1).intervalIntegrable)
        (by
          have h2 : ContinuousOn (fun x => (∫ y in x..B, G y)^2 / Real.exp (-(V x))) (uIcc A B) :=
            (hcontR.pow 2).div hρc (fun x _ => Real.exp_ne_zero _)
          exact (continuousOn_const.mul h2).intervalIntegrable)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [← hkey, hsplit] at hAM
  have hfinal : (∫ x in A..B, g x ^ 2 * Real.exp (-(V x)))
      ≤ (1/(2*c)) * (∫ x in A..B, dg x^2 * Real.exp (-(V x)))
        + (c/2) * ((1/c) * (∫ x in A..B, g x^2 * Real.exp (-(V x)))) := by
    have h3 : (∫ x in A..B, (∫ y in x..B, G y)^2 / Real.exp (-(V x)))
        ≤ (1/c) * (∫ x in A..B, g x^2 * Real.exp (-(V x))) := by
      rw [show (1/c) * (∫ x in A..B, g x^2 * Real.exp (-(V x)))
          = (∫ x in A..B, g x^2 * Real.exp (-(V x))) / c by ring]
      rw [le_div_iff₀ hc]
      linarith [hhardy]
    have h4 : (c/2) * (∫ x in A..B, (∫ y in x..B, G y)^2 / Real.exp (-(V x)))
        ≤ (c/2) * ((1/c) * (∫ x in A..B, g x^2 * Real.exp (-(V x)))) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    linarith [hAM, h4]
  have hstep : (1/2) * (∫ x in A..B, g x ^ 2 * Real.exp (-(V x)))
      ≤ (1/(2*c)) * (∫ x in A..B, dg x^2 * Real.exp (-(V x))) := by
    have h4 : (c/2) * ((1/c) * (∫ x in A..B, g x ^ 2 * Real.exp (-(V x))))
        = (1/2) * (∫ x in A..B, g x ^ 2 * Real.exp (-(V x))) := by
      field_simp
    rw [h4] at hfinal
    linarith [hfinal]
  have hstep2 : c * (∫ x in A..B, g x ^ 2 * Real.exp (-(V x)))
      ≤ (∫ x in A..B, dg x^2 * Real.exp (-(V x))) := by
    have h2c : (0:ℝ) < 2*c := by linarith
    have := mul_le_mul_of_nonneg_left hstep (le_of_lt h2c)
    have e1 : (2*c) * ((1/2) * (∫ x in A..B, g x ^ 2 * Real.exp (-(V x))))
        = c * (∫ x in A..B, g x ^ 2 * Real.exp (-(V x))) := by ring
    have e2 : (2*c) * ((1/(2*c)) * (∫ x in A..B, dg x^2 * Real.exp (-(V x))))
        = (∫ x in A..B, dg x^2 * Real.exp (-(V x))) := by field_simp
    rwa [e1, e2] at this
  rw [show (1/c) * (∫ x in A..B, dg x^2 * Real.exp (-(V x)))
      = (∫ x in A..B, dg x^2 * Real.exp (-(V x))) / c by ring]
  rw [le_div_iff₀ hc]
  linarith [hstep2]


lemma secant_lower_right (W : ℝ → ℝ) (hW : ConvexOn ℝ Set.univ W) {x : ℝ} (hx : 1 ≤ x) :
    W 0 + x * (W 1 - W 0) ≤ W x := by
  have h := hW.secant_mono (a := 0) (x := 1) (y := x) (mem_univ 0) (mem_univ 1) (mem_univ x)
    (by norm_num) (by linarith) hx
  have h' : W 1 - W 0 ≤ (W x - W 0) / x := by simpa using h
  have hx0 : 0 < x := by linarith
  have := (le_div_iff₀ hx0).mp h'
  linarith

lemma secant_lower_left (W : ℝ → ℝ) (hW : ConvexOn ℝ Set.univ W) {x : ℝ} (hx : x ≤ -1) :
    W 0 + (-x) * (W (-1) - W 0) ≤ W x := by
  have h := hW.secant_mono (a := 0) (x := x) (y := -1) (mem_univ 0) (mem_univ x) (mem_univ (-1))
    (by linarith) (by norm_num) hx
  have h' : (W x - W 0) / x ≤ W 0 - W (-1) := by
    have h2 : (W (-1) - W 0) / (-1:ℝ) = W 0 - W (-1) := by ring
    simpa [h2] using h
  have hx0 : x < 0 := by linarith
  have := (div_le_iff_of_neg hx0).mp h'
  linarith

lemma amgm_pi (M : ℝ) (x : ℝ) :
    M * |x| ≤ Real.pi * x ^ 2 / 2 + M ^ 2 / (2 * Real.pi) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have h := sq_nonneg (Real.pi * |x| - M)
  have hexp : (Real.pi * |x| - M)^2 = Real.pi^2 * x^2 - 2*Real.pi*M*|x| + M^2 := by
    rw [sub_sq, mul_pow, sq_abs]; ring
  rw [hexp] at h
  rw [show Real.pi * x^2/2 + M^2/(2*Real.pi) = (Real.pi^2 * x^2 + M^2)/(2*Real.pi) by
    field_simp]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
  nlinarith [h]


lemma exp_neg_convex_sub_sq_integrable (V : ℝ → ℝ)
    (hV2 : ConvexOn ℝ Set.univ (fun x => V x - Real.pi * x ^ 2)) :
    Integrable (fun x => Real.exp (-(V x))) volume := by
  set W : ℝ → ℝ := fun x => V x - Real.pi * x ^ 2 with hWdef
  have hWconv : ConvexOn ℝ Set.univ W := hWdef.symm ▸ hV2
  have hWcont : Continuous W := continuousOn_univ.mp (hWconv.continuousOn isOpen_univ)
  have hWV : ∀ x, V x = W x + Real.pi * x ^ 2 := by
    intro x; rw [hWdef]; ring
  have hVcont : Continuous V := by
    have h2 : Continuous (fun x : ℝ => Real.pi * x ^ 2) := continuous_const.mul (continuous_pow 2)
    have h3 : Continuous (fun x : ℝ => W x + Real.pi * x ^ 2) := hWcont.add h2
    have heq : (fun x : ℝ => W x + Real.pi * x ^ 2) = V := funext (fun x => (hWV x).symm)
    rwa [heq] at h3
  set M : ℝ := max |W 1 - W 0| |W (-1) - W 0| with hMdef
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  obtain ⟨K, hK⟩ : ∃ K, ∀ x ∈ Icc (-1:ℝ) 1, K ≤ W x := by
    have hb := IsCompact.bddBelow_image (isCompact_Icc (a := (-1:ℝ)) (b := 1)) hWcont.continuousOn
    obtain ⟨K, hK⟩ := hb
    exact ⟨K, fun x hx => hK ⟨x, hx, rfl⟩⟩
  set C : ℝ := M^2/(2*Real.pi) + |W 0| + |K| + Real.pi/2 + 1 with hCdef
  have hWlow : ∀ x : ℝ, 1 ≤ |x| → W 0 - M * |x| ≤ W x := by
    intro x hx
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx
      have h1 := secant_lower_right W hWconv hx
      have h3 : |W 1 - W 0| * x ≤ M * |x| := by
        rw [abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_right (by rw [hMdef]; exact le_max_left _ _) h0
      have h2 : -( |W 1 - W 0| * x) ≤ x * (W 1 - W 0) := by
        have h4 := mul_le_mul_of_nonneg_right (neg_abs_le (W 1 - W 0)) h0
        nlinarith [h4]
      linarith
    · rw [abs_of_nonpos h0] at hx
      have hx2 : x ≤ -1 := by linarith
      have h1 := secant_lower_left W hWconv hx2
      have h3 : |W (-1) - W 0| * (-x) ≤ M * |x| := by
        rw [abs_of_nonpos h0]
        exact mul_le_mul_of_nonneg_right (by rw [hMdef]; exact le_max_right _ _) (by linarith)
      have h2 : -( |W (-1) - W 0| * (-x)) ≤ (-x) * (W (-1) - W 0) := by
        have h4 := mul_le_mul_of_nonneg_right (neg_abs_le (W (-1) - W 0)) (by linarith : (0:ℝ) ≤ -x)
        nlinarith [h4]
      linarith
  have hbound : ∀ x : ℝ, Real.pi * x^2/2 - C ≤ V x := by
    intro x
    have ham := amgm_pi M x
    rcases le_total 1 |x| with hx | hx
    · rw [hCdef]; linarith [hWlow x hx, ham, neg_abs_le (W 0), neg_abs_le K, hWV x, abs_nonneg K, abs_nonneg (W 0), Real.pi_pos]
    · have hI : x ∈ Icc (-1:ℝ) 1 := abs_le.mp hx
      have hKx := hK x hI
      have hq : (0:ℝ) ≤ Real.pi * x^2/2 := by positivity
      have hA : (0:ℝ) ≤ M^2/(2*Real.pi) := by positivity
      have hB : (0:ℝ) ≤ |W 0| := abs_nonneg _
      have hD : (0:ℝ) ≤ |K| := abs_nonneg K
      have hE : (0:ℝ) ≤ Real.pi/2 := by positivity
      rw [hCdef]
      linarith [hKx, hWV x, hq, hA, hB, hD, hE, neg_abs_le K]
  refine Integrable.mono' (f := fun x => Real.exp (-(V x)))
    ((integrable_exp_neg_mul_sq (show (0:ℝ) < Real.pi/2 by positivity)).const_mul (Real.exp C))
    (Real.continuous_exp.comp hVcont.neg).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have h := hbound x
  linarith


theorem interior_nonempty_of_convex_of_measure_ne_zero (J : Set ℝ) (hJ : Convex ℝ J)
    (h : volume J ≠ 0) : (interior J).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have haux : ∀ x ∈ J, ∀ y ∈ J, x < y → False := by
    intro x hx y hy hlt
    have hseg : Set.Ioo x y ⊆ J := fun z hz =>
      hJ.ordConnected.out hx hy (Ioo_subset_Icc_self hz)
    have hm : (x+y)/2 ∈ interior J :=
      interior_maximal hseg isOpen_Ioo ⟨by linarith, by linarith⟩
    rw [hne] at hm
    exact hm
  have hsub : J.Subsingleton := by
    intro x hx y hy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd hlt (haux x hx y hy)
    · exact heq
    · exact (haux y hy x hx hgt).elim
  exact h (Subsingleton.measure_zero hsub volume)

theorem interval_exhaustion_convex (J : Set ℝ) (hJ : Convex ℝ J) (hJm : MeasurableSet J)
    (hne : (interior J).Nonempty) :
    ∃ A B : ℕ → ℝ, (∀ n, A n < B n) ∧ (∀ n, Set.Ioo (A n) (B n) ⊆ J) ∧
      Monotone (fun n => Set.Ioo (A n) (B n)) ∧
      (∀ᵐ x ∂(volume.restrict J), ∃ n, x ∈ Set.Ioo (A n) (B n)) := by
  obtain ⟨x₀, hx₀_int⟩ := hne
  have hx₀J : x₀ ∈ J := interior_subset hx₀_int
  obtain ⟨ε, hεpos, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀_int)
  have hIoo : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ J := by
    intro z hz
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  set M : ℕ → ℝ := fun n => (n:ℝ) + |x₀| + ε + 1 with hMdef
  have hMge : ∀ n, |x₀| + ε ≤ M n := by
    intro n; simp only [hMdef]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hx₀M : ∀ n, x₀ ∈ Set.Icc (-(M n)) (M n) := by
    intro n
    have h1 : |x₀| ≤ M n := le_trans (le_add_of_nonneg_right hεpos.le) (hMge n)
    rw [mem_Icc]
    exact abs_le.mp h1
  set K : ℕ → Set ℝ := fun n => J ∩ Set.Icc (-(M n)) (M n) with hKdef
  have hbdd : ∀ n, BddBelow (K n) := by
    intro n; exact ⟨-(M n), fun y hy => hy.2.1⟩
  have hbdd' : ∀ n, BddAbove (K n) := by
    intro n; exact ⟨M n, fun y hy => hy.2.2⟩
  have hneK : ∀ n, (K n).Nonempty := fun n => ⟨x₀, hx₀J, hx₀M n⟩
  have hmem1 : ∀ n, x₀ - ε/2 ∈ K n := by
    intro n
    refine ⟨hIoo ⟨by linarith, by linarith⟩, ?_⟩
    have h1 : |x₀ - ε/2| ≤ |x₀| + ε/2 := by
      calc |x₀ - ε/2| ≤ |x₀ - 0| + |0 - ε/2| := abs_sub_le x₀ 0 (ε/2)
        _ = |x₀| + ε/2 := by
              rw [sub_zero, zero_sub, abs_neg, abs_of_pos (show (0:ℝ) < ε/2 by linarith)]
    have h2 : |x₀| + ε/2 ≤ M n := by have := hMge n; linarith
    exact abs_le.mp (le_trans h1 h2)
  have hmem2 : ∀ n, x₀ + ε/2 ∈ K n := by
    intro n
    refine ⟨hIoo ⟨by linarith, by linarith⟩, ?_⟩
    have h1 : |x₀ + ε/2| ≤ |x₀| + ε/2 := by
      calc |x₀ + ε/2| ≤ |x₀| + |ε/2| := abs_add_le _ _
        _ = |x₀| + ε/2 := by rw [abs_of_pos (show (0:ℝ) < ε/2 by linarith)]
    have h2 : |x₀| + ε/2 ≤ M n := by have := hMge n; linarith
    exact abs_le.mp (le_trans h1 h2)
  set A : ℕ → ℝ := fun n => sInf (K n) with hAdef
  set B : ℕ → ℝ := fun n => sSup (K n) with hBdef
  have hA : ∀ n, A n = sInf (K n) := fun n => congrFun hAdef n
  have hB : ∀ n, B n = sSup (K n) := fun n => congrFun hBdef n
  have hMmono : ∀ n, M n ≤ M (n+1) := by
    intro n; simp only [hMdef]; push_cast; linarith
  have hKmono : ∀ n, K n ⊆ K (n+1) := by
    intro n y hy
    simp only [hKdef, Set.mem_inter_iff, Set.mem_Icc] at hy ⊢
    exact ⟨hy.1, by linarith [hy.2.1, hMmono n], by linarith [hy.2.2, hMmono n]⟩
  have hstep : ∀ n, Set.Ioo (A n) (B n) ⊆ Set.Ioo (A (n+1)) (B (n+1)) := by
    intro n z hz
    rw [mem_Ioo] at hz ⊢
    have h1 : sInf (K (n+1)) ≤ sInf (K n) :=
      csInf_le_csInf (hbdd (n+1)) (hneK n) (hKmono n)
    have h2 : sSup (K n) ≤ sSup (K (n+1)) :=
      csSup_le_csSup (hbdd' (n+1)) (hneK n) (hKmono n)
    rw [← hA (n+1), ← hA n] at h1
    rw [← hB n, ← hB (n+1)] at h2
    exact ⟨lt_of_le_of_lt h1 hz.1, lt_of_lt_of_le hz.2 h2⟩
  refine ⟨A, B, ?_, ?_, monotone_nat_of_le_succ hstep, ?_⟩
  · intro n
    have h1 : A n ≤ x₀ - ε/2 := hA n ▸ csInf_le (hbdd n) (hmem1 n)
    have h2 : x₀ + ε/2 ≤ B n := hB n ▸ le_csSup (hbdd' n) (hmem2 n)
    linarith
  · intro n z hz
    rw [mem_Ioo] at hz
    obtain ⟨y, hy, hyz⟩ := (csInf_lt_iff (hbdd n) (hneK n)).mp (hA n ▸ hz.1)
    obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (hbdd' n) (hneK n)).mp (hB n ▸ hz.2)
    exact hJ.ordConnected.out hy.1 hw.1 ⟨le_of_lt hyz, le_of_lt hzw⟩
  · rw [ae_restrict_iff' hJm, ae_iff]
    have hcount : (Set.range A ∪ Set.range B).Countable :=
      (countable_range A).union (countable_range B)
    have hnull : volume (Set.range A ∪ Set.range B) = 0 :=
      Set.Countable.measure_zero hcount volume
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [Classical.not_imp] at hx
    obtain ⟨hxJ, hxP⟩ := hx
    obtain ⟨N, hN⟩ : ∃ N : ℕ, |x| ≤ M N := by
      refine ⟨⌈|x|⌉₊, ?_⟩
      have h1 : |x| ≤ ((⌈|x|⌉₊ : ℕ) : ℝ) := Nat.le_ceil |x|
      have h2 : ((⌈|x|⌉₊ : ℕ) : ℝ) ≤ M ⌈|x|⌉₊ := by
        simp only [hMdef]; linarith [abs_nonneg x₀, hεpos]
      linarith
    have hxK : x ∈ K N := by
      rw [hKdef]
      exact ⟨hxJ, abs_le.mp hN⟩
    have hAN : sInf (K N) ≤ x := csInf_le (hbdd N) hxK
    have hBN : x ≤ sSup (K N) := le_csSup (hbdd' N) hxK
    have hAN' : A N ≤ x := hA N ▸ hAN
    have hBN' : x ≤ B N := hB N ▸ hBN
    rcases lt_or_ge (A N) x with hlt | hge
    · right
      refine ⟨N, le_antisymm ?_ hBN'⟩
      by_contra hcon
      exact hxP ⟨N, hlt, lt_of_not_ge hcon⟩
    · left
      exact ⟨N, le_antisymm hAN' hge⟩

theorem tendsto_intervalIntegral_of_exhaustion (A B : ℕ → ℝ) (J : Set ℝ)
    (hAB : ∀ n, A n ≤ B n) (hsub : ∀ n, Set.Ioo (A n) (B n) ⊆ J)
    (hmono : Monotone (fun n => Set.Ioo (A n) (B n)))
    (hexh : ∀ᵐ x ∂(volume.restrict J), ∃ n, x ∈ Set.Ioo (A n) (B n))
    (f : ℝ → ℝ) (hf : IntegrableOn f J volume) :
    Tendsto (fun n => ∫ x in A n..B n, f x) atTop (𝓝 (∫ x in J, f x)) := by
  have hstep : ∀ n, ∫ x in A n..B n, f x = ∫ x in Set.Ioo (A n) (B n), f x := by
    intro n
    rw [intervalIntegral.integral_of_le (hAB n), integral_Ioc_eq_integral_Ioo]
  have hUJ : (⋃ n, Set.Ioo (A n) (B n)) ⊆ J := Set.iUnion_subset hsub
  have hUI : IntegrableOn f (⋃ n, Set.Ioo (A n) (B n)) volume := hf.mono_set hUJ
  have hlim := tendsto_setIntegral_of_monotone (f := f) (μ := volume)
    (s := fun n => Set.Ioo (A n) (B n)) (fun n => measurableSet_Ioo) hmono hUI
  have hmeasU : MeasurableSet (⋃ n, Set.Ioo (A n) (B n)) :=
    MeasurableSet.iUnion fun n => measurableSet_Ioo
  have hmemU : ∀ᵐ x ∂(volume.restrict J), x ∈ ⋃ n, Set.Ioo (A n) (B n) := by
    filter_upwards [hexh] with x hx
    exact Set.mem_iUnion.mpr hx
  have h0 : volume ((⋃ n, Set.Ioo (A n) (B n))ᶜ ∩ J) = 0 := by
    have h1 := ae_iff.mp hmemU
    rw [← Measure.restrict_apply hmeasU.compl]
    exact h1
  have hiff : ∀ᵐ x ∂volume, x ∈ (⋃ n, Set.Ioo (A n) (B n)) ↔ x ∈ J := by
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hxU : x ∉ ⋃ n, Set.Ioo (A n) (B n) := by
      intro hxU
      exact hx ⟨fun _ => hUJ hxU, fun _ => hxU⟩
    refine ⟨hxU, ?_⟩
    by_contra hxJ
    exact hx ⟨fun h => absurd h hxU, fun h => absurd h hxJ⟩
  have hae : (⋃ n, Set.Ioo (A n) (B n)) =ᵐ[volume] J := by
    filter_upwards [hiff] with x hx
    exact propext hx
  rw [show (∫ x in J, f x) = ∫ x in ⋃ n, Set.Ioo (A n) (B n), f x from
    (setIntegral_congr_set hae).symm]
  simp only [hstep]
  exact hlim


lemma integral_sub_const_mul (A B k : ℝ) (g w : ℝ → ℝ)
    (hg : ContinuousOn g (uIcc A B)) (hw : ContinuousOn w (uIcc A B)) :
    ∫ x in A..B, (g x - k) * w x = (∫ x in A..B, g x * w x) - k * (∫ x in A..B, w x) := by
  have h1 : IntervalIntegrable (fun x => g x * w x) volume A B := (hg.mul hw).intervalIntegrable
  have h3 : IntervalIntegrable (fun x => k * w x) volume A B := hw.intervalIntegrable.const_mul k
  rw [show (fun x => (g x - k) * w x) = fun x => g x * w x - k * w x by funext x; ring]
  rw [intervalIntegral.integral_sub h1 h3, intervalIntegral.integral_const_mul]

lemma integral_sq_sub_const_mul (A B k : ℝ) (g w : ℝ → ℝ)
    (hg : ContinuousOn g (uIcc A B)) (hw : ContinuousOn w (uIcc A B)) :
    ∫ x in A..B, (g x - k) ^ 2 * w x
      = (∫ x in A..B, g x ^ 2 * w x) - 2 * k * (∫ x in A..B, g x * w x)
        + k ^ 2 * (∫ x in A..B, w x) := by
  have h1 : IntervalIntegrable (fun x => g x ^ 2 * w x) volume A B :=
    ((hg.pow 2).mul hw).intervalIntegrable
  have h2 : IntervalIntegrable (fun x => g x * w x) volume A B := (hg.mul hw).intervalIntegrable
  have h3 : IntervalIntegrable (fun x => k ^ 2 * w x) volume A B := hw.intervalIntegrable.const_mul _
  rw [show (fun x => (g x - k) ^ 2 * w x)
      = fun x => g x ^ 2 * w x - 2 * k * (g x * w x) + k ^ 2 * w x by funext x; ring]
  rw [intervalIntegral.integral_add (h1.sub (h2.const_mul (2*k))) h3,
    intervalIntegral.integral_sub h1 (h2.const_mul (2*k)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem brascamp_lieb_of_C2 (V V' V'' g dg : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x)
    (hV''c : ∀ x, c ≤ V'' x) (hV''cont : Continuous V'')
    (x₁ : ℝ) (hx₁ : V' x₁ = 0)
    (J : Set ℝ) (hJ : Convex ℝ J) (hJm : MeasurableSet J)
    (hpos : 0 < ∫ x in J, Real.exp (-(V x)))
    (hgc : Continuous g) (hdgc : Continuous dg) (hdg : ∀ x, HasDerivAt g (dg x) x)
    (h2 : IntegrableOn (fun x => g x ^ 2 * Real.exp (-(V x))) J)
    (hgi : IntegrableOn (fun x => dg x ^ 2 * Real.exp (-(V x))) J)
    (hρ : IntegrableOn (fun x => Real.exp (-(V x))) J)
    (hgρ : IntegrableOn (fun x => g x * Real.exp (-(V x))) J)
    (hmean : ∫ x in J, g x * Real.exp (-(V x)) = 0) :
    ∫ x in J, g x ^ 2 * Real.exp (-(V x))
      ≤ (1 / c) * ∫ x in J, dg x ^ 2 * Real.exp (-(V x)) := by
  have hVcont : Continuous V := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have hρc : Continuous (fun x : ℝ => Real.exp (-(V x))) := Real.continuous_exp.comp hVcont.neg
  have hvol : volume J ≠ 0 := by
    intro h0
    have h1 := setIntegral_measure_zero (fun x : ℝ => Real.exp (-(V x))) h0
    rw [h1] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨A, B, hABlt, hsub, hmono, hexh⟩ :=
    interval_exhaustion_convex J hJ hJm (interior_nonempty_of_convex_of_measure_ne_zero J hJ hvol)
  have hAB : ∀ n, A n ≤ B n := fun n => (hABlt n).le
  set s : ℕ → ℝ := fun n => ∫ x in A n..B n, Real.exp (-(V x)) with hSdef
  set t : ℕ → ℝ := fun n => ∫ x in A n..B n, g x * Real.exp (-(V x)) with hTdef
  set cn : ℕ → ℝ := fun n => t n / s n with hCNdef
  have hs : ∀ n, s n = ∫ x in A n..B n, Real.exp (-(V x)) := fun n => congrFun hSdef n
  have ht : ∀ n, t n = ∫ x in A n..B n, g x * Real.exp (-(V x)) := fun n => congrFun hTdef n
  have hcn : ∀ n, cn n = t n / s n := fun n => congrFun hCNdef n
  have hs_pos : ∀ n, 0 < s n := by
    intro n
    rw [hs n]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (hρc.continuousOn.intervalIntegrable) (fun x _ => Real.exp_pos _) (hABlt n)
  have hmz : ∀ n, ∫ x in A n..B n, (g x - cn n) * Real.exp (-(V x)) = 0 := by
    intro n
    rw [integral_sub_const_mul (A n) (B n) (cn n) g
      (fun x => Real.exp (-(V x))) hgc.continuousOn hρc.continuousOn]
    rw [← ht n, ← hs n, hcn n, div_mul_cancel₀ _ (ne_of_gt (hs_pos n)), sub_self]
  have hineq : ∀ n, (∫ x in A n..B n, g x ^ 2 * Real.exp (-(V x)))
      ≤ (1 / c) * (∫ x in A n..B n, dg x ^ 2 * Real.exp (-(V x)))
        + (2 * cn n * t n - cn n ^ 2 * s n) := by
    intro n
    have hV''i : IntervalIntegrable V'' volume (A n) (B n) :=
      hV''cont.continuousOn.intervalIntegrable
    have htr := transfer_interval (A n) (B n) c x₁ V V' V'' (fun x => g x - cn n) dg
      (hAB n) hc hV hV' hV''c hx₁ hV''i
      (hgc.continuousOn.sub continuous_const.continuousOn) hdgc.continuousOn
      (fun x _ => (hdg x).sub_const (cn n)) (hmz n)
    have hexp : (∫ x in A n..B n, (g x - cn n) ^ 2 * Real.exp (-(V x)))
        = (∫ x in A n..B n, g x ^ 2 * Real.exp (-(V x))) - 2 * cn n * t n + cn n ^ 2 * s n := by
      rw [integral_sq_sub_const_mul (A n) (B n) (cn n) g
        (fun x => Real.exp (-(V x))) hgc.continuousOn hρc.continuousOn]
    rw [hexp] at htr
    linarith [htr]
  have hlim_s : Tendsto s atTop (𝓝 (∫ x in J, Real.exp (-(V x)))) := by
    rw [hSdef]
    exact tendsto_intervalIntegral_of_exhaustion A B J hAB hsub hmono hexh _ hρ
  have hlim_t : Tendsto t atTop (𝓝 0) := by
    rw [hTdef]
    have h := tendsto_intervalIntegral_of_exhaustion A B J hAB hsub hmono hexh
      (fun x => g x * Real.exp (-(V x))) hgρ
    rwa [hmean] at h
  have hlim_cn : Tendsto cn atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => t n / s n) atTop (𝓝 (0 / (∫ x in J, Real.exp (-(V x))))) :=
      hlim_t.div hlim_s (ne_of_gt hpos)
    rw [zero_div] at h1
    rw [hCNdef]
    exact h1
  have hlim_err : Tendsto (fun n => 2 * cn n * t n - cn n ^ 2 * s n) atTop (𝓝 0) := by
    have h := (((hlim_cn.const_mul 2).mul hlim_t).sub ((hlim_cn.pow 2).mul hlim_s))
    simpa using h
  have hlim_f2 : Tendsto (fun n => ∫ x in A n..B n, g x ^ 2 * Real.exp (-(V x))) atTop
      (𝓝 (∫ x in J, g x ^ 2 * Real.exp (-(V x)))) :=
    tendsto_intervalIntegral_of_exhaustion A B J hAB hsub hmono hexh _ h2
  have hlim_g2 : Tendsto (fun n => ∫ x in A n..B n, dg x ^ 2 * Real.exp (-(V x))) atTop
      (𝓝 (∫ x in J, dg x ^ 2 * Real.exp (-(V x)))) :=
    tendsto_intervalIntegral_of_exhaustion A B J hAB hsub hmono hexh _ hgi
  have hlim_g : Tendsto (fun n => (1 / c) * (∫ x in A n..B n, dg x ^ 2 * Real.exp (-(V x)))
      + (2 * cn n * t n - cn n ^ 2 * s n)) atTop
      (𝓝 ((1 / c) * (∫ x in J, dg x ^ 2 * Real.exp (-(V x))) + 0)) :=
    (hlim_g2.const_mul (1/c)).add hlim_err
  have hle := le_of_tendsto_of_tendsto' hlim_f2 hlim_g hineq
  simpa using hle

end BL1D

/-- **One-dimensional Brascamp-Lieb (variance) inequality.** -/
theorem convex_potential_one_dim_poincare (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hV2 : ConvexOn ℝ Set.univ (fun x => V x - Real.pi * x ^ 2))
    (J : Set ℝ) (hJ : Convex ℝ J) (hJm : MeasurableSet J)
    (hpos : 0 < ∫ x in J, Real.exp (-(V x)))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (h2 : MeasureTheory.IntegrableOn (fun x : ℝ => f x ^ 2 * Real.exp (-(V x))) J)
    (hg : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv f x) ^ 2 * Real.exp (-(V x))) J)
    (hmean : ∫ x in J, f x * Real.exp (-(V x)) = 0) :
    ∫ x in J, f x ^ 2 * Real.exp (-(V x))
      ≤ (1 / (2 * Real.pi)) * ∫ x in J, (deriv f x) ^ 2 * Real.exp (-(V x)) := by
  have hρV : IntegrableOn (fun x => Real.exp (-(V x))) J volume :=
    (BL1D.exp_neg_convex_sub_sq_integrable V hV2).integrableOn
  have hvolJ : volume J ≠ 0 := by
    intro h0
    have h1 := setIntegral_measure_zero (fun x : ℝ => Real.exp (-(V x))) h0
    rw [h1] at hpos
    exact lt_irrefl 0 hpos
  have hvolpos : 0 < volume J := lt_of_le_of_ne zero_le (Ne.symm hvolJ)
  obtain ⟨Vε, Vε', Vε'', hd1, hd2, hVε''cont, h2pi, hVεconv, hge, htend⟩ :=
    Commons.Analysis.Convex.convex_mollification_exists V hV hV2
  set ρn : ℕ → ℝ → ℝ := fun n x => Real.exp (-(Vε n x)) with hρn_def
  have hρn_eq : ∀ n x, ρn n x = Real.exp (-(Vε n x)) := fun n x => congrFun (congrFun hρn_def n) x
  set cn : ℕ → ℝ := fun n => (∫ x in J, f x * ρn n x) / (∫ x in J, ρn n x) with hcn_def
  have hcn_eq : ∀ n, cn n = (∫ x in J, f x * ρn n x) / (∫ x in J, ρn n x) :=
    fun n => congrFun hcn_def n
  have hρnc : ∀ n, Continuous (ρn n) := by
    intro n
    have : Continuous (Vε n) := continuous_iff_continuousAt.mpr (fun x => (hd1 n x).continuousAt)
    exact Real.continuous_exp.comp this.neg
  have hρn_nonneg : ∀ n x, 0 ≤ ρn n x := fun n x => by
    rw [hρn_eq n x]; exact (Real.exp_pos _).le
  have hρn_le : ∀ n x, ρn n x ≤ Real.exp (-(V x)) := fun n x => by
    rw [hρn_eq n x, Real.exp_le_exp]; exact neg_le_neg (hge n x)
  have hρn_int : ∀ n, IntegrableOn (ρn n) J volume := by
    intro n
    refine Integrable.mono' (g := fun x => Real.exp (-(V x))) hρV
      (hρnc n).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hρn_nonneg n x)]
    exact hρn_le n x
  have hρn_pos : ∀ n, 0 < ∫ x in J, ρn n x := by
    intro n
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => hρn_nonneg n x) (hρn_int n)]
    have hsupp : Function.support (ρn n) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      rw [hρn_eq n x]
      exact Real.exp_ne_zero _
    rw [hsupp, Set.univ_inter]
    exact hvolpos
  have h2n : ∀ n, IntegrableOn (fun x => f x ^ 2 * ρn n x) J volume := by
    intro n
    refine Integrable.mono' (g := fun x => f x ^ 2 * Real.exp (-(V x))) h2
      ((hf.continuous.pow 2 |>.mul (hρnc n)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρn_nonneg n x))]
    exact mul_le_mul_of_nonneg_left (hρn_le n x) (sq_nonneg _)
  have hgn : ∀ n, IntegrableOn (fun x => (deriv f x) ^ 2 * ρn n x) J volume := by
    intro n
    refine Integrable.mono' (g := fun x => (deriv f x) ^ 2 * Real.exp (-(V x))) hg
      (((hf.continuous_deriv (le_refl (1 : WithTop ℕ∞))).pow 2 |>.mul
        (hρnc n)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρn_nonneg n x))]
    exact mul_le_mul_of_nonneg_left (hρn_le n x) (sq_nonneg _)
  have hfn : ∀ n, IntegrableOn (fun x => f x * ρn n x) J volume := by
    intro n
    refine Integrable.mono' (g := fun x => (1/2) * (f x ^ 2 * ρn n x + ρn n x))
      ((h2n n).add (hρn_int n) |>.const_mul (1/2))
      ((hf.continuous.mul (hρnc n)).aestronglyMeasurable) ?_
    filter_upwards with x
    have hρ0 : (0:ℝ) ≤ ρn n x := hρn_nonneg n x
    have hkey : 2 * |f x| ≤ f x ^ 2 + 1 := by
      nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), abs_nonneg (f x)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
    calc |f x| * ρn n x ≤ ((f x ^ 2 + 1)/2) * ρn n x :=
          mul_le_mul_of_nonneg_right (by linarith) hρ0
      _ = (1/2) * (f x ^ 2 * ρn n x + ρn n x) := by ring
  have hmzn : ∀ n, ∫ x in J, (f x - cn n) * ρn n x = 0 := by
    intro n
    have hne : (∫ x in J, ρn n x) ≠ 0 := ne_of_gt (hρn_pos n)
    rw [show (fun x => (f x - cn n) * ρn n x)
        = fun x => f x * ρn n x - cn n * ρn n x by funext x; ring]
    rw [integral_sub (hfn n) ((hρn_int n).const_mul (cn n)), MeasureTheory.integral_const_mul, hcn_eq n]
    field_simp
    ring
  have h2n' : ∀ n, IntegrableOn (fun x => (f x - cn n) ^ 2 * ρn n x) J volume := by
    intro n
    refine Integrable.mono' (g := fun x => 2 * (f x ^ 2 * ρn n x) + (2 * cn n ^ 2) * ρn n x)
      (((h2n n).const_mul 2).add ((hρn_int n).const_mul (2 * cn n ^ 2)))
      (((hf.continuous.sub continuous_const).pow 2 |>.mul (hρnc n)).aestronglyMeasurable) ?_
    filter_upwards with x
    have hρ0 : (0:ℝ) ≤ ρn n x := hρn_nonneg n x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hρ0)]
    nlinarith [hρ0, sq_nonneg (f x - cn n), sq_nonneg (f x + cn n)]
  have hgρn : ∀ n, IntegrableOn (fun x => (f x - cn n) * ρn n x) J volume := by
    intro n
    have h := (hfn n).sub ((hρn_int n).const_mul (cn n))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hC2 : ∀ n, ∫ x in J, (f x - cn n) ^ 2 * ρn n x
      ≤ (1 / (2 * Real.pi)) * ∫ x in J, (deriv f x) ^ 2 * ρn n x := by
    intro n
    obtain ⟨x₁, hx₁⟩ := BL1D.exists_deriv_eq_zero_of_le (2 * Real.pi) (Vε' n) (Vε'' n)
      (by positivity) (hd2 n) (h2pi n)
    have h''c : Continuous (Vε'' n) := continuousOn_univ.mp (hVε''cont n)
    have hdfc : Continuous (deriv f) := hf.continuous_deriv (le_refl (1 : WithTop ℕ∞))
    have hdf : ∀ x, HasDerivAt f (deriv f x) x :=
      fun x => (hf.differentiable (by simp)).differentiableAt.hasDerivAt
    exact BL1D.brascamp_lieb_of_C2 (Vε n) (Vε' n) (Vε'' n) (fun x => f x - cn n) (deriv f)
      (2 * Real.pi) (by positivity)
      (hd1 n) (hd2 n) (h2pi n) h''c x₁ hx₁ J hJ hJm (hρn_pos n)
      (hf.continuous.sub continuous_const) hdfc (fun x => (hdf x).sub_const (cn n))
      (h2n' n) (hgn n) (hρn_int n) (hgρn n) (hmzn n)
  have hlim_ρn : Tendsto (fun n => ∫ x in J, ρn n x) atTop (𝓝 (∫ x in J, Real.exp (-(V x)))) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
      (l := atTop) (F := fun n x => ρn n x) (f := fun x => Real.exp (-(V x)))
      (fun x => Real.exp (-(V x)))
      (Filter.Eventually.of_forall fun n => (hρnc n).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hρn_nonneg n x)]
        exact hρn_le n x)
      hρV
      (Filter.Eventually.of_forall fun x => (Real.continuous_exp.tendsto (-(V x))).comp
        ((htend x).neg))
    simpa using h
  have hfabs : Integrable (fun x => |f x| * Real.exp (-(V x))) (volume.restrict J) := by
    have hVcont : Continuous V := continuousOn_univ.mp (hV.continuousOn isOpen_univ)
    refine Integrable.mono' (g := fun x => (1/2) * (f x ^ 2 * Real.exp (-(V x)) + Real.exp (-(V x))))
      ((h2.add hρV).const_mul (1/2))
      ((hf.continuous.abs.mul (Real.continuous_exp.comp hVcont.neg)).aestronglyMeasurable) ?_
    filter_upwards with x
    have hkey : 2 * |f x| ≤ f x ^ 2 + 1 := by
      nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), abs_nonneg (f x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    calc |f x| * Real.exp (-(V x)) ≤ ((f x ^ 2 + 1)/2) * Real.exp (-(V x)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = (1/2) * (f x ^ 2 * Real.exp (-(V x)) + Real.exp (-(V x))) := by ring
  have hlim_fρn : Tendsto (fun n => ∫ x in J, f x * ρn n x) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
      (l := atTop) (F := fun n x => f x * ρn n x) (f := fun x => f x * Real.exp (-(V x)))
      (fun x => |f x| * Real.exp (-(V x)))
      (Filter.Eventually.of_forall fun n => (hf.continuous.mul (hρnc n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρn_nonneg n x)]
        exact mul_le_mul_of_nonneg_left (hρn_le n x) (abs_nonneg _))
      hfabs
      (Filter.Eventually.of_forall fun x => by
        have h1 : Tendsto (fun n => f x * ρn n x) atTop (𝓝 (f x * Real.exp (-(V x)))) :=
          tendsto_const_nhds.mul ((Real.continuous_exp.tendsto (-(V x))).comp ((htend x).neg))
        simpa using h1)
    rw [hmean] at h
    simpa using h
  have hlim_cn : Tendsto cn atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (∫ x in J, f x * ρn n x) / (∫ x in J, ρn n x)) atTop
        (𝓝 (0 / (∫ x in J, Real.exp (-(V x))))) := hlim_fρn.div hlim_ρn (ne_of_gt hpos)
    rw [zero_div] at h1
    rw [hcn_def]
    exact h1
  have hbound_int : Integrable (fun x => 2 * (f x ^ 2 + 1) * Real.exp (-(V x)))
      (volume.restrict J) := by
    have h := (h2.add hρV).const_mul 2
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hlim_L : Tendsto (fun n => ∫ x in J, (f x - cn n) ^ 2 * ρn n x) atTop
      (𝓝 (∫ x in J, f x ^ 2 * Real.exp (-(V x)))) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
      (l := atTop) (F := fun n x => (f x - cn n) ^ 2 * ρn n x)
      (f := fun x => f x ^ 2 * Real.exp (-(V x)))
      (fun x => 2 * (f x ^ 2 + 1) * Real.exp (-(V x)))
      (Filter.Eventually.of_forall fun n => ((hf.continuous.sub continuous_const).pow 2 |>.mul
        (hρnc n)).aestronglyMeasurable)
      (by
        filter_upwards [Metric.tendsto_nhds.mp hlim_cn 1 zero_lt_one] with n hn
        filter_upwards with x
        have hcn1 : |cn n| ≤ 1 := by
          rw [Real.dist_eq, sub_zero] at hn; exact le_of_lt hn
        have hρ0 : (0:ℝ) ≤ ρn n x := hρn_nonneg n x
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hρ0)]
        have hsq : (f x - cn n) ^ 2 ≤ 2 * (f x ^ 2 + 1) := by
          nlinarith [hcn1, abs_nonneg (cn n), sq_abs (cn n), sq_nonneg (f x - cn n),
            sq_nonneg (f x + cn n)]
        calc (f x - cn n) ^ 2 * ρn n x ≤ (2 * (f x ^ 2 + 1)) * Real.exp (-(V x)) :=
              mul_le_mul hsq (hρn_le n x) hρ0 (by positivity)
          _ = 2 * (f x ^ 2 + 1) * Real.exp (-(V x)) := by ring)
      hbound_int
      (Filter.Eventually.of_forall fun x => by
        have h1 : Tendsto (fun n => (f x - cn n) ^ 2 * ρn n x) atTop
            (𝓝 ((f x - 0) ^ 2 * Real.exp (-(V x)))) :=
          (((tendsto_const_nhds.sub hlim_cn).pow 2).mul
            ((Real.continuous_exp.tendsto (-(V x))).comp ((htend x).neg)))
        simpa using h1)
    simpa using h
  have hlim_R : Tendsto (fun n => ∫ x in J, (deriv f x) ^ 2 * ρn n x) atTop
      (𝓝 (∫ x in J, (deriv f x) ^ 2 * Real.exp (-(V x)))) := by
    have hdfc : Continuous (deriv f) := hf.continuous_deriv (le_refl (1 : WithTop ℕ∞))
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
      (l := atTop) (F := fun n x => (deriv f x) ^ 2 * ρn n x)
      (f := fun x => (deriv f x) ^ 2 * Real.exp (-(V x)))
      (fun x => (deriv f x) ^ 2 * Real.exp (-(V x)))
      (Filter.Eventually.of_forall fun n => (hdfc.pow 2 |>.mul (hρnc n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρn_nonneg n x))]
        exact mul_le_mul_of_nonneg_left (hρn_le n x) (sq_nonneg _))
      hg
      (Filter.Eventually.of_forall fun x => by
        have h1 : Tendsto (fun n => (deriv f x) ^ 2 * ρn n x) atTop
            (𝓝 ((deriv f x) ^ 2 * Real.exp (-(V x)))) :=
          tendsto_const_nhds.mul ((Real.continuous_exp.tendsto (-(V x))).comp ((htend x).neg))
        simpa using h1)
    simpa using h
  have hmono : ∀ᶠ n in atTop, (∫ x in J, (f x - cn n) ^ 2 * ρn n x)
      ≤ (1 / (2 * Real.pi)) * (∫ x in J, (deriv f x) ^ 2 * ρn n x) :=
    Filter.Eventually.of_forall hC2
  have hfin := le_of_tendsto_of_tendsto hlim_L (hlim_R.const_mul (1/(2 * Real.pi))) hmono
  simpa using hfin



/-
## Structure of the proof (complete; no placeholders remain)

All helper lemmas live in the namespace `Commons.Analysis.Convex.BL1D`.

**Analysis.**  For a `C²` potential `V` with `V'' ≥ c ≥ 0` and `V' x₁ = 0` the
completion-of-squares identity `0 ≤ ∫ (u' + (c/2)(x-x₁)u)²`, the pointwise bound
`c²(x-x₁)² ≤ V' x²` (from the mean value theorem) and an integration by parts give the
one-dimensional weighted Hardy inequality

* `hardy_range` : `c ∫ R²/ρ ≤ ∫ (R')²/ρ`,  `ρ = exp(-V)`,

for test functions `R` vanishing at the endpoints (`ho_bound`, `slope_bound_le`,
`deriv_sq_ge`, `hardy_C2`, `pointwise1`, `pointwise2` are the ingredients).

Applying this to the primitive `R(t) = ∫_t^B g ρ` of a mean-zero `g`, plus the
integration-by-parts identity `∫ g²ρ = ∫ g' R` and a pointwise AM–GM step, yields

* `transfer_interval` : for `V'' ≥ c > 0` and `∫_A^B g ρ = 0`,
  `∫_A^B g²ρ ≤ (1/c) ∫_A^B (g')²ρ`.

**Localisation.**  `interior_nonempty_of_convex_of_measure_ne_zero` and
`interval_exhaustion_convex` produce an increasing sequence of open subintervals
`Ioo (A n) (B n) ⊆ J` exhausting `J` up to a null set;
`tendsto_intervalIntegral_of_exhaustion` is dominated convergence along this exhaustion.

**Reduction to `C²`.**  `brascamp_lieb_of_C2` combines the previous two items with the mean
correction `c n = t n / s n` (`s n = ∫_{A n}^{B n} ρ`, `t n = ∫_{A n}^{B n} gρ`) and the
observation `∫(g - c n)²ρ = ∫ g²ρ - 2c n t n + c n² s n`.

**General convex `V`.**  `exp_neg_convex_sub_sq_integrable` (coercivity, via the secant
bounds `secant_lower_left`/`secant_lower_right`) gives `∫_J exp(-V) < ∞`.  The commons
lemma `convex_mollification_exists` supplies smooth potentials `Vε n ≥ V` with
`Vε n'' ≥ 2π`, and `convex_potential_one_dim_poincare` applies
`brascamp_lieb_of_C2` to `Vε n` and `f - c n` with
`c n = (∫_J f exp(-Vε n))/(∫_J exp(-Vε n))`, then lets `n → ∞` by dominated convergence
(the dominating functions are the corresponding quantities for `V`, using
`exp(-Vε n) ≤ exp(-V)`).
-/

end

end Commons.Analysis.Convex