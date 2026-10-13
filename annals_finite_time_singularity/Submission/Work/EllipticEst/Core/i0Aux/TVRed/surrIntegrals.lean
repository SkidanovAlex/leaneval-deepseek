/-
Copyright: work module for the Elgindi finite-time singularity project.

# Weighted angular integrals of the trace-matching surrogate

For the two-sided trace-matching surrogate
`surrFun ψ F₀ F₁ L θ = F₀ ψ (θ/L) + F₁ ψ ((π/2 - θ)/L)` of a bump `ψ` (`IsBump ψ C`) and a
scale `L ∈ (0, π/4]`, the four weighted angular integrals

* `∫_{Iθ} (surrFun)² thEta`,
* `∫_{Iθ} (surrFun')² thEta`,
* `∫_{Iθ} (surrFun'')² thEta`,
* `∫_{Iθ} (surrFun')² qTh² thEta`

are all bounded by `1000 (C+1)² (F₀² + F₁²)` times the natural power of `L`
(`L^{1-η}`, `L^{-(1+η)}`, `L^{-(3+η)}`, `L^{-(3+η)}`).

The surrogate is supported in the two *shells* `[0, L/2]` and `[π/2 - L/2, π/2]`; its
first and second derivatives are supported in the narrower shells
`[L/4, L/2] ∪ [π/2 - L/2, π/2 - L/4]`, where both the weight `thEta θ = sin(2θ)^{-η}` and the
logarithmic derivative `qTh θ = 2η cot(2θ)` are bounded in terms of `L`.  The two ingredients
are

* the tail bound `∫_0^{L/2} sin(2θ)^{-η} dθ ≤ 200 L^{1-η}` (Jordan's inequality
  `sin(2θ) ≥ 4θ/π` on `[0, π/4]` and the elementary antiderivative of `x^{-η}`), and
* the shell bounds `thEta θ ≤ π^η L^{-η}`, `qTh θ² ≤ (2πη/L)²` on the shells
  (from `sin(2θ) ≥ L/π` there).

Together with the pointwise bounds `|surr| ≤ |F₀| + |F₁|`,
`|surr'| ≤ C(|F₀| + |F₁|)/L`, `|surr''| ≤ C(|F₀| + |F₁|)/L²` of `TVRed/BumpFacts.lean` these
give the four estimates by an elementary `integral_mono_of_nonneg` against an explicit
indicator majorant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

/-! ## 0. Elementary `rpow` bookkeeping -/

/-- `L^{-k} L^{-η} L = L^{-(k + η - 1)}` for `L > 0`. -/
lemma rpow_mul_L {L : ℝ} (hL : 0 < L) (k : ℝ) :
    L ^ (-k) * L ^ (-(Work.Spaces.eta)) * L = L ^ (-(k + Work.Spaces.eta - 1)) := by
  have h : L ^ (-(k + Work.Spaces.eta - 1))
      = L ^ (-k) * L ^ (-(Work.Spaces.eta)) * L := by
    rw [show -(k + Work.Spaces.eta - 1) = -k + (-(Work.Spaces.eta) + 1) by ring,
      Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
    ring
  exact h.symm

/-- `x / L = x L^{-1}` for `L > 0`. -/
lemma div_eq_mul_rpow_neg_one {L x : ℝ} (_hL : 0 < L) : x / L = x * L ^ (-1 : ℝ) := by
  rw [div_eq_mul_inv, Real.rpow_neg_one]

/-- `(x/L)² = x² L^{-2}` for `L > 0`. -/
lemma sq_div_eq {L x : ℝ} (hL : 0 < L) : (x / L) ^ 2 = x ^ 2 * L ^ (-2 : ℝ) := by
  have h : L ^ (-2 : ℝ) = ((L : ℝ) ^ 2)⁻¹ := by
    have he : (-2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_neg hL.le ((2 : ℕ) : ℝ), Real.rpow_natCast]
  rw [div_pow, div_eq_mul_inv, ← h]

/-- `(x/L²)² = x² L^{-4}` for `L > 0`. -/
lemma sq_div_sq_eq {L x : ℝ} (hL : 0 < L) : (x / L ^ 2) ^ 2 = x ^ 2 * L ^ (-4 : ℝ) := by
  have h : L ^ (-4 : ℝ) = ((L : ℝ) ^ 4)⁻¹ := by
    have he : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_neg hL.le ((4 : ℕ) : ℝ), Real.rpow_natCast]
  rw [div_pow, ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, div_eq_mul_inv, ← h]

/-- `(a/L)² (b/L)² = a² b² L^{-4}` for `L > 0`. -/
lemma sq_mul_sq_div {L a b : ℝ} (hL : 0 < L) :
    (a / L) ^ 2 * (b / L) ^ 2 = a ^ 2 * b ^ 2 * L ^ (-4 : ℝ) := by
  have h : L ^ (-4 : ℝ) = L ^ (-2 : ℝ) * L ^ (-2 : ℝ) := by
    rw [show (-4 : ℝ) = -2 + -2 by norm_num, Real.rpow_add hL]
  rw [sq_div_eq hL, sq_div_eq hL,
    show a ^ 2 * L ^ (-2 : ℝ) * (b ^ 2 * L ^ (-2 : ℝ))
      = a ^ 2 * b ^ 2 * (L ^ (-2 : ℝ) * L ^ (-2 : ℝ)) by ring, ← h]

/-! ## 1. The angular tails of `thEta` -/

/-- `thEta` is invariant under `θ ↦ π/2 - θ`. -/
lemma thEta_reflect (x : ℝ) :
    Work.FTS.EllipticEst.thEta (Real.pi / 2 - x) = Work.FTS.EllipticEst.thEta x := by
  simp only [Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-- Set integrals over `Icc a b` are interval integrals. -/
private lemma setIntegral_Icc_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]

/-- Jordan's inequality for the weight: on `[0, π/4]`,
`sin(2x)^{-η} ≤ (π/4)^η x^{-η}`. -/
lemma sin_two_rpow_eta_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * x ^ (-(Work.Spaces.eta)) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [mul_zero, Real.sin_zero,
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0), mul_zero]
  · have h2x0 : 0 ≤ 2 * x := by linarith
    have h2x1 : 2 * x ≤ Real.pi / 2 := by linarith [hx1, Real.pi_pos]
    have hj := Real.mul_le_sin h2x0 h2x1
    have hjeq : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
    rw [hjeq] at hj
    have hpos : 0 < (4 / Real.pi) * x := by positivity
    have key := Real.rpow_le_rpow_of_nonpos hpos hj
      (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
    have hcoef : (4 / Real.pi : ℝ) ^ (-(Work.Spaces.eta)) = (Real.pi / 4) ^ Work.Spaces.eta := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
        ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) Work.Spaces.eta, inv_div]
    have hmr : ((4 / Real.pi) * x) ^ (-(Work.Spaces.eta))
        = (Real.pi / 4) ^ Work.Spaces.eta * x ^ (-(Work.Spaces.eta)) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (le_of_lt h), hcoef]
    rw [hmr] at key
    exact key

/-- The left tail: `∫_0^{L/2} sin(2θ)^{-η} dθ ≤ 200 L^{1-η}`. -/
lemma thEta_tail_left {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have hhalf : (0 : ℝ) ≤ L / 2 := by linarith
  have hMint : IntegrableOn
      (fun θ : ℝ => (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (L / 2)) := by
    have h1 : IntegrableOn (fun θ : ℝ => θ ^ (-(Work.Spaces.eta))) (Set.Ioo (0 : ℝ) (L / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hhalf).mp
        (intervalIntegral.intervalIntegrable_rpow' (r := -(Work.Spaces.eta)) (a := 0) (b := L / 2)
          (by linarith [Work.Spaces.eta_lt_one]))
    exact h1.const_mul _
  have hcomp : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (L / 2),
          (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)) := by
    refine integral_mono_of_nonneg ?_ hMint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, hLp, Real.pi_pos])) _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact sin_two_rpow_eta_le ⟨le_of_lt hθ.1, by linarith [hθ.2, hLp]⟩
  have hMval : (∫ θ in Set.Ioo (0 : ℝ) (L / 2),
        (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)))
      = (Real.pi / 4) ^ Work.Spaces.eta
          * ((L / 2) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta)) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hhalf]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_rpow (Or.inl (by linarith [Work.Spaces.eta_lt_one]))]
    rw [show (-(Work.Spaces.eta) + 1 : ℝ) = 1 - Work.Spaces.eta by ring]
    rw [Real.zero_rpow (by linarith [Work.Spaces.eta_lt_one] : (1 : ℝ) - Work.Spaces.eta ≠ 0)]
    ring
  have hIcc : (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- arithmetic
  have ha1 : (Real.pi / 4) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (by positivity) (by linarith [Real.pi_lt_four]) (le_of_lt Work.Spaces.eta_pos)
  have hbc : (L / 2) ^ (1 - Work.Spaces.eta) ≤ L ^ (1 - Work.Spaces.eta) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith [Work.Spaces.eta_lt_one])
  have hk0 : (0 : ℝ) < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hc0 : (0 : ℝ) ≤ L ^ (1 - Work.Spaces.eta) := Real.rpow_nonneg hL.le _
  have hb0 : (0 : ℝ) ≤ (L / 2) ^ (1 - Work.Spaces.eta) := Real.rpow_nonneg (by linarith) _
  rw [hIcc]
  refine hcomp.trans ?_
  rw [hMval]
  suffices hkey : (Real.pi / 4) ^ Work.Spaces.eta
        * ((L / 2) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta)
      ≤ (200 * L ^ (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta) by
    exact le_of_mul_le_mul_right hkey hk0
  have hLHS : (Real.pi / 4) ^ Work.Spaces.eta
        * ((L / 2) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta)
      = (Real.pi / 4) ^ Work.Spaces.eta * (L / 2) ^ (1 - Work.Spaces.eta) := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hk0)]
  have hRHS : (200 * L ^ (1 - Work.Spaces.eta)) * (1 - Work.Spaces.eta)
      = 2 * L ^ (1 - Work.Spaces.eta) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = 1 / 100 by rw [Work.Spaces.eta]; norm_num]
    ring
  rw [hLHS, hRHS]
  calc (Real.pi / 4) ^ Work.Spaces.eta * (L / 2) ^ (1 - Work.Spaces.eta)
      ≤ 1 * L ^ (1 - Work.Spaces.eta) := mul_le_mul ha1 hbc hb0 (by norm_num)
    _ = L ^ (1 - Work.Spaces.eta) := one_mul _
    _ ≤ 2 * L ^ (1 - Work.Spaces.eta) := by nlinarith [hc0]

/-- The right tail: `∫_{π/2-L/2}^{π/2} sin(2θ)^{-η} dθ ≤ 200 L^{1-η}`. -/
lemma thEta_tail_right {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta) := by
  have hb : Real.pi / 2 - L / 2 ≤ Real.pi / 2 := by linarith [hLp, Real.pi_pos]
  have heq : (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2),
        Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ := by
    rw [setIntegral_Icc_eq_intervalIntegral hb, setIntegral_Icc_eq_intervalIntegral (by linarith)]
    have h1 : (∫ θ in (Real.pi / 2 - L / 2)..(Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in (Real.pi / 2 - L / 2)..(Real.pi / 2),
            Work.FTS.EllipticEst.thEta (Real.pi / 2 - θ) := by
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      exact (thEta_reflect θ).symm
    rw [h1, intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => Work.FTS.EllipticEst.thEta x) (Real.pi / 2),
      show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring,
      show Real.pi / 2 - (Real.pi / 2 - L / 2) = L / 2 by ring]
  rw [heq]
  exact thEta_tail_left hL hLp

/-! ## 2. The two shells -/

/-- The union of the two shells carrying the derivatives of the surrogate:
`[L/4, L/2] ∪ [π/2 - L/2, π/2 - L/4]`. -/
def shells (L : ℝ) : Set ℝ :=
  Set.Icc (L / 4) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2 - L / 4)

lemma shells_measurable (L : ℝ) : MeasurableSet (shells L) := by
  rw [shells]
  measurability

lemma shells_subset {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    shells L ⊆ Set.Icc (L / 4) (Real.pi / 2 - L / 4) := by
  intro x hx
  rw [shells] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, by linarith [h2, hLp, Real.pi_pos]⟩
  · exact ⟨by linarith [h1, hLp, Real.pi_pos], h2⟩

lemma shells_subset_Iθ {L : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    shells L ⊆ Work.Spaces.Iθ := by
  intro x hx
  have h := shells_subset hL hLp hx
  rw [Work.Spaces.Iθ]
  exact ⟨by linarith [h.1, hL], by linarith [h.2, Real.pi_pos]⟩

/-- On the shells the weight `sin(2θ)` is bounded below by `L/π`. -/
lemma sin_shell_le {L θ : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) (hθ : θ ∈ shells L) :
    L / Real.pi ≤ Real.sin (2 * θ) := by
  rw [shells] at hθ
  have hcoef : (0 : ℝ) < 2 / Real.pi := by positivity
  rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2θ0 : 0 ≤ 2 * θ := by linarith [h1, hL]
    have h2θ1 : 2 * θ ≤ Real.pi / 2 := by linarith [h2, hLp, Real.pi_pos]
    have hj := Real.mul_le_sin h2θ0 h2θ1
    calc L / Real.pi = 2 / Real.pi * (L / 2) := by ring
      _ ≤ 2 / Real.pi * (2 * θ) := mul_le_mul_of_nonneg_left (by linarith [h1]) hcoef.le
      _ ≤ Real.sin (2 * θ) := hj
  · have hy0 : 0 ≤ Real.pi - 2 * θ := by linarith [h2, Real.pi_pos]
    have hy1 : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith [h1]
    have hj := Real.mul_le_sin hy0 hy1
    have hsin : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) :=
      (Real.sin_pi_sub (2 * θ)).symm
    rw [hsin]
    calc L / Real.pi = 2 / Real.pi * (L / 2) := by ring
      _ ≤ 2 / Real.pi * (Real.pi - 2 * θ) :=
          mul_le_mul_of_nonneg_left (by linarith [h1, h2]) hcoef.le
      _ ≤ Real.sin (Real.pi - 2 * θ) := hj

/-- On the shells the weight is bounded by `π^η L^{-η}`. -/
lemma shell_thEta_le {L θ : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) (hθ : θ ∈ shells L) :
    Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)) := by
  have hsin := sin_shell_le hL hLp hθ
  have hkey := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < L / Real.pi) hsin
    (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
  have hcoef : (L / Real.pi) ^ (-(Work.Spaces.eta))
      = Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ L / Real.pi),
      Real.div_rpow hL.le (le_of_lt Real.pi_pos), div_eq_mul_inv, mul_inv, inv_inv,
      ← Real.rpow_neg hL.le]
    ring
  rw [hcoef] at hkey
  exact hkey

/-- On the shells the logarithmic derivative factor is bounded by `2πη/L`. -/
lemma shell_qTh_le {L θ : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4) (hθ : θ ∈ shells L) :
    (qTh θ) ^ 2 ≤ (2 * Real.pi * Work.Spaces.eta / L) ^ 2 := by
  have hsin := sin_shell_le hL hLp hθ
  have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le (by positivity) hsin
  have hcos : |Real.cos (2 * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hcot : |Real.cot (2 * θ)| ≤ Real.pi / L := by
    rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos]
    have h1 : |Real.cos (2 * θ)| / Real.sin (2 * θ) ≤ 1 / Real.sin (2 * θ) := by
      have h : (0 : ℝ) ≤ 1 / Real.sin (2 * θ) - |Real.cos (2 * θ)| / Real.sin (2 * θ) := by
        rw [← sub_div]
        exact div_nonneg (by linarith) hsinpos.le
      linarith
    have h2 : 1 / Real.sin (2 * θ) ≤ Real.pi / L := by
      rw [div_le_iff₀ hsinpos, div_mul_eq_mul_div, le_div_iff₀ hL]
      have h3 := (div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi)).mp hsin
      linarith [h3]
    linarith
  have hsq : (Real.cot (2 * θ)) ^ 2 ≤ (Real.pi / L) ^ 2 := by
    have hpiL : (0 : ℝ) < Real.pi / L := by positivity
    calc (Real.cot (2 * θ)) ^ 2 = |Real.cot (2 * θ)| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.pi / L) ^ 2 := by
          rw [← sq_abs (Real.pi / L), abs_of_pos hpiL]
          exact pow_le_pow_left₀ (abs_nonneg _) hcot 2
  calc (qTh θ) ^ 2 = (2 * Work.Spaces.eta) ^ 2 * (Real.cot (2 * θ)) ^ 2 := by
        rw [qTh]; ring
    _ ≤ (2 * Work.Spaces.eta) ^ 2 * (Real.pi / L) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (2 * Real.pi * Work.Spaces.eta / L) ^ 2 := by ring

/-! ## 3. The support of the surrogate and of its derivatives -/

lemma surr_eq_zero_of_mid (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (h1 : L / 2 ≤ θ) (h2 : θ ≤ Real.pi / 2 - L / 2) :
    surrFun ψ F₀ F₁ L θ = 0 := by
  have h1' : ψ (θ / L) = 0 := hψ.eq_zero _ (by rw [le_div_iff₀ hL]; linarith)
  have h2' : ψ ((Real.pi / 2 - θ) / L) = 0 := hψ.eq_zero _ (by rw [le_div_iff₀ hL]; linarith)
  rw [surrFun, h1', h2']
  ring

/-- The surrogate vanishes in the middle of the interval. -/
lemma surr_eq_zero_of_mem_Iθ_of_notMem (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) :
    surrFun ψ F₀ F₁ L θ = 0 := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  simp only [Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at h
  obtain ⟨hA, hB⟩ := h
  have h1 : L / 2 < θ := by
    rcases hA with h' | h'
    · linarith [hθ.1, h']
    · exact h'
  have h2 : θ < Real.pi / 2 - L / 2 := by
    rcases hB with h' | h'
    · exact h'
    · linarith [hθ.2, h']
  exact surr_eq_zero_of_mid hψ hL h1.le h2.le

/-- The first derivative of the surrogate vanishes off the two shells. -/
lemma deriv_surr_eq_zero_of_notMem (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (h : θ ∉ shells L) : deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  simp only [shells, Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at h
  obtain ⟨hA, hB⟩ := h
  have h1 : deriv ψ (θ / L) = 0 := by
    rcases hA with h1 | h1
    · exact hψ.deriv_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
    · exact hψ.deriv_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    rcases hB with h2 | h2
    · exact hψ.deriv_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
    · exact hψ.deriv_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
  rw [h1, h2]
  ring

/-- The second derivative of the surrogate vanishes off the two shells. -/
lemma deriv2_surr_eq_zero_of_notMem (hψ : IsBump ψ C) (hL : 0 < L) {θ : ℝ}
    (h : θ ∉ shells L) : deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  simp only [shells, Set.mem_union, Set.mem_Icc, not_or, not_and_or, not_le] at h
  obtain ⟨hA, hB⟩ := h
  have h1 : deriv (deriv ψ) (θ / L) = 0 := by
    rcases hA with h1 | h1
    · exact hψ.deriv2_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
    · exact hψ.deriv2_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
  have h2 : deriv (deriv ψ) ((Real.pi / 2 - θ) / L) = 0 := by
    rcases hB with h2 | h2
    · exact hψ.deriv2_eq_zero_right _ (by rw [lt_div_iff₀ hL]; linarith)
    · exact hψ.deriv2_eq_zero_left _ (by rw [div_lt_iff₀ hL]; linarith)
  rw [h1, h2]
  ring

/-! ## 4. The general shell integral estimate -/

/-- If `g ≥ 0` vanishes off the shells and is bounded by `M` there, then
`∫ g thEta ≤ M (π^η L^{-η}) (L/2)`: the weight is bounded by `π^η L^{-η}` on the shells,
which have total length `L/2`. -/
lemma shell_integral_le {g : ℝ → ℝ} {M : ℝ} (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hM : 0 ≤ M) (hg0 : ∀ θ, 0 ≤ g θ)
    (hbound : ∀ θ ∈ shells L, g θ ≤ M)
    (hzero : ∀ θ, θ ∉ shells L → g θ = 0)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :
    (∫ θ in Work.Spaces.Iθ, g θ * Work.FTS.EllipticEst.thEta θ)
      ≤ M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2) := by
  have hsubS : shells L ⊆ Work.Spaces.Iθ := shells_subset_Iθ hL hLp
  have hT0 : (0 : ℝ) ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt Real.pi_pos) _) (Real.rpow_nonneg hL.le _)
  have hth0 : ∀ θ ∈ shells L, 0 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have hmem := shells_subset_Iθ hL hLp hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hmem
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmem.1])
      (by linarith [hmem.2, Real.pi_pos])) _
  have hpoint : ∀ θ, g θ * Work.FTS.EllipticEst.thEta θ
      ≤ (shells L).indicator
          (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) θ := by
    intro θ
    by_cases hθ : θ ∈ shells L
    · rw [Set.indicator_of_mem hθ]
      calc g θ * Work.FTS.EllipticEst.thEta θ
          ≤ M * Work.FTS.EllipticEst.thEta θ :=
            mul_le_mul_of_nonneg_right (hbound θ hθ) (hth0 θ hθ)
        _ ≤ M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left (hshell θ hθ) hM
    · rw [Set.indicator_of_notMem hθ, hzero θ hθ]
      simp
  have hdisj : Disjoint (Set.Icc (L / 4) (L / 2))
      (Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2 - L / 4)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1, hLp, Real.pi_pos]
  have hvol : volume (shells L) = ENNReal.ofReal (L / 2) := by
    rw [shells, measure_union hdisj (by measurability), Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hval : (∫ θ in Work.Spaces.Iθ, (shells L).indicator
        (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) θ)
      = (M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) * (L / 2) := by
    rw [setIntegral_indicator (shells_measurable L), Set.inter_eq_right.mpr hsubS]
    rw [setIntegral_const, Measure.real_def, hvol, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
    ring
  have hint : Integrable ((shells L).indicator
      (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))))
      (volume.restrict (Work.Spaces.Iθ)) := by
    have : IntegrableOn (fun _ : ℝ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))))
        (Work.Spaces.Iθ) :=
      integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
    exact this.indicator (shells_measurable L)
  have hnn : 0 ≤ᵐ[volume.restrict (Work.Spaces.Iθ)]
      (fun θ => g θ * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    refine mul_nonneg (hg0 θ) ?_
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  calc (∫ θ in Work.Spaces.Iθ, g θ * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (shells L).indicator
          (fun _ => M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) θ :=
        integral_mono_of_nonneg hnn hint (Eventually.of_forall hpoint)
    _ = (M * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))) * (L / 2) := hval

/-! ## 5. The arithmetic of the constants -/

lemma arith_two {C F₀ F₁ : ℝ} (hC : 0 < C) :
    C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
  have hF : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h1 : (|F₀| + |F₁|) ^ 2 = F₀ ^ 2 + F₁ ^ 2 + 2 * (|F₀| * |F₁|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    have h2 : 2 * (|F₀| * |F₁|) ≤ F₀ ^ 2 + F₁ ^ 2 := by
      nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
    linarith
  have hpi : Real.pi ^ Work.Spaces.eta ≤ 4 := by
    have h1 : Real.pi ^ Work.Spaces.eta ≤ Real.pi ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
        (le_of_lt Work.Spaces.eta_lt_one)
    rw [Real.rpow_one] at h1
    linarith [Real.pi_lt_four]
  have hCsq : C ^ 2 ≤ (C + 1) ^ 2 := by nlinarith [hC]
  have hpF : (0 : ℝ) ≤ F₀ ^ 2 + F₁ ^ 2 := by positivity
  have h1 : C ^ 2 * (|F₀| + |F₁|) ^ 2 ≤ C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) :=
    mul_le_mul_of_nonneg_left hF (sq_nonneg C)
  have h2 : C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta
      ≤ C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) * 4 :=
    mul_le_mul h1 hpi (Real.rpow_nonneg (le_of_lt Real.pi_pos) _) (by positivity)
  have h3 : C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2
      ≤ 4 * C ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h4 : C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2
        ≤ C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) * 4 / 2 := by linarith
    have h5 : C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) * 4 / 2 = 4 * C ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
      ring
    linarith [h4, h5.le, h5.ge]
  have h6 : 4 * C ^ 2 * (F₀ ^ 2 + F₁ ^ 2) ≤ 4 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    nlinarith [hCsq, hpF]
  have h7 : 4 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    nlinarith [hpF, sq_nonneg (C + 1)]
  linarith [h3, h6, h7]

lemma arith_four {C F₀ F₁ : ℝ} (hC : 0 < C) :
    4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
        * Real.pi ^ Work.Spaces.eta / 2
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
  have hF : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h1 : (|F₀| + |F₁|) ^ 2 = F₀ ^ 2 + F₁ ^ 2 + 2 * (|F₀| * |F₁|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    have h2 : 2 * (|F₀| * |F₁|) ≤ F₀ ^ 2 + F₁ ^ 2 := by
      nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
    linarith
  have heta1 : Work.Spaces.eta ^ 2 ≤ 1 := by
    have h := Work.Spaces.eta_lt_one
    have h0 := Work.Spaces.eta_pos
    nlinarith
  have hpi3 : Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta ≤ 64 := by
    have h1 : Real.pi ^ Work.Spaces.eta ≤ Real.pi ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
        (le_of_lt Work.Spaces.eta_lt_one)
    rw [Real.rpow_one] at h1
    have h2 : Real.pi ^ 2 * Real.pi ≤ 64 := by
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    nlinarith [h1, h2, Real.rpow_nonneg (le_of_lt Real.pi_pos) (Work.Spaces.eta)]
  have hCsq : C ^ 2 ≤ (C + 1) ^ 2 := by nlinarith [hC]
  have hpF : (0 : ℝ) ≤ F₀ ^ 2 + F₁ ^ 2 := by positivity
  have h0 : (0 : ℝ) ≤ Real.pi ^ Work.Spaces.eta := Real.rpow_nonneg (le_of_lt Real.pi_pos) _
  have h1 : 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
        * Real.pi ^ Work.Spaces.eta / 2
      = 2 * (Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta) * Work.Spaces.eta ^ 2 * C ^ 2
          * (|F₀| + |F₁|) ^ 2 := by ring
  rw [h1]
  have h2 : 2 * (Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta) * Work.Spaces.eta ^ 2 * C ^ 2
      * (|F₀| + |F₁|) ^ 2 ≤ 2 * 64 * 1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) := by
    have h3 : Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
        ≤ 1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) := by
      have ha : Work.Spaces.eta ^ 2 * (|F₀| + |F₁|) ^ 2 ≤ 1 * (2 * (F₀ ^ 2 + F₁ ^ 2)) :=
        mul_le_mul heta1 hF (by positivity) (by norm_num)
      nlinarith [ha, sq_nonneg C]
    have h4 : Real.pi ^ 2 * Real.pi ^ Work.Spaces.eta
        * (Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2)
        ≤ 64 * (1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2))) :=
      mul_le_mul hpi3 h3 (by positivity) (by norm_num)
    nlinarith [h4]
  have h5 : 2 * 64 * 1 * C ^ 2 * (2 * (F₀ ^ 2 + F₁ ^ 2)) ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    nlinarith [hCsq, hpF]
  linarith [h2, h5]

/-! ## 6. The four estimates -/

private lemma main_first (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hT1 : (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta))
    (hT2 : (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 200 * L ^ (1 - Work.Spaces.eta)) :
    (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) := by
  have hsub : Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)
      ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, by linarith [h2, hLp, Real.pi_pos]⟩
    · exact ⟨by linarith [h1, hLp, Real.pi_pos], h2⟩
  have hpoint : ∀ᵐ θ ∂(volume.restrict (Work.Spaces.Iθ)),
      (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
            (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ) θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hθ' : θ ∈ Work.Spaces.Iθ := hθ
    by_cases hmem : θ ∈ Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)
    · rw [Set.indicator_of_mem hmem]
      have hb : |surrFun ψ F₀ F₁ L θ| ≤ |F₀| + |F₁| := surr_bound hψ θ
      have h1 : (surrFun ψ F₀ F₁ L θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
        rw [← sq_abs (surrFun ψ F₀ F₁ L θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h2 : 0 ≤ Work.FTS.EllipticEst.thEta θ := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ'
        rw [Work.FTS.EllipticEst.thEta]
        exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
          (by linarith [hθ'.2, Real.pi_pos])) _
      exact mul_le_mul_of_nonneg_right h1 h2
    · rw [Set.indicator_of_notMem hmem]
      have hz : surrFun ψ F₀ F₁ L θ = 0 :=
        surr_eq_zero_of_mem_Iθ_of_notMem hψ hL hθ' hmem
      rw [hz]
      simp
  have hInt1 : IntegrableOn Work.FTS.EllipticEst.thEta (Set.Icc (0 : ℝ) (L / 2)) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.mono_set (by
      intro x hx
      rw [Work.Spaces.Iθ]
      exact ⟨hx.1, by linarith [hx.2, hLp, Real.pi_pos]⟩)
  have hInt2 : IntegrableOn Work.FTS.EllipticEst.thEta
      (Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.mono_set (by
      intro x hx
      rw [Work.Spaces.Iθ]
      exact ⟨by linarith [hx.1, hLp, Real.pi_pos], hx.2⟩)
  have hunionInt : IntegrableOn Work.FTS.EllipticEst.thEta
      (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.mono_set hsub
  have hdisj : Disjoint (Set.Icc (0 : ℝ) (L / 2))
      (Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1, hLp, Real.pi_pos]
  have hmajInt : Integrable
      ((Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
        (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (volume.restrict (Work.Spaces.Iθ)) := by
    have hf : IntegrableOn (fun θ : ℝ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _
    exact hf.indicator (by measurability)
  have hval : (∫ θ in Work.Spaces.Iθ,
        (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
          (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ) θ)
      = (|F₀| + |F₁|) ^ 2 * ((∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
          + ∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ) := by
    rw [setIntegral_indicator (by measurability), Set.inter_eq_right.mpr hsub]
    rw [MeasureTheory.integral_const_mul,
      setIntegral_union hdisj (by measurability) hInt1 hInt2]
  have htail : (∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
      + (∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2), Work.FTS.EllipticEst.thEta θ)
      ≤ 400 * L ^ (1 - Work.Spaces.eta) := by linarith [hT1, hT2]
  have hnn : 0 ≤ᵐ[volume.restrict (Work.Spaces.Iθ)]
      (fun θ => (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hmem : θ ∈ Work.Spaces.Iθ := hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hmem
    refine mul_nonneg (sq_nonneg _) ?_
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmem.1])
      (by linarith [hmem.2, Real.pi_pos])) _
  have hmain := integral_mono_of_nonneg hnn hmajInt hpoint
  have hF : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
    have h1 : (|F₀| + |F₁|) ^ 2 = F₀ ^ 2 + F₁ ^ 2 + 2 * (|F₀| * |F₁|) := by
      rw [add_sq, sq_abs, sq_abs]
      ring
    have h2 : 2 * (|F₀| * |F₁|) ≤ F₀ ^ 2 + F₁ ^ 2 := by
      nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
    linarith
  have hC1 : (1 : ℝ) ≤ (C + 1) ^ 2 := by nlinarith [hψ.C_pos]
  have hL0 : (0 : ℝ) ≤ L ^ (1 - Work.Spaces.eta) := Real.rpow_nonneg hL.le _
  have habs : (0 : ℝ) ≤ (|F₀| + |F₁|) ^ 2 := by positivity
  calc (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (Set.Icc (0 : ℝ) (L / 2) ∪ Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2)).indicator
            (fun θ => (|F₀| + |F₁|) ^ 2 * Work.FTS.EllipticEst.thEta θ) θ := hmain
    _ = (|F₀| + |F₁|) ^ 2
          * ((∫ θ in Set.Icc (0 : ℝ) (L / 2), Work.FTS.EllipticEst.thEta θ)
            + ∫ θ in Set.Icc (Real.pi / 2 - L / 2) (Real.pi / 2),
                Work.FTS.EllipticEst.thEta θ) := hval
    _ ≤ (|F₀| + |F₁|) ^ 2 * (400 * L ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left htail habs
    _ ≤ (2 * (F₀ ^ 2 + F₁ ^ 2)) * (400 * L ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 800 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) := by ring
    _ ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) := by
        refine mul_le_mul_of_nonneg_right ?_ hL0
        nlinarith [hC1, sq_nonneg F₀, sq_nonneg F₁,
          mul_le_mul_of_nonneg_right hC1 (by positivity : (0 : ℝ) ≤ F₀ ^ 2 + F₁ ^ 2)]

private lemma main_second (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta)) := by
  have hB : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 := by positivity
  have hM0 : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) :=
    mul_nonneg hB (Real.rpow_nonneg hL.le _)
  have hbound : ∀ θ ∈ shells L,
      (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) := by
    intro θ hθ
    have hb : |deriv (surrFun ψ F₀ F₁ L) θ| ≤ C * (|F₀| + |F₁|) / L :=
      deriv_surr_bound hψ hL θ
    have h3 : (C * (|F₀| + |F₁|) / L) ^ 2 = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) := by
      rw [sq_div_eq hL]
      ring
    calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2
        = |deriv (surrFun ψ F₀ F₁ L) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ) := h3
  have hmain := shell_integral_le (g := fun θ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2)
    (M := C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ)) hL hLp hM0
    (fun θ => sq_nonneg _) hbound
    (fun θ hθ => by rw [deriv_surr_eq_zero_of_notMem hψ hL hθ]; ring) hshell
  refine hmain.trans ?_
  rw [show (C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-2 : ℝ))
        * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2)
      = (C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2)
          * (L ^ (-2 : ℝ) * L ^ (-(Work.Spaces.eta)) * L) by ring,
    rpow_mul_L (L := L) hL 2,
    show -(2 + Work.Spaces.eta - 1 : ℝ) = -(1 + Work.Spaces.eta) by ring]
  exact mul_le_mul_of_nonneg_right (arith_two hψ.C_pos)
    (Real.rpow_nonneg hL.le _)

private lemma main_third (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta)) := by
  have hB : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 := by positivity
  have hM0 : (0 : ℝ) ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) :=
    mul_nonneg hB (Real.rpow_nonneg hL.le _)
  have hbound : ∀ θ ∈ shells L,
      (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 ≤ C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
    intro θ hθ
    have hb : |deriv (deriv (surrFun ψ F₀ F₁ L)) θ| ≤ C * (|F₀| + |F₁|) / L ^ 2 :=
      deriv2_surr_bound hψ hL θ
    have h3 : (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
      rw [sq_div_sq_eq hL]
      ring
    calc (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        = |deriv (deriv (surrFun ψ F₀ F₁ L)) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (|F₀| + |F₁|) / L ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := h3
  have hmain := shell_integral_le
    (g := fun θ => (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2)
    (M := C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ)) hL hLp hM0
    (fun θ => sq_nonneg _) hbound
    (fun θ hθ => by rw [deriv2_surr_eq_zero_of_notMem hψ hL hθ]; ring) hshell
  refine hmain.trans ?_
  rw [show (C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ))
        * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2)
      = (C ^ 2 * (|F₀| + |F₁|) ^ 2 * Real.pi ^ Work.Spaces.eta / 2)
          * (L ^ (-4 : ℝ) * L ^ (-(Work.Spaces.eta)) * L) by ring,
    rpow_mul_L (L := L) hL 4,
    show -(4 + Work.Spaces.eta - 1 : ℝ) = -(3 + Work.Spaces.eta) by ring]
  exact mul_le_mul_of_nonneg_right (arith_two hψ.C_pos)
    (Real.rpow_nonneg hL.le _)

private lemma main_fourth (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hshell : ∀ θ ∈ shells L, Work.FTS.EllipticEst.thEta θ
      ≤ Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta)))
    (hqth : ∀ θ ∈ shells L, (qTh θ) ^ 2 ≤ (2 * Real.pi * Work.Spaces.eta / L) ^ 2) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta)) := by
  have hB : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 := by
    positivity
  have hM0 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
      * L ^ (-4 : ℝ) := mul_nonneg hB (Real.rpow_nonneg hL.le _)
  have hbound : ∀ θ ∈ shells L,
      (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2
        ≤ 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
    intro θ hθ
    have hb : |deriv (surrFun ψ F₀ F₁ L) θ| ≤ C * (|F₀| + |F₁|) / L :=
      deriv_surr_bound hψ hL θ
    have hb2 : (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := by
      calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2
          = |deriv (surrFun ψ F₀ F₁ L) θ| ^ 2 := (sq_abs _).symm
        _ ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hq := hqth θ hθ
    have hq0 : (0 : ℝ) ≤ (2 * Real.pi * Work.Spaces.eta / L) ^ 2 := by positivity
    calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2
        ≤ (C * (|F₀| + |F₁|) / L) ^ 2 * (2 * Real.pi * Work.Spaces.eta / L) ^ 2 :=
          mul_le_mul hb2 hq (sq_nonneg _) (by positivity)
      _ = 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ) := by
          rw [sq_mul_sq_div hL]
          ring
  have hmain := shell_integral_le
    (g := fun θ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2)
    (M := 4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ))
    hL hLp hM0 (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbound
    (fun θ hθ => by rw [deriv_surr_eq_zero_of_notMem hψ hL hθ]; ring) hshell
  refine hmain.trans ?_
  rw [show (4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2 * L ^ (-4 : ℝ))
        * (Real.pi ^ Work.Spaces.eta * L ^ (-(Work.Spaces.eta))) * (L / 2)
      = (4 * Real.pi ^ 2 * Work.Spaces.eta ^ 2 * C ^ 2 * (|F₀| + |F₁|) ^ 2
          * Real.pi ^ Work.Spaces.eta / 2)
          * (L ^ (-4 : ℝ) * L ^ (-(Work.Spaces.eta)) * L) by ring,
    rpow_mul_L (L := L) hL 4,
    show -(4 + Work.Spaces.eta - 1 : ℝ) = -(3 + Work.Spaces.eta) by ring]
  exact mul_le_mul_of_nonneg_right (arith_four hψ.C_pos) (Real.rpow_nonneg hL.le _)

end

theorem surrIntegrals {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (∫ θ in Work.Spaces.Iθ,
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) ∧
    (∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta))) ∧
    (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))) ∧
    (∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 *
          (Work.EllipticEst.Core.i0Aux.qTh θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ 1000 * (C + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))) :=
  ⟨main_first hψ hL hLp (thEta_tail_left hL hLp) (thEta_tail_right hL hLp),
   main_second hψ hL hLp (fun θ hθ => shell_thEta_le hL hLp hθ),
   main_third hψ hL hLp (fun θ hθ => shell_thEta_le hL hLp hθ),
   main_fourth hψ hL hLp (fun θ hθ => shell_thEta_le hL hLp hθ)
     (fun θ hθ => shell_qTh_le hL hLp hθ)⟩

end Work.EllipticEst.Core.i0Aux.TVRed
