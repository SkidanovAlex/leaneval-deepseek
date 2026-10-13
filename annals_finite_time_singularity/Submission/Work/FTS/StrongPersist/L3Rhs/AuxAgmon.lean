/-
# `AuxAgmon`: the one-dimensional Agmon inequality on the half-line

For a function `v` of class `C^1` on `(0,∞)` whose square, whose squared derivative, and whose
fourth power are integrable there,

  `∫_0^∞ v^4 ≤ 2 · (∫_0^∞ v²)^{3/2} · (∫_0^∞ (v')²)^{1/2}`,

i.e. the one-dimensional Gagliardo–Nirenberg (Agmon) interpolation inequality
`‖v‖_{L⁴} ≤ √2 · ‖v‖_{L²}^{3/4} ‖v'‖_{L²}^{1/4}` in its integrated form.  The constant `2` is
sharp for this formulation (`‖v²‖_∞ ≤ 2‖v v'‖_1 ≤ 2‖v‖_2 ‖v'‖_2`).

The proof of the pointwise sup bound (`agmon_pointwise_Ioi`, the only non-trivial ingredient) is
the classical Agmon argument run on `(0,∞)`: for `0 < x ≤ y`, the fundamental theorem of calculus
applied to `v²` gives `(v y)² - (v x)² = ∫_x^y 2 v v'`, and Cauchy–Schwarz bounds the right-hand
side by `2 A` where `A := ∫_0^∞ |v v'|`, so that `(v x)² > 2 A` would force `v y² > (v x)² - 2A > 0`
for *every* `y > x`, contradicting the integrability of `v²` on the tail.  Integrating
`(v x)^4 = (v x)² (v x)² ≤ 2A (v x)²` and using `A ≤ √(∫v²) √(∫(v')²)` (Cauchy–Schwarz for `L²`,
`agmon_cs_Ioi`) gives the claim.

The integrability of `|v v'|` on `(0,∞)`, needed to make sense of `A`, is the elementary AM–GM
estimate `|ab| ≤ (a² + b²)/2` applied to `v` and `v'`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Elementary prerequisites -/

/-- The AM–GM (arithmetic–geometric mean) estimate `|ab| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_mul, ← sq_abs a, ← sq_abs b]
    nlinarith [sq_nonneg (|a| - |b|)]
  linarith

/-- The `rpow` identity `x^(1/2) * x = x^(3/2)` for `x ≥ 0` (at `x = 0` both sides vanish). -/
private lemma rpow_half_mul_self (x : ℝ) (hx : 0 ≤ x) : x ^ (1 / 2 : ℝ) * x = x ^ (3 / 2 : ℝ) := by
  rcases hx.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    simp
  · have h1 : x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) = x ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add h, show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num]
    simpa using h1

/-- The purely algebraic step `2 (√P √Q) P = 2 P^{3/2} Q^{1/2}` for `P ≥ 0`. -/
private lemma two_sqrt_mul_eq (P Q : ℝ) (hP : 0 ≤ P) :
    2 * (Real.sqrt P * Real.sqrt Q) * P = 2 * P ^ (3 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have h : P ^ (1 / 2 : ℝ) * P = P ^ (3 / 2 : ℝ) := rpow_half_mul_self P hP
  calc 2 * (P ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) * P
      = 2 * Q ^ (1 / 2 : ℝ) * (P ^ (1 / 2 : ℝ) * P) := by ring
    _ = 2 * Q ^ (1 / 2 : ℝ) * P ^ (3 / 2 : ℝ) := by rw [h]
    _ = 2 * P ^ (3 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) := by ring

/-! ## Cauchy–Schwarz on the half-line -/

/-- Cauchy–Schwarz for the product `v v'` on `(0,∞)`:
`∫_0^∞ |v v'| ≤ √(∫_0^∞ v²) √(∫_0^∞ (v')²)`. -/
private lemma agmon_cs_Ioi (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ 1 v (Set.Ioi 0))
    (h2 : IntegrableOn (fun x : ℝ => (v x) ^ 2) (Set.Ioi 0))
    (hd2 : IntegrableOn (fun x : ℝ => (deriv v x) ^ 2) (Set.Ioi 0)) :
    (∫ x in Set.Ioi (0 : ℝ), |v x * deriv v x|)
      ≤ Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
        * Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2) := by
  have hmeasv : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hv.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hmeasd : AEStronglyMeasurable (deriv v) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hv.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).aestronglyMeasurable measurableSet_Ioi
  have hmv : MemLp v 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq hmeasv).mpr h2
  have hmd : MemLp (deriv v) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq hmeasd).mpr hd2
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (p := (2 : ℝ)) (q := (2 : ℝ)) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (f := v) (g := deriv v) (by simpa using hmv) (by simpa using hmd)
  have h1 : ∫ x in Set.Ioi (0 : ℝ), |v x * deriv v x|
      = ∫ a, ‖v a‖ * ‖deriv v a‖ ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
  have h2' : (∫ a, ‖v a‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      = ∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have h3' : (∫ a, ‖deriv v a‖ ^ (2 : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      = ∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [← h1, h2', h3'] at hcs
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  exact hcs

/-! ## The pointwise Agmon bound -/

/-- **Pointwise Agmon bound on the half-line.**  For `v` of class `C^1` on `(0,∞)` with `v²` and
`(v')²` integrable,

  `(v x)² ≤ 2 ∫_0^∞ |v v'|`   for every `x > 0`.

Otherwise `(v x)² - 2A > 0` with `A := ∫_0^∞ |v v'|`, and the fundamental theorem of calculus
together with the triangle inequality would give `(v y)² ≥ (v x)² - 2A > 0` for all `y > x`,
so `∫_x^{x+M} v² ≥ ((v x)² - 2A) M` for every `M > 0`, contradicting `∫_0^∞ v² < ∞`. -/
private lemma agmon_pointwise_Ioi (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ 1 v (Set.Ioi 0))
    (h2 : IntegrableOn (fun x : ℝ => (v x) ^ 2) (Set.Ioi 0))
    (hd2 : IntegrableOn (fun x : ℝ => (deriv v x) ^ 2) (Set.Ioi 0)) :
    ∀ x ∈ Set.Ioi (0 : ℝ), (v x) ^ 2 ≤ 2 * ∫ t in Set.Ioi (0 : ℝ), |v t * deriv v t| := by
  have hmeasv : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hv.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hmeasd : AEStronglyMeasurable (deriv v) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hv.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).aestronglyMeasurable measurableSet_Ioi
  -- integrability of `|v v'|`, by AM–GM against `(v² + (v')²)/2`
  have hprod_int : IntegrableOn (fun t => |v t * deriv v t|) (Set.Ioi (0 : ℝ)) := by
    have hmaj : IntegrableOn (fun t => ((v t) ^ 2 + (deriv v t) ^ 2) / 2) (Set.Ioi (0 : ℝ)) :=
      (h2.add hd2).div_const 2
    refine hmaj.mono' (hmeasv.mul hmeasd).norm ?_
    filter_upwards with t
    simpa only [Real.norm_eq_abs, abs_abs] using abs_mul_le_half_add_sq (v t) (deriv v t)
  set A := ∫ t in Set.Ioi (0 : ℝ), |v t * deriv v t| with hA
  intro x hx
  by_contra hcon
  push Not at hcon
  have hε : 0 < (v x) ^ 2 - 2 * A := by linarith
  -- the fundamental theorem of calculus plus the triangle inequality
  have hmain : ∀ y ∈ Set.Ioi x, (v x) ^ 2 - 2 * A ≤ (v y) ^ 2 := by
    intro y hy
    have hxy : x ≤ y := le_of_lt hy
    have hderiv : ∀ t ∈ uIcc x y, HasDerivAt (v ^ 2) (2 * v t * deriv v t) t := by
      intro t ht
      have ht0 : t ∈ Set.Ioi (0 : ℝ) := by
        rw [uIcc_of_le hxy] at ht
        exact lt_of_lt_of_le hx ht.1
      have hd : DifferentiableAt ℝ v t :=
        (hv.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds ht0)
      simpa using hd.hasDerivAt.pow 2
    have hint : IntervalIntegrable (fun t => 2 * v t * deriv v t) volume x y := by
      refine ContinuousOn.intervalIntegrable ?_
      have hsub : uIcc x y ⊆ Set.Ioi (0 : ℝ) := by
        rw [uIcc_of_le hxy]
        exact fun t ht => lt_of_lt_of_le hx ht.1
      exact ((continuousOn_const.mul (hv.continuousOn.mono hsub)).mul
        ((hv.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub))
    have hI : ∫ t in x..y, (2 * v t * deriv v t) = (v y) ^ 2 - (v x) ^ 2 := by
      simpa only [Pi.pow_apply] using
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hpt2 : ∀ t, |2 * v t * deriv v t| = 2 * |v t * deriv v t| := by
      intro t
      rw [show (2 : ℝ) * v t * deriv v t = 2 * (v t * deriv v t) by ring, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hb : |∫ t in x..y, 2 * v t * deriv v t| ≤ 2 * A := by
      calc |∫ t in x..y, 2 * v t * deriv v t|
          ≤ ∫ t in x..y, |2 * v t * deriv v t| :=
            intervalIntegral.abs_integral_le_integral_abs hxy
        _ = 2 * ∫ t in x..y, |v t * deriv v t| := by
              rw [← intervalIntegral.integral_const_mul]
              exact intervalIntegral.integral_congr (fun t _ => hpt2 t)
        _ ≤ 2 * (∫ t in Set.Ioi (0 : ℝ), |v t * deriv v t|) := by
              have hle : ∫ t in x..y, |v t * deriv v t|
                  ≤ ∫ t in Set.Ioi (0 : ℝ), |v t * deriv v t| := by
                rw [intervalIntegral.integral_of_le hxy]
                refine setIntegral_mono_set (s := Set.Ioc x y) (t := Set.Ioi (0 : ℝ)) hprod_int
                  (Eventually.of_forall (fun t => abs_nonneg _)) ?_
                exact Eventually.of_forall fun t ht => lt_trans hx ht.1
              linarith
        _ = 2 * A := by rw [hA]
    linarith [abs_le.mp hb]
  -- the contradiction: the tail of `∫ v²` is both `≥ ε M` and `≤ ∫_0^∞ v²`
  set B := ∫ t in Set.Ioi (0 : ℝ), (v t) ^ 2 with hB
  have hBnn : 0 ≤ B := by
    rw [hB]; exact integral_nonneg (fun t => sq_nonneg (v t))
  set M := B / ((v x) ^ 2 - 2 * A) + 1 with hM
  have hMpos : 0 < M := by
    rw [hM]
    have : 0 ≤ B / ((v x) ^ 2 - 2 * A) := div_nonneg hBnn (le_of_lt hε)
    linarith
  have hge : ((v x) ^ 2 - 2 * A) * M ≤ ∫ t in x..(x + M), (v t) ^ 2 := by
    have hconst : ∫ t in x..(x + M), ((v x) ^ 2 - 2 * A) = ((v x) ^ 2 - 2 * A) * M := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : x ≤ x + M) ?_ ?_ ?_
    · exact intervalIntegrable_const
    · refine ContinuousOn.intervalIntegrable ?_
      refine (hv.continuousOn.mono ?_).pow 2
      intro t ht
      rw [uIcc_of_le (by linarith : x ≤ x + M)] at ht
      exact lt_of_lt_of_le hx ht.1
    · intro t ht
      exact hmain t ht.1
  have hle : ∫ t in x..(x + M), (v t) ^ 2 ≤ B := by
    rw [hB, intervalIntegral.integral_of_le (by linarith : x ≤ x + M)]
    refine setIntegral_mono_set (s := Set.Ioc x (x + M)) (t := Set.Ioi (0 : ℝ)) h2
      (Eventually.of_forall (fun t => sq_nonneg (v t))) ?_
    exact Eventually.of_forall fun t ht => lt_trans hx ht.1
  have hkey : ((v x) ^ 2 - 2 * A) * M ≤ B := le_trans hge hle
  have hkey2 : ((v x) ^ 2 - 2 * A) * M = B + ((v x) ^ 2 - 2 * A) := by
    rw [hM, mul_add, mul_div_cancel₀ B (ne_of_gt hε), mul_one]
  linarith

/-! ## The main lemma -/

theorem AuxAgmon : ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ → ℝ,
    ContDiffOn ℝ 1 v (Set.Ioi 0) →
    MeasureTheory.IntegrableOn (fun x : ℝ => (v x) ^ 2) (Set.Ioi 0) →
    MeasureTheory.IntegrableOn (fun x : ℝ => (deriv v x) ^ 2) (Set.Ioi 0) →
    MeasureTheory.IntegrableOn (fun x : ℝ => (v x) ^ 4) (Set.Ioi 0) ∧
      (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 4)
        ≤ C * ((∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2) ^ (3 / 2 : ℝ))
            * ((∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2) ^ (1 / 2 : ℝ)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro v hv h2 hd2
  set A := ∫ t in Set.Ioi (0 : ℝ), |v t * deriv v t| with hA
  have hcs : A ≤ Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
      * Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2) := by
    rw [hA]; exact agmon_cs_Ioi v hv h2 hd2
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ), (v x) ^ 2 ≤ 2 * A := by
    rw [hA]; exact agmon_pointwise_Ioi v hv h2 hd2
  have hPnn : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (v x))
  -- the pointwise bound makes `v⁴` integrable on the half-line, dominated by `2A v²`
  have hmeasv : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hv.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have h4 : IntegrableOn (fun x : ℝ => (v x) ^ 4) (Set.Ioi 0) := by
    refine (h2.const_mul (2 * A)).mono' (hmeasv.pow 4) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hh := hpt x hx
    have h0 : 0 ≤ (v x) ^ 2 := sq_nonneg _
    have h4eq : (v x) ^ 4 = (v x) ^ 2 * (v x) ^ 2 := by ring
    have hle : (v x) ^ 4 ≤ (2 * A) * (v x) ^ 2 := by
      rw [h4eq]
      exact mul_le_mul_of_nonneg_right hh h0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle
  refine ⟨h4, ?_⟩
  have hmain : (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 4)
      ≤ 2 * A * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2) := by
    have hmono : (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 4)
        ≤ ∫ x in Set.Ioi (0 : ℝ), (2 * A) * (v x) ^ 2 :=
      setIntegral_mono_on (s := Set.Ioi (0 : ℝ)) h4 (h2.const_mul (2 * A)) measurableSet_Ioi
        (fun x hx => by
          have hh := hpt x hx
          have h0 : 0 ≤ (v x) ^ 2 := sq_nonneg _
          have h4eq : (v x) ^ 4 = (v x) ^ 2 * (v x) ^ 2 := by ring
          rw [h4eq]
          exact mul_le_mul_of_nonneg_right hh h0)
    have hval : (∫ x in Set.Ioi (0 : ℝ), (2 * A) * (v x) ^ 2)
        = 2 * A * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2) := by
      rw [integral_const_mul]
    linarith [hmono, hval]
  have hfin : 2 * A * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
      ≤ 2 * ((∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2) ^ (3 / 2 : ℝ))
          * ((∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2) ^ (1 / 2 : ℝ)) := by
    have hstep : 2 * A * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
        ≤ 2 * (Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
            * Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2))
          * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2) := by
      have hAP : A * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
          ≤ (Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
              * Real.sqrt (∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2))
            * (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2) :=
        mul_le_mul_of_nonneg_right hcs hPnn
      nlinarith [hAP]
    refine hstep.trans (le_of_eq ?_)
    exact two_sqrt_mul_eq (∫ x in Set.Ioi (0 : ℝ), (v x) ^ 2)
      (∫ x in Set.Ioi (0 : ℝ), (deriv v x) ^ 2) hPnn
  exact le_trans hmain hfin

end Work.FTS.StrongPersist.L3Rhs
