import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Equilibrium potential of an interval (classical identity)

First analytic brick for the arithmeticity of Serre's measure.  Let
`x(t) = (c+d)/2 + (d−c)/2·cos t` parametrize `[c,d]`.  For `x ∈ [c,d]` the
equilibrium potential satisfies the classical identity

    ∫ t in 0..π, log|x − x(t)| dt = π · log((d−c)/4)

equivalently `U^{μ_eq}(x) = −log((d−c)/4)` where μ_eq is the arcsine measure.

## Proof outline

1. Write `x(s) = (c+d)/2 + (d−c)/2·cos s` with `x = x(s)` for some `s ∈ [0,π]`
   (possible since `x ∈ [c,d]`; take `s = arccos((x−m)/r)`).  Use
   `cos s − cos t = −2·sin((s+t)/2)·sin((s−t)/2)`.
2. Split the log of the product and integrate termwise.  The two pieces
   `I± = ∫₀^π log|sin((s±t)/2)|dt` are each rewritten by the substitution
   `u = (s±t)/2`; adding the two pieces gives twice the integral of
   `log|sin|` over a window of length `π`, hence `−2π·log 2` by periodicity of
   `log∘sin` with period `π` and `integral_log_sin_zero_pi`.
3. Conclude `∫₀^π log|x(s)−x(t)|dt = π·log(2r) − 2π·log 2 = π·log(r/2)`,
   and `r/2 = (d−c)/4`.

Note: in this mathlib `Real.log` is extended by `log |x|` on negative numbers
(`Real.log_abs`) and `log 0 = 0`, so `log |y| = log y` pointwise and all
product splits are ordinary `Real.log_mul` identities that only fail on the
(discrete) zero set of the sine factors, which is handled almost everywhere.
-/

noncomputable section

open MeasureTheory
open scoped Real
open intervalIntegral

namespace Submission.EquilibriumPotential

/-- `log ∘ sin` has period `π`. -/
private lemma log_sin_periodic : Function.Periodic (fun x : ℝ => Real.log (Real.sin x)) Real.pi := by
  intro x
  change Real.log (Real.sin (x + π)) = Real.log (Real.sin x)
  rw [Real.sin_add_pi]
  exact Real.log_neg_eq_log (Real.sin x)

/-- The integral of `log ∘ sin` over any window of length `π` equals `-log 2 * π`. -/
private lemma intervalIntegral_log_sin_period (a : ℝ) :
    (∫ x in a..(a + Real.pi), Real.log (Real.sin x)) = -Real.log 2 * Real.pi := by
  rw [log_sin_periodic.intervalIntegral_add_eq a 0]
  simpa using integral_log_sin_zero_pi

/-- Change of variables `t ↦ (s+t)/2` in `∫₀^π log(sin ((s+t)/2))`. -/
private lemma log_sin_half_plus (s : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin ((s + t) / 2))) =
      2 * (∫ u in (s / 2)..((s + Real.pi) / 2), Real.log (Real.sin u)) := by
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin ((s + t) / 2)))
        = ∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin (s / 2 + (1 / 2 : ℝ) * t)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact congrArg Real.log
            (congrArg Real.sin (by ring : (s + t) / 2 = s / 2 + (1 / 2 : ℝ) * t))
    _ = 2 * (∫ u in (s / 2)..((s + Real.pi) / 2), Real.log (Real.sin u)) := by
          rw [intervalIntegral.integral_comp_add_mul (f := fun u : ℝ => Real.log (Real.sin u))
              (a := (0 : ℝ)) (b := Real.pi) (c := (1 / 2 : ℝ)) (d := s / 2)
              (by norm_num : (1 / 2 : ℝ) ≠ 0)]
          norm_num
          ring_nf

/-- Change of variables `t ↦ (s−t)/2` in `∫₀^π log(sin ((s−t)/2))`. -/
private lemma log_sin_half_minus (s : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin ((s - t) / 2))) =
      2 * (∫ u in ((s - Real.pi) / 2)..(s / 2), Real.log (Real.sin u)) := by
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin ((s - t) / 2)))
        = ∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin (s / 2 - (1 / 2 : ℝ) * t)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact congrArg Real.log
            (congrArg Real.sin (by ring : (s - t) / 2 = s / 2 - (1 / 2 : ℝ) * t))
    _ = 2 * (∫ u in ((s - Real.pi) / 2)..(s / 2), Real.log (Real.sin u)) := by
          rw [intervalIntegral.integral_comp_sub_mul (f := fun u : ℝ => Real.log (Real.sin u))
              (a := (0 : ℝ)) (b := Real.pi) (c := (1 / 2 : ℝ)) (d := s / 2)
              (by norm_num : (1 / 2 : ℝ) ≠ 0)]
          norm_num
          ring_nf

/-- For every `s`, the sum of the two pieces is `-2π log 2`. -/
private lemma two_piece_window (s : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin ((s + t) / 2))) +
      (∫ t in (0 : ℝ)..Real.pi, Real.log (Real.sin ((s - t) / 2))) =
        -2 * Real.pi * Real.log 2 := by
  rw [log_sin_half_plus s, log_sin_half_minus s]
  calc
    2 * (∫ u in (s / 2)..((s + π) / 2), Real.log (Real.sin u)) +
        2 * (∫ u in ((s - π) / 2)..(s / 2), Real.log (Real.sin u))
        = 2 * (∫ u in ((s - π) / 2)..((s + π) / 2), Real.log (Real.sin u)) := by
          rw [← mul_add]
          congr 1
          rw [add_comm]
          exact intervalIntegral.integral_add_adjacent_intervals
            (f := Real.log ∘ Real.sin)
            (a := (s - π) / 2) (b := s / 2) (c := (s + π) / 2)
            (intervalIntegrable_log_sin (a := (s - π) / 2) (b := s / 2))
            (intervalIntegrable_log_sin (a := s / 2) (b := (s + π) / 2))
    _ = -2 * π * Real.log 2 := by
          have hw := intervalIntegral_log_sin_period ((s - π) / 2)
          have hb : (s + π) / 2 = (s - π) / 2 + π := by ring
          rw [hb, hw]
          ring

/-- The set of zeros of `t ↦ sin ((s+t)/2)` is countable. -/
private lemma sin_half_add_zero_set (s : ℝ) :
    {t : ℝ | Real.sin ((s + t) / 2) = 0} = (fun n : ℤ => 2 * (n : ℝ) * Real.pi - s) '' Set.univ := by
  ext t
  constructor
  · intro ht
    rcases (Real.sin_eq_zero_iff.mp ht) with ⟨n, hn⟩
    refine ⟨n, trivial, ?_⟩
    have hn2 : s + t = 2 * (n : ℝ) * π := by nlinarith [hn]
    linarith
  · rintro ⟨n, -, ht⟩
    change Real.sin ((s + t) / 2) = 0
    rw [Real.sin_eq_zero_iff]
    refine ⟨n, ?_⟩
    rw [← ht]
    ring

/-- The set of zeros of `t ↦ sin ((s−t)/2)` is countable. -/
private lemma sin_half_sub_zero_set (s : ℝ) :
    {t : ℝ | Real.sin ((s - t) / 2) = 0} = (fun n : ℤ => s - 2 * (n : ℝ) * Real.pi) '' Set.univ := by
  ext t
  constructor
  · intro ht
    rcases (Real.sin_eq_zero_iff.mp ht) with ⟨n, hn⟩
    refine ⟨n, trivial, ?_⟩
    have hn2 : s - t = 2 * (n : ℝ) * π := by nlinarith [hn]
    linarith
  · rintro ⟨n, -, ht⟩
    change Real.sin ((s - t) / 2) = 0
    rw [Real.sin_eq_zero_iff]
    refine ⟨n, ?_⟩
    rw [← ht]
    ring

/-- Almost surely (in fact, off a countable set), both half-angle sines are nonzero. -/
private lemma eventually_sin_half_ne_zero (s : ℝ) :
    ∀ᵐ t, ¬(Real.sin ((s + t) / 2) = 0 ∨ Real.sin ((s - t) / 2) = 0) := by
  rw [MeasureTheory.ae_iff]
  simp only [not_not]
  rw [show {t : ℝ | Real.sin ((s + t) / 2) = 0 ∨ Real.sin ((s - t) / 2) = 0} =
      {t : ℝ | Real.sin ((s + t) / 2) = 0} ∪ {t : ℝ | Real.sin ((s - t) / 2) = 0} by
    ext t; simp]
  rw [sin_half_add_zero_set s, sin_half_sub_zero_set s]
  exact measure_union_null
    (Set.Countable.measure_zero (Set.countable_univ.image _) volume)
    (Set.Countable.measure_zero (Set.countable_univ.image _) volume)

/-- Pointwise identity: on the complement of the zero set of `sin((s±t)/2)`,
`log (r·(cos s − cos t)) = log(2r) + log sin((s+t)/2) + log sin((s−t)/2)`. -/
private lemma log_product_split (r s t : ℝ) (hr : 0 < r)
    (hA : Real.sin ((s + t) / 2) ≠ 0) (hB : Real.sin ((s - t) / 2) ≠ 0) :
    Real.log (r * (Real.cos s - Real.cos t)) =
      Real.log (2 * r) + Real.log (Real.sin ((s + t) / 2)) + Real.log (Real.sin ((s - t) / 2)) := by
  have hc : r * (Real.cos s - Real.cos t) =
      -(2 * r) * (Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2)) := by
    rw [Real.cos_sub_cos]
    ring
  have hr0 : r ≠ 0 := hr.ne'
  have h2r0 : -(2 * r) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hr0)
  have hprod : Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2) ≠ 0 := mul_ne_zero hA hB
  calc
    Real.log (r * (Real.cos s - Real.cos t))
        = Real.log (-(2 * r) * (Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2))) := by
          rw [hc]
    _ = Real.log (-(2 * r)) + Real.log (Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2)) := by
          rw [Real.log_mul h2r0 hprod]
    _ = Real.log (2 * r) + Real.log (Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2)) := by
          rw [Real.log_neg_eq_log (2 * r)]
    _ = Real.log (2 * r) + Real.log (Real.sin ((s + t) / 2)) + Real.log (Real.sin ((s - t) / 2)) := by
          rw [Real.log_mul hA hB]
          ring

/-- Interval integrability of `t ↦ log(sin ((s+t)/2))` on `[0, π]`. -/
private lemma integrable_log_sin_half_plus (s : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log (Real.sin ((s + t) / 2))) volume (0 : ℝ) Real.pi := by
  have hf : IntervalIntegrable (Real.log ∘ Real.sin) volume (s / 2) ((s + Real.pi) / 2) :=
    intervalIntegrable_log_sin
  have hF' : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (x * (1 / 2 : ℝ))))
      volume s (s + Real.pi) := by
    simpa [show (s / 2) / (1 / 2 : ℝ) = s by ring,
      show ((s + Real.pi) / 2) / (1 / 2 : ℝ) = s + Real.pi by ring]
      using hf.comp_mul_right (c := (1 / 2 : ℝ))
  have hfun2 : (fun x : ℝ => Real.log (Real.sin ((s + x) / 2))) =
      fun x => Real.log (Real.sin ((s + x) * (1 / 2 : ℝ))) := by
    funext x
    congr 1
    ring
  simpa [hfun2, show s - s = (0 : ℝ) by ring, show s + Real.pi - s = Real.pi by ring]
    using hF'.comp_add_left s

/-- Interval integrability of `t ↦ log(sin ((s−t)/2))` on `[0, π]`. -/
private lemma integrable_log_sin_half_minus (s : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log (Real.sin ((s - t) / 2))) volume (0 : ℝ) Real.pi := by
  have hf : IntervalIntegrable (Real.log ∘ Real.sin) volume ((s - Real.pi) / 2) (s / 2) :=
    intervalIntegrable_log_sin
  have hF' : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (x * (1 / 2 : ℝ))))
      volume (s - Real.pi) s := by
    simpa [show ((s - Real.pi) / 2) / (1 / 2 : ℝ) = s - Real.pi by ring,
      show (s / 2) / (1 / 2 : ℝ) = s by ring]
      using hf.comp_mul_right (c := (1 / 2 : ℝ))
  have hfun2 : (fun x : ℝ => Real.log (Real.sin ((s - x) / 2))) =
      fun x => Real.log (Real.sin ((s - x) * (1 / 2 : ℝ))) := by
    funext x
    congr 1
    ring
  have hrev : IntervalIntegrable (fun t : ℝ => Real.log (Real.sin ((s - t) / 2)))
      volume Real.pi (0 : ℝ) := by
    simpa [hfun2, show s - (s - Real.pi) = Real.pi by ring, show s - s = (0 : ℝ) by ring]
      using hF'.comp_sub_left s
  simpa using hrev.symm

/-- Core computation: for `r > 0` and any `s`,
`∫₀^π log(r·(cos s − cos t)) dt = π·log(r/2)`. -/
private lemma integral_log_mul_cos_sub (r s : ℝ) (hr : 0 < r) :
    (∫ t in (0 : ℝ)..Real.pi, Real.log (r * (Real.cos s - Real.cos t))) =
      Real.pi * Real.log (r / 2) := by
  let p1 : ℝ → ℝ := fun t => Real.log (Real.sin ((s + t) / 2))
  let p2 : ℝ → ℝ := fun t => Real.log (Real.sin ((s - t) / 2))
  let C : ℝ := Real.log (2 * r)
  have hcongr :
      (∫ t in (0 : ℝ)..Real.pi, Real.log (r * (Real.cos s - Real.cos t))) =
        (∫ t in (0 : ℝ)..Real.pi, (C + p1 t + p2 t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [eventually_sin_half_ne_zero s] with t ht
    intro hmem
    have hA : Real.sin ((s + t) / 2) ≠ 0 := fun h => ht (Or.inl h)
    have hB : Real.sin ((s - t) / 2) ≠ 0 := fun h => ht (Or.inr h)
    dsimp [C, p1, p2]
    exact log_product_split r s t hr hA hB
  have hp1 : IntervalIntegrable p1 volume (0 : ℝ) Real.pi := by
    simpa [p1] using integrable_log_sin_half_plus s
  have hp2 : IntervalIntegrable p2 volume (0 : ℝ) Real.pi := by
    simpa [p2] using integrable_log_sin_half_minus s
  have hC : IntervalIntegrable (fun _ : ℝ => C) volume (0 : ℝ) Real.pi :=
    intervalIntegrable_const
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log (r * (Real.cos s - Real.cos t)))
        = ∫ t in (0 : ℝ)..Real.pi, (C + p1 t + p2 t) := hcongr
    _ = (∫ t in (0 : ℝ)..Real.pi, (C + p1 t)) + ∫ t in (0 : ℝ)..Real.pi, p2 t := by
          exact intervalIntegral.integral_add (f := fun t : ℝ => C + p1 t) (g := p2)
            (IntervalIntegrable.add hC hp1) hp2
    _ = (∫ t in (0 : ℝ)..Real.pi, C) + (∫ t in (0 : ℝ)..Real.pi, p1 t) +
          ∫ t in (0 : ℝ)..Real.pi, p2 t := by
          rw [intervalIntegral.integral_add (f := fun _ : ℝ => C) (g := p1) hC hp1]
    _ = Real.pi * C + ((∫ t in (0 : ℝ)..Real.pi, p1 t) + ∫ t in (0 : ℝ)..Real.pi, p2 t) := by
          rw [intervalIntegral.integral_const]
          simp
          ring
    _ = Real.pi * C - 2 * Real.pi * Real.log 2 := by
          dsimp [p1, p2]
          rw [two_piece_window s]
          ring
    _ = Real.pi * Real.log (r / 2) := by
          have hr0 : r ≠ 0 := hr.ne'
          have hlogmul : Real.log (2 * r) = Real.log 2 + Real.log r :=
            Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr0
          have hlogdiv : Real.log (r / 2) = Real.log r - Real.log 2 :=
            Real.log_div hr0 (by norm_num : (2 : ℝ) ≠ 0)
          dsimp [C]
          rw [hlogmul, hlogdiv]
          ring

/-- Same integral with the affine chart `m + r·cos s`: absolute values are removed by the
extension convention `Real.log_abs`. -/
private lemma intervalIntegral_log_abs_cos_sub (m r s : ℝ) (hr : 0 < r) :
    (∫ t in (0 : ℝ)..Real.pi,
        Real.log |(m + r * Real.cos s) - (m + r * Real.cos t)|) =
      Real.pi * Real.log (r / 2) := by
  calc
    (∫ t in (0 : ℝ)..Real.pi, Real.log |(m + r * Real.cos s) - (m + r * Real.cos t)|)
        = ∫ t in (0 : ℝ)..Real.pi, Real.log (r * (Real.cos s - Real.cos t)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp
          rw [Real.log_abs]
          congr 1
          ring
    _ = Real.pi * Real.log (r / 2) := integral_log_mul_cos_sub r s hr

/-- `∫ t in 0..π, log|x − ((c+d)/2 + (d−c)/2·cos t)| dt = π · log((d−c)/4)`
for `x ∈ [c,d]` with `c < d`. -/
lemma intervalIntegral_log_abs_chart_sub {c d x : ℝ} (hcd : c < d)
    (hx : x ∈ Set.Icc c d) :
    (∫ t in (0 : ℝ)..Real.pi,
        Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|) =
      Real.pi * Real.log ((d - c) / 4) := by
  let m : ℝ := (c + d) / 2
  let r : ℝ := (d - c) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hcd) (by norm_num)
  have hxeq : ∃ s : ℝ, x = m + r * Real.cos s := by
    have hcm : c = m - r := by dsimp [m, r]; ring
    have hdm : d = m + r := by dsimp [m, r]; ring
    have hle1 : -r ≤ x - m := by
      have hxc : c ≤ x := hx.1
      rw [hcm] at hxc
      linarith
    have hle2 : x - m ≤ r := by
      have hxd : x ≤ d := hx.2
      rw [hdm] at hxd
      linarith
    have hx1 : -1 ≤ (x - m) / r := by
      exact (le_div_iff₀ hr).2 (by simpa using hle1)
    have hx2 : (x - m) / r ≤ 1 := by
      exact (div_le_iff₀ hr).2 (by simpa using hle2)
    let s : ℝ := Real.arccos ((x - m) / r)
    refine ⟨s, ?_⟩
    have hcos : Real.cos s = (x - m) / r := by
      dsimp [s]
      exact Real.cos_arccos hx1 hx2
    have htmp : m + r * ((x - m) / r) = x := by
      rw [mul_comm r ((x - m) / r)]
      rw [div_mul_cancel₀ (x - m) hr.ne']
      ring
    calc x = m + r * ((x - m) / r) := htmp.symm
         _ = m + r * Real.cos s := by rw [hcos]
  rcases hxeq with ⟨s, hxs⟩
  have hQ : (d - c) / 4 = r / 2 := by dsimp [r]; ring_nf
  calc
    (∫ t in (0 : ℝ)..Real.pi,
        Real.log |x - ((c + d) / 2 + (d - c) / 2 * Real.cos t)|)
        = ∫ t in (0 : ℝ)..Real.pi,
            Real.log |(m + r * Real.cos s) - (m + r * Real.cos t)| := by
          rw [hxs]
    _ = Real.pi * Real.log (r / 2) := intervalIntegral_log_abs_cos_sub m r s hr
    _ = Real.pi * Real.log ((d - c) / 4) := by rw [← hQ]

end Submission.EquilibriumPotential
