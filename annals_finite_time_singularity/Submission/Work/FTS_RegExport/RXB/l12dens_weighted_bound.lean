/-
# `Work.FTS_RegExport.RXB.l12dens_weighted_bound`

The weighted pointwise-in-`s` bound on the `L₁₂`-density

  `|L₁₂dens f s| ≤ C · (√s/(1+s)²) · |f|_{ℋ⁴}`

for a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`),
honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`) and with vanishing boundary traces
(`Work.FTS.Nonlin.BdryTraces α 4 f`).  It is the density input of the zero-mode passage to the
limit, where it turns a uniform `ℋ⁴`-bound on the class-`C` approximants into an `L¹(ds)`-majorant
(`√s/(1+s)² ∈ L¹(0,∞)`, `Work.FTS_RegExport.RXB.integrableOn_sqrt_div_sq`).

## The mathematics

`L₁₂dens f s = (1/s)·∫_θ K(θ) f(s,θ) dθ` with `K(θ) = 3 sinθ cos²θ ≥ 0`.  The weight
`√s/(1+s)²` is *exactly* the sharp scaling of the radial variable: it is produced by the
two-sided radial Hardy inequality in the weight `w(z) = (1+z)²/z²`.

* For every `θ ∈ (0,π/2)` put `v := f(·,θ)`.  By the two radial clauses of `BdryTraces`, `v`
  vanishes at `0⁺` and at `+∞`, and `t·v'(t) = D_z f(t,θ)`.  Writing
  `ψ(t) = t/(1+t)² = 1/(t·w(t))`, Cauchy–Schwarz on `[0,s]` (for `s ≤ 1`) resp. on `[s,B]`
  (for `1 ≤ s ≤ B`) gives

    `|v(s)| ≤ √(∫_0^s (t v' w)²)·√(∫_0^s ψ²)`  resp.
    `|g B - g s| ≤ √(∫ (t v' w)²)·√(∫_s^B ψ²)`,

  and the two elementary estimates `∫_0^s ψ² ≤ s³` (`s ≤ 1`), `∫_s^B ψ² ≤ 1/s` (`1 ≤ s`),
  turned into `√(∫_0^s ψ²) ≤ 4·√s·s/(1+s)²` resp. `√(∫_s^B ψ²) ≤ 4·√s·s/(1+s)²`, yield the
  two-sided weighted Hardy inequality `|v(s)| ≤ 4·(√s·s/(1+s)²)·√(∫_{t>0}(t v' w)²)`
  (`weighted_hardy_two_sided_of_continuousOn` below), the limits being taken along `0⁺` resp. `+∞` (the same
  Cauchy–Schwarz bound holds for every `ε ∈ (0,s)` resp. `B ≥ s`).

* Dividing by `s` and using Cauchy–Schwarz in `θ` against `K ∈ L²(Iθ)`,

    `|L₁₂dens f s| ≤ 4·(√s/(1+s)²)·∫_θ K θ·√(∫_{t>0}(D_z f·w)²) ≤ 20·(√s/(1+s)²)·|f|_{ℋ⁴}`,

  because `√(∫_{Iθ}K²) ≤ 5` and `∫_θ ∫_{t>0} (D_z f·w)² ≤ HkSq α 4 f` (the `i = 1` slot of
  `HkIntegrand`, since `sin(2θ)^{η/2} ≤ 1`).  The three analytic inputs of this second half are
  the delegated lemmas `DzSlice_l2` (a.e. radial-slice integrability of `(D_z f·w)²`, and the
  `L²_θ`-bound by `HkSq`), `K_mul_sqrt_le_of_L2` (Cauchy–Schwarz against `K`) and
  `tendsto_nhdsGT_zero_of_radial_trace` (the `z → 0⁺` clause of `BdryTraces` for the datum
  itself).

The constant `20` is not optimised.

The development is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.Construction.Defs
import Submission.Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace
import Submission.Work.FTS_RegExport.RXB.DzSlice_l2
import Submission.Work.FTS_RegExport.RXB.K_mul_sqrt_le_of_L2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The two-sided weighted radial Hardy inequality

The auxiliary weight `ψ t = t/(1+t)² = 1/(t·w t)`, two elementary integral estimates for it, and
the Hardy inequality itself (proved by integrating from `0` resp. from `+∞` and letting the
endpoint tend to `0⁺` resp. `+∞`). -/

/-- `ψ t = t/(1+t)²`, the reciprocal of `t·w(t)`. -/
private def psi (t : ℝ) : ℝ := t / (1 + t) ^ 2

private lemma psi_sq_eq (t : ℝ) : psi t ^ 2 = t ^ 2 / (1 + t) ^ 4 := by
  unfold psi
  rw [div_pow, show ((1 + t) ^ 2) ^ 2 = (1 + t) ^ 4 by ring]

private lemma psi_mul (c : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    (t * c t * Work.Spaces.w t) * psi t = c t := by
  have h1 : (1 + t) ≠ 0 := by positivity
  have ht0 : t ≠ 0 := ne_of_gt ht
  unfold psi Work.Spaces.w
  field_simp

private lemma psi_cont : ContinuousOn psi (Set.Ioi (-1 : ℝ)) := by
  unfold psi
  refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2)
    (fun x hx => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hx])))

/-- The pointwise bound `ψ t ^ 2 ≤ t ^ 2` for `t ≥ 0`. -/
private lemma psi_sq_le_sq {t : ℝ} (ht : 0 ≤ t) : psi t ^ 2 ≤ t ^ 2 := by
  rw [psi_sq_eq, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + t) ^ 4)]
  have h1 : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_pow₀ (by linarith)
  nlinarith [sq_nonneg t]

/-- The pointwise bound `ψ t ^ 2 ≤ 1/t²` for `t > 0`. -/
private lemma psi_sq_le_inv_sq {t : ℝ} (ht : 0 < t) : psi t ^ 2 ≤ 1 / t ^ 2 := by
  rw [psi_sq_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (1 + t), sq_nonneg t, ht]

/-- `√(∫_0^s ψ²) ≤ 4·(√s·s/(1+s)²)` for `0 < s ≤ 1`. -/
private lemma psi_sqrt_small {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := by
  have hcont1 : ContinuousOn (fun t : ℝ => psi t ^ 2) (Set.uIcc (0 : ℝ) s) := by
    rw [Set.uIcc_of_le hs.le]
    exact (psi_cont.mono (fun x hx => by
      have h1 : (0 : ℝ) ≤ x := hx.1
      show (-1 : ℝ) < x
      linarith)).pow 2
  have hcont2 : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc (0 : ℝ) s) := by
    rw [Set.uIcc_of_le hs.le]
    exact continuousOn_id.pow 2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hs.le
    (hcont1.intervalIntegrable (μ := volume)) (hcont2.intervalIntegrable (μ := volume))
    (fun t ht => psi_sq_le_sq ht.1)
  have hval : (∫ t in (0 : ℝ)..s, t ^ 2) = s ^ 3 / 3 := by
    rw [integral_pow]; norm_num
  rw [hval] at hmono
  have h2 : (∫ t in (0 : ℝ)..s, psi t ^ 2) ≤ s ^ 3 := by
    have h3 : (0 : ℝ) ≤ s ^ 3 := by positivity
    linarith
  have h4 : Real.sqrt (s ^ 3) = Real.sqrt s * s := by
    rw [show s ^ 3 = s * s ^ 2 by ring, Real.sqrt_mul hs.le, Real.sqrt_sq hs.le]
  have h5 : Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) ≤ Real.sqrt s * s := by
    rw [← h4]; exact Real.sqrt_le_sqrt h2
  refine le_trans h5 ?_
  have hsq : (1 + s) ^ 2 ≤ 4 := by nlinarith
  have hnn : 0 ≤ Real.sqrt s * s := mul_nonneg (Real.sqrt_nonneg _) hs.le
  rw [show (4 : ℝ) * (Real.sqrt s * s / (1 + s) ^ 2) = (4 * (Real.sqrt s * s)) / (1 + s) ^ 2
    by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
  nlinarith [hnn, hsq]

/-- `√(∫_s^B ψ²) ≤ 4·(√s·s/(1+s)²)` for `1 ≤ s ≤ B`. -/
private lemma psi_sqrt_large {s B : ℝ} (hs : 1 ≤ s) (hsB : s ≤ B) :
    Real.sqrt (∫ t in s..B, psi t ^ 2) ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hcont1 : ContinuousOn (fun t : ℝ => psi t ^ 2) (Set.uIcc s B) := by
    rw [Set.uIcc_of_le hsB]
    exact (psi_cont.mono (fun x hx => by
      have h1 : s ≤ x := hx.1
      show (-1 : ℝ) < x
      linarith)).pow 2
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.uIcc s B) := by
    rw [Set.uIcc_of_le hsB]
    refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hs0 hx.1))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hsB
    (hcont1.intervalIntegrable (μ := volume)) (hcont2.intervalIntegrable (μ := volume))
    (fun t ht => psi_sq_le_inv_sq (lt_of_lt_of_le hs0 ht.1))
  -- the exact value of `∫_s^B 1/t²`
  have hderiv : ∀ x ∈ Set.uIcc s B, HasDerivAt (fun y : ℝ => -y⁻¹) (1 / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hsB] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hs0 hx.1)
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
    have h2 : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ 2)⁻¹)) x := h1.neg
    simpa only [neg_neg, inv_eq_one_div] using h2
  have hintInt : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume s B :=
    hcont2.intervalIntegrable (μ := volume)
  have hval : (∫ t in s..B, 1 / t ^ 2) = 1 / s - 1 / B := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintInt
    rw [h]
    simp only [inv_eq_one_div]
    ring
  have hle1 : (∫ t in s..B, 1 / t ^ 2) ≤ 1 / s := by
    rw [hval]
    have hB0 : (0 : ℝ) ≤ B := le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 1) hs) hsB
    have h1B : 0 ≤ 1 / B := div_nonneg (by norm_num) hB0
    linarith
  have hbound : (∫ t in s..B, psi t ^ 2) ≤ 1 / s := le_trans hmono hle1
  -- conclude
  have hsqrt : Real.sqrt (1 / s) ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := by
    rw [one_div, Real.sqrt_inv, inv_eq_one_div, div_le_iff₀ (Real.sqrt_pos.mpr hs0)]
    have hsp : Real.sqrt s * Real.sqrt s = s := by
      rw [← sq]; exact Real.sq_sqrt hs0.le
    have hkey : 4 * (Real.sqrt s * s / (1 + s) ^ 2) * Real.sqrt s
        = 4 * ((Real.sqrt s * Real.sqrt s) * s) / (1 + s) ^ 2 := by ring
    rw [hkey, hsp, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
    nlinarith
  calc Real.sqrt (∫ t in s..B, psi t ^ 2) ≤ Real.sqrt (1 / s) := Real.sqrt_le_sqrt hbound
    _ ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := hsqrt

/-- **Two-sided weighted radial Hardy inequality.**  For `g` differentiable on `(0,∞)` with
derivative `c` continuous there, vanishing at `0⁺` and at `+∞`, and with `t·c·w ∈ L²(0,∞)`
(`w t = (1+t)²/t²`),

  `|g s| ≤ 4·(√s·s/(1+s)²)·√(∫_{t>0} (t·c t·w t)²)`.

The two sides of the cut `s = 1` are handled by integrating from `0` (using `g 0⁺ = 0`) resp.
from `+∞` (using `g → 0` at infinity), and the two elementary estimates
`∫_0^s ψ² ≤ s³` (`s ≤ 1`) resp. `∫_s^B ψ² ≤ 1/s` (`s ≥ 1`) with `ψ t = t/(1+t)² = 1/(t·w t)`. -/
theorem weighted_hardy_two_sided_of_continuousOn {g c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi (0 : ℝ)))
    (hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (c t) t)
    (hlim0 : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hliminf : Tendsto g atTop (nhds 0))
    (hint : IntegrableOn (fun t => (t * c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    {s : ℝ} (hs : 0 < s) :
    |g s| ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) *
      Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2) := by
  -- the fundamental-theorem + Cauchy-Schwarz step on an interval `[a,b]`, `0 < a ≤ b`
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b →
      |g b - g a| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
        * Real.sqrt (∫ t in a..b, psi t ^ 2) := by
    intro a b ha hab
    have hmem : ∀ x ∈ Set.uIcc a b, (0 : ℝ) < x := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact lt_of_lt_of_le ha hx.1
    have hin : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioi (0 : ℝ) := fun x hx => hmem x hx
    have hIntc : IntervalIntegrable c volume a b :=
      (hc.mono hin).intervalIntegrable (μ := volume)
    have hFTC : ∫ t in a..b, c t = g b - g a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hderiv x (hmem x hx)) hIntc
    have hcongr : (∫ t in a..b, c t)
        = ∫ t in a..b, (t * c t * Work.Spaces.w t) * psi t :=
      intervalIntegral.integral_congr (fun x hx => (psi_mul c (hmem x hx)).symm)
    have hcontW : ContinuousOn (fun t : ℝ => Work.Spaces.w t) (Set.uIcc a b) := by
      unfold Work.Spaces.w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hmem x hx))
    have hcont1 : ContinuousOn (fun t : ℝ => t * c t * Work.Spaces.w t) (Set.uIcc a b) :=
      (continuousOn_id.mul (hc.mono hin)).mul hcontW
    have hcont2 : ContinuousOn (fun t : ℝ => psi t) (Set.uIcc a b) :=
      psi_cont.mono (fun x hx => by
        show (-1 : ℝ) < x
        linarith [hmem x hx])
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab hcont1 hcont2
    have hleI : (∫ t in a..b, (t * c t * Work.Spaces.w t) ^ 2)
        ≤ ∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      refine MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall fun x => sq_nonneg _)
        (Eventually.of_forall fun x hx => ?_)
      exact hmem x (by rw [Set.uIcc_of_le hab]; exact ⟨le_of_lt hx.1, hx.2⟩)
    rw [← hFTC, hcongr]
    calc |∫ t in a..b, (t * c t * Work.Spaces.w t) * psi t|
        ≤ Real.sqrt (∫ t in a..b, (t * c t * Work.Spaces.w t) ^ 2)
            * Real.sqrt (∫ t in a..b, psi t ^ 2) := hcs
      _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * Real.sqrt (∫ t in a..b, psi t ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hleI) (Real.sqrt_nonneg _)
  rcases le_total s 1 with hs1 | hs1
  · -- ## small `s`: integrate from `0`
    have hcontPsi : ContinuousOn (fun t : ℝ => psi t ^ 2) (Set.Icc (0 : ℝ) s) :=
      (psi_cont.mono (fun x hx => by
        have h1 : (0 : ℝ) ≤ x := hx.1
        show (-1 : ℝ) < x
        linarith)).pow 2
    have hbound : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) s →
        |g s| - |g ε| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) := by
      intro ε hε
      have hεs : ε ≤ s := le_of_lt hε.2
      have h1 := hkey ε s hε.1 hεs
      have h2 : |g s| - |g ε| ≤ |g s - g ε| := abs_sub_abs_le_abs_sub (g s) (g ε)
      have hlepsi : (∫ t in ε..s, psi t ^ 2) ≤ ∫ t in (0 : ℝ)..s, psi t ^ 2 := by
        rw [intervalIntegral.integral_of_le hεs, intervalIntegral.integral_of_le hs.le]
        refine MeasureTheory.setIntegral_mono_set
          (hcontPsi.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
          (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall fun x hx => ?_)
        exact ⟨lt_trans hε.1 hx.1, hx.2⟩
      calc |g s| - |g ε| ≤ |g s - g ε| := h2
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * Real.sqrt (∫ t in ε..s, psi t ^ 2) := h1
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlepsi) (Real.sqrt_nonneg _)
    have htend : Tendsto (fun ε : ℝ => |g s| - |g ε|) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (|g s|)) := by
      have h : Tendsto (fun ε : ℝ => |g s| - |g ε|) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (|g s| - |0|)) := tendsto_const_nhds.sub hlim0.abs
      simpa using h
    have hev : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        |g s| - |g ε| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝 0)
          (Iio_mem_nhds (show (0 : ℝ) < s from hs))] with ε hε0 hεs
      exact hbound ε ⟨hε0, hεs⟩
    have hmain := le_of_tendsto htend hev
    calc |g s| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) := by simpa using hmain
      _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) :=
          mul_le_mul_of_nonneg_left (psi_sqrt_small hs hs1) (Real.sqrt_nonneg _)
      _ = 4 * (Real.sqrt s * s / (1 + s) ^ 2)
            * Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2) := by ring
  · -- ## large `s`: integrate towards `+∞`
    have hbound : ∀ B : ℝ, s ≤ B →
        |g s| - |g B| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) := by
      intro B hsB
      have h1 := hkey s B hs hsB
      have h2 : |g s| - |g B| ≤ |g B - g s| := by
        rw [abs_sub_comm (g B) (g s)]
        exact abs_sub_abs_le_abs_sub (g s) (g B)
      have h3 := psi_sqrt_large hs1 hsB
      calc |g s| - |g B| ≤ |g B - g s| := h2
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * Real.sqrt (∫ t in s..B, psi t ^ 2) := h1
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    have htend : Tendsto (fun B : ℝ => |g s| - |g B|) atTop (nhds (|g s|)) := by
      have h : Tendsto (fun B : ℝ => |g s| - |g B|) atTop (nhds (|g s| - |0|)) :=
        tendsto_const_nhds.sub hliminf.abs
      simpa using h
    have hev : ∀ᶠ B in atTop,
        |g s| - |g B| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) := by
      filter_upwards [eventually_ge_atTop s] with B hB
      exact hbound B hB
    have hmain := le_of_tendsto htend hev
    calc |g s| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) := by simpa using hmain
      _ = 4 * (Real.sqrt s * s / (1 + s) ^ 2)
            * Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2) := by ring

/-! ## The density bound -/

theorem l12dens_weighted_bound {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlin.BdryTraces α 4 f →
      ∀ s : ℝ, 0 < s →
        |Work.Construction.L12dens f s|
          ≤ C * (Real.sqrt s / (1 + s) ^ 2) * Work.Spaces.HkNorm α 4 f := by
  refine ⟨20, by norm_num, ?_⟩
  intro f hF hmem hbd s hs
  -- the `θ`-side package: a.e. radial-slice integrability, measurability of the Hardy square
  -- root, its `L²`-mass bound, and the Cauchy–Schwarz bound against `K`
  obtain ⟨hsliceInt, hGaesm, hG2int, hG2le⟩ := DzSlice_l2 (α := α) (f := f) hF hmem
  obtain ⟨hKGint, hKGle⟩ :=
    K_mul_sqrt_le_of_L2 (M := Work.Spaces.HkSq α 4 f) hGaesm
      (fun θ => Real.sqrt_nonneg _) hG2int hG2le (Work.Spaces.HkSq_nonneg α 4 f)
  set G : ℝ → ℝ := fun θ => Real.sqrt (∫ t in Set.Ioi (0 : ℝ),
      (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2) with hGdef
  set c4 : ℝ := 4 * (Real.sqrt s * s / (1 + s) ^ 2) with hc4
  -- almost every angle is interior
  have hioo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)]
      with σ h hmem'
    exact h.mpr hmem'
  -- the a.e. two-sided radial Hardy bound at the angle `θ`
  have hpoint : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |f s θ| ≤ c4 * G θ := by
    filter_upwards [hsliceInt, hioo] with θ hint hθ
    have hsint : MeasureTheory.IntegrableOn
        (fun t => (t * Work.Spaces.pz f t θ * Work.Spaces.w t) ^ 2) (Set.Ioi 0) := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz] using hint
    have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f t θ) t :=
      fun t ht => hF.hasDerivAt_slice hθ ht
    have hc : ContinuousOn (fun t : ℝ => Work.Spaces.pz f t θ) (Set.Ioi 0) :=
      (hF.pz).curry_z hθ |>.continuousOn
    have hb := (hbd 0 0 (by norm_num)).1 θ hθ
    have hlim0 : Tendsto (fun z => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsGT_zero_of_radial_trace (by
        simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
          using hb.1)
    have hliminf : Tendsto (fun z => f z θ) atTop (nhds 0) :=
      Work.FTS.H2.HQ.tendsto_atTop_zero_of_traces (by
        simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
          using hb.2)
    have h := weighted_hardy_two_sided_of_continuousOn hc hderiv hlim0 hliminf hsint hs
    simpa only [hc4, hGdef, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
      using h
  -- integrability of the majorant
  have hmajInt : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * (c4 * G θ))
      Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn (fun θ => c4 * (Work.Spaces.K θ * G θ))
        Work.Spaces.Iθ := hKGint.integrable.const_mul c4
    exact h.congr (Filter.Eventually.of_forall fun θ => by ring)
  -- integrability of the minorant `θ ↦ K θ |f s θ|`
  have hfaesm : MeasureTheory.AEStronglyMeasurable (fun θ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => f p.1 p.2)
      hF.continuousOn hs
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K; fun_prop
  have hKfInt : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * |f s θ|)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hmajInt (hKcont.aestronglyMeasurable.mul ?_) ?_
    · simpa only [Real.norm_eq_abs] using hfaesm.norm
    · filter_upwards [hpoint, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hpt hθmem
      rw [Real.norm_of_nonneg
        (mul_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθmem) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left hpt (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθmem)
  have hmono : (fun θ => Work.Spaces.K θ * |f s θ|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => Work.Spaces.K θ * (c4 * G θ)) := by
    filter_upwards [hpoint, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hpt hθmem
    exact mul_le_mul_of_nonneg_left hpt (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθmem)
  -- the density is the angular integral of `K f` divided by `s`
  have hL12 : Work.Construction.L12dens f s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ) / s := by
    rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ,
      ← MeasureTheory.integral_div]
  have hpull : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (c4 * G θ))
      = c4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hKGle' : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ)
      ≤ 5 * Work.Spaces.HkNorm α 4 f := by
    simpa only [hGdef, Work.Spaces.HkNorm] using hKGle
  calc |Work.Construction.L12dens f s|
      = |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ) / s| := by rw [hL12]
    _ = |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ| / s := by
        rw [abs_div, abs_of_pos hs]
    _ ≤ (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * f s θ|) / s := by
        gcongr
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (f := fun θ => Work.Spaces.K θ * f s θ)
    _ = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f s θ|) / s := by
        congr 1
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => by
          rw [abs_mul, abs_of_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ)]
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (c4 * G θ)) / s := by
        gcongr 1
        exact MeasureTheory.integral_mono_ae hKfInt hmajInt hmono
    _ = (c4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ)) / s := by rw [hpull]
    _ ≤ (c4 * (5 * Work.Spaces.HkNorm α 4 f)) / s := by
        gcongr
    _ = 20 * (Real.sqrt s / (1 + s) ^ 2) * Work.Spaces.HkNorm α 4 f := by
        rw [hc4]
        field_simp
        ring

end Work.FTS_RegExport.RXB
