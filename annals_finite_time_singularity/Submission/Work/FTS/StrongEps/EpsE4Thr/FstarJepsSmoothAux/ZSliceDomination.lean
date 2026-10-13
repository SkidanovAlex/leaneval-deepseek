import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.abs_le_sqrt_interval_integral
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.zSlice_sq_le_marginal
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.integrableOn_theta_marginal_HkIntegrand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Domination of a `z`-slice family by an integrable function of `θ`

Given `W` smooth on the open quadrant and `W ∈ ℋ¹`, and a compact interval `[a,b] ⊂ (0,∞)`
of radii, there is a *single* function `G` of the angle, integrable on `(0,π/2)`, which
dominates all the slices `θ ↦ W z θ`, `z ∈ [a,b]`.

The proof is the one-dimensional Agmon/Morrey argument in the radial variable, at fixed
angle: for `z ∈ [a,b]` and `θ ∈ (0,π/2)` the fundamental theorem of calculus gives

  `|W z θ| ≤ √(∫_J W(·,θ)²) / √L + √L · √(∫_J ∂_zW(·,θ)²)`,   `J = [a,b+1]`, `L = |J|`,

and the two `L²`-norms over `J` are bounded by the angular marginal `∫_J HkIntegrand`
(using `w z ≥ 1`, `sin(2θ)^{η/2} ≤ 1` and `z ≥ a`).  Since

  `√(A·Φ) ≤ (A + Φ)/2`   (`A ≥ 0`, `Φ ≥ 0`),

the dominating function may be taken to be a *sum*, `C · (1 + Φ(θ))`, whose integral over
`(0,π/2)` is finite because `Φ` is integrable there (Tonelli applied to the two conjuncts of
`HkMem α 1 W`).
-/

/-- An interval integral is the integral over the corresponding closed set. -/
private theorem intervalIntegral_eq_setIntegral_Icc {c d : ℝ} (h : c ≤ d) (f : ℝ → ℝ) :
    (∫ x in c..d, f x) = ∫ x in Set.Icc c d, f x := by
  rw [intervalIntegral.integral_of_le h, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The `ℋ^k`-integrand is nonnegative. -/
private theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  exact add_nonneg (Work.Spaces.hkZSum_nonneg α k f z θ)
    (Work.Spaces.hkMixedSum_nonneg α k f z θ)

/-- The constant of the domination estimate. -/
private noncomputable def zSliceConst (a b : ℝ) : ℝ :=
  (1 / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a)) * Real.sqrt (1 / min 1 (a ^ 2))

private theorem zSliceConst_nonneg {a b : ℝ} (_ha : 0 < a) (hab : a ≤ b) :
    0 ≤ zSliceConst a b := by
  have hL : 0 < b + 1 - a := by linarith
  have hLnn : 0 ≤ Real.sqrt (b + 1 - a) := Real.sqrt_nonneg _
  rw [zSliceConst]
  exact mul_nonneg (add_nonneg (div_nonneg zero_le_one hLnn) hLnn)
    (Real.sqrt_nonneg _)

theorem ZSliceDomination {α : ℝ} {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ G : ℝ → ℝ, MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2)) ∧
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ := by
  have hLpos : 0 < b + 1 - a := by linarith
  have hmpos : 0 < min 1 (a ^ 2) := lt_min one_pos (pow_pos ha 2)
  have hminv : 0 ≤ 1 / min 1 (a ^ 2) := le_of_lt (one_div_pos.mpr hmpos)
  have hφint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ∫ z in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_theta_marginal_HkIntegrand hsm hmem ha (by linarith)
  refine ⟨fun θ => (zSliceConst a b + 1) *
      (1 + ∫ z in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W z θ), ?_, ?_⟩
  · -- integrability of the majorant
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (Real.pi / 2)) :=
      integrableOn_const (C := 1) measure_Ioo_lt_top.ne
    have h2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (1 : ℝ) + ∫ z in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W z θ)
        (Set.Ioo 0 (Real.pi / 2)) := h1.add hφint
    exact h2.integrable.const_mul (zSliceConst a b + 1)
  · intro z hz θ hθ
    have hzJ : z ∈ Set.Icc a (b + 1) := ⟨hz.1, by linarith [hz.2]⟩
    have hder : ∀ x ∈ Set.Icc a (b + 1),
        HasDerivAt (fun x' : ℝ => W x' θ) (Work.Spaces.pz W x θ) x :=
      fun x hx => hsm.hasDerivAt_slice hθ (by linarith [hx.1])
    have hg'cont : ContinuousOn (fun x : ℝ => Work.Spaces.pz W x θ) (Set.Icc a (b + 1)) :=
      ((hsm.pz).curry_z hθ).continuousOn.mono (fun x hx => lt_of_lt_of_le ha hx.1)
    have hAb := abs_le_sqrt_interval_integral (c := a) (d := b + 1)
      (by linarith : a < b + 1) hder hg'cont z hzJ
    rw [intervalIntegral_eq_setIntegral_Icc (c := a) (d := b + 1) (by linarith : a ≤ b + 1)
        (fun x => (W x θ) ^ 2),
      intervalIntegral_eq_setIntegral_Icc (c := a) (d := b + 1) (by linarith : a ≤ b + 1)
        (fun x => (Work.Spaces.pz W x θ) ^ 2)] at hAb
    let A : ℝ := ∫ x in Set.Icc a (b + 1), (W x θ) ^ 2
    let B : ℝ := ∫ x in Set.Icc a (b + 1), (Work.Spaces.pz W x θ) ^ 2
    let Φ : ℝ := ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ
    have hA0 : 0 ≤ A := by
      show 0 ≤ ∫ x in Set.Icc a (b + 1), (W x θ) ^ 2
      exact setIntegral_nonneg measurableSet_Icc (fun x _ => sq_nonneg _)
    have hB0 : 0 ≤ B := by
      show 0 ≤ ∫ x in Set.Icc a (b + 1), (Work.Spaces.pz W x θ) ^ 2
      exact setIntegral_nonneg measurableSet_Icc (fun x _ => sq_nonneg _)
    have hΦ0 : 0 ≤ Φ := by
      show 0 ≤ ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ
      exact setIntegral_nonneg measurableSet_Icc (fun x _ => HkIntegrand_nonneg α 1 W x θ)
    have hAB : A + B ≤ (1 / min 1 (a ^ 2)) * Φ := by
      show (∫ x in Set.Icc a (b + 1), (W x θ) ^ 2)
          + (∫ x in Set.Icc a (b + 1), (Work.Spaces.pz W x θ) ^ 2)
          ≤ (1 / min 1 (a ^ 2)) * ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ
      exact zSlice_sq_le_marginal hsm hmem ha (by linarith) hθ
    have hAle : A ≤ (1 / min 1 (a ^ 2)) * Φ := le_trans (le_add_of_nonneg_right hB0) hAB
    have hBle : B ≤ (1 / min 1 (a ^ 2)) * Φ := le_trans (le_add_of_nonneg_left hA0) hAB
    have hsqrtA : Real.sqrt A ≤ Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
      calc Real.sqrt A ≤ Real.sqrt ((1 / min 1 (a ^ 2)) * Φ) := Real.sqrt_le_sqrt hAle
        _ = Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := Real.sqrt_mul hminv Φ
    have hsqrtB : Real.sqrt B ≤ Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
      calc Real.sqrt B ≤ Real.sqrt ((1 / min 1 (a ^ 2)) * Φ) := Real.sqrt_le_sqrt hBle
        _ = Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := Real.sqrt_mul hminv Φ
    have hbnd : |W z θ| ≤ zSliceConst a b * Real.sqrt Φ := by
      have hLnn : 0 ≤ Real.sqrt (b + 1 - a) := Real.sqrt_nonneg _
      have hstep : Real.sqrt A / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a) * Real.sqrt B
          ≤ (1 / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a))
              * Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
        have e1 : Real.sqrt A / Real.sqrt (b + 1 - a)
            ≤ (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ) / Real.sqrt (b + 1 - a) :=
          div_le_div_of_nonneg_right hsqrtA hLnn
        have e2 : Real.sqrt (b + 1 - a) * Real.sqrt B
            ≤ Real.sqrt (b + 1 - a) * (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ) :=
          mul_le_mul_of_nonneg_left hsqrtB hLnn
        have hid : (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ) / Real.sqrt (b + 1 - a)
            + Real.sqrt (b + 1 - a) * (Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ)
            = (1 / Real.sqrt (b + 1 - a) + Real.sqrt (b + 1 - a))
              * Real.sqrt (1 / min 1 (a ^ 2)) * Real.sqrt Φ := by
          ring
        linarith [e1, e2, hid]
      rw [zSliceConst]
      exact le_trans hAb hstep
    have hsqrtle : Real.sqrt Φ ≤ 1 + Φ := by
      nlinarith [Real.sq_sqrt hΦ0, Real.sqrt_nonneg Φ, sq_nonneg (Real.sqrt Φ - 1 / 2)]
    have hCnn : 0 ≤ zSliceConst a b := zSliceConst_nonneg ha hab
    have hs1 : zSliceConst a b * Real.sqrt Φ ≤ zSliceConst a b * (1 + Φ) :=
      mul_le_mul_of_nonneg_left hsqrtle hCnn
    have hs2 : zSliceConst a b * (1 + Φ) ≤ (zSliceConst a b + 1) * (1 + Φ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hgoal : |W z θ| ≤ (zSliceConst a b + 1) * (1 + Φ) := by
      linarith [hbnd, hs1, hs2]
    show |W z θ| ≤ (zSliceConst a b + 1)
      * (1 + ∫ x in Set.Icc a (b + 1), Work.Spaces.HkIntegrand α 1 W x θ)
    exact hgoal

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
