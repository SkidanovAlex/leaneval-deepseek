import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.zHardyDefs
import Submission.Work.FTS.EllipticEst.zHardyCutDefs
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_exists
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The cutoff and its elementary properties -/

/-- The cutoff `zCut φ k` is `psiFun φ k` on `(0,∞)` and `0` on `(-∞,0]`; the second
convention makes `h = zCut φ k · g` vanish identically on `(-∞,1/k²]`, as required by the
support hypothesis of the compactly supported Hardy inequality. -/
def zCut (φ : ℝ → ℝ) (k : ℕ) (z : ℝ) : ℝ := if 0 < z then psiFun φ k z else 0

/-- A function which vanishes on a neighbourhood of `x` has derivative `0` at `x`. -/
theorem deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] 0) :
    deriv f x = 0 :=
  ((hasDerivAt_const (x := x) (c := 0)).congr_of_eventuallyEq h).deriv

/-- Two functions which agree on a neighbourhood of `x` have the same derivative at `x`. -/
theorem deriv_congr_of_eventuallyEq {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    deriv f x = deriv g x := h.deriv_eq

/-- On `(0,∞)` the cutoff `zCut φ k` is `psiFun φ k`. -/
theorem zCut_of_pos {φ : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : 0 < z) : zCut φ k z = psiFun φ k z := by
  simp only [zCut, if_pos hz]

/-- On `(-∞,0]` the cutoff `zCut φ k` vanishes. -/
theorem zCut_of_nonpos {φ : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : z ≤ 0) : zCut φ k z = 0 := by
  simp only [zCut, if_neg (not_lt.mpr hz)]

/-- The derivative of a `C^∞` function on `(0,∞)` is again `C^∞` there.  The order is the
*smooth* order `smoothOrder = ∞` (the literal `⊤` of `ContDiff` is the analytic order). -/
theorem contDiffOn_deriv_of_isOpen {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ smoothOrder f (Set.Ioi 0)) :
    ContDiffOn ℝ smoothOrder (deriv f) (Set.Ioi 0) :=
  hf.deriv_of_isOpen isOpen_Ioi (by simp [smoothOrder])

/-- The square of the weight `w(z) = (1+z)²/z²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) 2
    intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)
  simpa only [Work.Spaces.w] using h

/-- `m ↦ (m : ℝ) + 2` tends to `∞`. -/
theorem tendsto_natCast_add_two : Tendsto (fun m : ℕ => ((m : ℝ) + 2)) atTop atTop := by
  have h1 : Tendsto (fun m : ℕ => ((m + 2 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h1

/-! ## The radial weighted Hardy inequality

The boundary terms of `zHardy_pointwise` are killed here by replacing `g` with the
*logarithmically* localised functions `zCut φ k · g` (`H` below): those are compactly supported
inside `(0,∞)`, so that for them the flux `zFlux` has compact support and `∫ (zFlux)'(z) dz = 0`
*exactly*, with no boundary limit and no sequence of "good" points.  The price is the
commutator of the cutoff with `z ∂_z`, controlled by `|z ψ'_k| ≤ K / log k → 0`
(`ZCuts.zCut_props`), and one passes `k → ∞` by dominated convergence (dominated by `w² g²`,
which is integrable by hypothesis).  The constant obtained is `8` (`4` from the pointwise
inequality times `2` from `(a+b)² ≤ 2a² + 2b²`). -/

/-- **The radial weighted Hardy inequality.**  For every smooth `g` on `(0,∞)` with both
weighted integrals finite, `∫ w² g² ≤ 4 ∫ w² (z ∂_z g)²`, where `w z = (1+z)²/z²`.

The completion-of-squares identity is `zHardy_pointwise` in `Submission/Work/FTS/EllipticEst/zHardyDefs.lean`:
for `z > 0` and `h` differentiable at `z`,
`0 ≤ 4 w² (z h')² - w² h² + 4 (d/dz)(zFlux h)(z)` with `zFlux h z = zA z · h² · w² · z`,
`zA z = (z-3)/(2(1+z))`.  Integrating over `(ε, R)` and letting `ε ↓ 0`, `R ↑ ∞` along
sequences killing the boundary terms (`zA → -3/2` at `0` where `zFlux → 0` because
`∫w²h² < ∞` and `h` is continuous, `zA → 1/2` at `∞` where `zFlux ≥ 0` eventually) gives the
claim with constant `4`. -/
theorem zHardy_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ), ContDiffOn ℝ ⊤ g (Set.Ioi 0) →
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * g z ^ 2) Work.Spaces.Iz →
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * g z ^ 2)
      ≤ C * ∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2 := by
  refine ⟨8, by norm_num, ?_⟩
  intro g hg hD hF
  -- `g` is analytic (`ContDiffOn ℝ ⊤`), hence in particular `C^∞`
  have hg' : ContDiffOn ℝ smoothOrder g (Set.Ioi 0) := hg.of_le le_top
  have hIzF : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * g z ^ 2)
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * g z ^ 2 := by
    rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hIzD : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2)
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2 := by
    rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [hIzF, hIzD]
  set A : ℝ := ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * g z ^ 2 with hA
  set B : ℝ := ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2 with hB
  have hF' : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * g z ^ 2) (Set.Ioi 0) :=
    hF.mono_set Set.Ioi_subset_Ici_self
  have hD' : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2)
      (Set.Ioi 0) := hD.mono_set Set.Ioi_subset_Ici_self
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨φ, K, hφ⟩ := ZCuts.zCut_exists
  -- ## The main inequality at cutoff level `k ≥ 2`
  have hkey : ∀ k : ℕ, 2 ≤ k →
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (zCut φ k z * g z) ^ 2)
        ≤ 8 * (K / Real.log (k : ℝ)) ^ 2 * A + 8 * B := by
    intro k hk
    obtain ⟨hcdψ, hsuppψ, honeψ, hbddψ, hderψ⟩ := ZCuts.zCut_props hφ k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hK0 : 0 ≤ K := hφ.2.2.2.2.1
    set H : ℝ → ℝ := fun z => psiFun φ k z * g z with hH
    have hcdH : ContDiffOn ℝ smoothOrder H (Set.Ioi 0) := hcdψ.mul hg'
    have hcdh : ContDiffOn ℝ smoothOrder (fun z => zCut φ k z * g z) (Set.Ioi 0) :=
      hcdH.congr (fun z hz => by rw [hH, zCut_of_pos (show (0:ℝ) < z from hz)])
    have hsupp : ∀ z, z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z →
        (zCut φ k z * g z) = 0 := by
      intro z hz
      by_cases hz0 : 0 < z
      · have hψ : psiFun φ k z = 0 := by
          rcases hz with hz | hz
          · exact hsuppψ z hz0 (Or.inl hz)
          · exact hsuppψ z hz0 (Or.inr hz)
        simp only [zCut, if_pos hz0, hψ, zero_mul]
      · simp only [zCut, if_neg hz0, zero_mul]
    have ha : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
    have hab : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
      have h4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [h4]
    have hcore := ZCuts.zHardy_compact ha hab hcdh hsupp
    have hrew1 : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (zCut φ k z * g z) ^ 2)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * H z ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun z hz => by rw [hH, zCut_of_pos (show (0:ℝ) < z from hz)])
    have hrew2 : (∫ z in Set.Ioi 0,
          (Work.Spaces.w z) ^ 2 * (z * deriv (fun z => zCut φ k z * g z) z) ^ 2)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      have hev : (fun y => zCut φ k y * g y) =ᶠ[𝓝 z] H := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        rw [hH, zCut_of_pos (show (0:ℝ) < y from hy)]
      rw [deriv_congr_of_eventuallyEq hev]
    rw [hrew1, hrew2] at hcore
    -- bound the derivative term
    have hbnd : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2)
        ≤ 2 * (K / Real.log (k : ℝ)) ^ 2 * A + 2 * B := by
      have hpt : ∀ z ∈ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2),
          (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2
            ≤ 2 * (K / Real.log (k : ℝ)) ^ 2 * ((Work.Spaces.w z) ^ 2 * g z ^ 2)
              + 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) := by
        intro z hz
        have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
        have hdψ : DifferentiableAt ℝ (psiFun φ k) z :=
          (hcdψ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz0)
        have hdg : DifferentiableAt ℝ g z :=
          (hg.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz0)
        have hder : deriv H z = deriv (psiFun φ k) z * g z + psiFun φ k z * deriv g z := by
          rw [hH]
          exact deriv_mul hdψ hdg
        have hψsq1 : (psiFun φ k z) ^ 2 ≤ 1 := by
          have h1 := (hbddψ z).1
          have h2 := (hbddψ z).2
          nlinarith
        have hψb : (z * deriv (psiFun φ k) z) ^ 2 ≤ (K / Real.log (k : ℝ)) ^ 2 := by
          have hb0 : 0 ≤ K / Real.log (k : ℝ) := div_nonneg hK0 hlogk.le
          have h := hderψ z hz0
          rw [sq_le_sq, abs_of_nonneg hb0]
          exact h
        have hmain : (z * deriv H z) ^ 2
            ≤ 2 * (K / Real.log (k : ℝ)) ^ 2 * g z ^ 2 + 2 * (z * deriv g z) ^ 2 := by
          have hsplit : z * deriv H z
              = (z * deriv (psiFun φ k) z) * g z + (z * psiFun φ k z) * deriv g z := by
            rw [hder]; ring
          rw [hsplit]
          have hsq : ((z * deriv (psiFun φ k) z) * g z + (z * psiFun φ k z) * deriv g z) ^ 2
              ≤ 2 * ((z * deriv (psiFun φ k) z) * g z) ^ 2
                + 2 * ((z * psiFun φ k z) * deriv g z) ^ 2 := by
            nlinarith [sq_nonneg ((z * deriv (psiFun φ k) z) * g z
              - (z * psiFun φ k z) * deriv g z)]
          have hA1 : ((z * deriv (psiFun φ k) z) * g z) ^ 2
              ≤ (K / Real.log (k : ℝ)) ^ 2 * g z ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right hψb (sq_nonneg _)
          have hA2 : ((z * psiFun φ k z) * deriv g z) ^ 2 ≤ z ^ 2 * (deriv g z) ^ 2 := by
            have h1 : (z * psiFun φ k z) ^ 2 ≤ z ^ 2 := by
              rw [mul_pow]
              nlinarith [hψsq1, sq_nonneg z]
            calc ((z * psiFun φ k z) * deriv g z) ^ 2
                = (z * psiFun φ k z) ^ 2 * (deriv g z) ^ 2 := by ring
              _ ≤ z ^ 2 * (deriv g z) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          linarith [hsq, hA1, hA2]
        have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hfin := mul_le_mul_of_nonneg_left hmain hw2
        calc (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (2 * (K / Real.log (k : ℝ)) ^ 2 * g z ^ 2
                + 2 * (z * deriv g z) ^ 2) := hfin
          _ = 2 * (K / Real.log (k : ℝ)) ^ 2 * ((Work.Spaces.w z) ^ 2 * g z ^ 2)
                + 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) := by ring
      set G : ℝ → ℝ := fun z => 2 * (K / Real.log (k : ℝ)) ^ 2 * ((Work.Spaces.w z) ^ 2 * g z ^ 2)
          + 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) with hG
      have hG1 : IntegrableOn (fun z => 2 * (K / Real.log (k : ℝ)) ^ 2
          * ((Work.Spaces.w z) ^ 2 * g z ^ 2)) (Set.Ioi 0) :=
        hF'.const_mul (2 * (K / Real.log (k : ℝ)) ^ 2)
      have hG2 : IntegrableOn (fun z => 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2))
          (Set.Ioi 0) := hD'.const_mul 2
      have hGint : IntegrableOn G (Set.Ioi 0) := by
        rw [hG]
        exact hG1.add hG2
      have hGnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] G := by
        rw [hG]
        refine Filter.Eventually.of_forall (fun z => ?_)
        simp only [Pi.zero_apply]
        have h1 : 0 ≤ 2 * (K / Real.log (k : ℝ)) ^ 2 := by positivity
        have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 * g z ^ 2 := by positivity
        have h3 : 0 ≤ (Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2 := by positivity
        have h4 : 0 ≤ 2 * (K / Real.log (k : ℝ)) ^ 2 * ((Work.Spaces.w z) ^ 2 * g z ^ 2) :=
          mul_nonneg h1 h2
        have h5 : 0 ≤ 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) :=
          mul_nonneg (by norm_num) h3
        linarith
      have hdx : ContinuousOn (fun z : ℝ => deriv H z) (Set.Ioi 0) :=
        (contDiffOn_deriv_of_isOpen hcdH).continuousOn
      have hdgx : ContinuousOn (fun z : ℝ => deriv g z) (Set.Ioi 0) :=
        (contDiffOn_deriv_of_isOpen hg').continuousOn
      have hcf_cont : ContinuousOn
          (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2) (Set.Ioi 0) := by
        have h1 : ContinuousOn (fun z : ℝ => z * deriv H z) (Set.Ioi 0) :=
          continuousOn_id.mul hdx
        exact continuousOn_w_sq.mul (h1.pow 2)
      have hcG_cont : ContinuousOn G (Set.Ioi 0) := by
        rw [hG]
        refine ContinuousOn.add (ContinuousOn.mul (continuousOn_const) ?_)
          (ContinuousOn.mul continuousOn_const ?_)
        · exact continuousOn_w_sq.mul (hg.continuousOn.pow 2)
        · have h1 : ContinuousOn (fun z : ℝ => z * deriv g z) (Set.Ioi 0) :=
            continuousOn_id.mul hdgx
          exact continuousOn_w_sq.mul (h1.pow 2)
      have hsupp_f : ∀ x ∈ Set.Ioi 0 \ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2),
          (Work.Spaces.w x) ^ 2 * (x * deriv H x) ^ 2 = 0 := by
        intro x hx
        have hx0 : 0 < x := hx.1
        have hxa : x < 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 < x := by
          by_contra h
          push_neg at h
          exact hx.2 ⟨h.1, h.2⟩
        have hH0 : H =ᶠ[𝓝 x] 0 := by
          rcases hxa with h | h
          · filter_upwards [isOpen_Ioo.mem_nhds ⟨hx0, h⟩] with y hy
            have hψ : psiFun φ k y = 0 := hsuppψ y hy.1 (Or.inl hy.2.le)
            simp only [hH, hψ, zero_mul, Pi.zero_apply]
          · filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
            have hψ : psiFun φ k y = 0 :=
              hsuppψ y (lt_trans (lt_trans ha hab) hy) (Or.inr hy.le)
            simp only [hH, hψ, zero_mul, Pi.zero_apply]
        have hdH : deriv H x = 0 := deriv_eq_zero_of_eventuallyEq_zero hH0
        rw [hdH]
        ring
      have hIf : IntervalIntegrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2)
          volume (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) :=
        (hcf_cont.mono (by
          rw [uIcc_of_le hab.le]
          exact fun x hx => lt_of_lt_of_le ha hx.1)).intervalIntegrable
      have hIG : IntervalIntegrable G volume (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) :=
        (hcG_cont.mono (by
          rw [uIcc_of_le hab.le]
          exact fun x hx => lt_of_lt_of_le ha hx.1)).intervalIntegrable
      have hmono : (∫ z in (1 / (k : ℝ) ^ 2)..((k : ℝ) ^ 2),
            (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2)
          ≤ ∫ z in (1 / (k : ℝ) ^ 2)..((k : ℝ) ^ 2), G z :=
        intervalIntegral.integral_mono_on hab.le hIf hIG hpt
      have hmono2 : (∫ z in Set.Ioc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2), G z)
          ≤ ∫ z in Set.Ioi 0, G z := by
        refine MeasureTheory.setIntegral_mono_set hGint hGnonneg ?_
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        exact lt_trans ha hx.1
      calc (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2)
          = ∫ z in Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2),
              (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2 :=
            setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
              (fun z hz => lt_of_lt_of_le ha hz.1) hsupp_f
        _ = ∫ z in (1 / (k : ℝ) ^ 2)..((k : ℝ) ^ 2),
              (Work.Spaces.w z) ^ 2 * (z * deriv H z) ^ 2 := by
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab.le]
        _ ≤ ∫ z in (1 / (k : ℝ) ^ 2)..((k : ℝ) ^ 2), G z := hmono
        _ = ∫ z in Set.Ioc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2), G z :=
            intervalIntegral.integral_of_le hab.le
        _ ≤ ∫ z in Set.Ioi 0, G z := hmono2
        _ = 2 * (K / Real.log (k : ℝ)) ^ 2 * A + 2 * B := by
            rw [hG, hA, hB, MeasureTheory.integral_add hG1 hG2,
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
            try ring
    linarith [hcore, hbnd]
  -- ## Transfer to the index `m + 2` and take the limit
  have hkey2 : ∀ m : ℕ,
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (zCut φ (m + 2) z * g z) ^ 2)
        ≤ 8 * (K / Real.log ((m : ℝ) + 2)) ^ 2 * A + 8 * B := by
    intro m
    have h := hkey (m + 2) (by omega)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hDCT : Tendsto (fun m : ℕ =>
      ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (zCut φ (m + 2) z * g z) ^ 2) atTop (𝓝 A) := by
    rw [hA]
    refine tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioi 0))
      (F := fun m : ℕ => fun z => (Work.Spaces.w z) ^ 2 * (zCut φ (m + 2) z * g z) ^ 2)
      (f := fun z => (Work.Spaces.w z) ^ 2 * g z ^ 2)
      (fun z => (Work.Spaces.w z) ^ 2 * g z ^ 2) ?_ hF' ?_ ?_
    · intro m
      have hψcd : ContDiffOn ℝ smoothOrder (psiFun φ (m + 2)) (Set.Ioi 0) :=
        (ZCuts.zCut_props hφ (m + 2) (by omega)).1
      have hcont : ContinuousOn
          (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (zCut φ (m + 2) z * g z) ^ 2) (Set.Ioi 0) := by
        have h1 : ContinuousOn (fun z : ℝ => zCut φ (m + 2) z * g z) (Set.Ioi 0) :=
          (hψcd.mul hg').continuousOn.congr
            (fun z hz => by rw [zCut_of_pos (show (0:ℝ) < z from hz)])
        exact continuousOn_w_sq.mul (h1.pow 2)
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · intro m
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      have hbb := (ZCuts.zCut_props hφ (m + 2) (by omega)).2.2.2.1 a
      have hzc : zCut φ (m + 2) a = psiFun φ (m + 2) a := zCut_of_pos ha
      rw [hzc, Real.norm_eq_abs]
      have hψ2 : (psiFun φ (m + 2) a) ^ 2 ≤ 1 := by
        have h1 := hbb.1
        have h2 := hbb.2
        nlinarith
      have hw2 : 0 ≤ (Work.Spaces.w a) ^ 2 := sq_nonneg _
      have hnn : 0 ≤ (Work.Spaces.w a) ^ 2 * (psiFun φ (m + 2) a * g a) ^ 2 := by positivity
      rw [abs_of_nonneg hnn]
      have hstep : (psiFun φ (m + 2) a) ^ 2 * g a ^ 2 ≤ 1 * g a ^ 2 :=
        mul_le_mul_of_nonneg_right hψ2 (sq_nonneg _)
      calc (Work.Spaces.w a) ^ 2 * (psiFun φ (m + 2) a * g a) ^ 2
          = (Work.Spaces.w a) ^ 2 * ((psiFun φ (m + 2) a) ^ 2 * g a ^ 2) := by
            rw [mul_pow]
        _ ≤ (Work.Spaces.w a) ^ 2 * (1 * g a ^ 2) := mul_le_mul_of_nonneg_left hstep hw2
        _ = (Work.Spaces.w a) ^ 2 * g a ^ 2 := by ring
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      have ha0 : 0 < a := ha
      have h2 : Tendsto (fun m : ℕ => ((m : ℝ) + 2)) atTop atTop := tendsto_natCast_add_two
      have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop h2
      have hev : ∀ᶠ m : ℕ in atTop, zCut φ (m + 2) a = 1 := by
        filter_upwards [h1.eventually (Iic_mem_nhds ha0), h2.eventually_ge_atTop a] with m hm1 hm2
        have hψ : psiFun φ (m + 2) a = 1 := by
          refine (ZCuts.zCut_props hφ (m + 2) (by omega)).2.2.1 a ha0 ?_ ?_
          · simpa only [Nat.cast_add, Nat.cast_ofNat] using hm1
          · simpa only [Nat.cast_add, Nat.cast_ofNat] using hm2
        rw [zCut_of_pos ha0, hψ]
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hev] with m hm
      rw [hm, one_mul]
  have hlimRHS : Tendsto (fun m : ℕ => 8 * (K / Real.log ((m : ℝ) + 2)) ^ 2 * A + 8 * B)
      atTop (𝓝 (8 * B)) := by
    have hlog : Tendsto (fun m : ℕ => Real.log ((m : ℝ) + 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_add_two
    have hq : Tendsto (fun m : ℕ => K / Real.log ((m : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hq2 : Tendsto (fun m : ℕ => (K / Real.log ((m : ℝ) + 2)) ^ 2) atTop (𝓝 0) := by
      simpa using hq.pow 2
    have h2 : Tendsto (fun m : ℕ => 8 * (K / Real.log ((m : ℝ) + 2)) ^ 2 * A) atTop (𝓝 0) := by
      have h := (hq2.mul (tendsto_const_nhds (x := A))).const_mul 8
      simpa only [zero_mul, mul_zero, mul_assoc] using h
    have h3 := h2.add (tendsto_const_nhds (x := 8 * B))
    simpa only [zero_add] using h3
  exact le_of_tendsto_of_tendsto' hDCT hlimRHS hkey2

end Work.FTS.EllipticEst

end
