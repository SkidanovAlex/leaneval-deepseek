/-
Copyright: work module for the Elgindi finite-time singularity project.

# The open-quadrant assembly for `|Ḡ(α,F)·sin 2θ|_{H^k} ≤ C|F|_{H^k}`

Adapted (namespace `Work.FTS.EllipticEst.Cert.GbarSin`) from the team scratch development
`Submission/Work/FTS/EllipticEst/_gbar_open_int.lean`: the three deferred steps
`FstarDzIter_chain_open` and `HarOp_eq_sub_of_chain` are now imported from their own modules
instead of being `sorry` placeholders, and the weighted Hardy inequality is proved here in the
form `HarOp_weighted_integral_cont` (measurability of the source from the continuity of its
primitive) rather than imported.

This module proves `Work.FTS.EllipticEst.Gbar_Hk_le_open`: for every `k` there is `C > 0`,
independent of `α ∈ (0,1]`, such that

  `|Ḡ(α,F)·sin 2θ|_{H^k} ≤ C |F|_{H^k}`

for every source `F` which is `C^∞` on the **open** quadrant `Q0 = (0,∞) × (0,π/2)` (the class
`Work.FTS.EllipticEst.SmoothOpen`, i.e. the raw shape `∀ n, ContDiffOn ℝ n (uncurry F) Q0` of
the statement) and which lies in `ℋ^k` (`Work.Spaces.HkMem`).  This is the open-quadrant
counterpart of `Work.FTS.EllipticEst.Gbar_Hk_fts`, which assumes smoothness on a neighbourhood
of the *closed* quadrant.

## Mathematic

Write `β = 5/α`, `c = -(3/(4α))`, `Ḡ = Ḡ(α,F)`, and for `j ≤ k` let

  `U_j = F_*(D_z^j F)`,  `A_j = ∫_θ (D_z^j F · w/sin(2θ)^{η/2})²`

be the angular moment of the `j`-th `D_z`-iterate of the source and the `j`-th weighted
`L²`-slice.  The `H^k` norm of the target is controlled by the radial derivatives of `Ḡ`
(`gbar_HkIntegrand_target_le`), so it suffices to bound `∫_z w²(D_z^j Ḡ)²` for `j ≤ k`.  The
chain of facts is

1. (Cauchy–Schwarz, `FstarDzIter_sq_mul_w_le_open`)
   `(U_j z)² w(z)² ≤ (π/2) A_j(z)`;
2. (chain rule, `FstarDzIter_chain_open`) `U_j z - U_j s = ∫_s^z U_{j+1}(r)/r dr` for `j+1 ≤ k`;
   this makes `U_j` (an absolutely continuous primitive of a locally integrable function) a
   *continuous* function on `(0,∞)` for `j+1 ≤ k`
   (`continuousOn_of_primitive_of_sqrt_bound`);
3. consequently `D_z(Ḡ) = c·(U_0 - β HarOp β U_0)` etc. — differentiating the Hardy operator is
   legitimate (`rDz_HarOp_of_continuousAt`) and the integration by parts
   (`HarOp_eq_sub_of_chain`) converts `U_j - β HarOp β U_j` into `HarOp β U_{j+1}`;
   induction gives the exact radial identity `D_z^j Ḡ = c·HarOp β U_j` on `(0,∞)`
   (`rDzIter_Gbar_eq_open`);
4. (weighted Hardy inequality, `HarOp_weighted_integral_cont`)
   `∫ w²(HarOp β U_j)² ≤ (100/β²) ∫ w² U_j²`;
   the factor `1/β²` cancels the explicit `1/α²` in `c²` and makes the constant of the estimate
   `α`-independent.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllipticEst.DthIter_mul_of_angular
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.continuousOn_of_primitive_of_sqrt_bound
import Submission.Work.FTS.EllipticEst.rDz_HarOp_of_continuousAt
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HarOp_eq_sub_of_chain
import Submission.Work.FTS.EllipticEst.HarOp_weighted_lintegral
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarSin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The angular weight is continuous -/

theorem gbar_continuousOn_sinCos2 :
    ContinuousOn Work.Elliptic.sinCos2 (Set.Icc 0 (π / 2)) := by
  unfold Work.Elliptic.sinCos2; fun_prop

/-! ## The angular constants -/

/-- A uniform (in `α ∈ (0,1]`) bound for `(D_θ^i sin 2θ)² sin(2θ)^{-γ}`. -/
noncomputable def gbar_angC (i : ℕ) : ℝ := Classical.choose (sinIter_weight_bound i)

theorem gbar_angC_nonneg (i : ℕ) : 0 ≤ gbar_angC i :=
  (Classical.choose_spec (sinIter_weight_bound i)).1

theorem gbar_angC_bound (i : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ gbar_angC i :=
  (Classical.choose_spec (sinIter_weight_bound i)).2 α hα hα1 θ hθ

/-- The angular constant of the estimate of order `k`. -/
noncomputable def gbar_Kang (k : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range (k + 1), gbar_angC i

theorem gbar_Kang_pos (k : ℕ) : 0 < gbar_Kang k := by
  have h : 0 ≤ ∑ i ∈ Finset.range (k + 1), gbar_angC i :=
    Finset.sum_nonneg fun i _ => gbar_angC_nonneg i
  simp only [gbar_Kang]
  linarith

/-! ## Elementary angular facts -/

theorem gbar_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- `sin(2θ)² / (sin(2θ)^{η/2})² ≤ 1` on the angular interval. -/
theorem gbar_sin_two_ratio_sq_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 / ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
  have hs_nn := gbar_sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs_nn with hs | hs
  · rw [← hs]
    simp
  · have hpow : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    have hnum : (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    rw [hpow, hnum, ← Real.rpow_sub hs (y := (2 : ℝ)) (z := Work.Spaces.eta)]
    exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by
      have h := Work.Spaces.eta_lt_one; linarith)

/-- The first-sum term of the target `H^k`-integrand is bounded by `A² w²`. -/
theorem gbar_sin_two_term_le (A w : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (A * Real.sin (2 * θ) * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ A ^ 2 * w ^ 2 := by
  have hs_nn := gbar_sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs_nn with hs | hs
  · rw [← hs, mul_zero, zero_mul, show (0 : ℝ) ^ 2 = 0 by norm_num]
    exact mul_nonneg (sq_nonneg A) (sq_nonneg w)
  · have hratio := gbar_sin_two_ratio_sq_le_one hθ
    have he : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hs _)
    calc (A * Real.sin (2 * θ) * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = A ^ 2 * w ^ 2 *
            ((Real.sin (2 * θ)) ^ 2 / ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2) := by
          simp only [mul_pow, div_pow]
          ring
      _ ≤ A ^ 2 * w ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg (sq_nonneg A) (sq_nonneg w))
      _ = A ^ 2 * w ^ 2 := by ring

/-- The mixed term of the target `H^k`-integrand is bounded by `w² · angC i · A²`. -/
theorem gbar_sinIter_Wt_term_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) (A z : ℝ)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (A * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * gbar_angC i * A ^ 2 := by
  have hb := gbar_angC_bound i α hα hα1 hθ
  have hs_nn := gbar_sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs_nn with hs | hs
  · have hW : Work.Spaces.Wt α z θ = 0 := by
      rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hs,
        Real.zero_rpow (show -(Work.Spaces.gam α / 2) ≠ 0 by
          have hg := Work.Spaces.gam_pos hα
          intro hc
          linarith [neg_eq_zero.mp hc]),
        mul_zero]
    rw [hW, mul_zero, show (0 : ℝ) ^ 2 = 0 by norm_num]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (gbar_angC_nonneg i)) (sq_nonneg A)
  · have hpow : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    calc (A * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * A ^ 2 *
            ((sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hpow]
          ring
      _ ≤ (Work.Spaces.w z) ^ 2 * A ^ 2 * gbar_angC i :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Work.Spaces.w z) ^ 2 * gbar_angC i * A ^ 2 := by ring

/-! ## The factorisations of the `D`-derivatives of the target -/

theorem gbar_DzIter_target_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      = rDzIter i (Work.Elliptic.Gbar α F) z * Real.sin (2 * θ) :=
  DzIter_mul_of_radial i (Work.Elliptic.Gbar α F) (fun θ => Real.sin (2 * θ)) z θ

theorem gbar_DthIter_target_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      = fun z θ => Work.Elliptic.Gbar α F z * sinIter i θ := by
  funext z θ
  rw [DthIter_mul_of_angular i (Work.Elliptic.Gbar α F) (fun θ => Real.sin (2 * θ)) z θ]
  rfl

theorem gbar_mixed_target_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      = rDzIter j (Work.Elliptic.Gbar α F) z * sinIter i θ := by
  simp only [Work.Spaces.mixed]
  rw [gbar_DthIter_target_eq α F i]
  exact DzIter_mul_of_radial j (Work.Elliptic.Gbar α F) (fun θ => sinIter i θ) z θ

/-! ## The pointwise comparison of the `H^k`-integrands -/

theorem gbar_HkIntegrand_target_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      ≤ gbar_Kang k * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
          * ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∑ j ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [gbar_DzIter_target_eq α F i z θ]
    calc (rDzIter i (Work.Elliptic.Gbar α F) z * Real.sin (2 * θ)
          * ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (rDzIter i (Work.Elliptic.Gbar α F) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          gbar_sin_two_term_le _ _ hθ
      _ = (Work.Spaces.w z) ^ 2 * (rDzIter i (Work.Elliptic.Gbar α F) z) ^ 2 := by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * gbar_angC i * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, gbar_mixed_target_eq α F j i z θ]
            exact gbar_sinIter_Wt_term_le α hα hα1 i _ z hθ
          · rw [if_neg hc]
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (gbar_angC_nonneg i)) (sq_nonneg _)
      _ = (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
            (∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
          calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  (Work.Spaces.w z) ^ 2 * gbar_angC i *
                    (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
              = ∑ i ∈ Finset.range (k + 1), ((Work.Spaces.w z) ^ 2 * gbar_angC i) *
                  (∑ j ∈ Finset.range (k + 1),
                    (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
            _ = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.w z) ^ 2 * gbar_angC i) *
                  (∑ j ∈ Finset.range (k + 1),
                    (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
                rw [Finset.sum_mul]
            _ = (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
                  (∑ j ∈ Finset.range (k + 1),
                    (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
                have e1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.w z) ^ 2 * gbar_angC i)
                    = (Work.Spaces.w z) ^ 2 * ∑ i ∈ Finset.range (k + 1), gbar_angC i :=
                  (Finset.mul_sum _ _ _).symm
                have e2 : (∑ j ∈ Finset.range (k + 1),
                      (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
                    = (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
                      (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 :=
                  (Finset.mul_sum _ _ _).symm
                rw [e1, e2]
                ring
  rw [Work.Spaces.HkIntegrand]
  have htot : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
          * ((Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ (1 + ∑ i ∈ Finset.range (k + 1), gbar_angC i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by
    calc _ ≤ (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
          + (∑ i ∈ Finset.range (k + 1), gbar_angC i) *
            (∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) :=
          add_le_add h1 h2
      _ = (1 + ∑ i ∈ Finset.range (k + 1), gbar_angC i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) := by ring
  refine htot.trans (le_of_eq ?_)
  have e2 : (∑ j ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := (Finset.mul_sum _ _ _).symm
  rw [e2]
  simp only [gbar_Kang]
  ring

/-! ## The angular moment `U_j` and the weighted slice `A_j` -/

/-- The angular moment `U_j = F_*(D_z^j F)` of the `j`-th `D_z`-iterate of the source. -/
noncomputable def Uj (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z

/-- The `j`-th weighted `L²`-slice `A_j = ∫_θ (D_z^j F · w/sin(2θ)^{η/2})²`. -/
noncomputable def Aj (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

@[simp] theorem Uj_apply (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Uj F j z = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z := rfl

@[simp] theorem Aj_apply (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Aj F j z = ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl

/-- The `j`-th summand of the `H^k`-integrand is integrable on the angular slice and is
dominated by the whole `H^k`-integrand. -/
theorem Aj_le_HkIntegrand_integral (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Aj F j z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
  rw [Aj_apply]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 z hz) (Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k F z θ j hj)

/-- `(0,∞)` and `[0,∞)` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  exact Measure.restrict_congr_set Ioi_ae_eq_Ici

/-- The `z ↦ A_j(z)` is a.e. strongly measurable. -/
theorem Aj_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (Aj F j) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (Function.uncurry fun z θ : ℝ =>
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
    (hF.continuousOn_summand j).pow 2
  have h := aestronglyMeasurable_integral_Itheta_Q0
    (fun z θ : ℝ => (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    hg (fun _ : ℝ => (1 : ℝ)) continuousOn_const
  change AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) _
  simpa only [mul_one] using h

/-- The angular moment `z ↦ U_j(z)` is a.e. strongly measurable. -/
theorem Uj_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (Uj F j) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (Function.uncurry (Work.Spaces.DzIter j F)) Q0 :=
    (hF.DzIter j).continuousOn
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter j F) hg
    Work.Elliptic.sinCos2 gbar_continuousOn_sinCos2
  change AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ) _
  simpa only [mul_one] using h

/-- The slice functional `A_j` is integrable on `(0,∞)`, with integral bounded by `HkSq`. -/
theorem Aj_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (Aj F j) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, Aj F j z) ≤ Work.Spaces.HkSq α k F := by
  have hmaj : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    rw [restrict_Ioi_eq_restrict_Iz]
    exact hmem.2
  refine ⟨?_, ?_⟩
  · refine hmaj.mono' (Aj_aesm α k F hF j) ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ‖Aj F j z‖ ≤ _
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
    rw [Aj_apply, Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact Aj_le_HkIntegrand_integral α k F hmem j hj hzI
  · have h1 : (∫ z in Set.Ioi 0, Aj F j z)
        ≤ ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
        integral_nonneg fun θ => sq_nonneg _) hmaj ?_
      show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), _
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun z hz =>
        Aj_le_HkIntegrand_integral α k F hmem j hj (by
          rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz))
    refine h1.trans (le_of_eq ?_)
    rw [Work.Spaces.HkSq, restrict_Ioi_eq_restrict_Iz]

/-! ## Preliminaries: square-root bounds and integrability -/

/-- For a nonnegative integrable function on a finite-measure set, its square root is
integrable. -/
theorem integrableOn_sqrt {A : ℝ → ℝ} {S : Set ℝ} (hSmeas : MeasurableSet S)
    (hS : volume S ≠ ⊤) (hA : IntegrableOn A S) (hAnn : ∀ r ∈ S, 0 ≤ A r) :
    IntegrableOn (fun r => Real.sqrt (A r)) S := by
  refine Integrable.mono' ((integrableOn_const (s := S) (C := (1 : ℝ)) hS).add hA)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable) ?_
  · show ∀ᵐ r ∂(volume.restrict S), ‖Real.sqrt (A r)‖ ≤ (1 : ℝ) + A r
    rw [ae_restrict_iff' hSmeas]
    refine Eventually.of_forall fun r hr => ?_
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_iff.mpr ⟨by linarith [hAnn r hr],
      by nlinarith [hAnn r hr, sq_nonneg (A r)]⟩

/-- The Cauchy–Schwarz bound `|U_j z| ≤ √(π/2)·√(A_j z)/w(z)`. -/
theorem Uj_sqrt_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    |Uj F j z| ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z := by
  have hsq : (Uj F j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (π / 2) * Aj F j z :=
    FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hz
  have hA0 : 0 ≤ Aj F j z := integral_nonneg fun θ => sq_nonneg _
  have hw0 : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hdiv : (Uj F j z) ^ 2 ≤ ((π / 2) * Aj F j z) / (Work.Spaces.w z) ^ 2 :=
    (le_div_iff₀ (pow_pos hw0 2)).mpr hsq
  have hTnn : 0 ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z := by positivity
  have hTsq : (Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z) ^ 2
      = ((π / 2) * Aj F j z) / (Work.Spaces.w z) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hA0]
  have hU2 : (Uj F j z) ^ 2 ≤ (Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z) ^ 2 := by
    rw [hTsq]; exact hdiv
  calc |Uj F j z| = Real.sqrt ((Uj F j z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z) ^ 2) :=
        Real.sqrt_le_sqrt hU2
    _ = Real.sqrt (π / 2) * Real.sqrt (Aj F j z) / Work.Spaces.w z := Real.sqrt_sq hTnn

/-- The Cauchy–Schwarz bound `(U_j z)² w(z)² ≤ (π/2) A_j(z)`, integrated. -/
theorem Uj_sq_mul_w_integrable (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2)
        ≤ (π / 2) * Work.Spaces.HkSq α k F := by
  have hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    rw [restrict_Ioi_eq_restrict_Iz]
    exact hmem.2
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2 ≤ (π / 2) *
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
    have h1 : (Uj F j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (π / 2) * Aj F j z :=
      FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hz
    have h2 := Aj_le_HkIntegrand_integral α k F hmem j hj hzI
    calc (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2
        = (Uj F j z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ (π / 2) * Aj F j z := h1
      _ ≤ (π / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
    rw [hfun]
    refine ContinuousOn.pow ?_ 2
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hz)))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) (volume.restrict (Set.Ioi 0)) :=
    (hw2.aestronglyMeasurable measurableSet_Ioi).mul ((Uj_aesm α k F hF j).pow 2)
  have hmaj : IntegrableOn (fun z => (π / 2) *
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)) (Set.Ioi 0) :=
    hB.const_mul _
  refine ⟨hmaj.mono' haesm ?_, ?_⟩
  · show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ‖(Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2‖ ≤ _
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpoint z hz
  · have hInt : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2)
        ≤ ∫ z in Set.Ioi 0, (π / 2) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hmaj ?_
      show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), _
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun z hz => hpoint z hz
    refine hInt.trans (le_of_eq ?_)
    rw [integral_const_mul, Work.Spaces.HkSq, restrict_Ioi_eq_restrict_Iz]

/-! ## Continuity of the angular moments -/

theorem Uj_continuousOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (Uj F j) (Set.Ioi 0) := by
  refine continuousOn_of_primitive_of_sqrt_bound (u := Uj F j) (v := Uj F (j + 1))
    (A := Aj F (j + 1)) (Aj_integrableOn α k F hF hmem (j + 1) hj).1 ?_ ?_
  · intro r hr
    exact Uj_sqrt_bound α k F hF hmem (j + 1) hj hr
  · intro s z hs hsz
    exact FstarDzIter_chain_open α k F hF hmem j hj hs hsz


/-! ## Integrability of the `D_z^j Ḡ` and the radial identity -/

/-- The integral of a constant over `Iθ`. -/
theorem gbar_integral_Iθ_const (c : ℝ) :
    (∫ θ in Work.Spaces.Iθ, c) = (π / 2) * c := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  rw [hvol]

/-- A finite sum of integrable functions is integrable. -/
theorem gbar_integrable_finsetSum (μ : Measure ℝ) (s : Finset ℕ) (f : ℕ → ℝ → ℝ)
    (h : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integrable_zero (α := ℝ) (μ := μ))
  | insert a s ha ih =>
      have hsum : (fun z => ∑ i ∈ insert a s, f i z)
          = (fun z => f a z + ∑ i ∈ s, f i z) := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsum]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `s^(β-1)·U_j` is interval integrable on `[0,z]`. -/
theorem intervalIntegrable_rpow_Uj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ)
    (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k)
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s) volume 0 z := by
  have hβ5 : 5 ≤ bet α := by rw [bet, le_div_iff₀ hα]; linarith
  have hβp : 0 < bet α := by linarith
  have hsqrt : IntegrableOn (fun s => Real.sqrt (Aj F j s)) (Set.Ioo 0 z) :=
    integrableOn_sqrt measurableSet_Ioo (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      ((Aj_integrableOn α k F hF hmem j hj).1.mono_set (fun r hr => hr.1))
      (fun r _ => integral_nonneg fun θ => sq_nonneg _)
  have hAjnn : ∀ r ∈ Set.Ioo (0:ℝ) z, 0 ≤ Aj F j r :=
    fun r _ => integral_nonneg fun θ => sq_nonneg _
  have hbd : ∀ s ∈ Set.Ioc (0:ℝ) z,
      ‖s ^ (bet α - 1) * Uj F j s‖
        ≤ Real.sqrt (π / 2) * (1 + z) ^ (bet α + 1) * Real.sqrt (Aj F j s) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hU := Uj_sqrt_bound α k F hF hmem j hj hs0
    have hnn : 0 ≤ s ^ (bet α - 1) := Real.rpow_nonneg hs0.le _
    have hdiv : s ^ (bet α + 1) / (1 + s) ^ 2 ≤ (1 + z) ^ (bet α + 1) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + s) ^ 2)]
      calc s ^ (bet α + 1) ≤ (1 + z) ^ (bet α + 1) :=
            Real.rpow_le_rpow hs0.le (by linarith [hs.2]) (by linarith : (0:ℝ) ≤ bet α + 1)
        _ ≤ (1 + z) ^ (bet α + 1) * (1 + s) ^ 2 :=
            le_mul_of_one_le_right (Real.rpow_nonneg (by linarith [hs.2]) _)
              (by nlinarith [hs0])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    have hw : Work.Spaces.w s = (1 + s) ^ 2 / s ^ 2 := rfl
    have hstep : s ^ (bet α - 1) * (Real.sqrt (π / 2) * Real.sqrt (Aj F j s)
        / Work.Spaces.w s)
        = Real.sqrt (π / 2) * Real.sqrt (Aj F j s)
          * (s ^ (bet α + 1) / (1 + s) ^ 2) := by
      rw [hw]
      have hsp : s ^ (bet α - 1) * (s ^ (2:ℝ)) = s ^ (bet α + 1) := by
        rw [← Real.rpow_add hs0]
        congr 1
        ring
      field_simp
      rw [show s ^ 2 = s ^ (2:ℝ) from (Real.rpow_natCast s 2).symm]
      calc s ^ (bet α - 1) * Real.sqrt (Aj F j s) * s ^ (2:ℝ)
          = Real.sqrt (Aj F j s) * (s ^ (bet α - 1) * s ^ (2:ℝ)) := by ring
        _ = Real.sqrt (Aj F j s) * s ^ (bet α + 1) := by rw [hsp]
    calc s ^ (bet α - 1) * |Uj F j s|
        ≤ s ^ (bet α - 1) * (Real.sqrt (π / 2) * Real.sqrt (Aj F j s) / Work.Spaces.w s) :=
          mul_le_mul_of_nonneg_left hU hnn
      _ = Real.sqrt (π / 2) * Real.sqrt (Aj F j s) * (s ^ (bet α + 1) / (1 + s) ^ 2) := hstep
      _ ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F j s) * (1 + z) ^ (bet α + 1) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = Real.sqrt (π / 2) * (1 + z) ^ (bet α + 1) * Real.sqrt (Aj F j s) := by ring
  have haesm : AEStronglyMeasurable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hcont : ContinuousOn (fun s : ℝ => s ^ (bet α - 1)) (Set.Ioc 0 z) :=
      (Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ bet α - 1)).continuousOn
    have h1 : AEStronglyMeasurable (Uj F j) (volume.restrict (Set.Ioc (0:ℝ) z)) :=
      (Uj_aesm α k F hF j).mono_measure (Measure.restrict_mono (fun s hs => hs.1) le_rfl)
    exact ((hcont.aestronglyMeasurable measurableSet_Ioc).mul h1)
  have hsqrt' : IntegrableOn (fun s => Real.sqrt (Aj F j s)) (Set.Ioc 0 z) :=
    integrableOn_sqrt measurableSet_Ioc (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      ((Aj_integrableOn α k F hF hmem j hj).1.mono_set (fun r hr => hr.1))
      (fun r _ => integral_nonneg fun θ => sq_nonneg _)
  have hint : IntegrableOn (fun s => Real.sqrt (π / 2) * (1 + z) ^ (bet α + 1)
      * Real.sqrt (Aj F j s)) (Set.Ioc 0 z) :=
    hsqrt'.const_mul _
  rw [IntervalIntegrable]
  refine ⟨hint.mono' haesm ?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => hbd s hs
  have hemp : Set.Ioc z 0 = ∅ := by
    rw [Set.Ioc_eq_empty_iff]
    exact not_lt.mpr hz.le
  rw [hemp]
  exact integrableOn_empty

/-! ## The exact radial identity and the per-order bound -/

/-- **The radial identity**: `D_z^j Ḡ(α,F) = -(3/(4α))·HarOp(5/α)(U_j)` on `(0,∞)`. -/
theorem rDzIter_Gbar_eq_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j ≤ k → Set.EqOn (rDzIter j (Work.Elliptic.Gbar α F))
      (fun z => -(3 / (4 * α)) * HarOp (bet α) (Uj F j) z) (Set.Ioi 0) := by
  intro j
  induction j with
  | zero =>
      intro hj z hz
      have h := Gbar_eq_HarOp α (ne_of_gt hα) F z
      have hfun : (Uj F 0) = (fun s : ℝ => Work.Elliptic.Fstar F s) := by
        funext s; simp
      simpa only [rDzIter_zero, hfun, Work.Spaces.DzIter_zero] using h
  | succ j ih =>
      intro hj z hz
      have hjk : j ≤ k := by omega
      have hj1k : j + 1 ≤ k := hj
      have hidj : Set.EqOn (rDzIter j (Work.Elliptic.Gbar α F))
          (fun w => -(3 / (4 * α)) * HarOp (bet α) (Uj F j) w) (Set.Ioi 0) := ih hjk
      have hev : rDzIter j (Work.Elliptic.Gbar α F) =ᶠ[𝓝 z]
          (fun w => -(3 / (4 * α)) * HarOp (bet α) (Uj F j) w) :=
        (Filter.eventually_mem_set.mpr (Ioi_mem_nhds hz)).mono (fun w hw => hidj hw)
      rw [rDzIter_succ, rDz, Filter.EventuallyEq.deriv_eq hev, deriv_const_mul_field]
      have hβp : 0 < bet α := by rw [bet]; positivity
      have hβ1 : 1 < bet α := by rw [bet, lt_div_iff₀ hα]; linarith
      have hcont : ContinuousOn (Uj F j) (Set.Ioi 0) := Uj_continuousOn α k F hF hmem j hj1k
      have hint : IntervalIntegrable (fun s : ℝ => s ^ (bet α - 1) * Uj F j s) volume 0 z :=
        intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hjk hz
      have hD6 := rDz_HarOp_of_continuousAt (bet α) hβp hz hcont hint
      rw [rDz] at hD6
      have hchainD4 : ∀ s ∈ Set.Ioo (0 : ℝ) z,
          Uj F j z - Uj F j s = ∫ r in s..z, Uj F (j + 1) r / r :=
        fun s hs => FstarDzIter_chain_open α k F hF hmem j hj1k hs.1 hs.2.le
      have hintD4 : IntegrableOn (fun r : ℝ => Uj F (j + 1) r / r) (Set.Ioo 0 z) := by
        have hsqrt : IntegrableOn (fun r => Real.sqrt (Aj F (j + 1) r)) (Set.Ioo 0 z) :=
          integrableOn_sqrt measurableSet_Ioo
            (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
            ((Aj_integrableOn α k F hF hmem (j + 1) hj1k).1.mono_set (fun r hr => hr.1))
            (fun r _ => integral_nonneg fun θ => sq_nonneg _)
        refine (hsqrt.const_mul (Real.sqrt (π / 2))).mono' ?_ ?_
        · have hU : AEStronglyMeasurable (Uj F (j + 1))
              (volume.restrict (Set.Ioo (0:ℝ) z)) :=
            (Uj_aesm α k F hF (j + 1)).mono_measure
              (Measure.restrict_mono (fun s hs => hs.1) le_rfl)
          have hInv : AEStronglyMeasurable (fun r : ℝ => r⁻¹)
              (volume.restrict (Set.Ioo (0:ℝ) z)) :=
            ((continuousOn_id.inv₀ (fun r hr => ne_of_gt hr.1)).aestronglyMeasurable
              measurableSet_Ioo)
          exact hU.mul hInv
        · show ∀ᵐ r ∂(volume.restrict (Set.Ioo (0:ℝ) z)),
            ‖Uj F (j + 1) r / r‖ ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r)
          rw [ae_restrict_iff' measurableSet_Ioo]
          refine Eventually.of_forall fun r hr => ?_
          have hr0 : 0 < r := hr.1
          have hU := Uj_sqrt_bound α k F hF hmem (j + 1) hj1k hr0
          have hAw : 1 ≤ r * Work.Spaces.w r := by
            rw [Work.Spaces.w]
            field_simp
            nlinarith [hr0, sq_nonneg r, pow_pos hr0 3]
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0, div_eq_mul_inv]
          calc |Uj F (j + 1) r| * r⁻¹
              ≤ (Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) / Work.Spaces.w r) * r⁻¹ :=
                mul_le_mul_of_nonneg_right hU (by positivity)
            _ = Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) * (r * Work.Spaces.w r)⁻¹ := by
                ring
            _ ≤ Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) * 1 := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact inv_le_one_of_one_le₀ hAw
            _ = Real.sqrt (π / 2) * Real.sqrt (Aj F (j + 1) r) := by ring
      have hD4 := HarOp_eq_sub_of_chain (bet α) hβ1 hz hintD4 hchainD4
      have hgoal : z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
          = -(3 / (4 * α)) * (-bet α * HarOp (bet α) (Uj F j) z + Uj F j z) := by
        rw [show z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
            = -(3 / (4 * α)) * (z * deriv (HarOp (bet α) (Uj F j)) z) by ring, hD6]
      show z * (-(3 / (4 * α)) * deriv (HarOp (bet α) (Uj F j)) z)
          = -(3 / (4 * α)) * HarOp (bet α) (Uj F (j + 1)) z
      rw [hgoal, hD4]
      ring

/-- **The weighted `L²` Hardy estimate, with the measurability of the source supplied by the
continuity of its primitive.**

The `∫⁻`-form `HarOp_weighted_lintegral` needs only the square-integrability of the source, but
its Bochner-integral upgrade requires the a.e. strong measurability of `HarOp β f`.  That is what
the hypothesis `hint` is for: it makes the primitive `z ↦ ∫_0^z s^(β-1) f s ds` continuous on
`(0,∞)` (`continuousOn_primitive_Ioi`), hence `HarOp β f` continuous there.  In the application
`f = F_*(D_z^j F)` the hypothesis is `intervalIntegrable_rpow_Uj`. -/
theorem HarOp_weighted_integral_cont (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0))
    (hint : ∀ z : ℝ, 0 < z →
      IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * f s) volume 0 z)
    (hfw : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  -- continuity, hence a.e. strong measurability, of `HarOp β f`
  have hcont : ContinuousOn (fun z => HarOp β f z) (Set.Ioi 0) := by
    have hp : ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) (Set.Ioi 0) :=
      continuousOn_primitive_Ioi hint
    have hfun : (fun z => HarOp β f z)
        = fun z => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s := by
      funext z; rfl
    rw [hfun]
    exact (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))).mul hp
  have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h2 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by funext z; rfl
    rw [h2]
    exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2
  have hmeas : AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (hw2.mul (hcont.pow 2)).aestronglyMeasurable measurableSet_Ioi
  have hnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2 :=
    Eventually.of_forall fun z => by positivity
  have hnnf : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ (Work.Spaces.w z) ^ 2 * (f z) ^ 2 :=
    Eventually.of_forall fun z => by positivity
  -- the `∫⁻`-form of the weighted Hardy inequality
  have hlin := HarOp_weighted_lintegral β hβ f hf
  have hUsq : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2))
      = ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfw hnnf).symm
  have hfin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
      ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hlin
    rw [hUsq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hintg : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      (Set.Ioi 0) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).1 hfin
  refine ⟨hintg, ?_⟩
  have h1 : ENNReal.ofReal
        (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintg hnn
  have h3 : ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal ((100 / β ^ 2) *
          ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) := by
    have hmul : ENNReal.ofReal ((100 / β ^ 2) *
          ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2)
        = ENNReal.ofReal (100 / β ^ 2) *
          ENNReal.ofReal (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2) :=
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 100 / β ^ 2)
    rw [h1, hmul, ← hUsq]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
    (integral_nonneg fun z => by positivity))).1 h3

/-- **The weighted `L²` bound of `D_z^j Ḡ`**, with constant `(9/4)(π/2)` independent of `α`. -/
theorem Gbar_rDzIter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
          ≤ (9 / 4) * (π / 2) * Work.Spaces.HkSq α k F := by
  have hβ5 : 5 ≤ bet α := by rw [bet, le_div_iff₀ hα]; linarith
  have hU2 : IntegrableOn (fun z => (Uj F j z) ^ 2) (Set.Ioi 0) := by
    refine (Uj_sq_mul_w_integrable α k F hF hmem j hj).1.mono' ((Uj_aesm α k F hF j).pow 2) ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ‖(Uj F j z) ^ 2‖ ≤ (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hw1 : 1 ≤ Work.Spaces.w z := by
      have hz2 : (0:ℝ) < z ^ 2 := pow_pos (Set.mem_Ioi.mp hz) 2
      rw [Work.Spaces.w, le_div_iff₀ hz2]
      nlinarith [Set.mem_Ioi.mp hz]
    have hw0 : 0 ≤ Work.Spaces.w z := by linarith [hw1]
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [hw1, hw0]
    nlinarith [hw2, sq_nonneg (Uj F j z)]
  obtain ⟨hH_int, hH_le⟩ := HarOp_weighted_integral_cont (bet α) hβ5 (Uj F j) hU2
    (fun z hz => intervalIntegrable_rpow_Uj α hα hα1 k F hF hmem j hj hz)
    (Uj_sq_mul_w_integrable α k F hF hmem j hj).1
  have hid := rDzIter_Gbar_eq_open α hα hα1 k F hF hmem j hj
  have hae : (fun z => (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z => (Work.Spaces.w z) ^ 2 *
        ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun z hz => by rw [hid hz]
  have hconst : ((-(3 / (4 * α))) ^ 2) * (100 / (bet α) ^ 2) = 9 / 4 := by
    rw [bet]; field_simp; ring
  have hg_int : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    refine Integrable.congr (hH_int.const_mul ((-(3 / (4 * α))) ^ 2)) ?_
    filter_upwards with z
    ring
  have hkey : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
        (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      ≤ (9 / 4) * (π / 2) * Work.Spaces.HkSq α k F := by
    calc (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
            ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2 := integral_congr_ae hae
      _ = ((-(3 / (4 * α))) ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
            (HarOp (bet α) (Uj F j) z) ^ 2 := by
          rw [show (fun z => (Work.Spaces.w z) ^ 2 *
                ((-(3 / (4 * α))) * HarOp (bet α) (Uj F j) z) ^ 2)
              = (fun z => ((-(3 / (4 * α))) ^ 2) *
                ((Work.Spaces.w z) ^ 2 * (HarOp (bet α) (Uj F j) z) ^ 2)) from
            funext fun z => by ring,
            integral_const_mul]
      _ ≤ ((-(3 / (4 * α))) ^ 2) * ((100 / (bet α) ^ 2) *
            ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Uj F j z) ^ 2) :=
          mul_le_mul_of_nonneg_left hH_le (sq_nonneg _)
      _ ≤ ((-(3 / (4 * α))) ^ 2) * ((100 / (bet α) ^ 2) *
            ((π / 2) * Work.Spaces.HkSq α k F)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (Uj_sq_mul_w_integrable α k F hF hmem j hj).2
      _ = (9 / 4) * (π / 2) * Work.Spaces.HkSq α k F := by
          rw [← mul_assoc, hconst]
          ring
  refine ⟨?_, ?_⟩
  · show Integrable _ (volume.restrict Work.Spaces.Iz)
    rw [← restrict_Ioi_eq_restrict_Iz]
    exact hg_int.congr hae.symm
  · have hset : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
        = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 *
          (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 := by
      rw [restrict_Ioi_eq_restrict_Iz]
    rw [hset]
    exact hkey

/-! ## The `H^k`-square estimate and the main theorem -/

theorem Gbar_HkSq_le_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      ≤ (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) * Work.Spaces.HkSq α k F := by
  have hpc : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
        ≤ gbar_Kang k * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2 :=
    fun z hz θ hθ => gbar_HkIntegrand_target_le α hα hα1 k F z θ hz hθ
  have hmeas : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ)
        ≤ (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
    intro z hz
    have hstep : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α k _ z θ)
        (integrableOn_const hmeas)
        (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
          (hpc z hz θ hθ).trans (le_of_eq (mul_assoc _ _ _)))
    exact hstep.trans (le_of_eq (gbar_integral_Iθ_const _))
  have hsum : IntegrableOn (fun z => ∑ j ∈ Finset.range (k + 1),
      (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2) Work.Spaces.Iz :=
    gbar_integrable_finsetSum (volume.restrict Work.Spaces.Iz) (Finset.range (k + 1))
      (fun j z => (Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)
      (fun j hj => (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
  have hIntmaj : IntegrableOn (fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
      ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)))
      Work.Spaces.Iz := by
    have heq : (fun z => ∑ j ∈ Finset.range (k + 1), ((π / 2) * gbar_Kang k) *
          ((Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2))
        = (fun z => (π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2))) := by
      funext z
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← heq]
    refine gbar_integrable_finsetSum (volume.restrict Work.Spaces.Iz) (Finset.range (k + 1))
      (fun j z => ((π / 2) * gbar_Kang k) *
        ((Work.Spaces.w z) ^ 2 * (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) fun j hj => ?_
    exact (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1.const_mul _
  calc Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
      = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ) := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, ((π / 2) * (gbar_Kang k * ((Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ) hIntmaj
          (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hslice z hz)
    _ = (π / 2) * (gbar_Kang k * ∑ j ∈ Finset.range (k + 1),
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (rDzIter j (Work.Elliptic.Gbar α F) z) ^ 2)) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_const_mul]
        congr 1
        rw [setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
          (fun z _ => Finset.mul_sum _ _ _)]
        exact MeasureTheory.integral_finsetSum (Finset.range (k + 1))
          (fun j hj => (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
    _ ≤ (π / 2) * (gbar_Kang k * ∑ j ∈ Finset.range (k + 1),
          ((9 / 4) * (π / 2) * Work.Spaces.HkSq α k F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (le_of_lt (gbar_Kang_pos k))
        exact (Gbar_rDzIter_bound α hα hα1 k F hF hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
    _ = (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) *
          Work.Spaces.HkSq α k F := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem Gbar_Hk_le_open_SmoothOpen (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → SmoothOpen F → Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  refine ⟨Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2)))), ?_, ?_⟩
  · have hK : 0 < gbar_Kang k := gbar_Kang_pos k
    positivity
  · intro α F hα hα1 hF hmem
    have hDnn : (0 : ℝ) ≤ (π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) := by
      have hK : 0 < gbar_Kang k := gbar_Kang_pos k
      positivity
    have hsq := Gbar_HkSq_le_open α hα hα1 k F hF hmem
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        ≤ Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2))) *
            Work.Spaces.HkSq α k F) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((π / 2) * gbar_Kang k * ((k + 1 : ℝ) * ((9 / 4) * (π / 2)))) *
            Real.sqrt (Work.Spaces.HkSq α k F) := Real.sqrt_mul hDnn _

theorem Gbar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  obtain ⟨C, hC, h⟩ := Gbar_Hk_le_open_SmoothOpen k
  exact ⟨C, hC, fun α F hα hα1 hFraw hmem =>
    h α F hα hα1 (smoothOpen_of_forall hFraw) hmem⟩

end Work.FTS.EllipticEst.Cert.GbarSin
