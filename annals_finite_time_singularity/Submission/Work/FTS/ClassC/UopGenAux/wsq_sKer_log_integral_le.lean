import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.UopGenAux

/-!
### The weighted logarithmic Schur bound for the bump `sKer`

We prove

`∫_{z>0} w(z)² · sKer δ (log z - log y) dz ≤ 5 · w(y)² · y`  (`0 < δ ≤ 1/2`, `y > 0`),

where `w(z) = (1+z)²/z²` and `sKer δ` is the normalised smooth bump of `MollDefs`.

The proof has three ingredients:

* the substitution `z = exp s`, which turns the half-line integral into a convolution
  against `sKer δ` on the logarithmic variable (`MeasureTheory.integral_comp_exp`);
* the pointwise comparison `w(e^s)² e^s ≤ 5 · w(e^t)² e^t` for `|s - t| ≤ 1/2`
  (`EllPkgAux.wExpCmp`, whose numerical content is `e^{3/2} ≤ 5`), combined with
  `sKer δ (s - t) = 0` whenever `δ ≤ |s - t|`;
* the normalisation `∫ sKer δ = 1`.

The constant `5` comes from the pointwise comparison: the kernel has vanishing moments of
order `< 1` only up to the factor `e^{δ}` contributed by the logarithmic Jacobian, and
`e^{3/2} ≤ 5`.
-/

/-- `sKer ε` is continuous. -/
private lemma pk5_sKer_continuous (ε : ℝ) : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  have h : Work.FTS.EllSol.PkgK5.K5c.sKer ε
      = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Work.FTS.EllSol.PkgK5.K5c.sBump (t / ε) := by
    funext t; rw [Work.FTS.EllSol.PkgK5.K5c.sKer]
  rw [h]
  exact continuous_const.mul
    (Work.FTS.EllSol.PkgK5.K5c.sBump_continuous.comp (continuous_id.div_const ε))

/-- `sKer ε` has compact support (contained in `[-ε, ε]`). -/
private lemma pk5_sKer_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

/-- `sKer ε` is integrable for `ε > 0`. -/
private lemma pk5_sKer_integrable {ε : ℝ} (hε : 0 < ε) :
    MeasureTheory.Integrable (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
  (pk5_sKer_continuous ε).integrable_of_hasCompactSupport (pk5_sKer_hasCompactSupport hε)

theorem wsq_sKer_log_integral_le {δ y : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hy : 0 < y) :
    (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - Real.log y))
      ≤ 5 * ((Work.Spaces.w y) ^ 2 * y) := by
  -- integrability of the shifted kernel
  have hker : MeasureTheory.Integrable
      (fun x : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)) :=
    (pk5_sKer_integrable hδ).comp_sub_right (Real.log y)
  have hmass : (∫ x : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)) = 1 := by
    rw [MeasureTheory.integral_sub_right_eq_self (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log y),
      Work.FTS.EllSol.PkgK5.K5c.sKer_integral_eq_one hδ]
  -- the substitution `z = exp x`
  have hsub : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - Real.log y))
      = ∫ x : ℝ, Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
          * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)) := by
    rw [← MeasureTheory.integral_comp_exp
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - Real.log y))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.log_exp, smul_eq_mul]
  -- the pointwise comparison
  have hpt : ∀ x : ℝ, Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y))
      ≤ 5 * ((Work.Spaces.w y) ^ 2 * y)
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by
    intro x
    by_cases hx : |x - Real.log y| ≤ 1 / 2
    · have hc := Work.FTS.EllSol.EllPkgAux.wExpCmp x (Real.log y) hx
      rw [Real.exp_log hy] at hc
      have h1 : Real.exp x * (Work.Spaces.w (Real.exp x)) ^ 2
          ≤ 5 * ((Work.Spaces.w y) ^ 2 * y) := by
        rw [mul_comm ((Work.Spaces.w (Real.exp x)) ^ 2) (Real.exp x)] at hc
        exact hc
      calc Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
            * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y))
          = (Real.exp x * (Work.Spaces.w (Real.exp x)) ^ 2)
              * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by ring
        _ ≤ (5 * ((Work.Spaces.w y) ^ 2 * y))
              * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) :=
            mul_le_mul_of_nonneg_right h1 (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ _)
        _ = 5 * ((Work.Spaces.w y) ^ 2 * y)
              * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by ring
    · -- outside the support of the kernel both sides vanish
      rw [not_le] at hx
      have hz : Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) = 0 :=
        Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (le_trans hδ2 hx.le)
      rw [hz]
      simp
  refine le_trans hsub.le ?_
  have hmain : (∫ x : ℝ, Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)))
      ≤ ∫ x : ℝ, 5 * ((Work.Spaces.w y) ^ 2 * y)
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x
      exact mul_nonneg (Real.exp_pos x).le
        (mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ _))
    · exact hker.const_mul (5 * ((Work.Spaces.w y) ^ 2 * y))
    · filter_upwards with x
      exact hpt x
  refine le_trans hmain ?_
  rw [MeasureTheory.integral_const_mul, hmass]
  exact le_of_eq (by ring)

end Work.FTS.ClassC.UopGenAux
