import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

/-! ## The two null endpoints of `Iθ`

`sin(2θ)` vanishes exactly at `θ = 0` and `θ = π/2`, where the `η`-weighted block
`f·w/√(sin 2θ^η)` degenerates.  Off these two points the plain block `f·w` is
dominated by it, which is enough because `(0,π/2)` is co-null in `Iθ`. -/

/-- The open interval `(0,π/2)` is co-null in `Iθ`, so the two restricted measures agree. -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- Off the two null endpoints of `Iθ`, the plain block `Xw f = f·w` is dominated by the
`ℋ¹`-integrand, because the `D_z⁰`-summand of the latter is `(f·w/√(sin 2θ^η))²` and
`√(sin 2θ^η) ≤ 1` there. -/
private theorem sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Coercivity.Xw f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
          Real.rpow_le_rpow (le_of_lt hs0) hs1
            (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Work.Spaces.w z) ^ 2
      ≤ ((f z θ * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos ht0 2)]
    have ht2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
      nlinarith [ht0, ht1]
    simpa using mul_le_mul_of_nonneg_left ht2 (sq_nonneg (f z θ * Work.Spaces.w z))
  have hterm : (Work.Coercivity.Xw f z θ) ^ 2
      ≤ (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp only [Work.Coercivity.Xw, Work.Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm
    (Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))

/-- `|Xw f|²_{L²} = |f·w|²_{L²} ≤ |f|²_{ℋ¹}`, by the a.e. pointwise domination above and
two applications of `integral_mono_of_nonneg`. -/
private theorem L2Sq_Xw_le_HkSq (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 1 f) :
    Work.Spaces.L2Sq (Work.Coercivity.Xw f) ≤ Work.Spaces.HkSq α 1 f := by
  rw [Work.Spaces.L2Sq, Work.Spaces.HkSq]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmem.2 ?_
  refine ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 z hz) (sq_Xw_le_HkIntegrand_ae α f z)

/-- The four weighted `ℋ¹` blocks are individually dominated by the `ℋ¹`-norm square: for
`f ∈ ℋ¹` (only the honest iterated integrability `Work.Spaces.HkMem α 1 f` is needed — no
smoothness), `L2Sq` of each of `Xeta f = f·w/√sin^η`, `XetaDz f = D_z f·w/√sin^η`,
`XgamDth α f = D_θf·W`, `Xw f = f·w` is at most `HkSq α 1 f`.

ROUTE.  `Work.Spaces.L2Sq_DzIter_le_HkSq` (`i = 0` resp. `i = 1`) and
`Work.Spaces.L2Sq_mixed_le_HkSq` (`(i,j) = (1,0)`) give the first three by definitional
rewriting.  For `Xw` dominate the integrand pointwise a.e. by `HkIntegrand α 1 f`: on
`θ ∈ (0,π/2)` we have `0 < sin(2θ) ≤ 1`, so `sin(2θ)^{η/2} ≤ 1` and hence
`(f z θ·w z)² ≤ (f z θ·w z / sin(2θ)^{η/2})²`, the `(i=0)`-summand of the integrand; the two
endpoints are null.  Then integrate with `MeasureTheory.integral_mono_of_nonneg` twice
(inner slice and outer `z`-integral against `hmem.1`/`hmem.2`). -/
theorem L2Sq_blocks_le_HkSq (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 1 f) :
    Work.Spaces.L2Sq (Work.Coercivity.Xeta f) ≤ Work.Spaces.HkSq α 1 f ∧
    Work.Spaces.L2Sq (Work.Coercivity.XetaDz f) ≤ Work.Spaces.HkSq α 1 f ∧
    Work.Spaces.L2Sq (Work.Coercivity.XgamDth α f) ≤ Work.Spaces.HkSq α 1 f ∧
    Work.Spaces.L2Sq (Work.Coercivity.Xw f) ≤ Work.Spaces.HkSq α 1 f := by
  refine ⟨Work.Spaces.L2Sq_DzIter_le_HkSq α 1 f hmem 0 (by norm_num),
    Work.Spaces.L2Sq_DzIter_le_HkSq α 1 f hmem 1 (by norm_num),
    Work.Spaces.L2Sq_mixed_le_HkSq α 1 f hmem 1 0 (by norm_num) (by norm_num),
    L2Sq_Xw_le_HkSq α f hmem⟩

end Work.FTS.CoercivityFix.Assembly
