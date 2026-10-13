import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.cc.wwEta
import Submission.Work.FTS.GalBasis.cc.wwBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

/-!
# Integrability of the angular quotient `D_z^b D_θ f / sin(2θ)` near `θ = 0`

The layer lemmas of `Work.FTS.GalBasis.cc` (`sharp_layer_le`, `wrongWeight_layer_tendsto_zero`)
need the *interval* integrability of `θ ↦ D_z^b D_θ f (z,θ) / sin(2θ)` on `[0,2t]` for a fixed
`z > 0`, with `2t ≤ π/4` (so `sin(2θ)` is small only at the left endpoint).

For a merely `C^∞`-on-the-open-quadrant `f` this is *not* continuity at `θ = 0` — the quotient may
well be unbounded there — but it is a genuine `L¹` statement, and the `ℋ^4`-membership forbids the
blow-up: writing

  `D_z^b D_θ f / sin(2θ) = (D_z^b D_θ f · W) · (w⁻¹ · sin(2θ)^{γ/2 - 1})`,

the first factor is (up to a summand) square-integrable because `HkIntegrand α 4 f` dominates
`(mixed b 1 f · W)²` for `b ≤ 3`, and the second is square-integrable because `γ > 1` makes
`sin(2θ)^{γ-2}` integrable on `(0,2t]` (the sharp Hardy-side exponent).  Cauchy–Schwarz /
`2|xy| ≤ x² + y²` then gives the `L¹`-bound.

The two auxiliary facts used below are `Work.Spaces.sq_le_HkIntegrand_mixed` (a mixed summand of
`HkIntegrand` is dominated by the whole integrand) and
`Work.FTS.GalBasis.cc.integrableOn_sin_pow_sub_two` (`sin(2θ)^{γ-2} ∈ L¹(0,b)` for `γ > 1`,
`b ≤ π/4`).
-/

/-! ## Continuity of the `W`-weight on the open quadrant -/

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2) (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The angular slice of the weighted mixed derivative `D_z^j D_θ^i f · W` is a.e. strongly
measurable, for `z > 0`. -/
lemma aesm_slice_mixed_Wt {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _
    (((hsm.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hz

/-- The square of the angular slice above is a.e. strongly measurable. -/
lemma aesm_slice_mixed_Wt_sq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  convert (aesm_slice_mixed_Wt hsm α j i hz).pow 2 using 1

/-! ## The main lemma -/

theorem intervalIntegrable_mixed_div_sin {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {b : ℕ} (hb4 : b ≤ 3) (hγ : 1 < Work.Spaces.gam α) {z : ℝ} (hz : 0 < z)
    {t : ℝ} (ht : 0 < t) (h2t : 2 * t ≤ Real.pi / 4) :
    IntervalIntegrable (fun θ : ℝ => Work.Spaces.mixed b 1 f z θ / Real.sin (2 * θ)) volume 0 (2 * t) := by
  have h0 : (0:ℝ) ≤ 2 * t := by linarith
  have hsub : Set.Ioc (0:ℝ) (2 * t) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt hθ.1, by linarith [hθ.2, h2t, Real.pi_pos]⟩
  have hsinpos : ∀ θ ∈ Set.Ioc (0:ℝ) (2 * t), 0 < Real.sin (2 * θ) := fun θ hθ =>
    sin_two_pos hθ.1 (by linarith [hθ.2, h2t, Real.pi_pos])
  have hzmem : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  refine intervalIntegrable_of_integrableOn_Ioc h0 ?_
  have hHk : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      (Set.Ioc 0 (2 * t)) := (hmem.1 z hzmem).mono_set hsub
  -- the `θ`-factor `g = D_z^b D_θ f · W` is square-integrable: `g²` is a mixed summand of
  -- `HkIntegrand α 4 f`, which is integrable on the angular slice.
  have hg2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (Set.Ioc 0 (2 * t)) := by
    refine MeasureTheory.Integrable.mono' hHk ?_ ?_
    · exact (aesm_slice_mixed_Wt_sq hsm α b 1 hz).mono_set hsub
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b (le_refl 1) (by omega)
  -- the `sin`-factor `h = w⁻¹ · sin(2θ)^{γ/2-1}` is square-integrable since `γ > 1`.
  have hh2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) ^ 2)
      (Set.Ioc 0 (2 * t)) := by
    have hbase : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) (Set.Ioc 0 (2 * t)) :=
      integrableOn_sin_pow_sub_two hγ h2t
    refine MeasureTheory.IntegrableOn.congr_fun (hbase.const_mul ((Work.Spaces.w z)⁻¹ ^ 2)) ?_
      measurableSet_Ioc
    intro θ hθ
    have hs := hsinpos θ hθ
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
      congr 1
      ring
    change (Work.Spaces.w z)⁻¹ ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)
      = ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) ^ 2
    rw [mul_pow, hsq]
  -- the dominating function `(g² + h²)/2`
  have hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 / 2
        + ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) ^ 2 / 2)
      (Set.Ioc 0 (2 * t)) :=
    (hg2.div_const 2).add (hh2.div_const 2)
  -- a.e. strong measurability of the quotient, from continuity on the open quadrant
  have hFaesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed b 1 f z θ / Real.sin (2 * θ))
      (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * t))) := by
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.mixed b 1 f p.1 p.2 / Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 := by
      refine ((hsm.mixed b 1).continuousOn).div ?_ ?_
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
      · intro p hp
        obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    exact (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz).mono_set hsub
  refine MeasureTheory.Integrable.mono' hGint hFaesm ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun θ hθ => ?_
  have hs := hsinpos θ hθ
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  -- the pointwise factorisation of the quotient
  have hss : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
      * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1) = (Real.sin (2 * θ))⁻¹ := by
    rw [← Real.rpow_add hs, show -(Work.Spaces.gam α / 2) + (Work.Spaces.gam α / 2 - 1) = -1 by ring,
      Real.rpow_neg_one]
  have hcore : (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
      * ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1))
      = (Real.sin (2 * θ))⁻¹ := by
    have hstep2 : (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
        * ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1))
        = (Work.Spaces.w z * (Work.Spaces.w z)⁻¹)
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
            * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)) := by ring
    rw [hstep2, mul_inv_cancel₀ hwz, one_mul, hss]
  have hprod : (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ)
      * ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1))
      = Work.Spaces.mixed b 1 f z θ / Real.sin (2 * θ) := by
    change (Work.Spaces.mixed b 1 f z θ
        * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))))
      * ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1))
      = Work.Spaces.mixed b 1 f z θ * (Real.sin (2 * θ))⁻¹
    have hstep : (Work.Spaces.mixed b 1 f z θ
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))))
        * ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1))
        = Work.Spaces.mixed b 1 f z θ
          * ((Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
            * ((Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1))) := by
      ring
    rw [hstep, hcore]
  rw [← hprod, Real.norm_eq_abs, abs_mul]
  -- AM–GM
  set X := Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ
  set Y := (Work.Spaces.w z)⁻¹ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2 - 1)
  have hAG := sq_nonneg (|X| - |Y|)
  rw [sub_sq, sq_abs, sq_abs] at hAG
  nlinarith [hAG]

end Work.FTS.GalBasis.cc
