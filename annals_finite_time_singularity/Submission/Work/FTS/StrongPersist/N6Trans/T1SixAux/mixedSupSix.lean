/-
# `Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix`

The α-uniform pointwise bound for the *mixed* slots `D_z^b D_θ^a f`, `1 ≤ a`, `a + b ≤ 4`,
in the level-six open-quadrant class (`Work.FTS.EllipticEst.SmoothOpen` +
`Work.Spaces.HkMem α 6 f`):

  `|D_z^b D_θ^a f(z,θ)| ≤ C · |f|_{ℋ⁶}`   (`z > 0`, `0 < θ < π/2`),

with a constant `C` independent of `α ∈ (0,1]`, of `f` and of `(z,θ)`.

This is the level-six/order-four shift of the proved
`Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn` (`1 ≤ i`, `i + j ≤ 2`, `|·|_{ℋ⁴}`).
The route is verbatim the level-four one and is α-uniform:

* **radial window.**  Fix the angle `θ` and put `h(x) := D_z^bD_θ^a f(x,θ)`, `R := max z 2`.
  The window form of the radial Hardy inequality (`Work.FTS.TransportS.half_line_window_bound`)
  gives, for `z ≤ R`,

    `h(z)² ≤ 2 ∫_z^{2R} (x h'(x) w(x))² dx + (2/R) ∫_R^{2R} h(x)² dx`,

  and `x · ∂_x(D_z^bD_θ^a f) = D_z^{b+1}D_θ^a f` is definitional, so the first integrand is the
  `(b+1,a)`-slot weighted by `w`.

* **angular domination.**  Both integrands are dominated *pointwise in* `x` by the angular
  slice of the `ℋ⁶`-integrand, by the level-six total-variation device
  `Work.FTS.StrongPersist.N6Trans.T1SixAux.sliceBoundSix`:

    `(D_z^jD_θ^if(x,θ))² w(x)² ≤ 5 ∫_{Iθ} HkIntegrand α 6 f x θ'`   (`1 ≤ i`, `i+j+1 ≤ 6`),

  which uses the two adjacent angular slots `(j,i)` and `(j,i+1)` — both admissible with the
  *full* exponent `γ ≥ 1`, which is exactly why no factor `1/√(γ-1)` appears.  The index
  hypothesis is tight: the `(b+1,a)`-slot of the window term needs `a + (b+1) + 1 ≤ 6`, i.e.
  `a + b ≤ 4`.

* **integration.**  Integrating the domination in `x` and using `HkMem α 6 f` (finiteness of
  `∫_z ∫_θ HkIntegrand α 6 f`) bounds both window terms by `5 · HkSq α 6 f`, so

    `(D_z^bD_θ^af(z,θ))² ≤ 15 · HkSq α 6 f`,  hence  `|D_z^bD_θ^af(z,θ)| ≤ √15 · |f|_{ℋ⁶}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.sliceBoundSix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem mixedSupSix : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ b a : ℕ, 1 ≤ a → a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C * Work.Spaces.HkNorm α 6 f := by
  refine ⟨Real.sqrt 15, Real.sqrt_pos_of_pos (by norm_num), ?_⟩
  intro α f hα hα1 hF hmem b a ha hab z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ, hθ2⟩
  set R : ℝ := max z 2 with hRdef
  have hzR : z ≤ R := le_max_left z 2
  have hR2 : (2 : ℝ) ≤ R := le_max_right z 2
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR2
  have hz2R : z ≤ 2 * R := by linarith
  have hR2R : R ≤ 2 * R := by linarith
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- hypotheses of the radial window bound
  have hderiv : ∀ x ∈ Set.Icc z (2 * R),
      HasDerivAt (fun x => Work.Spaces.mixed b a f x θ)
        (Work.Spaces.pz (Work.Spaces.mixed b a f) x θ) x :=
    fun x hx => (hF.mixed b a).hasDerivAt_slice hθI (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x => Work.Spaces.mixed b a f x θ) (Set.Icc R (2 * R)) :=
    ((hF.mixed b a).curry_z hθI).continuousOn.mono
      (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x => Work.Spaces.pz (Work.Spaces.mixed b a f) x θ)
      (Set.Icc z (2 * R)) :=
    (((hF.mixed b a).pz).curry_z hθI).continuousOn.mono
      (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : IntegrableOn (fun x => (Work.Spaces.mixed b a f x θ) ^ 2)
      (Set.Icc R (2 * R)) := (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hzR hderiv hcont hcont' hint
  have hwin' : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 2 * (∫ x in z..(2 * R),
            (x * Work.Spaces.pz (Work.Spaces.mixed b a f) x θ * Work.Spaces.w x) ^ 2)
        + (2 / R) * ∫ x in R..(2 * R), (Work.Spaces.mixed b a f x θ) ^ 2 := hwin
  -- the weighted-derivative term
  have hwcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.w x) (Set.Icc z (2 * R)) := by
    change ContinuousOn (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) (Set.Icc z (2 * R))
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hmcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed (b + 1) a f x θ)
      (Set.Icc z (2 * R)) :=
    (((hF.mixed (b + 1) a).curry_z hθI).continuousOn).mono
      (fun x hx => lt_of_lt_of_le hz hx.1)
  have hIntL1 : IntervalIntegrable
      (fun x => (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2)
      volume z (2 * R) := by
    refine (show ContinuousOn
      (fun x => (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2)
      (Set.uIcc z (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact (hmcont1.mul hwcont1).pow 2
  have hIntR1 : IntervalIntegrable
      (fun x => 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ')
      volume z (2 * R) :=
    (show IntegrableOn (fun x => 5 * ∫ θ' in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f x θ') (Set.uIcc z (2 * R)) volume from by
      rw [Set.uIcc_of_le hz2R]
      exact (hmem.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz hx.1))).const_mul
        5).intervalIntegrable
  have hpt1 : ∀ x ∈ Set.Icc z (2 * R),
      (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2
        ≤ 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ' := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
    have h := sliceBoundSix hα hα1 hF hmem (j := b + 1) (i := a) ha (by omega) hx0 hθI
    have h2 : (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2
        = (Work.Spaces.mixed (b + 1) a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by ring
    rw [h2]; exact h
  have hmono1 : (∫ x in z..(2 * R), (Work.Spaces.mixed (b + 1) a f x θ
        * Work.Spaces.w x) ^ 2)
      ≤ 5 * ∫ x in z..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hpt1
  have hbig1 : (∫ x in z..(2 * R),
        (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ'))
      ≤ Work.Spaces.HkSq α 6 f := by
    rw [intervalIntegral.integral_of_le hz2R]
    refine setIntegral_mono_set hmem.2 (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x hx => ?_)
    · exact integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 6 f x θ'
    · exact le_of_lt (lt_trans hz hx.1)
  have hcongr1 : (∫ x in z..(2 * R), (x * Work.Spaces.pz (Work.Spaces.mixed b a f) x θ
        * Work.Spaces.w x) ^ 2)
      = ∫ x in z..(2 * R), (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rfl
  have hstep1 : (∫ x in z..(2 * R), (x * Work.Spaces.pz (Work.Spaces.mixed b a f) x θ
        * Work.Spaces.w x) ^ 2) ≤ 5 * Work.Spaces.HkSq α 6 f := by
    rw [hcongr1]
    calc (∫ x in z..(2 * R), (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2)
        ≤ 5 * ∫ x in z..(2 * R),
            (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ') := hmono1
      _ ≤ 5 * Work.Spaces.HkSq α 6 f := by linarith
  -- the window average term
  have hIntL2 : IntervalIntegrable (fun x => (Work.Spaces.mixed b a f x θ) ^ 2)
      volume R (2 * R) := by
    refine (show ContinuousOn (fun x => (Work.Spaces.mixed b a f x θ) ^ 2)
      (Set.uIcc R (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcont.pow 2
  have hwcont2 : ContinuousOn (fun x : ℝ => Work.Spaces.w x) (Set.Icc R (2 * R)) := by
    change ContinuousOn (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) (Set.Icc R (2 * R))
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hRpos hx.1))
  have hIntM2 : IntervalIntegrable
      (fun x => (Work.Spaces.mixed b a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      volume R (2 * R) := by
    refine (show ContinuousOn
      (fun x => (Work.Spaces.mixed b a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      (Set.uIcc R (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact (hcont.pow 2).mul (hwcont2.pow 2)
  have hIntR2 : IntervalIntegrable
      (fun x => 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ')
      volume R (2 * R) :=
    (show IntegrableOn (fun x => 5 * ∫ θ' in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f x θ') (Set.uIcc R (2 * R)) volume from by
      rw [Set.uIcc_of_le hR2R]
      exact (hmem.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hRpos hx.1))).const_mul
        5).intervalIntegrable
  have hpt2a : ∀ x ∈ Set.Icc R (2 * R),
      (Work.Spaces.mixed b a f x θ) ^ 2
        ≤ (Work.Spaces.mixed b a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    have h1 : 1 ≤ (Work.Spaces.w x) ^ 2 :=
      one_le_pow₀ (Work.FTS.TransportS.one_le_w hx0)
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f x θ)]
  have hpt2b : ∀ x ∈ Set.Icc R (2 * R),
      (Work.Spaces.mixed b a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2
        ≤ 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ' := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact sliceBoundSix hα hα1 hF hmem (j := b) (i := a) ha (by omega) hx0 hθI
  have hmono2a : (∫ x in R..(2 * R), (Work.Spaces.mixed b a f x θ) ^ 2)
      ≤ ∫ x in R..(2 * R),
          (Work.Spaces.mixed b a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 :=
    intervalIntegral.integral_mono_on hR2R hIntL2 hIntM2 hpt2a
  have hmono2b : (∫ x in R..(2 * R),
        (Work.Spaces.mixed b a f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      ≤ 5 * ∫ x in R..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hR2R hIntM2 hIntR2 hpt2b
  have hbig2 : (∫ x in R..(2 * R),
        (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ'))
      ≤ Work.Spaces.HkSq α 6 f := by
    rw [intervalIntegral.integral_of_le hR2R]
    refine setIntegral_mono_set hmem.2 (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x hx => ?_)
    · exact integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 6 f x θ'
    · exact le_of_lt (lt_trans hRpos hx.1)
  have hstep2 : (∫ x in R..(2 * R), (Work.Spaces.mixed b a f x θ) ^ 2)
      ≤ 5 * Work.Spaces.HkSq α 6 f := by
    have h1 : 5 * (∫ x in R..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f x θ'))
        ≤ 5 * Work.Spaces.HkSq α 6 f := by linarith
    linarith [hmono2a, hmono2b, h1]
  -- conclusion
  have hYnn : 0 ≤ ∫ x in R..(2 * R), (Work.Spaces.mixed b a f x θ) ^ 2 :=
    intervalIntegral.integral_nonneg hR2R fun x _ => sq_nonneg _
  have hcoef : 2 / R ≤ 1 := by
    rw [div_le_one hRpos]; linarith
  have hcoef2 : (2 / R) * (∫ x in R..(2 * R), (Work.Spaces.mixed b a f x θ) ^ 2)
      ≤ (∫ x in R..(2 * R), (Work.Spaces.mixed b a f x θ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hcoef hYnn
    rwa [one_mul] at h
  have hfinal : (Work.Spaces.mixed b a f z θ) ^ 2 ≤ 15 * Work.Spaces.HkSq α 6 f := by
    linarith [hwin', hcoef2, hstep1, hstep2]
  calc |Work.Spaces.mixed b a f z θ| = Real.sqrt ((Work.Spaces.mixed b a f z θ) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (15 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt 15 * Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 15 * Work.Spaces.HkNorm α 6 f := by
        rw [Work.Spaces.HkNorm]

end Work.FTS.StrongPersist.N6Trans.T1SixAux
