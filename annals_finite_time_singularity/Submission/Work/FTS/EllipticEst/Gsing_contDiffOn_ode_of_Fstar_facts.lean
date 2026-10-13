import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.Elliptic.GsingFuncs
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.FM.Core2
import Submission.Work.Coercivity.L12f_contDiffOn_infty

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Smoothness of the singular term `Gsing` and the second-order ODE it solves

`Work.Elliptic.Gsing α F = Gstar α F + Gbar α F` with
`Gstar α F = -(1/(4α)) L₁₂(F)` and
`Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds`.

The assumptions of the statement feed us the *first derivative* of each of the two
non-elementary ingredients:

* `hL12` gives `∂_z(L₁₂ F)(z) = -3 F_*(z)/z`;
* `hFsm` and `hFint` give, through the fundamental theorem of calculus, the derivative of
  the integral `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds`, namely the integrand.

So both `L₁₂ F` and `J` are *antiderivatives of smooth functions* on the open set
`(0,∞)`, hence smooth to all orders there (`contDiffOn_all_of_forall_hasDerivAt`), and the
same holds for `Gsing`.  The second-order ODE is `Work.Elliptic.Gsing_ode`. -/

/-- **Smoothness of an antiderivative.**  If `f` has derivative `g` at every point of an
open set `s`, and `g` is `C^m` on `s` for every `m` (in particular `C^∞`), then `f` is `C^m`
on `s` for every `m`.

The derivative datum is only available pointwise, so the smoothness of `f` is obtained by
induction on the order: the `C^{m+1}`-criterion on an open set converts
`ContDiffOn ℝ (m+1) f s` into `DifferentiableOn ℝ f s ∧ ContDiffOn ℝ m (deriv f) s`, and
`deriv f` agrees with `g` on `s`. -/
theorem contDiffOn_all_of_forall_hasDerivAt {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ∀ m : ℕ, ContDiffOn ℝ m g s) :
    ∀ m : ℕ, ContDiffOn ℝ m f s := by
  have hstep : ∀ m : ℕ, ContDiffOn ℝ (m + 1) f s := by
    intro m
    rw [contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro hm
      exact absurd hm (WithTop.natCast_ne_top m)
    · exact (hg m).congr fun x hx => (hf x hx).deriv
  intro m
  cases m with
  | zero => exact contDiffOn_zero.mpr (hstep 0).continuousOn
  | succ m => exact hstep m

theorem Gsing_contDiffOn_ode_of_Fstar_facts (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0))
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  -- ## 1. the two derivative data
  -- `F_*` is differentiable at every `z > 0`, with derivative `deriv F_* z`
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- the integral `∫_0^z s^{(5-α)/α} F_*(s) ds` has derivative the integrand
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    set p : ℝ := (5 - α) / α with hp
    have hpow : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun s : ℝ => s ^ p) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id (fun x hx => ne_of_gt hx)
    have hker : ContinuousOn (fun s : ℝ => s ^ p * Work.Elliptic.Fstar F s) (Set.Ioi 0) :=
      hpow.continuousOn.mul (hFsm 0).continuousOn
    have hmain : HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ p * Work.Elliptic.Fstar F s)
        (z ^ p * Work.Elliptic.Fstar F z) z := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · -- the integrand is integrable on `(0,z]`, because
        -- `|s^{(5-α)/α} F_*(s)| ≤ z^{5/α} |F_*(s)/s|` there
        rw [intervalIntegrable_iff, Set.uIoc_of_le hzpos.le]
        have hH : IntegrableOn (fun s : ℝ => Work.Elliptic.Fstar F s / s) (Set.Ioc 0 z) :=
          hFint.mono_set fun s hs => hs.1
        refine (hH.norm.const_mul (z ^ (5 / α))).mono' ?_ ?_
        · exact (hker.mono fun s hs => hs.1).aestronglyMeasurable measurableSet_Ioc
        · rw [ae_restrict_iff' measurableSet_Ioc]
          refine Eventually.of_forall fun s hs => ?_
          have hs0 : 0 < s := hs.1
          have hsz : s ≤ z := hs.2
          have hrpow : s ^ (5 / α) ≤ z ^ (5 / α) :=
            Real.rpow_le_rpow hs0.le hsz (by positivity)
          have hp' : p = 5 / α - 1 := by
            rw [hp]
            field_simp
          have hsp : s ^ p = s ^ (5 / α) / s := by
            rw [hp', Real.rpow_sub hs0, Real.rpow_one]
          rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hs0.le p), hsp, norm_div,
            Real.norm_of_nonneg hs0.le]
          rw [show s ^ (5 / α) / s * ‖Work.Elliptic.Fstar F s‖
              = s ^ (5 / α) * (‖Work.Elliptic.Fstar F s‖ / s) by ring]
          exact mul_le_mul_of_nonneg_right hrpow (div_nonneg (norm_nonneg _) hs0.le)
      · exact hker.stronglyMeasurableAtFilter isOpen_Ioi z hz
      · exact hker.continuousAt (isOpen_Ioi.mem_nhds hz)
    simpa only [hp] using hmain
  -- ## 2. smoothness of the two derivative functions
  have hSmL12 : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) := by
    intro m
    have h3 : ContDiffOn ℝ m (fun z : ℝ => (3 : ℝ) * Work.Elliptic.Fstar F z) (Set.Ioi 0) :=
      contDiffOn_const.mul (hFsm m)
    have hdiv : ContDiffOn ℝ m (fun z : ℝ => (3 : ℝ) * Work.Elliptic.Fstar F z / z)
        (Set.Ioi 0) :=
      h3.div contDiffOn_id fun z hz => ne_of_gt hz
    exact hdiv.neg
  have hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    contDiffOn_all_of_forall_hasDerivAt isOpen_Ioi hL12 hSmL12
  have hSmJ : ∀ m : ℕ,
      ContDiffOn ℝ m (fun z : ℝ => z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z)
        (Set.Ioi 0) := by
    intro m
    have hpow : ContDiffOn ℝ m (fun z : ℝ => z ^ ((5 - α) / α)) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id fun x hx => ne_of_gt hx
    exact hpow.mul (hFsm m)
  have hJfun : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Jfun α F) (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    change HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
      s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z
    exact hJ z hz
  have hJsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Jfun α F) (Set.Ioi 0) := by
    intro m
    change ContDiffOn ℝ m (fun z' => ∫ s in (0 : ℝ)..z',
      s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi 0)
    exact contDiffOn_all_of_forall_hasDerivAt isOpen_Ioi hJ hSmJ m
  -- ## 3. smoothness of the two summands
  have hGstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    have hfun : (Work.Elliptic.Gstar α F)
        = fun z : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F z := rfl
    rw [hfun]
    exact (contDiffOn_const (c := -(1 / (4 * α)))).mul (hL12sm m)
  have hAbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Abar α) (Set.Ioi 0) := by
    intro m
    have hfun : (Work.Elliptic.Abar α)
        = fun z : ℝ => -(3 / (4 * α)) * z ^ (-(5 / α)) := rfl
    rw [hfun]
    have hpow : ContDiffOn ℝ m (fun z : ℝ => z ^ (-(5 / α))) (Set.Ioi 0) :=
      ContDiffOn.rpow_const_of_ne contDiffOn_id fun x hx => ne_of_gt hx
    exact (contDiffOn_const (c := -(3 / (4 * α)))).mul hpow
  have hGbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    have hfun : (Work.Elliptic.Gbar α F)
        = fun z : ℝ => (Work.Elliptic.Abar α z * Work.Elliptic.Jfun α F z) := rfl
    rw [hfun]
    exact (hAbar m).mul (hJsm m)
  -- ## 4. assembly
  refine ⟨fun m => ?_, fun z hz => ?_⟩
  · have hfun : (Work.Elliptic.Gsing α F)
        = fun z : ℝ => Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z := rfl
    rw [hfun]
    exact (hGstar m).add (hGbar m)
  · exact Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ z hz

end Work.FTS.EllipticEst
