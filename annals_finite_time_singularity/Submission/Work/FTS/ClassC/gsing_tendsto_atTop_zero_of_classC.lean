/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Gsing α g z → 0` as `z → ∞` for a `ClassC` datum

The target of `FTS/ClassC` is `Work.FTS.ClassC.gsing_tendsto_atTop_zero_of_classC`: for every
`α > 0` and every `g` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen g`)
and honestly in `ℋ⁷` (`Work.Spaces.HkMem α 7 g`), the singular term
`Work.Elliptic.Gsing α g z = Gstar α g z + Gbar α g z` tends to `0` as `z → ∞`.

## The route

The whole content is the *unweighted* `L²`-honesty of `g`, and that is what makes the
statement non-trivial at `z = 0`: `HkMem` controls `∫_θ (g z θ · w z / sin(2θ)^{η/2})²` and
`w 0 = 0`, so `HkMem` carries **no** information on the slice `z = 0` (indeed `SmoothOpen` is
only smoothness on the *open* quadrant).  The fix is to replace the value of `g` at the single
point `z = 0` by `0`: the modified datum `patch g` differs from `g` on the null set `{z = 0}`
only, hence

* `L2Mem (patch g)` holds (the slices at `z > 0` are a.e. dominated by
  `HkIntegrand α 0 g z ·` because the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1` on the open
  quadrant, and the `z = 0` slice of `patch g` vanishes);
* `Gsing α (patch g) z = Gsing α g z` for every `z > 0`, because both `Gstar` and `Gbar` only
  see `F_*(g)(r)` for `r > 0` (`Fstar_patch`).

The existing theorem `Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero` finishes the job: it
proves `Gsing α F z → 0` from `L2Mem F` alone (its `Gstar` half is the tail of the `L¹`
function `L12Maj F`, its `Gbar` half is `harOp_tendsto_zero`, the weighted Hardy transform of
the angular moment, with the Cauchy–Schwarz majorant `√(π/2 ∫_θ F²)`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The patch at `z = 0` -/

/-- `patch g` is `g` with the value on the null slice `z = 0` replaced by `0`.  It agrees with
`g` on the open quadrant, so all the weighted/`L²` estimates are unchanged; the point is that
`HkMem` gives no information at `z = 0`, while `L2Mem` asks for it. -/
def patch (g : Fn) : Fn := fun z θ => if z = 0 then 0 else g z θ

theorem patch_apply_of_ne {g : Fn} {z θ : ℝ} (hz : z ≠ 0) : patch g z θ = g z θ := by
  simp [patch, hz]

@[simp] theorem patch_apply_zero (g : Fn) (θ : ℝ) : patch g 0 θ = 0 := by
  simp [patch]

/-! ## Elementary weight facts -/

/-- On the open quadrant the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1`. -/
private lemma one_le_wdiv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs_pos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
  have hs_le : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _)
      (by rw [Work.Spaces.eta]; norm_num)
  rw [one_le_div hs_pos]
  exact le_trans hs_le hw

/-- Pointwise domination of `(g z θ)²` by the `k = 0` integrand on the open quadrant. -/
private lemma sq_le_wdiv_sq {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (g z θ) ^ 2
      ≤ (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hr : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    one_le_wdiv hz hθ
  have hr0 : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    le_trans zero_le_one hr
  have habs : |g z θ|
      ≤ |g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact le_mul_of_one_le_right (abs_nonneg _) hr
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (g z θ)) habs 2

/-- The open interval `(0,π/2)` and the closed `Iθ` carry the same restriction of Lebesgue
measure (they differ by the two null endpoints). -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact Ioo_ae_eq_Icc)

/-! ## `L²`-honesty of the patch -/

/-- `HkMem α 0 g` plus `SmoothOpen g` imply the *unweighted* honesty `L2Mem (patch g)`. -/
theorem L2Mem_patch {α : ℝ} {g : Fn} (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 0 g) : Work.Spaces.L2Mem (patch g) := by
  have hcontQ : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hreg.continuousOn
  -- ## the angular slices
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => (patch g z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · have h0 : (fun θ => (patch g 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; simp
      rw [h0]
      exact integrableOn_zero
    · have hzpos : 0 < z := lt_of_le_of_ne' hz hz0
      have hfun : (fun θ => (patch g z θ) ^ 2) = fun θ => (g z θ) ^ 2 := by
        funext θ; rw [patch_apply_of_ne (g := g) hz0]
      rw [hfun]
      refine Integrable.mono' (hmem.1 z hz) ?_ ?_
      · have h1 := (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (Function.uncurry g) hcontQ hzpos).pow 2
        refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
        simp only [Function.uncurry, Pi.pow_apply]
      · rw [← restrict_Ioo_eq_restrict_Iθ]
        refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact le_trans (sq_le_wdiv_sq hzpos hθ)
          (by simpa only [Work.Spaces.DzIter_zero] using
            Work.Spaces.sq_le_HkIntegrand_z α 0 g z θ 0 (le_refl 0))
  refine ⟨hslice, ?_⟩
  -- ## the radial integral
  have hc : ContinuousOn (fun p : ℝ × ℝ => (patch g p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have h2 : ((Function.uncurry g) ^ 2) = fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 := by
        funext p
        rcases p with ⟨a, b⟩
        simp
      simpa only [h2] using hcontQ.pow 2
    refine h1.congr ?_
    intro p hp
    show (patch g p.1 p.2) ^ 2 = (g p.1 p.2) ^ 2
    rw [patch_apply_of_ne (g := g) (ne_of_gt hp.1)]
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (patch g z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    have := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (patch g p.1 p.2) ^ 2) hc).integral_prod_right'
    simpa only using this
  refine Integrable.mono' hmem.2 haesm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
  rcases eq_or_ne z 0 with rfl | hz0
  · have h0 : (∫ θ in Work.Spaces.Iθ, (patch g 0 θ) ^ 2) = 0 := by
      simp [patch]
    rw [h0]
    exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ
  · have hzpos : 0 < z := lt_of_le_of_ne' hz hz0
    refine integral_mono_ae (hslice z hz) (hmem.1 z hz) ?_
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    simp only [patch_apply_of_ne (g := g) hz0]
    exact le_trans (sq_le_wdiv_sq hzpos hθ)
      (by simpa only [Work.Spaces.DzIter_zero] using
        Work.Spaces.sq_le_HkIntegrand_z α 0 g z θ 0 (le_refl 0))

/-! ## `Gsing` only sees `g` on `z > 0` -/

/-- The angular moment of `patch g` agrees with that of `g` at every `r > 0`. -/
theorem Fstar_patch (g : Fn) {r : ℝ} (hr : 0 < r) :
    Work.Elliptic.Fstar (patch g) r = Work.Elliptic.Fstar g r := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [patch_apply_of_ne (g := g) (ne_of_gt hr)]

/-- `Gstar` of `patch g` equals `Gstar` of `g` for `z > 0` (both only see `F_*(r)` for
`r > 0`). -/
theorem gstar_patch {α : ℝ} (g : Fn) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Gstar α (patch g) z = Work.Elliptic.Gstar α g z := by
  rw [Work.Elliptic.Gstar, Work.Elliptic.Gstar, Work.Elliptic.L12, Work.Elliptic.L12]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  rw [Work.Elliptic.L12dens, Work.Elliptic.L12dens]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [patch_apply_of_ne (g := g) (ne_of_gt (lt_trans hz hr))]

/-- `Gbar` of `patch g` equals `Gbar` of `g` for `z > 0`. -/
theorem gbar_patch {α : ℝ} (g : Fn) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Gbar α (patch g) z = Work.Elliptic.Gbar α g z := by
  rw [Work.Elliptic.Gbar, Work.Elliptic.Gbar]
  congr 1
  rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [Fstar_patch g hs.1]

/-- `Gsing` of `patch g` equals `Gsing` of `g` at every `z > 0`. -/
theorem gsing_patch {α : ℝ} (g : Fn) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Gsing α (patch g) z = Work.Elliptic.Gsing α g z := by
  rw [Work.Elliptic.Gsing, Work.Elliptic.Gsing, gstar_patch g hz, gbar_patch g hz]

/-! ## The target -/

theorem gsing_tendsto_atTop_zero_of_classC {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 7 g) :
    Filter.Tendsto (fun z => Work.Elliptic.Gsing α g z) Filter.atTop (nhds 0) := by
  have hmem0 : Work.Spaces.HkMem α 0 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 0 (Nat.zero_le 7) hmem
  have hL2 : Work.Spaces.L2Mem (patch g) := L2Mem_patch hreg hmem0
  have h := Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero α (patch g) hα hL2
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  exact gsing_patch g (by linarith : 0 < z)

end Work.FTS.ClassC
