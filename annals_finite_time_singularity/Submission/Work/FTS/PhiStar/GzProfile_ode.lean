/-
# `GzProfile_ode`: the explicit radial profile solves the radial model equation

`GzProfile α = -Gsing α (Construction.Fstar α)` is the paper's explicit radial profile `G` of
§'The singular term'.  The general ODE for `Gsing` is `Work.Elliptic.Gsing_ode`:

`α²z² Gsing'' + α(5+α) z Gsing' = (15/4) F_*`

on `z > 0`, for any `F` whose angular moment `F_* = Fstar F` is differentiable and whose
primitive `∫_0^z s^{(5-α)/α} F_*(s) ds` has the expected derivative.  For the profile
`F = Construction.Fstar α` all three analytic hypotheses are elementary:

* `L₁₂(F_*) = 2α/(1+z)` (`Work.Elliptic.L12_profile`), so `z ↦ L₁₂(F_*)(z)` is the explicit
  rational function `z ↦ 2α/(1+z)` near every `z > 0`, with derivative `-2α/(1+z)²`; and
  `-3 F_*(z)/z = -2α/(1+z)²` because `F_*(z) = α (2z/(1+z)²)/3` (`EllFstar_Fstar`);
* `F_*` is the explicit rational function `z ↦ α (2z/(1+z)²)/3`, differentiable on `z > 0`;
* `s ↦ s^{(5-α)/α} F_*(s)` is continuous on `(-1,∞)` (the exponent `(5-α)/α ≥ 0`), so the
  fundamental theorem of calculus gives the derivative of its primitive.

Since `(15/4) F_*(z) = (15/4)·(α φ(z)/3) = (5α/4) φ(z)` with `φ = VocabO.phiR`, and since
`GzProfile α = -Gsing α F`, the sign flip turns `Gsing_ode` into

`-(α²z² Gz'') - α(5+α) z Gz' = (5α/4) φ(z)`,

which is exactly `GzOde α (GzProfile α)`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.H2.PhiStarE.Gbar_wiln

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem GzProfile_ode {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    GzOde α (GzProfile α) := by
  have hα1' : α ≤ 1 := by linarith
  -- The derivative of `z ↦ L₁₂(F_*)(z)`, from the explicit form `2α/(1+z)`.
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 (Work.Construction.Fstar α) z')
        (-(3 * Work.Elliptic.Fstar (Work.Construction.Fstar α) z / z)) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hev : (fun z' => Work.Elliptic.L12 (Work.Construction.Fstar α) z')
        =ᶠ[𝓝 z] (fun z' => 2 * α / (1 + z')) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
      have h := Work.Elliptic.L12_profile α hα hα1' z' (le_of_lt hz')
      rwa [show (fun w θ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w)
        = Work.Construction.Fstar α from rfl] at h
    have hder : HasDerivAt (fun z' : ℝ => 2 * α / (1 + z')) (-(2 * α) / (1 + z) ^ 2) z := by
      have hnum : HasDerivAt (fun _ : ℝ => 2 * α) 0 z := hasDerivAt_const z _
      have hden : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
        simpa using (hasDerivAt_id z).const_add 1
      have h := hnum.div hden (by linarith : (1 + z) ≠ 0)
      convert h using 1
      ring
    refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
    simp only [Work.FM.Fstar]
    field_simp
  -- `F_*` is differentiable on `z > 0`.
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar (Work.Construction.Fstar α))
        (deriv (Work.Elliptic.Fstar (Work.Construction.Fstar α)) z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    rw [hasDerivAt_deriv_iff]
    have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
    have hden : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
      have h := (hasDerivAt_id z).const_add 1
      convert h.pow 2 using 1
      · funext u; simp
      · simp
    have hnum : HasDerivAt (fun z : ℝ => α * (2 * z)) (α * 2) z := by
      simpa using ((hasDerivAt_id z).const_mul 2).const_mul α
    have hq : HasDerivAt (fun z : ℝ => α * (2 * z) / (1 + z) ^ 2)
        ((α * 2 * (1 + z) ^ 2 - α * (2 * z) * (2 * (1 + z))) / ((1 + z) ^ 2) ^ 2) z :=
      hnum.div hden (pow_ne_zero 2 hz1)
    have hq3 := hq.div_const 3
    rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
    simp only [Work.FM.Fstar]
    have hfun : (fun z : ℝ => α * (2 * z / (1 + z) ^ 2) / 3)
        = (fun z : ℝ => α * (2 * z) / (1 + z) ^ 2 / 3) := by
      funext u; ring
    rw [hfun]
    exact hq3.differentiableAt
  -- The primitive of `s ↦ s^{(5-α)/α} F_*(s)`, by the fundamental theorem of calculus.
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hq : 0 ≤ (5 - α) / α := by
      have h5 : (0 : ℝ) < 5 - α := by linarith
      positivity
    have hFon : ContinuousOn
        (fun s : ℝ => Work.Elliptic.Fstar (Work.Construction.Fstar α) s) (Set.Ioi (-1)) := by
      rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
      simp only [Work.FM.Fstar]
      apply ContinuousOn.div
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro s hs
          exact pow_ne_zero 2 (by linarith [show (-1 : ℝ) < s from hs])
      · exact continuousOn_const
      · intro s hs; norm_num
    have hon : ContinuousOn (fun s : ℝ =>
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) s) (Set.Ioi (-1)) :=
      (Real.continuous_rpow_const hq).continuousOn.mul hFon
    have hsub : Set.Icc (0 : ℝ) z ⊆ Set.Ioi (-1) := fun s hs => by
      simp only [Set.mem_Ioi]; linarith [hs.1, hzpos]
    have hInt : IntervalIntegrable (fun s : ℝ =>
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) s) volume 0 z := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le]
      exact ((hon.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hz1 : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    exact intervalIntegral.integral_hasDerivAt_right hInt
      (hon.stronglyMeasurableAtFilter isOpen_Ioi z hz1) (hon.continuousAt (isOpen_Ioi.mem_nhds hz1))
  intro z hz
  have hode := Work.Elliptic.Gsing_ode α (Work.Construction.Fstar α) hα hL12 hFc hJ z hz
  -- `(15/4) F_*(z) = (5α/4) φ(z)` for the profile.
  have hval : (15 / 4) * Work.Elliptic.Fstar (Work.Construction.Fstar α) z
      = (5 * α / 4) * Work.FTS.VocabO.phiR z := by
    rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
    rw [show Work.FTS.VocabO.phiR = Work.FM.Fstar from rfl]
    simp only [Work.FM.Fstar]
    ring
  -- `GzProfile = -Gsing`: the derivatives flip sign.
  have hd1 : deriv (GzProfile α) z
      = - deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z := by
    have h1 : GzProfile α = -(Work.Elliptic.Gsing α (Work.Construction.Fstar α)) := rfl
    rw [h1, deriv.neg]
  have h2 : iteratedDeriv 2 (GzProfile α) z
      = - iteratedDeriv 2 (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z := by
    change iteratedDeriv 2 (fun z => -(Work.Elliptic.Gsing α (Work.Construction.Fstar α) z)) z = _
    rw [iteratedDeriv_fun_neg]
  have h2b : iteratedDeriv 2 (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z
      = deriv (fun z' => deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z') z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2b, hd1]
  rw [show -(α ^ 2 * z ^ 2 * (-(deriv (fun z' =>
            deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z') z)))
      - α * (5 + α) * z * (-(deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z))
      = α ^ 2 * z ^ 2 * deriv (fun z' =>
            deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z
      from by ring, hode, hval]

end Work.FTS.PhiStar
