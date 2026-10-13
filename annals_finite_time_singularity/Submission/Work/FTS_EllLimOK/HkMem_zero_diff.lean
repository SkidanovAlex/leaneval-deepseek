/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_EllLimOK.HkMem_zero_diff` — `ℋ⁰` is closed under the difference of two `BoxReg`
profiles

The uniqueness obligation `Defs3.ClosedUniq3` compares two jet-cluster-limits `Ψ`, `Ψ'` of the same
operator.  Both satisfy `HkMem α 0` (the *lower* vanishing condition `∫ (f·w)² < ∞`, `w ~ 1/z²`) and
both are `BoxReg` (jointly `C²` on every closed box `[a,b] × [0,π/2]`, `0 < a ≤ b`).  The
difference `diff Ψ Ψ' = (fun z θ => Ψ z θ - Ψ' z θ)` must again satisfy `HkMem α 0`, because the
whole energy method of the chapter runs on it.

At level `0` the `ℋ⁰`-integrand is a *single square*

`HkIntegrand α 0 f z θ = (f z θ · w z / sin(2θ)^{η/2})²`

(the `D_z`-sum has the one term `i = 0` and the mixed double sum is empty), so the difference of
two members is dominated pointwise by

`HkIntegrand α 0 (f - g) ≤ 2·HkIntegrand α 0 f + 2·HkIntegrand α 0 g`,

which is precisely the shape of the majorant lemma `Work.FTS.LocData.HkMem_of_majorant`.  The only
thing that lemma still needs is the *measurability* of the integrand of the difference, and this is
where `BoxReg` is used: on the open quadrant `(0,∞) × (0,π/2)` the difference of two `BoxReg`
profiles is `C²` (`BoxReg.diff`, `BoxReg.contDiffOn_Qd`), the slot weight
`w z / sin(2θ)^{η/2}` is continuous there (its denominator `sin(2θ)` is strictly positive on
`(0,π/2)`), and hence the `ℋ⁰`-integrand of the difference is continuous on the open quadrant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.UniqDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- At level `k = 0` the `ℋ⁰`-integrand collapses to a single square: the `D_z`-sum has the one
term `i = 0` and the mixed double sum is empty. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The radial slot weight `z ↦ w z` is continuous on `(0,∞)`. -/
theorem continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
  refine ContinuousOn.div ?_ ?_ ?_
  · exact ((continuous_const.add continuous_id).pow 2).continuousOn
  · exact (continuous_id.pow 2).continuousOn
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)

/-- The angular slot weight `θ ↦ sin(2θ)^{η/2}` is continuous on `(0,π/2)`. -/
theorem continuousOn_sin_two_rpow :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (π / 2)) := by
  refine ContinuousOn.rpow_const ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · intro θ _
    exact Or.inr (by rw [Work.Spaces.eta]; norm_num)

/-- The full slot weight `(z,θ) ↦ w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_slotWeight :
    ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · exact continuousOn_w.comp continuousOn_fst (fun p hp => hp.1)
  · exact continuousOn_sin_two_rpow.comp continuousOn_snd (fun p hp => hp.2)
  · intro p hp
    have h2 : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
    exact ne_of_gt (Real.rpow_pos_of_pos h2 _)

/-- The `ℋ⁰`-integrand of a function continuous on the open quadrant is continuous there. -/
theorem continuousOn_HkIntegrand_zero (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  ContinuousOn.congr ((hf.mul continuousOn_slotWeight).pow 2)
    (fun p _ => HkIntegrand_zero_eq α f p.1 p.2)

/-- `(x - y)² ≤ 2x² + 2y²` (the elementary majorant used below). -/
private theorem sq_sub_le_two (x y : ℝ) : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

theorem HkMem_zero_diff {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hΨ' : Work.Spaces.HkMem α 0 Ψ')
    (hbΨ : Work.FTS_EllLimOK.BoxReg Ψ) (hbΨ' : Work.FTS_EllLimOK.BoxReg Ψ') :
    Work.Spaces.HkMem α 0 (Work.FTS_EllLimOK.diff Ψ Ψ') := by
  -- The difference of two `BoxReg` profiles is continuous on the open quadrant.
  have hcont : ContinuousOn (Function.uncurry (diff Ψ Ψ'))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    ((BoxReg.diff hbΨ hbΨ').contDiffOn_Qd).continuousOn
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
      + 2 * Work.Spaces.HkIntegrand α 0 Ψ' z θ)
    (continuousOn_HkIntegrand_zero α hcont) ?_ ?_ ?_
  · -- the angular slices of the majorant are integrable
    intro z hz
    exact ((hΨ.1 z hz).const_mul 2).add ((hΨ'.1 z hz).const_mul 2)
  · -- the `θ`-integral of the majorant is integrable
    refine MeasureTheory.IntegrableOn.congr_fun
      ((hΨ.2.const_mul 2).add (hΨ'.2.const_mul 2)) ?_ measurableSet_Ici
    intro z hz
    show 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)
      = ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
          + 2 * Work.Spaces.HkIntegrand α 0 Ψ' z θ)
    rw [integral_add ((hΨ.1 z hz).const_mul 2) ((hΨ'.1 z hz).const_mul 2),
      integral_const_mul, integral_const_mul]
  · -- the pointwise domination by the majorant
    intro z _ θ _
    rw [HkIntegrand_zero_eq α (diff Ψ Ψ') z θ, HkIntegrand_zero_eq α Ψ z θ,
      HkIntegrand_zero_eq α Ψ' z θ, diff_apply]
    nlinarith [sq_sub_le_two
      (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

end Work.FTS_EllLimOK
