/-
# `Transfer/HkSq_Dz_le_Q0Sm.lean` — `|D_z X|²_{ℋ^m} ≤ |X|²_{ℋ^{m+1}}` at finite order

The transfer of the level-4 coercivity of the clean operator `𝓛̂` to the paper's operator
`𝓛_Γ^T` runs on the weakened additivity package `Assembly.Comm2w`, whose hypotheses are
*finite order* smoothness of the blocks on the open quadrant `Qd` (`Transfer.Q0Sm k X`)
rather than the analytic classes `SmoothNbhd`/`SmoothQuad` of the older chapters.  The
corresponding `ℋ^k`-norm estimate has to be available in the same class, and this file
supplies its **integrated** form:

  `HkSq α m (D_z X) ≤ HkSq α (m+1) X`  for `X ∈ C^{m+1}` on `Qd` and `X ∈ ℋ^{m+1}`.

The pointwise content (every summand of `HkIntegrand α m (D_z X)` is a summand of
`HkIntegrand α (m+1) X` with the same weight) is the sibling module
`Transfer/HkIntegrand_Dz_le_succ_Q0Sm.lean`; here it is stated there on the open quadrant,
while the two `HkSq`'s integrate over the closed domain `Iz × Iθ`, which differs from the
open quadrant by the two null sets `{z = 0}` and `{θ = 0, π/2}`.  So the assembly is:

* a.e. in `z ∈ Iz` the radius is positive (`ae_mem_Ioi_Iz_Q0Sm`), and a.e. in `θ ∈ Iθ` the
  angle lies in `(0, π/2)` (`ae_mem_Ioo_Iθ_Q0Sm`);
* the angular comparison `∫_θ HkIntegrand α m (D_z X) z · ≤ ∫_θ HkIntegrand α (m+1) X z ·`
  for such `z`, by `integral_mono_of_nonneg` (the dominating integrable function is the
  angular slice of `HkMem α (m+1) X`, the dominated one is nonnegative: the integrand is a
  sum of squares);
* the radial comparison over `z ∈ Iz`, again by `integral_mono_of_nonneg`, the radial
  integrability of the dominating function being the second half of `HkMem α (m+1) X`.

Unlike the corresponding `D_θ` statement, no hypothesis `0 < α` is needed: the pure family
keeps the lighter weight `w/√sin(2θ)^η` on both sides, and the mixed family keeps `W`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkIntegrand_Dz_le_succ_Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two null sets -/

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`: `Icc 0 (π/2)` and
`Ioo 0 (π/2)` coincide up to the null set of the two endpoints. -/
theorem ae_mem_Ioo_Iθ_Q0Sm :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- Almost every radius of `Iz = [0, ∞)` is positive: `Ici 0` and `Ioi 0` coincide up to the
null set `{0}`. -/
theorem ae_mem_Ioi_Iz_Q0Sm :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The integrated estimate -/

theorem HkSq_Dz_le_Q0Sm (α : ℝ) (m : ℕ) {X : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.Q0Sm (m + 1) X)
    (hm : Work.Spaces.HkMem α (m + 1) X) :
    Work.Spaces.HkSq α m (Work.Spaces.Dz X) ≤ Work.Spaces.HkSq α (m + 1) X := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  -- the outer (radial) comparison
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dz X) z θ) hm.2 ?_
  -- for a.e. `z ∈ Iz` the radius is positive, hence the pointwise domination applies a.e. in θ
  refine ae_mem_Ioi_Iz_Q0Sm.mono fun z hz => ?_
  have hzI : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dz X) z θ)
    (hm.1 z hzI) ?_
  exact ae_mem_Ioo_Iθ_Q0Sm.mono fun θ hθ =>
    HkIntegrand_Dz_le_succ_Q0Sm α m h z θ ⟨hz, hθ⟩

end Work.FTS.CoercivityFix.Transfer
