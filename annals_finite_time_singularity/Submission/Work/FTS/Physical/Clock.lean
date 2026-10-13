/-
# `Work.FTS.Physical.Clock` — the clock `τ ↦ t` of the dynamic rescaling (umbrella)

The amplitude `A(τ)` of the rescaled solution solves `A' = -(1+μ)A` with `1/2 ≤ 1+μ ≤ 2`.  This
module collects the consequences that the physical reconstruction uses; each is proved in its own
file of the `Clock/` directory and re-exported here under the stable name `PhysClock.<lemma>`:

* `A s ≤ A τ · e^{-(s-τ)/2}` for `τ ≤ s` (`Clock/A_le_exp_mul`), whence `A` is integrable on
  `[0,∞)` (`Clock/integrableOn_A`): the blow-up happens in finite time;
* `t(τ) = ∫₀^τ A` is strictly increasing (`Clock/t_strictMonoOn`) with `t'(τ) = A(τ) > 0`
  (`Clock/hasDerivAt_t`);
* the **tail identity** `T - t(τ) = ∫_τ^∞ A` (`Clock/T_sub_t_eq_tail`) and the **comparison**
  `T - t(τ) ≤ 2 A(τ)` (`Clock/tail_le_two_mul`) — the quantitative form `A ≍ T - t` of the clock,
  which is exactly the input of the `c/(T-t)` vorticity lower bound;


The inhabitation obligation of `PhysClock` is discharged by the explicit clock
`PhysClock.expClock` (`A(τ) = e^{-τ}`, `μ = 0`), giving the `Inhabited` instance below.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.A_le_exp_mul
import Submission.Work.FTS.Physical.Clock.integrableOn_A
import Submission.Work.FTS.Physical.Clock.T_sub_t_eq_tail
import Submission.Work.FTS.Physical.Clock.tail_le_two_mul
import Submission.Work.FTS.Physical.Clock.hasDerivAt_t
import Submission.Work.FTS.Physical.Clock.t_strictMonoOn
import Submission.Work.FTS.Physical.Clock.T_pos
import Submission.Work.FTS.Physical.Clock.continuousOn_t
import Submission.Work.FTS.Physical.Clock.tendsto_t_atTop
import Submission.Work.FTS.Physical.Clock.exists_t_eq
import Submission.Work.FTS.Physical.Clock.exists_inverse_clock
import Submission.Work.FTS.Physical.Clock.clock_slope_tendsto
import Submission.Work.FTS.Physical.Clock.A_le_two_mul_tail
import Submission.Work.FTS.Physical.Clock.clockInv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal Interval

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-- **The exponential clock** `A(τ) = e^{-τ}`, `μ = 0`: the inhabitation obligation of
`PhysClock`.  Here `1 + μ = 1`, the modulation ODE is `A' = -A`, and the decay bound
`A s ≤ A τ e^{-(s-τ)/2}` is an equality. -/
noncomputable def expClock : PhysClock where
  A := fun τ => Real.exp (-τ)
  mu := fun _ => 0
  hApos := by intro τ _; exact Real.exp_pos _
  hAcont := (Real.continuous_exp.comp continuous_neg).continuousOn
  hAderiv := by
    intro τ _
    have h2 : HasDerivAt (fun x : ℝ => -x) (-1) τ := (hasDerivAt_id τ).neg
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-τ) * (-1)) τ :=
      (Real.hasDerivAt_exp (-τ)).comp τ h2
    have h4 : Real.exp (-τ) * (-1) = -((1 : ℝ) + 0) * Real.exp (-τ) := by ring
    rw [h4] at h3
    exact h3
  hmu_lo := by intro τ _; norm_num
  hmu_hi := by intro τ _; norm_num

noncomputable instance : Inhabited PhysClock := ⟨expClock⟩

/-- `A` is nonnegative in fake time. -/
theorem PhysClock.A_nonneg (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ C.A τ :=
  (C.hApos τ hτ).le

/-- **The decay bound**: `A` decreases at least as fast as `e^{-τ/2}`.  This is the only place
where the modulation bound `1 + μ ≥ 1/2` is used. -/
theorem PhysClock.A_le_exp_mul (C : PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A s ≤ C.A τ * Real.exp (-(s - τ) / 2) :=
  Work.FTS.Physical.Clock.A_le_exp_mul C hτ hτs

/-- **`A` decays exponentially**: in particular `A τ ≤ A 0 · e^{-τ/2}`. -/
theorem PhysClock.A_le_initial (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.A τ ≤ C.A 0 * Real.exp (-τ / 2) := by
  simpa using C.A_le_exp_mul le_rfl hτ

/-- **`A` is integrable on `[0,∞)`**: the blow-up happens in finite time and
`T = ∫₀^∞ A < ∞`. -/
theorem PhysClock.integrableOn_A (C : PhysClock) : IntegrableOn C.A (Set.Ici 0) :=
  Work.FTS.Physical.Clock.integrableOn_A C

/-- **The tail identity** `T - t(τ) = ∫_τ^∞ A ds`. -/
theorem PhysClock.T_sub_t_eq_tail (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.T - C.t τ = ∫ s in Set.Ici τ, C.A s :=
  Work.FTS.Physical.Clock.T_sub_t_eq_tail C hτ

/-- **The clock comparison** `T - t(τ) ≤ 2 A(τ)`: the physical time left to blow-up is comparable
to the amplitude. -/
theorem PhysClock.tail_le_two_mul (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.T - C.t τ ≤ 2 * C.A τ :=
  Work.FTS.Physical.Clock.tail_le_two_mul C hτ

/-- **`t' = A`**: the physical time is the integral of the amplitude. -/
theorem PhysClock.hasDerivAt_t (C : PhysClock) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt C.t (C.A τ) τ :=
  Work.FTS.Physical.Clock.hasDerivAt_t C hτ

/-- `t = ∫₀^τ A` is strictly increasing on the fake-time half-line. -/
theorem PhysClock.t_strictMonoOn (C : PhysClock) : StrictMonoOn C.t (Set.Ici 0) :=
  Work.FTS.Physical.Clock.t_strictMonoOn C

/-- `t` is continuous on `[0,∞)`. -/
theorem PhysClock.continuousOn_t (C : PhysClock) : ContinuousOn C.t (Set.Ici 0) :=
  Work.FTS.Physical.Clock.continuousOn_t C

/-- The blow-up time is positive. -/
theorem PhysClock.T_pos (C : PhysClock) : 0 < C.T :=
  Work.FTS.Physical.Clock.T_pos C

/-- **`t(τ) → T`** as `τ → ∞`: the physical time exhausts the blow-up interval. -/
theorem PhysClock.tendsto_t_atTop (C : PhysClock) : Tendsto C.t atTop (𝓝 C.T) :=
  Work.FTS.Physical.Clock.tendsto_t_atTop C

/-- **Surjectivity of the clock.**  Every physical time `t ∈ [0,T)` is `t(τ)` for some fake time
`τ ≥ 0`; this is the abstract form of the existence of the inverse clock `t ↦ τ(t)`. -/
theorem PhysClock.exists_t_eq (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    ∃ τ : ℝ, 0 ≤ τ ∧ C.t τ = t :=
  Work.FTS.Physical.Clock.exists_t_eq C ht

/-- **The clock comparison at a prescribed physical time.**  Every physical time `t ∈ [0,T)` is
realised by a fake time `τ ≥ 0` at which the remaining time is bounded by `2 A τ`:
`T - t ≤ 2 A(τ(t))`.  This is the form in which the `c/(T-t)` vorticity lower bound consumes the
clock. -/
theorem PhysClock.exists_tau_with_tail (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    ∃ τ : ℝ, 0 ≤ τ ∧ C.t τ = t ∧ C.T - t ≤ 2 * C.A τ := by
  obtain ⟨τ, hτ, hτt⟩ := C.exists_t_eq ht
  exact ⟨τ, hτ, hτt, by rw [← hτt]; exact C.tail_le_two_mul hτ⟩

/-- **The inverse clock.**  There is a function `τ : ℝ → ℝ` with `t(τ(t)) = t`, `τ(t) ≥ 0`,
`T - t ≤ 2 A(τ(t))` for every `t ∈ [0,T)`, differentiable on `(0,T)` with `τ'(t) = 1/A(τ(t))`. -/
theorem PhysClock.exists_inverse_clock (C : PhysClock) :
    ∃ tau : ℝ → ℝ, (∀ t ∈ Set.Ico 0 C.T, C.t (tau t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ tau t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (tau t)) ∧
      ∀ t ∈ Set.Ioo 0 C.T, HasDerivAt tau ((C.A (tau t))⁻¹) t :=
  Work.FTS.Physical.Clock.exists_inverse_clock C

/-- **The lower half of the clock comparison**: `A τ ≤ 2 (T - t τ)`.  Together with
`tail_le_two_mul` this is `A(τ) ≍ T - t(τ)`; it is the input that converts a lower bound
`‖ω(·,t)‖ ≥ c/A(τ(t))` into the blow-up rate `c'/(T-t)`. -/
theorem PhysClock.A_le_two_mul_tail (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.A τ ≤ 2 * (C.T - C.t τ) :=
  Work.FTS.Physical.Clock.A_le_two_mul_tail C hτ

/-- **The extended inverse clock** `Work.FTS.Physical.clockInv`: the inverse clock continued to the
left of `0` by its tangent line, so that it is differentiable at `0` as well. -/
noncomputable abbrev PhysClock.clockInv (C : PhysClock) : ℝ → ℝ := Work.FTS.Physical.clockInv C

end Work.FTS.Physical
