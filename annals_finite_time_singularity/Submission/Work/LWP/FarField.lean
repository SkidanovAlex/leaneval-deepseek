/-
# `Work.LWP.FarField` — the far-field estimates consumed by the Stability layer's `St4`

The Stability layer's far-field step needs, for a vorticity supported in a ball of radius `R`,
the decay of the velocity and of its derivative at infinity

  `‖BS ω x‖ ≤ C R³ / ‖x‖²`,  `‖D BS ω x‖ ≤ C R³ / ‖x‖³`   for `‖x‖ ≥ 2R`,

*uniformly in time*, so that the far-field part of the solution is controlled by support transport
alone.  The pointwise statements are proved in `Submission/Work/LWP/BiotSavart/`
(`Work.LWP.BiotSavart.farField_decay_const`, `Work.LWP.BiotSavart.farField_decay_fderiv_const`);
this module records the uniform-in-time forms.

The companion hypothesis — that the support of the vorticity *stays* in a fixed ball — is the
transport statement `Work.LWP.Transport.support_transport` together with the flow theory of
`Work.LWP.Flow`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.BiotSavart
import Submission.Work.LWP.BiotSavart.farField_decay_const
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv_const

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-- **Far-field decay of the velocity, uniform in time.**  If the vorticity is supported in
`B(0,R)` and bounded by `M` at every time `t ∈ [0,T)`, then `u(·,t) = biotSavart (ω(·,t))` obeys
the `‖x‖⁻²` far-field bound with a constant independent of `t`. -/
theorem farField_decay_uniform {ω : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ t ∈ Ico 0 T, ∀ y : R3, ‖ω y t‖ ≤ M)
    (hsupp : ∀ t ∈ Ico 0 T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ t ∈ Ico 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖biotSavart (fun y => ω y t) x‖ ≤ (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2 :=
  fun t ht x hx =>
    BiotSavart.farField_decay_const hR hM (fun y => hω t ht y) (fun y => hsupp t ht y) x hx

/-- A variant with the support hypothesis phrased as a bound on the slice supports: if every slice
`ω(·,t)`, `t ∈ [0,T)`, is supported in the *fixed* ball `B(0,R)` and bounded by `M`, the far-field
estimate holds uniformly. -/
theorem farField_decay_uniform_of_support {ω : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ t ∈ Ico 0 T, ∀ y : R3, ‖ω y t‖ ≤ M)
    (hsupp : ∀ t ∈ Ico 0 T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖biotSavart (fun y => ω y t) x‖ ≤ C * M * R ^ 3 / ‖x‖ ^ 2 :=
  ⟨4 / 3, by norm_num, farField_decay_uniform hR hM hω hsupp⟩


/-- **Far-field decay of the derivative, uniform in time.**  If the vorticity is supported in
`B(0,R)` and bounded by `M` at every time, then `D (biotSavart (ω(·,t)))` obeys the `‖x‖⁻³`
far-field bound with a constant independent of `t`. -/
theorem farField_decay_fderiv_uniform {ω : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hω : ∀ t ∈ Ico 0 T, ∀ y : R3, ‖ω y t‖ ≤ M)
    (hsupp : ∀ t ∈ Ico 0 T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ t ∈ Ico 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (biotSavart (fun y => ω y t)) x‖ ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3 :=
  fun t ht x hx =>
    BiotSavart.farField_decay_fderiv_const hR hM (fun y => hω t ht y) (fun y => hsupp t ht y) x hx

/-- **The `St4` far-field package**: for a vorticity whose slices are uniformly supported in
`B(0,R)` and uniformly bounded by `M`, both the velocity and its derivative obey their far-field
bounds with constants independent of time. -/
theorem farField_decay_uniform_pair {ω : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hω : ∀ t ∈ Ico 0 T, ∀ y : R3, ‖ω y t‖ ≤ M)
    (hsupp : ∀ t ∈ Ico 0 T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    (∀ t ∈ Ico 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖biotSavart (fun y => ω y t) x‖ ≤ (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2) ∧
    (∀ t ∈ Ico 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (biotSavart (fun y => ω y t)) x‖ ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3) :=
  ⟨farField_decay_uniform hR.le hM hω hsupp, farField_decay_fderiv_uniform hR hM hω hsupp⟩

end Work.LWP
