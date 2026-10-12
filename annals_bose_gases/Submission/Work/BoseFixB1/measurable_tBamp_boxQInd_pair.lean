import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.measurable_boxQInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.measurable_tBamp_boxQInd_pair`

Joint measurability of the squared windowed-exponential amplitude of FS's box mean-free
projection `Q_{B,i}Ψ = boxQInd volA A i Ψ` (FS `eq:HBU`) in the *pair* `q = (p, x)`,
where `p ∈ ℝ³` is the Fourier mode and `x ∈ X n` the configuration:

    (p, x) ↦ ‖tBamp χ p (boxQInd volA A i Ψ) i x‖ ^ 2

is `Measurable` for `A` a measurable box, `χ` a continuous window and `Ψ` a measurable
state.  This is the `(p, x)`-joint companion of the fixed-`p` measurability
`Work.FibreKinPot.Trunc.measurable_tBamp_of_measurable` and of the fixed-`u` sliding
companion `Work.BoseFixB1.aemeasurable_boxQInd_sliding`; it is the measurability input
for the `p`-space integration of the `p`-diagonal kinetic form
`Work.UBBInputs8.tBdiagFormInd` at a fixed state.

## The argument

Unfolding `tBamp` (which is a Bochner integral over `z ∈ ℝ³`),

    (p,x) ↦ ∫ z, (χ z : ℂ) · exp(−i⟪p,z⟫) · (boxQInd volA A i Ψ (x_{i←z}) : ℂ),

all of whose factors are jointly *measurable* in `((p,x), z)`:

* `χ` is continuous, hence `z ↦ χ z` is measurable;
* `((p,x), z) ↦ exp(−i⟪p,z⟫)` is (a continuous function of) `(p,z)`, composed with the
  measurable (indeed continuous) pairing `((p,x), z) ↦ (p, z)`;
* `((p,x), z) ↦ boxQInd volA A i Ψ (x_{i←z})`: `boxQInd` is measurable in its state
  argument by `Work.SlotWord.measurable_boxQInd`, and the update map
  `((p,x), z) ↦ x_{i←z}` is measurable by `Measurable.update'`.

The Bochner integral is measurable in the parameter by the parametric-integral
(Tonelli–Fubini for the marginal) measurability lemma
`MeasureTheory.StronglyMeasurable.integral_prod_right'` — a *measurability* statement, so
neither integrability nor finiteness nor any support hypothesis on `χ` is needed.  Passing
to `‖·‖ ^ 2` (continuous on `ℂ`) closes by `Measurable.norm` and `Measurable.pow_const`.
-/

namespace Work.BoseFixB1

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem measurable_tBamp_boxQInd_pair {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    {volA : ℝ} {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Measurable Ψ) (i : Fin n) :
    Measurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA A i Ψ) i q.2‖ ^ 2) := by
  -- the box mean-free projection is measurable in the state
  have hQm : Measurable (fun x : Submission.BoseGases.X n =>
      Work.UBBInputs8.boxQInd volA A i Ψ x) :=
    Work.SlotWord.measurable_boxQInd volA A hA i hΨ
  -- measurability of the amplitude in the pair `(p, x)`
  have hmeastB : Measurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA A i Ψ) i q.2) := by
    -- the jointly measurable integrand of the defining integral of `tBamp`
    have hJ : Measurable (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
        EuclideanSpace ℝ (Fin 3) =>
        (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ))) *
          (Work.UBBInputs8.boxQInd volA A i Ψ (Function.update q.1.2 i q.2) : ℂ)) := by
      have hexp : Measurable (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
          EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ q.1.1 q.2 : ℂ)))) := by
        have hpair : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
            EuclideanSpace ℝ (Fin 3) => (q.1.1, q.2)) := by fun_prop
        have hcont : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
            EuclideanSpace ℝ (Fin 3) => (inner ℝ q.1.1 q.2 : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_inner.comp hpair)
        exact (Complex.continuous_exp.comp ((continuous_const.mul hcont).neg)).measurable
      have hupd : Measurable (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
          EuclideanSpace ℝ (Fin 3) => Function.update q.1.2 i q.2) := by
        have hpair : Measurable (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) ×
            EuclideanSpace ℝ (Fin 3) => (q.1.2, q.2)) := by fun_prop
        exact (measurable_update' (X := fun _ : Fin n => EuclideanSpace ℝ (Fin 3))
          (a := i)).comp hpair
      refine Measurable.mul (Measurable.mul ?_ hexp) ?_
      · exact Complex.continuous_ofReal.measurable.comp (hχ.measurable.comp measurable_snd)
      · exact Complex.continuous_ofReal.measurable.comp (hQm.comp hupd)
    have hSM := hJ.stronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable
  exact hmeastB.norm.pow_const 2

end Work.BoseFixB1
