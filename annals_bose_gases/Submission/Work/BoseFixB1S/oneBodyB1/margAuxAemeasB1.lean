import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.oneBodyB1.corrInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneBodyB1.margAuxAemeasB1` — a.e. measurability of the windowed cut word

The target is the measurability half of the `u`-marginal of the windowed `bsW`-word

    `u ↦ bsW (fsKinCoeff c) (fun z ↦ chiB ℓ d u z * W u z)`,

with a kernel `W : ℝ³ → ℝ³ → ℝ` that is only **jointly measurable**
(`hW : Measurable (Function.uncurry W)`) — in particular it may depend on `u` in a
non-continuous way.  (The sibling statement
`Work.BoseFixB1S.oneBodyB1.aestronglyMeasurable_bsW_sliding` treats the *continuous*
kernel; the present one is the general measurable case needed by the
`CorrInputB1`/`marginalB1` interface.)

The argument is the standard `integral_prod_right'` device, used twice (compare
`Work.OneBodyKin.MeasurableBSOneBody` and `Work.hlocWire2.tBdiagFormInd_slot_aemeas`):
`kinFT`, and then `bsW` itself, are *parametric Bochner integrals* over all of `ℝ³`,
where no integrability is available on the integrand; strong measurability of a
partial integral **without** integrability hypotheses is exactly what
`MeasureTheory.StronglyMeasurable.integral_prod_right'` supplies.

Concretely:

* the joint integrand `J ((u,p),z) = e^{−i⟪p,z⟫}·(χ_{B(u)}(z)·W u z : ℂ)` is strongly
  measurable on `(ℝ³ × ℝ³) × ℝ³`: the exponential is continuous, `χ_{B(u)}` is jointly
  continuous (`chiB ℓ d u z = chiScale ℓ z · chiScale (ℓd)(z − (ℓd)•u)`, a product of
  compositions of the continuous bump `chi`), and `W` is measurable, hence strongly
  measurable on the second-countable `ℝ`, while `ℝ → ℂ` is continuous;
* integrating out `z` gives `(u,p) ↦ kinFT (χ_{B(u)}·W u·) p` strongly measurable;
* multiplying by `fsKinCoeff c ‖p‖` (continuous) and `‖·‖²` keeps it;
* integrating out `p` gives strong measurability of `u ↦ bsW (fsKinCoeff c)(…)`, so a
  fortiori `AEMeasurable` against `volume`.

No positivity of `ℓ`, `d` and no integrability of `W` is used.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.BoseFixB1S.oneBodyB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem margAuxAemeasB1 {ℓ d c : ℝ}
    {W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : Measurable (Function.uncurry W)) :
    AEMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiB ℓ d u z * W u z))
      MeasureTheory.volume := by
  classical
  -- The joint `(u,p,z)`-integrand of the two nested Bochner integrals.
  let J : (E3 × E3) × E3 → ℂ := fun q =>
    Complex.exp (-(Complex.I * (inner ℝ q.1.2 q.2 : ℂ))) *
      ((Submission.BoseGases.chiB ℓ d q.1.1 q.2 * W q.1.1 q.2 : ℝ) : ℂ)
  -- `χ_{B(u)}(z)` is *jointly* continuous in `(u,z)` (no positivity of `ℓ`,`d` needed).
  have hchiBc : Continuous (fun q : (E3 × E3) × E3 =>
      Submission.BoseGases.chiB ℓ d q.1.1 q.2) := by
    unfold Submission.BoseGases.chiB Submission.BoseGases.chiScale
    exact (Submission.BoseGases.chi_continuous.comp (by fun_prop)).mul
      (Submission.BoseGases.chi_continuous.comp (by fun_prop))
  -- `W` read on the product is strongly measurable (`ℝ` is second countable).
  have hWsm : StronglyMeasurable (fun q : (E3 × E3) × E3 => W q.1.1 q.2) :=
    (hW.comp (by fun_prop : Measurable
      (fun q : (E3 × E3) × E3 => (q.1.1, q.2)))).stronglyMeasurable
  have hprod : StronglyMeasurable (fun q : (E3 × E3) × E3 =>
      Submission.BoseGases.chiB ℓ d q.1.1 q.2 * W q.1.1 q.2) :=
    hchiBc.stronglyMeasurable.mul hWsm
  have hJ : StronglyMeasurable J := by
    refine (by fun_prop : Continuous (fun q : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.2 q.2 : ℂ))))).stronglyMeasurable.mul ?_
    exact Complex.continuous_ofReal.comp_stronglyMeasurable hprod
  -- Integrate out the position `z`: the `(u,p) ↦ kinFT` map.
  have hK : StronglyMeasurable (fun q : E3 × E3 => ∫ z : E3, J (q, z)) :=
    hJ.integral_prod_right' (ν := MeasureTheory.volume)
  have hfs : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
    unfold Submission.BoseGases.fsKinCoeff
    fun_prop
  -- Attach the symbol `fsKinCoeff c ‖p‖` and the squared norm.
  have hG : StronglyMeasurable (fun q : E3 × E3 =>
      Submission.BoseGases.fsKinCoeff c ‖q.2‖ * ‖(∫ z : E3, J (q, z))‖ ^ 2) :=
    ((hfs.comp continuous_norm).measurable.comp measurable_snd).stronglyMeasurable.mul
      (hK.norm.pow 2)
  -- Integrate out the momentum `p`: the `u ↦ bsW …` map.
  have hfinal : StronglyMeasurable (fun u : E3 =>
      ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖(∫ z : E3, J ((u, p), z))‖ ^ 2) :=
    hG.integral_prod_right' (ν := MeasureTheory.volume)
  simpa only [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi,
    Submission.BoseGases.kinFT, J] using hfinal.aemeasurable

end Work.BoseFixB1S.oneBodyB1
