import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# Measurability of the shifted integral `g ↦ ∫ u, f (g * u) ∂α`

Let `G = SL₃(ℝ) = Work.EKLContract.SL3`. For a compactly supported continuous function
`f : G → ℝ` and a Borel measure `α` on `G` which is finite on compact sets, the left translate
integral

    g ↦ ∫ u, f (g * u) ∂α

is Borel measurable.  This is the measurability input used whenever a leafwise measure
`μ_x^U` is tested against a translate of a fixed compactly supported continuous function
(the `condexp` field of `Work.EKLContract.IsLeafwise`).

Mathematically: `G` is a σ-compact locally compact group, so `α` is σ-finite; the uncurried
integrand `(g, u) ↦ f (g * u)` is continuous, hence strongly measurable; and the integral of a
strongly measurable function with respect to a σ-finite kernel is strongly measurable
(`MeasureTheory.StronglyMeasurable.integral_kernel_prod_right`, applied to the constant kernel
`ProbabilityTheory.Kernel.const G α`).

Formally, the only missing library input is the topology of `G`: Mathlib cannot synthesize
`SecondCountableTopology`, `LocallyCompactSpace` or `SigmaCompactSpace` for
`Matrix.SpecialLinearGroup (Fin 3) ℝ`, because `Matrix` is a plain `def` which instance search
does not unfold.  We build the needed instances *locally inside the proof* (the matrix space is
a finite product of copies of `ℝ`, and `SL₃(ℝ)` is the closed locus `det = 1`), so that this
module neither depends on nor pollutes the global instance space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

set_option linter.style.haveILetI false

namespace Work.EKLC6Core

theorem measurable_shift_integral {α : MeasureTheory.Measure Work.EKLContract.SL3}
    [MeasureTheory.IsFiniteMeasureOnCompacts α]
    (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) :
    Measurable (fun g : Work.EKLContract.SL3 => ∫ u, f (g * u) ∂α) := by
  -- The matrix space is a finite product of copies of `ℝ`, hence second countable and
  -- locally compact, and `SL₃(ℝ)` is the closed subset `{A | det A = 1}` of it.
  haveI hMat2 : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  haveI hMatLC : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  have hClosed : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} :=
    isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const
  haveI hSL2 : SecondCountableTopology Work.EKLContract.SL3 :=
    inferInstanceAs
      (SecondCountableTopology ↥({A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} : Set _))
  haveI hSLLC : LocallyCompactSpace Work.EKLContract.SL3 := hClosed.locallyCompactSpace
  -- Hence `SL₃(ℝ)` is σ-compact, so `α` is σ-finite (finite on compacts).
  haveI hSLσ : SigmaCompactSpace Work.EKLContract.SL3 := inferInstance
  -- The uncurried integrand `(g, u) ↦ f (g * u)` is continuous, hence strongly measurable.
  have hcont : Continuous
      (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => f (p.1 * p.2)) := by
    fun_prop
  have hsm : StronglyMeasurable
      (Function.uncurry (fun g u : Work.EKLContract.SL3 => f (g * u))) :=
    hcont.stronglyMeasurable
  -- Integrate against the constant (s-finite) kernel `u ↦ α`.
  have h2 := StronglyMeasurable.integral_kernel_prod_right
    (κ := ProbabilityTheory.Kernel.const Work.EKLContract.SL3 α) hsm
  simpa [ProbabilityTheory.Kernel.const_apply] using h2.measurable

end Work.EKLC6Core
