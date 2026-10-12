import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.lowMult_eq_zero_of_not_integrable`

The low-momentum multiplier `Work.BoseBoxFix.lowMult fc κ ℓ ψ` (FS §7, `Q_L = Q f_L(√−Δ)`) is
*defined* as the free-space Fourier-multiplier integral

`lowMult fc κ ℓ ψ x = (2π)⁻³ Re ∫_p e^{i⟪p,x⟫} f(‖p‖/κ) · kinFT (1_{acube ℓ}·ψ) p dp`

(`Submission/WorK/SmallBoxBridge/Defs.lean`, with `Submission.BoseGases.kinFT u p = ∫_y e^{−i⟪p,y⟫}u y dy`).
Both integrals are Bochner integrals, hence vanish on non-integrable integrands
(`MeasureTheory.integral_undef`).  Consequently, whenever the box restriction `1_{acube ℓ}·ψ` fails
to be integrable, the *inner* transform `kinFT (1_{acube ℓ}·ψ)` is the junk value `0` for **every**
frequency `p`, and the outer integral is therefore `0` as well: the multiplier degenerates to the
zero function.  That is the content of the target lemma.  (The hypothesis `0 < ℓ` is not needed:
the degeneration is independent of the box size.)

The two reusable ingredients are recorded separately:

* `not_integrable_ofReal` — non-integrability passes from an `ℝ`-valued function to its `ℂ`-valued
  coercion (taking real parts would produce an integral of the given real function);
* `kinFT_eq_zero_of_not_integrable` — `kinFT u p = 0` for every `p` when `u` is not integrable:
  multiplication by the unit-modulus factor `e^{i⟪p,·⟫} = (e^{−i⟪p,·⟫})⁻¹` preserves integrability,
  so the integrand of `kinFT` is non-integrable too and `MeasureTheory.integral_undef` applies.
-/

namespace Work.PCFU

open MeasureTheory

set_option linter.unusedVariables false

noncomputable section

/-- Non-integrability passes from an `ℝ`-valued function to its `ℂ`-valued coercion: the two
functions have the same norm, and `ℂ`-integrability would imply `ℝ`-integrability by taking real
parts (`Integrable.re`, `Complex.ofReal_re`). -/
lemma not_integrable_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : ¬ MeasureTheory.Integrable f μ) :
    ¬ MeasureTheory.Integrable (fun z => (f z : ℂ)) μ := by
  intro hInt
  exact hf (hInt.re.congr (Filter.Eventually.of_forall fun z => by simp))

/-- `Submission.BoseGases.kinFT u p` is the Bochner integral `∫ y, e^{−i⟪p,y⟫} · u y`, and
multiplication by the unit-modulus factor `e^{i⟪p,y⟫}` preserves integrability, because
`e^{i⟪p,y⟫} · (e^{−i⟪p,y⟫} · u y) = u y`.  Hence a non-integrable `u` gives a non-integrable
integrand, so the integral is the junk value `0`, for every frequency `p`. -/
lemma kinFT_eq_zero_of_not_integrable {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : ¬ MeasureTheory.Integrable u) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT u p = 0 := by
  rw [Submission.BoseGases.kinFT]
  refine MeasureTheory.integral_undef ?_
  intro hInt
  refine hu ((hInt.bdd_mul (c := 1) (f := fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (Complex.I * (inner ℝ p y : ℂ))) ?_ ?_).congr
      (Filter.Eventually.of_forall fun y => ?_))
  · fun_prop
  · filter_upwards with y
    exact le_of_eq (by rw [Complex.norm_exp]; simp)
  · show Complex.exp (Complex.I * (inner ℝ p y : ℂ)) *
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u y) = u y
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem lowMult_eq_zero_of_not_integrable {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ¬ MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.acube ℓ).indicator ψ u)) :
    Work.BoseBoxFix.lowMult fc κ ℓ ψ = 0 := by
  funext x
  rw [Work.BoseBoxFix.lowMult]
  have hkin : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p = 0 :=
    fun p => kinFT_eq_zero_of_not_integrable (not_integrable_ofReal h) p
  simp [hkin]

end

end Work.PCFU
