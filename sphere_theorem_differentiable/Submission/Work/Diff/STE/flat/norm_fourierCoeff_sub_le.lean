/-
# Sup-norm bound for the difference of Fourier coefficients

If two functions agree up to `C` in the sup norm on the unit cube, then every Fourier
coefficient of their difference is bounded by `C`.  This is the elementary "Fourier
coefficients are contractions" estimate used by the flat (torus) short-time-existence
argument: it controls the Galerkin right-hand side in terms of a sup-norm bound.

The only measure-theoretic content is that `f` and `g` are continuous on the *closed* cube
(so that the coefficient integrals exist and the integral is additive), while the sup-norm
bound is assumed on the half-open cube `(0,1]ⁿ` (a fundamental domain for the torus).
-/
import Mathlib
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.LayerA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory

/-- A function continuous on the closed cube is integrable on the (bounded) unit cube. -/
lemma integrableOn_unitCube_of_continuousOn {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : ContinuousOn F (Work.Diff.STE.Flat.Galerkin.closedCube n)) :
    Integrable F (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
  (ContinuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc) hF).mono_set
    (by
      intro x hx
      simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
      exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩)

/-- The volume of the restricted unit cube, as a real number, is `1`. -/
lemma real_univ_restrict_unitCube (n : ℕ) :
    (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))).real Set.univ = 1 := by
  rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Work.Diff.STE.volume_unitCube, ENNReal.toReal_one]

theorem norm_fourierCoeff_sub_le {n : ℕ} {f g : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (Work.Diff.STE.Flat.Galerkin.closedCube n))
    (hg : ContinuousOn g (Work.Diff.STE.Flat.Galerkin.closedCube n))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n), ‖f x - g x‖ ≤ C) (k : Fin n → ℤ) :
    ‖Work.Diff.STE.fourierCoeff f k - Work.Diff.STE.fourierCoeff g k‖ ≤ C := by
  have iF : Integrable (fun x => Work.Diff.STE.fourierExp (-k) x * f x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    integrableOn_unitCube_of_continuousOn
      ((Work.Diff.STE.continuous_fourierExp (-k)).continuousOn.mul hf)
  have iG : Integrable (fun x => Work.Diff.STE.fourierExp (-k) x * g x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    integrableOn_unitCube_of_continuousOn
      ((Work.Diff.STE.continuous_fourierExp (-k)).continuousOn.mul hg)
  -- the coefficient is additive in the function
  have hdiff : Work.Diff.STE.fourierCoeff f k - Work.Diff.STE.fourierCoeff g k
      = Work.Diff.STE.fourierCoeff (fun x => f x - g x) k := by
    rw [Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierCoeff,
      ← MeasureTheory.integral_sub iF iG]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hdiff, Work.Diff.STE.fourierCoeff]
  -- the characters have modulus one, so the sup-norm bound carries over to the integral
  have hae : ∀ᵐ x ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))),
      ‖Work.Diff.STE.fourierExp (-k) x * (f x - g x)‖ ≤ C := by
    rw [MeasureTheory.ae_restrict_iff' Work.Diff.STE.measurableSet_unitCube]
    exact Filter.Eventually.of_forall fun x hx => by
      rw [norm_mul, Work.Diff.STE.tpd_norm_fourierExp, one_mul]
      exact h x hx
  have hb := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) hae
  rwa [real_univ_restrict_unitCube n, mul_one] at hb

end Work.Diff.STE.flat
