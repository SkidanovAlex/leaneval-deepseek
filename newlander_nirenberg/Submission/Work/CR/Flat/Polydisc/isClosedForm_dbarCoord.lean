import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The derivative of the `j`-th `∂̄`-operator, evaluated on a vector `v`:
`D(∂̄_j u)(z)·v = (1/2)( (D²u(z)·v)(e_j) + i · (D²u(z)·v)(i e_j) )`, where
`e_j = Pi.single j 1` and `i e_j = Pi.single j Complex.I` are the real and imaginary
unit vectors in the `j`-th coordinate direction.  This is the chain rule for
`∂̄_j u = (1/2)(du(·)(e_j) + i·du(·)(i e_j))`. -/
lemma fderiv_dbarCoord_apply {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : ContDiffAt ℝ 2 u z) (j : Fin n) (v : Fin n → ℂ) :
    fderiv ℝ (dbarCoord j u) z v =
      (1/2) * ((fderiv ℝ (fderiv ℝ u) z v) (Pi.single j 1)
        + Complex.I * ((fderiv ℝ (fderiv ℝ u) z v) (Pi.single j Complex.I))) := by
  have hc : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : fderiv ℝ (fun z => fderiv ℝ u z (Pi.single j 1)) z
      = (fderiv ℝ (fderiv ℝ u) z).flip (Pi.single j 1) := by
    rw [fderiv_clm_apply (c := fun z => fderiv ℝ u z)
      (u := fun _ : Fin n → ℂ => Pi.single j 1) hc (differentiableAt_const _)]
    simp
  have hB : fderiv ℝ (fun z => fderiv ℝ u z (Pi.single j Complex.I)) z
      = (fderiv ℝ (fderiv ℝ u) z).flip (Pi.single j Complex.I) := by
    rw [fderiv_clm_apply (c := fun z => fderiv ℝ u z)
      (u := fun _ : Fin n → ℂ => Pi.single j Complex.I) hc (differentiableAt_const _)]
    simp
  have hAd : DifferentiableAt ℝ (fun z => fderiv ℝ u z (Pi.single j 1)) z :=
    hc.clm_apply (differentiableAt_const _)
  have hBd : DifferentiableAt ℝ (fun z => fderiv ℝ u z (Pi.single j Complex.I)) z :=
    hc.clm_apply (differentiableAt_const _)
  have hBd2 : DifferentiableAt ℝ (fun z => Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) z :=
    hBd.const_mul Complex.I
  have hsum : DifferentiableAt ℝ (fun z => fderiv ℝ u z (Pi.single j 1)
      + Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) z := hAd.add hBd2
  rw [show dbarCoord j u = (fun z => (1/2 : ℂ) * (fderiv ℝ u z (Pi.single j 1)
      + Complex.I * fderiv ℝ u z (Pi.single j Complex.I))) from rfl]
  rw [fderiv_const_mul hsum (1/2)]
  rw [show (fun z => fderiv ℝ u z (Pi.single j 1)
          + Complex.I * fderiv ℝ u z (Pi.single j Complex.I))
        = (fun z => fderiv ℝ u z (Pi.single j 1))
          + (fun z => Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) from rfl]
  rw [fderiv_add hAd hBd2]
  rw [fderiv_const_mul hBd Complex.I, hA, hB]
  simp [smul_eq_mul]
  ring_nf

/-- The `(0,1)`-form `∂̄u` is closed: this is the flat `∂̄² = 0`, packaged in the
`IsClosedForm` vocabulary.  Concretely it says that a form of the shape
`j ↦ dbarCoord j u` is admissible input for the flat `∂̄`-Poincaré statements
`exists_dbar_solution_polydisc` / `exists_dbar_solution_polydisc_holderNorm`, which
ask for `IsClosedForm f`. -/
theorem isClosedForm_dbarCoord {n : ℕ} (u : (Fin n → ℂ) → ℂ)
    (hu : ∀ z : Fin n → ℂ, ContDiffAt ℝ 2 u z) :
    IsClosedForm (fun j : Fin n => dbarCoord j u) := by
  intro j k z
  have hu' := hu z
  have hsymm : ∀ a b : Fin n → ℂ,
      (fderiv ℝ (fderiv ℝ u) z a) b = (fderiv ℝ (fderiv ℝ u) z b) a :=
    fun a b => (hu'.isSymmSndFDerivAt (by simp)).eq a b
  simp only [dbarCoord]
  rw [fderiv_dbarCoord_apply u z hu' j (Pi.single k 1),
      fderiv_dbarCoord_apply u z hu' j (Pi.single k Complex.I),
      fderiv_dbarCoord_apply u z hu' k (Pi.single j 1),
      fderiv_dbarCoord_apply u z hu' k (Pi.single j Complex.I)]
  rw [hsymm (Pi.single k 1) (Pi.single j 1), hsymm (Pi.single k 1) (Pi.single j Complex.I),
      hsymm (Pi.single k Complex.I) (Pi.single j 1),
      hsymm (Pi.single k Complex.I) (Pi.single j Complex.I)]
  ring_nf

end Work.CR.Flat.Polydisc
