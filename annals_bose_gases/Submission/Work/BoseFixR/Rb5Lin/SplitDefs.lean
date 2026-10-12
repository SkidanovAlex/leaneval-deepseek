import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The orthogonal decomposition `ℝ³ ≅ ℝ² × ℝ` for `radial_fourier_sinc`

This module provides the coordinate split of `ℝ³ = EuclideanSpace ℝ (Fin 3)` into its first
two coordinates and its third coordinate, which is the geometric input of the radial Fourier
computation `Work.BoseFixR.Rb5Lin.radial_fourier_sinc`.

* `splitVec (y, s)` is the vector of `ℝ³` with first two coordinates `y` and third coordinate `s`;
* `splitVec_apply_two` and `norm_splitVec_sq` record its coordinates and its norm;
* `measurePreserving_splitVec` records that the split is measure preserving for
  `volume.prod volume` on `ℝ² × ℝ`;
* `integral_splitVec_prod` is the resulting Fubini identity used by the main theorem.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixR.Rb5Lin

/-- The vector of `ℝ³ = EuclideanSpace ℝ (Fin 3)` whose first two coordinates are those of
`p.1 : ℝ² = EuclideanSpace ℝ (Fin 2)` and whose third coordinate is `p.2`. -/
def splitVec (p : EuclideanSpace ℝ (Fin 2) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
    (p.2, WithLp.ofLp p.1))

/-- The third coordinate of `splitVec (y, s)` is `s`. -/
theorem splitVec_apply_two (y : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : splitVec (y, s) 2 = s := by
  simp [splitVec, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.insertNth_apply_same]

/-- The first coordinate of `splitVec (y, s)` is the first coordinate of `y`. -/
theorem splitVec_apply_zero (y : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : splitVec (y, s) 0 = y 0 := by
  simp only [splitVec, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  rw [Fin.insertNth_apply_below (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide)]
  simp

/-- The second coordinate of `splitVec (y, s)` is the second coordinate of `y`. -/
theorem splitVec_apply_one (y : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : splitVec (y, s) 1 = y 1 := by
  simp only [splitVec, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  rw [Fin.insertNth_apply_below (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide)]
  simp

/-- The norm of `splitVec (y, s)` is the Euclidean norm of the pair `(y, s)`. -/
theorem norm_splitVec_sq (y : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    ‖splitVec (y, s)‖ ^ 2 = ‖y‖ ^ 2 + s ^ 2 := by
  rw [splitVec, PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_three]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.insertNth_apply_same]
  nth_rewrite 1 [show (0 : Fin 3) = Fin.succAbove (2 : Fin 3) (0 : Fin 2) from rfl]
  nth_rewrite 1 [show (1 : Fin 3) = Fin.succAbove (2 : Fin 3) (1 : Fin 2) from rfl]
  rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The coordinate split `ℝ² × ℝ → ℝ³` is measure preserving for the product of the Lebesgue
measures and the Lebesgue measure of `ℝ³`. -/
theorem measurePreserving_splitVec :
    MeasureTheory.MeasurePreserving (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => splitVec p)
      (volume.prod volume) volume := by
  have h1 : MeasureTheory.MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => (WithLp.ofLp p.1, p.2))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.prod (PiLp.volume_preserving_ofLp (Fin 2)) (MeasurePreserving.id volume)
  have h2 : MeasureTheory.MeasurePreserving (fun q : (Fin 2 → ℝ) × ℝ => (q.2, q.1))
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  have h3 : MeasureTheory.MeasurePreserving (fun q : ℝ × (Fin 2 → ℝ) =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm q)
      (volume.prod volume) volume :=
    MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
  have h4 : MeasureTheory.MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have h := h4.comp (h3.comp (h2.comp h1))
  simpa [Function.comp_def, splitVec] using h

/-- Measurability of the split map. -/
theorem measurable_splitVec :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => splitVec p) :=
  measurePreserving_splitVec.measurable

/-- The measure-preserving split, as an identity of Bochner integrals (Fubini form): the integral
over `ℝ³` of any a.e. strongly measurable function is the integral over `ℝ² × ℝ` of its pullback. -/
theorem integral_splitVec (G : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hG : AEStronglyMeasurable G volume) :
    ∫ z : EuclideanSpace ℝ (Fin 3), G z = ∫ p : EuclideanSpace ℝ (Fin 2) × ℝ, G (splitVec p) := by
  have h := measurePreserving_splitVec
  rw [← h.map_eq]
  exact integral_map h.measurable.aemeasurable (by rwa [h.map_eq])

/-- Integrability transfers along the split map. -/
theorem integrable_splitVec {G : EuclideanSpace ℝ (Fin 3) → ℝ} (hG : Integrable G volume) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => G (splitVec p)) (volume.prod volume) :=
  measurePreserving_splitVec.integrable_comp_of_integrable hG

/-- The Fubini form of the decomposition: integrating over first `ℝ²` and then `ℝ`. -/
theorem integral_splitVec_prod (G : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ)
    (hG : Integrable G (volume.prod volume)) :
    (∫ p : EuclideanSpace ℝ (Fin 2) × ℝ, G p) = ∫ s : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2), G (y, s) :=
  integral_prod_symm G hG

end Work.BoseFixR.Rb5Lin
