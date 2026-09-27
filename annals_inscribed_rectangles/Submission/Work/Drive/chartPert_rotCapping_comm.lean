import Mathlib
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping

/-!
# The chart perturbation commutes with the rotation of the capping space

The chart perturbation family `Work.Drive.chartPert τ` of `Submission/Work/Drive/exists_chartPert.lean`
acts, in the model `cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`, on the radial coordinate by
the level scaling `r ↦ exp (exp⁻¹ r + τ 0)` and on the projective coordinate by the projectivisation of
the *left* multiplication `1 + classGen τ` (`Work.Drive.classMap τ`); the rotation `rotCapping t` acts
on the projective coordinate by `Work.Drive.projRot t`, the projectivisation of the diagonal rotation
`diagRot t` (`Work.Drive.cappingSpaceHomeoProj_rotCapping`).

The point of this file is that these two actions commute.  Algebraically the reason is that

* `classMap τ` is left multiplication by the quaternion `1 + τ₁ i + τ₂ j + τ₃ k`, while
* `diagRot t` is *right* multiplication by the complex number `circ t = e^{iπt}`,

and left and right multiplications commute (associativity).  Concretely, with the complex coordinates
`c₁`, `c₂` of `ℂ² ≅ ℝ⁴`, `diagRot t` multiplies `c₁` by `circ t` and `c₂` by `star (circ t)`, and
`classGen τ` acts by

`c₁ (classGen τ w) = (τ 1) i c₁ w - (τ 2 + τ 3 i) star (c₂ w)`,
`c₂ (classGen τ w) = (τ 1) i c₂ w + (τ 2 + τ 3 i) star (c₁ w)`

(`chartPert_comm_c₁_classGen`, `chartPert_comm_c₂_classGen`), from which the commutation
`classEquiv τ (diagRot t x) = diagRot t (classEquiv τ x)` is a computation in `ℂ`
(`chartPert_comm_classEquiv_diagRot`).

The main result, `Work.Drive.chartPert_rotCapping_comm`, is the corresponding statement on the capping
space and is a consequence of the projective commutation `chartPert_comm_classMap_projRot` through the
model homeomorphism `cappingSpaceHomeoProj`.
-/

set_option maxHeartbeats 1000000

namespace Work.Drive

open scoped LinearAlgebra.Projectivization

noncomputable section

/-! ## Additivity of the two complex coordinates -/

lemma chartPert_comm_c₁_add (a b : Eucl 3) : c₁ (a + b) = c₁ a + c₁ b := by
  simp only [c₁, PiLp.add_apply]
  push_cast
  ring

lemma chartPert_comm_c₂_add (a b : Eucl 3) : c₂ (a + b) = c₂ a + c₂ b := by
  simp only [c₂, PiLp.add_apply]
  push_cast
  ring

/-! ## The class generator in complex coordinates

`classGen τ` is left multiplication by the imaginary quaternion `τ 1 i + τ 2 j + τ 3 k`; on `ℂ²` this
is the pair of formulas below (`i` acts as `Complex.I`, and `j` conjugates the second coordinate). -/

lemma chartPert_comm_c₁_classGen (τ w : Eucl 3) :
    c₁ (classGen τ w)
      = ((τ.ofLp 1 : ℂ)) * Complex.I * c₁ w
        - ((τ.ofLp 2 : ℂ) + (τ.ofLp 3 : ℂ) * Complex.I) * star (c₂ w) := by
  have hc1 : c₁ w = (w.ofLp 0 : ℂ) + (w.ofLp 1 : ℂ) * Complex.I := by simp [c₁]
  have hc2 : c₂ w = (w.ofLp 2 : ℂ) + (w.ofLp 3 : ℂ) * Complex.I := by simp [c₂]
  rw [c₁, classGen_ofLp_0, classGen_ofLp_1, hc1, hc2]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I] <;>
    ring

lemma chartPert_comm_c₂_classGen (τ w : Eucl 3) :
    c₂ (classGen τ w)
      = ((τ.ofLp 1 : ℂ)) * Complex.I * c₂ w
        + ((τ.ofLp 2 : ℂ) + (τ.ofLp 3 : ℂ) * Complex.I) * star (c₁ w) := by
  have hc1 : c₁ w = (w.ofLp 0 : ℂ) + (w.ofLp 1 : ℂ) * Complex.I := by simp [c₁]
  have hc2 : c₂ w = (w.ofLp 2 : ℂ) + (w.ofLp 3 : ℂ) * Complex.I := by simp [c₂]
  rw [c₂, classGen_ofLp_2, classGen_ofLp_3, hc1, hc2]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I] <;>
    ring

/-! ## The class equivalence commutes with the diagonal rotation -/

/-- **Left multiplication by `1 + classGen τ` commutes with right multiplication by `circ t`**, i.e.
`classEquiv τ (diagRot t x) = diagRot t (classEquiv τ x)`.  Both sides are equal to the point of `ℂ²`
with coordinates `circ t * c₁ x + (τ 1) i (circ t * c₁ x) - (τ 2 + τ 3 i) (circ t) star (c₂ x)` and
`star (circ t) * c₂ x + (τ 1) i (star (circ t) * c₂ x) + (τ 2 + τ 3 i) (star (circ t)) star (c₁ x)`. -/
theorem chartPert_comm_classEquiv_diagRot (t : ℝ) (τ x : Eucl 3) :
    classEquiv τ (diagRot t x) = diagRot t (classEquiv τ x) := by
  have h1 : c₁ (classEquiv τ (diagRot t x)) = c₁ (diagRot t (classEquiv τ x)) := by
    simp only [classEquiv_apply, chartPert_comm_c₁_add, c₁_diagRot, chartPert_comm_c₁_classGen,
      c₂_diagRot]
    rw [star_mul, star_star]
    ring
  have h2 : c₂ (classEquiv τ (diagRot t x)) = c₂ (diagRot t (classEquiv τ x)) := by
    simp only [classEquiv_apply, chartPert_comm_c₂_add, c₂_diagRot, chartPert_comm_c₂_classGen,
      c₁_diagRot]
    rw [star_mul]
    ring
  rw [← ofComplex_c₁_c₂ (classEquiv τ (diagRot t x)),
    ← ofComplex_c₁_c₂ (diagRot t (classEquiv τ x)), h1, h2]

/-- **The class map commutes with the rotation of `ℝP³`.** -/
theorem chartPert_comm_classMap_projRot (t : ℝ) (τ : Eucl 3)
    (p : Projectivization ℝ (Eucl 3)) :
    classMap τ (projRot t p) = projRot t (classMap τ p) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projRot_mk t v hv, classMap_mk τ (diagRot t v) (diagRot_ne_zero t hv),
      classMap_mk τ v hv, projRot_mk t (classEquiv τ v) (classEquiv_ne_zero hv)]
    refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, ?_⟩
    simp [chartPert_comm_classEquiv_diagRot t τ v]

/-! ## The statement on the capping space -/

theorem chartPert_rotCapping_comm (t : ℝ) (τ : EuclideanSpace ℝ (Fin 4)) :
    ∀ p : Work.Drive.CappingSpace,
      Work.Drive.chartPert τ (Work.Drive.rotCapping ((t : ℝ) : UnitAddCircle) p)
        = Work.Drive.rotCapping ((t : ℝ) : UnitAddCircle) (Work.Drive.chartPert τ p) := by
  intro p
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_chartPert, cappingSpaceHomeoProj_rotCapping]
  simp only [coordFam]
  refine Prod.ext rfl ?_
  exact chartPert_comm_classMap_projRot t τ _

end

end Work.Drive
