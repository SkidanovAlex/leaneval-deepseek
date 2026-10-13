/-
Copyright: work module for the Elgindi finite-time singularity project.

# The cross product of `ℝ³`: bilinearity, continuity, and the coordinate formulas for
`curl` and `div`

Auxiliary module for `Work.FTS.BSSwirl.integral_vorticity_eq` (the self-adjointness of the curl
operator `∫ ⟪∇×V, Ψ⟫ = ∫ ⟪V, ∇×Ψ⟫`).

It provides:

* `crossR3` — the cross product of two vectors of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, transported from
  the coordinate cross product `(Fin 3 → ℝ) →ₗ (Fin 3 → ℝ) →ₗ (Fin 3 → ℝ)`;
* `crossBilin` — the same product as a *continuous* bilinear map, so that the classical product rule
  (`HasFDerivAt.clm_apply`) gives the derivative of `x ↦ V x × Ψ x`;
* `inner_crossR3_cyclic₁`, `inner_crossR3_cyclic₂` — the cyclic identities
  `⟪a × b, c⟫ = ⟪a, b × c⟫` and `⟪a, b × c⟫ = ⟪b, c × a⟫` for the scalar triple product;
* `vorticity_eq_sum_crossR3` — the curl of a field is `∑ i, eᵢ × ∂ᵢu`;
* `div_eq_sum_inner` — the divergence of a field is `∑ i, ⟪eᵢ, ∂ᵢu⟫`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open FiniteTimeSingularity MeasureTheory
open scoped Matrix

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## The cross product of two vectors of `ℝ³` -/

/-- The cross product of `a b : ℝ³`, transported from the coordinate cross product on
`Fin 3 → ℝ`. -/
def crossR3 (a b : R3) : R3 := WithLp.toLp 2 (a.ofLp ⨯₃ b.ofLp)

@[simp] lemma crossR3_ofLp (a b : R3) : (crossR3 a b).ofLp = a.ofLp ⨯₃ b.ofLp := rfl

/-- Anticommutativity of the cross product, in the orientation suited to `simp`. -/
@[simp] lemma neg_crossR3 (a b : R3) : - crossR3 a b = crossR3 b a := by
  simp only [crossR3, ← WithLp.toLp_neg, cross_anticomm]

/-- The cross product is antisymmetric. -/
lemma crossR3_anticomm (a b : R3) : crossR3 a b = - crossR3 b a := by
  simp only [← neg_crossR3 b a]

lemma crossR3_add_left (a₁ a₂ b : R3) : crossR3 (a₁ + a₂) b = crossR3 a₁ b + crossR3 a₂ b := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_add, map_add, LinearMap.add_apply, Pi.add_apply]

lemma crossR3_smul_left (c : ℝ) (a b : R3) : crossR3 (c • a) b = c • crossR3 a b := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_smul, map_smul, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]

lemma crossR3_add_right (a b₁ b₂ : R3) : crossR3 a (b₁ + b₂) = crossR3 a b₁ + crossR3 a b₂ := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_add, map_add, Pi.add_apply]

lemma crossR3_smul_right (c : ℝ) (a b : R3) : crossR3 a (c • b) = c • crossR3 a b := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_smul, map_smul, Pi.smul_apply, smul_eq_mul]

/-- The norm of the cross product is at most the product of the norms. -/
lemma norm_crossR3_le (a b : R3) : ‖crossR3 a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := InnerProductGeometry.norm_ofLp_crossProduct a b
  rw [crossR3, h]
  have h1 : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
  have h2 : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg a) (norm_nonneg b)
  nlinarith [h1, h2]

/-- The cross product of `ℝ³` as a continuous bilinear map. -/
def crossBilin : R3 →L[ℝ] R3 →L[ℝ] R3 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ crossR3 crossR3_add_left crossR3_smul_left crossR3_add_right
      crossR3_smul_right)
    1 (fun a b => by simpa using norm_crossR3_le a b)

@[simp] lemma crossBilin_apply (a b : R3) : crossBilin a b = crossR3 a b := rfl

@[simp] lemma crossR3_zero_right (a : R3) : crossR3 a 0 = 0 := by simp [crossR3]

@[simp] lemma crossR3_zero_left (b : R3) : crossR3 0 b = 0 := by simp [crossR3]

/-! ## The scalar triple product -/

/-- The inner product of two vectors of `ℝ³` is the coordinatewise dot product. -/
lemma inner_eq_dot (u v : R3) : inner ℝ u v = u.ofLp ⬝ᵥ v.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply]
  rw [star_trivial]
  ring

/-- The cyclic identity for the scalar triple product: `⟪a × b, c⟫ = ⟪a, b × c⟫`. -/
lemma inner_crossR3_cyclic₁ (a b c : R3) :
    inner ℝ (crossR3 a b) c = inner ℝ a (crossR3 b c) := by
  rw [inner_eq_dot, inner_eq_dot, crossR3_ofLp, crossR3_ofLp,
    dotProduct_comm (a.ofLp ⨯₃ b.ofLp) c.ofLp]
  exact triple_product_permutation c.ofLp a.ofLp b.ofLp

/-- The cyclic identity for the scalar triple product: `⟪a, b × c⟫ = ⟪b, c × a⟫`. -/
lemma inner_crossR3_cyclic₂ (a b c : R3) :
    inner ℝ a (crossR3 b c) = inner ℝ b (crossR3 c a) := by
  rw [inner_eq_dot, inner_eq_dot, crossR3_ofLp, crossR3_ofLp]
  exact triple_product_permutation a.ofLp b.ofLp c.ofLp

/-! ## The curl and the divergence in the standard basis -/

/-- The curl of a field is `∑ i, eᵢ × ∂ᵢu`. -/
lemma vorticity_eq_sum_crossR3 (u : R3 → R3) (x : R3) :
    vorticity u x = ∑ i, crossR3 (e i) (fderiv ℝ u x (e i)) := by
  simp [vorticity, crossR3]

/-- The divergence of a field is `∑ i, ⟪eᵢ, ∂ᵢu⟫`. -/
lemma div_eq_sum_inner (u : R3 → R3) (x : R3) :
    div u x = ∑ i, inner ℝ (e i) (fderiv ℝ u x (e i)) := by
  rw [div,
    show (fderiv ℝ u x).trace ℝ R3 = ((fderiv ℝ u x) : R3 →ₗ[ℝ] R3).trace ℝ R3 from rfl,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-! ## The derivative of a cross product of two fields -/

/-- **Product rule for the cross product.**  If `V` and `Ψ` are differentiable at `x`, then so is
`y ↦ V y × Ψ y`, with derivative `∂V(x)[·] × Ψ(x) + V(x) × ∂Ψ(x)[·]`. -/
theorem hasFDerivAt_crossR3 {V Ψ : R3 → R3} {x : R3}
    (hV : HasFDerivAt V (fderiv ℝ V x) x) (hΨ : HasFDerivAt Ψ (fderiv ℝ Ψ x) x) :
    HasFDerivAt (fun y => crossR3 (V y) (Ψ y))
      ((crossBilin.flip (Ψ x)).comp (fderiv ℝ V x) + (crossBilin (V x)).comp (fderiv ℝ Ψ x))
      x := by
  have hc : HasFDerivAt (fun y => crossBilin (V y)) (crossBilin.comp (fderiv ℝ V x)) x :=
    crossBilin.hasFDerivAt.comp x hV
  have hmain := hc.clm_apply hΨ
  have hEq : (crossBilin (V x)).comp (fderiv ℝ Ψ x)
      + (crossBilin.comp (fderiv ℝ V x)).flip (Ψ x)
      = (crossBilin.flip (Ψ x)).comp (fderiv ℝ V x)
        + (crossBilin (V x)).comp (fderiv ℝ Ψ x) := by
    ext u
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  simpa only [crossBilin_apply, hEq] using hmain

/-- The cross product of two `C^n` fields is `C^n`. -/
theorem contDiff_crossR3 {V Ψ : R3 → R3} {n : ℕ∞} (hV : ContDiff ℝ n V) (hΨ : ContDiff ℝ n Ψ) :
    ContDiff ℝ n (fun y => crossR3 (V y) (Ψ y)) :=
  (crossBilin.contDiff.comp hV).clm_apply hΨ

/-- The curl of a `C¹` field is continuous. -/
theorem continuous_vorticity {u : R3 → R3} (hu : ContDiff ℝ 1 u) : Continuous (vorticity u) := by
  have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hfun : vorticity u = fun x => ∑ i, crossBilin (e i) (fderiv ℝ u x (e i)) := by
    funext x
    simp only [vorticity_eq_sum_crossR3, crossBilin_apply]
  rw [hfun]
  refine continuous_finset_sum _ fun i _ => ?_
  refine (crossBilin (e i)).continuous.comp ?_
  have h2 : Continuous fun x => (ContinuousLinearMap.apply ℝ R3 (e i)) (fderiv ℝ u x) :=
    (ContinuousLinearMap.apply ℝ R3 (e i)).continuous.comp h1
  simpa [ContinuousLinearMap.apply_apply] using h2

end

end Work.FTS.BSSwirl
