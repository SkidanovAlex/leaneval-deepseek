import Mathlib
import Submission.Work.Whitney.LocalModel

/-!
# The mirror of Whitney's local model changes the sign of its double point

The file proves that precomposing Whitney's local model `model n` (`Submission/Work/Whitney/LocalModel.lean`)
with the linear *mirror* `mirrorFun n` (which negates the first coordinate of the second block) flips the
sign of the determinant of the "two sheets" map at the double point `±e₀`.

The mathematical content is the chain rule followed by multiplicativity of the determinant:

* `mirrorFun n` is the linear map `mirrorLin n = LinearMap.prodMap LinearMap.id (secondMirror n)`, whose
  determinant is `-1` (`det_mirrorLin`);
* hence `fderiv ℝ (mirrorFun n ∘ model n) x = (mirrorLin n).comp (fderiv ℝ (model n) x)`
  (`fderiv_mirror_model`), by the chain rule (`fderiv_comp`) and the fact that the derivative of a
  continuous linear map is itself (`ContinuousLinearMap.fderiv`);
* `LinearMap.coprod` is "diagonal" with respect to precomposition (`LinearMap.comp_coprod`) and
  `LinearMap.det` is multiplicative (`LinearMap.det_comp`).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- `uu n = ∏ i, (1 + x i ^ 2)` is differentiable. -/
private lemma uu_differentiable (n : ℕ) [NeZero n] : Differentiable ℝ (uu n) := by
  unfold uu; fun_prop

/-- `uu n x = ∏ i, (1 + x i ^ 2)` never vanishes (every factor is `≥ 1`). -/
private lemma uu_ne_zero (n : ℕ) [NeZero n] (x : Fin n → ℝ) : uu n x ≠ 0 := by
  unfold uu
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => by positivity)

/-- Whitney's local model is differentiable at every point (it is built from the polynomial `uu n`,
which never vanishes, by field operations). -/
private lemma model_differentiableAt (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    DifferentiableAt ℝ (model n) x := by
  have hu : DifferentiableAt ℝ (fun y : Fin n → ℝ => uu n y) x :=
    (uu_differentiable n).differentiableAt
  have hux : uu n x ≠ 0 := uu_ne_zero n x
  have hA : DifferentiableAt ℝ (fun y : Fin n → ℝ =>
      (fun i => y i - (if i = 0 then 2 * y i / uu n y else 0))) x := by
    rw [differentiableAt_pi]
    intro i
    by_cases hi : i = 0
    · subst hi; simp only [if_true]; fun_prop
    · simp only [if_neg hi]; fun_prop
  have hB : DifferentiableAt ℝ (fun y : Fin n → ℝ =>
      (fun i => if i = 0 then 1 / uu n y else y 0 * y i / uu n y)) x := by
    rw [differentiableAt_pi]
    intro i
    by_cases hi : i = 0
    · subst hi; simp only [if_true]; fun_prop
    · simp only [if_neg hi]; fun_prop
  exact hA.prodMk hB

/-- The "second block" of the mirror, as a linear map: `v ↦ (fun i => if i = 0 then - v i else v i)`.
It negates exactly the first coordinate. -/
private noncomputable def secondMirror (n : ℕ) [NeZero n] : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi (fun i : Fin n =>
    ((if i = 0 then (-1 : ℝ) else 1) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ∘ₗ
      (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ))

/-- `mirrorFun n` as a linear map: the identity on the first block, `secondMirror n` on the second. -/
private noncomputable def mirrorLin (n : ℕ) [NeZero n] :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.prodMap LinearMap.id (secondMirror n)

/-- `mirrorLin n` continuously. -/
private noncomputable def mirrorCLM (n : ℕ) [NeZero n] :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.toContinuousLinearMap (mirrorLin n)

/-- `mirrorLin n` is the mirror `mirrorFun n` on points. -/
private lemma mirrorLin_apply (n : ℕ) [NeZero n] (y : (Fin n → ℝ) × (Fin n → ℝ)) :
    mirrorLin n y = mirrorFun n y := by
  refine Prod.ext rfl ?_
  funext i
  by_cases h : i = 0 <;>
    simp [mirrorLin, secondMirror, LinearMap.pi_apply, LinearMap.prodMap_apply, mirrorFun, h]

/-- The continuous linear map `mirrorCLM n` is the mirror `mirrorFun n` on points. -/
private lemma mirrorCLM_apply (n : ℕ) [NeZero n] (y : (Fin n → ℝ) × (Fin n → ℝ)) :
    mirrorCLM n y = mirrorFun n y := by
  simp only [mirrorCLM]
  exact mirrorLin_apply n y

/-- The mirror has determinant `-1`: it is the identity on the first block and a map negating exactly
one coordinate (in the sense of the basis `Pi.basisFun ℝ (Fin n)`) on the second block. -/
private lemma det_mirrorLin (n : ℕ) [NeZero n] : LinearMap.det (mirrorLin n) = -1 := by
  have hdet : LinearMap.det (secondMirror n) = -1 := by
    have hdet' : ∀ i : Fin n,
        LinearMap.det (((if i = 0 then (-1 : ℝ) else 1) •
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ))) = (if i = 0 then (-1 : ℝ) else 1) := by
      intro i
      rw [LinearMap.det_ring]
      by_cases h : i = 0 <;> simp [h]
    rw [secondMirror, LinearMap.det_pi]
    simp only [hdet']
    simp
  rw [mirrorLin, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hdet]

/-- Chain rule for the mirrored model: the derivative of `mirrorFun n ∘ model n` is the mirror
applied to the derivative of `model n`. -/
private lemma fderiv_mirror_model (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    ((fderiv ℝ (mirrorFun n ∘ model n) x :
        (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) :
      (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)))
      = (mirrorLin n).comp ((fderiv ℝ (model n) x :
          (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) :
        (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) := by
  have hfun : mirrorFun n = ⇑(mirrorCLM n) := funext fun y => (mirrorCLM_apply n y).symm
  have hMdiff : DifferentiableAt ℝ (mirrorFun n) (model n x) := by
    rw [hfun]; exact (mirrorCLM n).differentiableAt
  have hchain := fderiv_comp (𝕜 := ℝ) (f := model n) (g := mirrorFun n) (x := x)
    hMdiff (model_differentiableAt n x)
  rw [hchain]
  have hfd : fderiv ℝ (mirrorFun n) (model n x) = mirrorCLM n := by
    rw [hfun]; exact ContinuousLinearMap.fderiv (mirrorCLM n)
  rw [hfd, ContinuousLinearMap.toLinearMap_comp]
  simp only [mirrorCLM, LinearMap.coe_toContinuousLinearMap]

/-- Mirroring Whitney's local model in the first coordinate of the *second* block (`mirrorFun n`, from `Submission/Work/Whitney/LocalModel.lean`) flips the sign of its double point: the determinant of the "two sheets" map changes sign.  Note `mirrorFun n` is linear of determinant `-1` and fixes the linear inclusion `inclModel` (`mirrorFun_inclModel`), so the mirrored model is just as glueable as the original one. -/
theorem mirror_det_neg (n : ℕ) [NeZero n] :
    LinearMap.det (((fderiv ℝ (Work.Whitney.mirrorFun n ∘ Work.Whitney.model n)
          (Work.Whitney.e0 n)).coprod
        (fderiv ℝ (Work.Whitney.mirrorFun n ∘ Work.Whitney.model n) (-(Work.Whitney.e0 n)))) :
      ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) =
      - LinearMap.det (((fderiv ℝ (Work.Whitney.model n) (Work.Whitney.e0 n)).coprod
        (fderiv ℝ (Work.Whitney.model n) (-(Work.Whitney.e0 n)))) :
      ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) := by
  rw [ContinuousLinearMap.coe_coprod, ContinuousLinearMap.coe_coprod]
  rw [fderiv_mirror_model n (Work.Whitney.e0 n),
    fderiv_mirror_model n (-(Work.Whitney.e0 n)), ← LinearMap.comp_coprod]
  rw [LinearMap.det_comp, det_mirrorLin]
  ring

end Work.Whitney
