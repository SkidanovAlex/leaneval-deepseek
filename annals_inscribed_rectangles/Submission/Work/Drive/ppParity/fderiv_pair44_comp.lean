import Mathlib
import Submission.Work.Drive.pairMeetDefs

/-!
# The derivative of the packing `(f, g) ↦ pair44 (f ·) (g ·)`

`Work.Drive.pair44 a b` stacks two vectors of `ℝ⁴` into a vector of `ℝ⁸` (the first four coordinates
are those of `a`, the last four those of `b`).  This file proves that this stacking is jointly smooth
in the two arguments and that its derivative never costs more than twice the larger of the two
derivatives:

> for differentiable `f g : X → ℝ⁴`, the map `y ↦ pair44 (f y) (g y)` is differentiable at `x` and
> `‖fderiv (y ↦ pair44 (f y) (g y)) x‖ ≤ 2 * max ‖fderiv f x‖ ‖fderiv g x‖`.

The mathematical content is two facts:

* `pair44`, viewed as a map of the pair, is linear (`pair44LM`, `pair44CLM`), so that the chain rule
  computes the derivative as `pair44CLM ∘ (fderiv f x).prod (fderiv g x)`;
* `‖pair44 a b‖ ≤ ‖a‖ + ‖b‖` (`pair44_norm_le`), from the exact identity
  `‖pair44 a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2` (`pair44_norm_sq`), which splits the `ℓ²` norm on `Fin 8`
  into the two `ℓ²` norms on the two blocks `Fin 4` (`pair44_sum_eight`).

The constant `2` is then the triangle inequality `‖a‖ + ‖b‖ ≤ 2 * max ‖a‖ ‖b‖`.
-/

namespace Work.Drive.ppParity

open scoped Topology

/-! ## `pair44` as a linear map of the pair -/

/-- The stacking `pair44` of two `ℝ⁴`-vectors, as a linear map of the pair. -/
noncomputable def pair44LM :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 8) where
  toFun p := Work.Drive.pair44 p.1 p.2
  map_add' p q := by
    ext i
    fin_cases i <;> simp [Work.Drive.pair44, WithLp.ofLp_toLp]
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [Work.Drive.pair44, WithLp.ofLp_toLp]

/-- The stacking `pair44` of two `ℝ⁴`-vectors, as a continuous linear map of the pair. -/
noncomputable def pair44CLM :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) →L[ℝ] EuclideanSpace ℝ (Fin 8) :=
  LinearMap.toContinuousLinearMap pair44LM

@[simp] lemma pair44CLM_apply (p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    pair44CLM p = Work.Drive.pair44 p.1 p.2 := rfl

@[simp] lemma pair44CLM_apply' (a b : EuclideanSpace ℝ (Fin 4)) :
    pair44CLM (a, b) = Work.Drive.pair44 a b := rfl

/-! ## The exact norm of the stacking -/

/-- Splitting a sum over `Fin 8` into the two blocks of four. -/
lemma pair44_sum_eight (g : Fin 8 → ℝ) :
    ∑ i : Fin 8, g i = ∑ i : Fin 4, g (Fin.castAdd 4 i) + ∑ i : Fin 4, g (Fin.natAdd 4 i) := by
  rw [← Equiv.sum_comp (finSumFinEquiv (m := 4) (n := 4)) g, Fintype.sum_sum_type]
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- **The norm of the stacking is the `ℓ²` norm of the pair**: the packing `pair44` is an isometry
of `ℝ⁴ × ℝ⁴` (with the sup norm on the pair) onto its image. -/
lemma pair44_norm_sq (a b : EuclideanSpace ℝ (Fin 4)) :
    ‖Work.Drive.pair44 a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : ‖Work.Drive.pair44 a b‖ ^ 2
      = ∑ i : Fin 8, ‖(Work.Drive.pair44 a b).ofLp i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 8 => ℝ) (Work.Drive.pair44 a b)
  have h2 : ‖a‖ ^ 2 = ∑ i : Fin 4, ‖a.ofLp i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 => ℝ) a
  have h3 : ‖b‖ ^ 2 = ∑ i : Fin 4, ‖b.ofLp i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 => ℝ) b
  rw [h1, h2, h3, pair44_sum_eight]
  simp [Work.Drive.pair44]

/-- **The triangle inequality for the stacking**: `‖pair44 a b‖ ≤ ‖a‖ + ‖b‖`. -/
lemma pair44_norm_le (a b : EuclideanSpace ℝ (Fin 4)) :
    ‖Work.Drive.pair44 a b‖ ≤ ‖a‖ + ‖b‖ := by
  have h := pair44_norm_sq a b
  have hle : ‖Work.Drive.pair44 a b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg b, mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  have h2 : |‖Work.Drive.pair44 a b‖| ≤ |‖a‖ + ‖b‖| := sq_le_sq.mp hle
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h2

/-! ## The derivative of the composite -/

theorem fderiv_pair44_comp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → EuclideanSpace ℝ (Fin 4)} {x : X}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y : X => Work.Drive.pair44 (f y) (g y)) x ∧
    ‖fderiv ℝ (fun y : X => Work.Drive.pair44 (f y) (g y)) x‖ ≤
      2 * max ‖fderiv ℝ f x‖ ‖fderiv ℝ g x‖ := by
  have hpair : HasFDerivAt (fun y : X => (f y, g y))
      ((fderiv ℝ f x).prod (fderiv ℝ g x)) x := hf.hasFDerivAt.prodMk hg.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : X => pair44CLM (f y, g y))
      (pair44CLM.comp ((fderiv ℝ f x).prod (fderiv ℝ g x))) x :=
    (ContinuousLinearMap.hasFDerivAt pair44CLM).comp x hpair
  have hfun : (fun y : X => Work.Drive.pair44 (f y) (g y))
      = fun y : X => pair44CLM (f y, g y) := by
    funext y; rw [pair44CLM_apply]
  have hderiv : fderiv ℝ (fun y : X => Work.Drive.pair44 (f y) (g y)) x
      = pair44CLM.comp ((fderiv ℝ f x).prod (fderiv ℝ g x)) := by
    rw [hfun]; exact hcomp.fderiv
  constructor
  · rw [hfun]; exact hcomp.differentiableAt
  · rw [hderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, pair44CLM_apply]
    have h1 : ‖fderiv ℝ f x v‖ ≤ max ‖fderiv ℝ f x‖ ‖fderiv ℝ g x‖ * ‖v‖ :=
      le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have h2 : ‖fderiv ℝ g x v‖ ≤ max ‖fderiv ℝ f x‖ ‖fderiv ℝ g x‖ * ‖v‖ :=
      le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    calc ‖Work.Drive.pair44 (fderiv ℝ f x v) (fderiv ℝ g x v)‖
        ≤ ‖fderiv ℝ f x v‖ + ‖fderiv ℝ g x v‖ := pair44_norm_le _ _
      _ ≤ max ‖fderiv ℝ f x‖ ‖fderiv ℝ g x‖ * ‖v‖
            + max ‖fderiv ℝ f x‖ ‖fderiv ℝ g x‖ * ‖v‖ := add_le_add h1 h2
      _ = 2 * max ‖fderiv ℝ f x‖ ‖fderiv ℝ g x‖ * ‖v‖ := by ring

end Work.Drive.ppParity
