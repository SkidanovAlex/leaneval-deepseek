import Mathlib
import Submission.Work.Drive.classTripleSystem
import Submission.Work.Drive.qform_bilinear

/-!
# The `y`-derivative of the class system

This file proves `Work.Drive.fderiv_classSystem_y`: for a fixed parameter `p`, the derivative of
`y' ↦ classSystem V A p y'` (the pair of `qform`-differences of the three perturbed class lifts,
stacked by `pair33`) at a point `y` in the direction `z` is obtained by the product rule from the
derivatives of the three lift maps `y' ↦ A p k (V k (parOf y' k))`.

The auxiliary material is the calculus of the two structural maps:

* `qformCLM`, the curried continuous bilinear map `(v, w) ↦ qform v w`, built from the linear maps
  `qformRight`/`qformLeft` of `Submission/Work/Drive/classTripleSystem.lean` via
  `LinearMap.toContinuousLinearMap` (finite dimension supplies continuity, so no explicit norm
  bound is needed);
* `pair33LeftCLM`, `pair33RightCLM`, the two continuous linear maps `a ↦ pair33 a 0`,
  `a ↦ pair33 0 a` whose sum is `pair33`;

and the two product rules `fderiv_qform_apply` (for a curried CLM applied to two differentiable
maps, via `HasFDerivAt.clm_apply`) and `fderiv_pair33_apply` (for the stacking of two maps, via
`HasFDerivAt.add`).
-/

namespace Work.Drive

namespace ClassSystemDeriv

noncomputable section

open scoped ContDiff Topology

/-! ## 1. `qform` as a continuous bilinear map -/

/-- `w ↦ qform v w` as a continuous linear map. -/
def qformRightCLM (v : Eucl 3) : Eucl 3 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap (qformRight v)

@[simp] lemma qformRightCLM_apply (v w : Eucl 3) : qformRightCLM v w = qform v w := rfl

/-- `(v, w) ↦ qform v w` as a linear map of the first variable into the space of continuous linear
maps in the second variable. -/
def qformLM : Eucl 3 →ₗ[ℝ] Eucl 3 →L[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := qformRightCLM v
  map_add' v v' := by ext w; simp [qform_add_left]
  map_smul' c v := by ext w; simp [qform_smul_left]

/-- **`qform` as a curried continuous bilinear map.** -/
def qformCLM : Eucl 3 →L[ℝ] Eucl 3 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap qformLM

@[simp] lemma qformCLM_apply (v w : Eucl 3) : qformCLM v w = qform v w := rfl

/-! ## 2. `pair33` as a sum of two continuous linear maps -/

/-- The first half of `pair33`, `a ↦ pair33 a 0`, as a linear map. -/
def pair33LeftLM : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 6) where
  toFun a := pair33 a 0
  map_add' a a' := by ext j; fin_cases j <;> simp
  map_smul' c a := by ext j; fin_cases j <;> simp

/-- The second half of `pair33`, `a ↦ pair33 0 a`, as a linear map. -/
def pair33RightLM : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 6) where
  toFun a := pair33 0 a
  map_add' a a' := by ext j; fin_cases j <;> simp
  map_smul' c a := by ext j; fin_cases j <;> simp

def pair33LeftCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 6) :=
  LinearMap.toContinuousLinearMap pair33LeftLM

def pair33RightCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 6) :=
  LinearMap.toContinuousLinearMap pair33RightLM

@[simp] lemma pair33LeftCLM_apply (a : EuclideanSpace ℝ (Fin 3)) :
    pair33LeftCLM a = pair33 a 0 := rfl

@[simp] lemma pair33RightCLM_apply (a : EuclideanSpace ℝ (Fin 3)) :
    pair33RightCLM a = pair33 0 a := rfl

/-- `pair33` is the sum of its two halves. -/
lemma pair33_add_zero (a b : EuclideanSpace ℝ (Fin 3)) : pair33 a 0 + pair33 0 b = pair33 a b := by
  ext j; fin_cases j <;> simp

/-! ## 3. The two product rules -/

/-- **Product rule for the stacking `pair33`**: for differentiable `F`, `G` the derivative of
`y' ↦ pair33 (F y') (G y')` is `z ↦ pair33 (fderiv F y z) (fderiv G y z)`. -/
lemma fderiv_pair33_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → EuclideanSpace ℝ (Fin 3)} {y : E} (z : E)
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    fderiv ℝ (fun y' => pair33 (F y') (G y')) y z = pair33 (fderiv ℝ F y z) (fderiv ℝ G y z) := by
  have hleft : HasFDerivAt (fun y' : E => pair33LeftCLM (F y'))
      (pair33LeftCLM.comp (fderiv ℝ F y)) y :=
    (ContinuousLinearMap.hasFDerivAt pair33LeftCLM).comp y hF.hasFDerivAt
  have hright : HasFDerivAt (fun y' : E => pair33RightCLM (G y'))
      (pair33RightCLM.comp (fderiv ℝ G y)) y :=
    (ContinuousLinearMap.hasFDerivAt pair33RightCLM).comp y hG.hasFDerivAt
  have hsum : HasFDerivAt (fun y' : E => pair33LeftCLM (F y') + pair33RightCLM (G y'))
      (pair33LeftCLM.comp (fderiv ℝ F y) + pair33RightCLM.comp (fderiv ℝ G y)) y :=
    hleft.add hright
  have h := hsum.fderiv
  have hfun : (fun y' : E => pair33 (F y') (G y')) =
      (fun y' : E => pair33LeftCLM (F y') + pair33RightCLM (G y')) := by
    funext y'; simp [pair33_add_zero]
  rw [hfun, h]
  simp [pair33_add_zero]

/-- **Product rule for `qform`**: for differentiable `u`, `w` the derivative of
`y' ↦ qform (u y') (w y')` in the direction `z` is
`qform (fderiv u y z) (w y) + qform (u y) (fderiv w y z)`. -/
lemma fderiv_qform_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u w : E → Eucl 3} {y : E} (z : E)
    (hu : DifferentiableAt ℝ u y) (hw : DifferentiableAt ℝ w y) :
    fderiv ℝ (fun y' => qform (u y') (w y')) y z
      = qform (fderiv ℝ u y z) (w y) + qform (u y) (fderiv ℝ w y z) := by
  have hc : HasFDerivAt (fun y' : E => qformCLM (u y')) (qformCLM.comp (fderiv ℝ u y)) y :=
    (ContinuousLinearMap.hasFDerivAt qformCLM).comp y hu.hasFDerivAt
  have h := (hc.clm_apply hw.hasFDerivAt).fderiv
  have hfun : (fun y' : E => qform (u y') (w y')) =
      (fun y' : E => qformCLM (u y') (w y')) := by
    funext y'; simp
  rw [hfun, h]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    qformCLM_apply]
  rw [add_comm]

/-- **The `(y, z)`-derivative of the class map of three lift maps**: the product rule for
`y' ↦ pair33 (qform (b₀ y') (b₁ y')) (qform (b₀ y') (b₂ y'))`. -/
lemma fderiv_pair33_qform_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b0 b1 b2 : E → Eucl 3) (y z : E)
    (hb0 : DifferentiableAt ℝ b0 y) (hb1 : DifferentiableAt ℝ b1 y) (hb2 : DifferentiableAt ℝ b2 y) :
    fderiv ℝ (fun y' => pair33 (qform (b0 y') (b1 y')) (qform (b0 y') (b2 y'))) y z
      = pair33 (qform (fderiv ℝ b0 y z) (b1 y) + qform (b0 y) (fderiv ℝ b1 y z))
               (qform (fderiv ℝ b0 y z) (b2 y) + qform (b0 y) (fderiv ℝ b2 y z)) := by
  have h01 : DifferentiableAt ℝ (fun y' => qform (b0 y') (b1 y')) y := by
    have h : DifferentiableAt ℝ (fun y' => qformCLM (b0 y')) y :=
      (ContinuousLinearMap.hasFDerivAt qformCLM).differentiableAt.comp y hb0
    simpa using h.clm_apply hb1
  have h02 : DifferentiableAt ℝ (fun y' => qform (b0 y') (b2 y')) y := by
    have h : DifferentiableAt ℝ (fun y' => qformCLM (b0 y')) y :=
      (ContinuousLinearMap.hasFDerivAt qformCLM).differentiableAt.comp y hb0
    simpa using h.clm_apply hb2
  rw [fderiv_pair33_apply z h01 h02]
  congr 1
  · exact fderiv_qform_apply z hb0 hb1
  · exact fderiv_qform_apply z hb0 hb2

end

end ClassSystemDeriv

theorem fderiv_classSystem_y {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.Eucl 3)
    (hV : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V k))
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3)
    (p : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Tgt 6) (z : Work.Drive.Tgt 6) :
    fderiv ℝ (fun y' : Work.Drive.Tgt 6 => Work.Drive.classSystem V A p y') y z
      = Work.Drive.pair33
          (Work.Drive.qform
              (fderiv ℝ (fun y' : Work.Drive.Tgt 6 => A p 0 (V 0 (Work.Drive.parOf y' 0))) y z)
              (A p 1 (V 1 (Work.Drive.parOf y 1)))
            + Work.Drive.qform (A p 0 (V 0 (Work.Drive.parOf y 0)))
              (fderiv ℝ (fun y' : Work.Drive.Tgt 6 => A p 1 (V 1 (Work.Drive.parOf y' 1))) y z))
          (Work.Drive.qform
              (fderiv ℝ (fun y' : Work.Drive.Tgt 6 => A p 0 (V 0 (Work.Drive.parOf y' 0))) y z)
              (A p 2 (V 2 (Work.Drive.parOf y 2)))
            + Work.Drive.qform (A p 0 (V 0 (Work.Drive.parOf y 0)))
              (fderiv ℝ (fun y' : Work.Drive.Tgt 6 => A p 2 (V 2 (Work.Drive.parOf y' 2))) y z)) := by
  have hdiff : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y' : Tgt 6 => A p k (V k (parOf y' k))) y := by
    intro k
    have hVk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Tgt 6 => V k (parOf y' k)) :=
      (hV k).comp (contDiff_parOf k)
    have huk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y' : Tgt 6 => A p k (V k (parOf y' k))) :=
      ContDiff.continuousLinearMap_comp (A p k) hVk
    exact huk.contDiffAt.differentiableAt (by simp)
  have h := ClassSystemDeriv.fderiv_pair33_qform_apply
    (b0 := fun y' : Tgt 6 => A p 0 (V 0 (parOf y' 0)))
    (b1 := fun y' : Tgt 6 => A p 1 (V 1 (parOf y' 1)))
    (b2 := fun y' : Tgt 6 => A p 2 (V 2 (parOf y' 2))) y z (hdiff 0) (hdiff 1) (hdiff 2)
  simpa only [classSystem] using h

end Work.Drive
