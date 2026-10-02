import Mathlib
import Submission.Work.Whitney.Stability
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# The tensor product of complex line bundles (gluing data), and the determinant trick

`Work.Gen.tensorLine Z₁ Z₂` is the tensor product of two complex *line* bundle cores: the index type
is the product of the two covers, and the transition function is the product of the two scalar
transition functions.

The reason this module exists is the **determinant trick**: for a rank-two complex bundle `V` over
`B`, the tautological quotient `π^*V/ℂ·s` over the punctured total space `V∖0` is *canonically*
isomorphic to the pullback of the determinant line bundle `Λ²V`, via the map
`w ↦ w ∧ s` (wedging with the tautological point).  Applying this to `V = L₁ ⊕ L₂`, whose
determinant is `L₁ ⊗ L₂`, and using the descent equation of the Chern recursion gives

  `c₁(L₁ ⊕ L₂) = c₁(L₁ ⊗ L₂)`,

so the additivity of `c₁` on a Whitney sum of two line bundles is *equivalent* to the
multiplicativity of `c₁` on the tensor product (see `Submission/Work/Gen/lineSum_c1.lean`).
-/

namespace Work.Gen

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The one-dimensional model fibre `ℂ¹` -/

/-- The canonical generator of the one-dimensional model fibre `ℂ¹`. -/
def oneVec : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1

/-- Every vector of `ℂ¹` is a multiple of `oneVec`. -/
theorem oneVec_apply (v : EuclideanSpace ℂ (Fin 1)) : v = v.ofLp 0 • oneVec := by
  ext i; fin_cases i; simp [oneVec]

theorem oneVec_ne_zero : (oneVec : EuclideanSpace ℂ (Fin 1)) ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v.ofLp 0) h
  simpa [oneVec] using this

/-- **The scalar of a `ℂ`-linear endomorphism of `ℂ¹`**: the element `c` with `f = c • id`. -/
def scl (f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) : ℂ := (f oneVec).ofLp 0

/-- The defining property of `scl`: every `ℂ`-linear endomorphism of `ℂ¹` is scalar. -/
theorem scl_apply (f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
    (v : EuclideanSpace ℂ (Fin 1)) : f v = (scl f) • v := by
  rw [oneVec_apply v, map_smul, oneVec_apply (f oneVec), scl]
  simp only [smul_smul]
  congr 1
  ring

theorem scl_eq_of_apply (f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) (c : ℂ)
    (h : ∀ v, f v = c • v) : scl f = c := by
  have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v.ofLp 0) (h oneVec)
  simpa [scl, oneVec] using h1

theorem scl_smul_id (f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    f = (scl f) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [scl_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]

theorem scl_id : scl (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) = 1 := by
  rw [scl_eq_of_apply _ 1]
  intro v
  rw [ContinuousLinearMap.id_apply, one_smul]

theorem scl_smul (c : ℂ) (f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    scl (c • f) = c * scl f := by
  rw [scl_eq_of_apply _ (c * scl f)]
  intro v
  rw [ContinuousLinearMap.smul_apply, scl_apply, smul_smul]

/-- **The scalar of a scalar multiple of the identity is that scalar.** -/
theorem scl_smul_id_eq (c : ℂ) :
    scl (c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) = c := by
  rw [scl_smul, scl_id, mul_one]

theorem scl_comp (f g : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    scl (f.comp g) = scl f * scl g := by
  rw [scl_eq_of_apply _ (scl f * scl g)]
  intro v
  rw [ContinuousLinearMap.comp_apply, scl_apply g v, ContinuousLinearMap.map_smul, scl_apply,
    smul_smul, mul_comm (scl g) (scl f)]

theorem continuous_scl :
    Continuous fun f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1) => scl f := by
  have h1 : Continuous fun f : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1) =>
      f oneVec := continuous_eval_const oneVec
  have h2 : Continuous fun v : EuclideanSpace ℂ (Fin 1) => v.ofLp 0 :=
    PiLp.continuous_apply 2 (fun _ : Fin 1 => ℂ) 0
  exact h2.comp h1

/-! ## The tensor product -/

variable {ι₁ ι₂ : Type}

/-- **The tensor product of two complex line bundle cores**, over the product cover: the transition
functions multiply (each is a scalar multiplication, and `ℂ ⊗ ℂ ≅ ℂ`). -/
def tensorLine (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) (ι₁ × ι₂) where
  baseSet p := Z₁.baseSet p.1 ∩ Z₂.baseSet p.2
  isOpen_baseSet p := (Z₁.isOpen_baseSet p.1).inter (Z₂.isOpen_baseSet p.2)
  indexAt x := (Z₁.indexAt x, Z₂.indexAt x)
  mem_baseSet_at x := ⟨Z₁.mem_baseSet_at x, Z₂.mem_baseSet_at x⟩
  coordChange p q x := (scl (Z₁.coordChange p.1 q.1 x) * scl (Z₂.coordChange p.2 q.2 x)) •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))
  coordChange_self p x hx v := by
    have hs1 : scl (Z₁.coordChange p.1 p.1 x) = 1 := by
      have hfun : Z₁.coordChange p.1 p.1 x = ContinuousLinearMap.id ℂ _ := by
        apply ContinuousLinearMap.ext
        intro w
        exact Z₁.coordChange_self p.1 x hx.1 w
      rw [hfun, scl_id]
    have hs2 : scl (Z₂.coordChange p.2 p.2 x) = 1 := by
      have hfun : Z₂.coordChange p.2 p.2 x = ContinuousLinearMap.id ℂ _ := by
        apply ContinuousLinearMap.ext
        intro w
        exact Z₂.coordChange_self p.2 x hx.2 w
      rw [hfun, scl_id]
    rw [hs1, hs2]
    simp
  continuousOn_coordChange p q := by
    have h1 : ContinuousOn (fun x => scl (Z₁.coordChange p.1 q.1 x))
        (Z₁.baseSet p.1 ∩ Z₁.baseSet q.1) :=
      continuous_scl.comp_continuousOn (Z₁.continuousOn_coordChange p.1 q.1)
    have h2 : ContinuousOn (fun x => scl (Z₂.coordChange p.2 q.2 x))
        (Z₂.baseSet p.2 ∩ Z₂.baseSet q.2) :=
      continuous_scl.comp_continuousOn (Z₂.continuousOn_coordChange p.2 q.2)
    have hmul : ContinuousOn
        (fun x => scl (Z₁.coordChange p.1 q.1 x) * scl (Z₂.coordChange p.2 q.2 x))
        ((Z₁.baseSet p.1 ∩ Z₂.baseSet p.2) ∩ (Z₁.baseSet q.1 ∩ Z₂.baseSet q.2)) :=
      (h1.mono (fun x hx => ⟨hx.1.1, hx.2.1⟩)).mul (h2.mono (fun x hx => ⟨hx.1.2, hx.2.2⟩))
    exact hmul.smul (continuousOn_const :
      ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)

  coordChange_comp p q r x hx v := by
    have hx1 : x ∈ Z₁.baseSet p.1 ∩ Z₁.baseSet q.1 := ⟨hx.1.1.1, hx.1.2.1⟩
    have hx1' : x ∈ Z₁.baseSet q.1 ∩ Z₁.baseSet r.1 :=
      ⟨hx1.2, (show x ∈ Z₁.baseSet r.1 from hx.2.1)⟩
    have hx2 : x ∈ Z₂.baseSet p.2 ∩ Z₂.baseSet q.2 := ⟨hx.1.1.2, hx.1.2.2⟩
    have hx2' : x ∈ Z₂.baseSet q.2 ∩ Z₂.baseSet r.2 :=
      ⟨hx2.2, (show x ∈ Z₂.baseSet r.2 from hx.2.2)⟩
    have hfun1 : Z₁.coordChange p.1 r.1 x
        = (Z₁.coordChange q.1 r.1 x).comp (Z₁.coordChange p.1 q.1 x) := by
      apply ContinuousLinearMap.ext
      intro w
      exact (Z₁.coordChange_comp p.1 q.1 r.1 x ⟨hx1, hx.2.1⟩ w).symm
    have hfun2 : Z₂.coordChange p.2 r.2 x
        = (Z₂.coordChange q.2 r.2 x).comp (Z₂.coordChange p.2 q.2 x) := by
      apply ContinuousLinearMap.ext
      intro w
      exact (Z₂.coordChange_comp p.2 q.2 r.2 x ⟨hx2, hx.2.2⟩ w).symm
    have hs1 : scl (Z₁.coordChange p.1 r.1 x)
        = scl (Z₁.coordChange p.1 q.1 x) * scl (Z₁.coordChange q.1 r.1 x) := by
      rw [hfun1, scl_comp]; ring
    have hs2 : scl (Z₂.coordChange p.2 r.2 x)
        = scl (Z₂.coordChange p.2 q.2 x) * scl (Z₂.coordChange q.2 r.2 x) := by
      rw [hfun2, scl_comp]; ring
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [hs1, hs2]
    congr 1
    ring

@[simp] theorem tensorLine_baseSet (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) (p : ι₁ × ι₂) :
    (tensorLine Z₁ Z₂).baseSet p = Z₁.baseSet p.1 ∩ Z₂.baseSet p.2 := rfl

@[simp] theorem tensorLine_indexAt (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) (x : B) :
    (tensorLine Z₁ Z₂).indexAt x = (Z₁.indexAt x, Z₂.indexAt x) := rfl

@[simp] theorem tensorLine_coordChange (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) (p q : ι₁ × ι₂) (x : B) :
    (tensorLine Z₁ Z₂).coordChange p q x =
      (scl (Z₁.coordChange p.1 q.1 x) * scl (Z₂.coordChange p.2 q.2 x)) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := rfl

/-- The tensor product commutes with pullback, definitionally. -/
theorem tensorLine_bundleComap {B' : Type} [TopologicalSpace B'] (f : C(B', B))
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Work.Thom.bundleComap (tensorLine Z₁ Z₂) f
      = tensorLine (Work.Thom.bundleComap Z₁ f) (Work.Thom.bundleComap Z₂ f) := rfl

end

end Work.Gen
