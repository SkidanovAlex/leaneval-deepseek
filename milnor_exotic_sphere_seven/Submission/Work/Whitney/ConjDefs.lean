import Mathlib
import Submission.Work.Thom.complexification
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.BundleIsoGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The conjugate complex bundle `Ē` of a complex gluing-data bundle `E`

For a complex vector bundle `E` (in the gluing-data model, with model fibre
`EuclideanSpace ℂ (Fin m)`), the **conjugate bundle** `Ē` is the complex bundle over the same base,
with the same cover and the same index map, whose transition functions are the *conjugates*
`conj ∘ g_{ij} ∘ conj` of those of `E` (an anti-linear operation that is again `ℂ`-linear, hence
legitimate as a transition function).  Fibrewise it is `E` with the opposite complex structure; the
classical facts are

* `E_ℝ ⊗_ℝ ℂ ≅ E ⊕ Ē`  (the realification's complexification splits into the two complex
  structures on the same real bundle),
* `c_j(Ē) = (-1)^j c_j(E)`,
* for a complex line bundle `L`: `p₁(L_ℝ) = c₁(L) ⌣ c₁(L)` (deliverable item 4 of the WHITNEY
  subproject).

This file constructs the fibre-level conjugation (`Work.Whitney.conjC`,
`Work.Whitney.conjCLM` — the conjugation of a complex-linear endomorphism, an *anti*-linear
operation), the bundle `Work.Whitney.conjCore`, and its basic functorial API.  The topological
comparison of the total spaces of `Z` and `conjCore Z` (the identity map is a homeomorphism, because
the two trivialisation systems differ by the fixed homeomorphism `conjC`) is in
`Submission/Work/Whitney/ConjTopology.lean`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## The fibre-level conjugation -/

/-- **Complex conjugation of `ℂ^n`**, coordinatewise, as an `ℝ`-linear map. -/
def conjC (n : ℕ) : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun v := WithLp.toLp 2 (fun i => star (v i))
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

@[simp] theorem conjC_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    conjC n v = WithLp.toLp 2 (fun i => star (v i)) := rfl

theorem conjC_coord (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (conjC n v) i = star (v i) := by
  simp [conjC]

/-- `conjC` is `ℝ`-linear and intertwines the `ℂ`-action with the conjugated one:
`conjC (z • v) = star z • conjC v`. -/
theorem conjC_smul (n : ℕ) (z : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    conjC n (z • v) = star z • conjC n v := by
  ext i
  simp [conjC, map_mul]

theorem conjC_involutive (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    conjC n (conjC n v) = v := by
  ext i
  simp [conjC]

theorem conjC_neg (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) : conjC n (-v) = -conjC n v :=
  map_neg _ _

theorem conjC_cxMulI (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    conjC n (cxMulI v) = -cxMulI (conjC n v) := by
  ext i
  simp only [conjC, cxMulI, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_neg, Pi.neg_apply]
  rw [star_mul, show star (Complex.I) = -Complex.I from by simp]
  ring

theorem conjC_cxOfReal (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    conjC n (cxOfReal u) = cxOfReal u := by
  ext i
  simp [conjC, cxOfReal]

theorem conjC_cxMulI_cxOfReal (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    conjC n (cxMulI (cxOfReal u)) = -cxMulI (cxOfReal u) := by
  rw [conjC_cxMulI, conjC_cxOfReal]

/-- The coordinatewise conjugation as a **continuous** `ℝ`-linear map. -/
def conjCLC (n : ℕ) : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap (conjC n)

@[simp] theorem conjCLC_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    conjCLC n v = conjC n v := rfl

theorem continuous_conjC (n : ℕ) : Continuous (conjC n) :=
  (conjCLC n).continuous

theorem continuousOn_conjC (n : ℕ) {α : Type*} [TopologicalSpace α] {s : Set α}
    {f : α → EuclideanSpace ℂ (Fin n)} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => conjC n (f x)) s :=
  (continuous_conjC n).comp_continuousOn hf

/-! ## Conjugation of a complex-linear endomorphism -/

/-- Conjugating a real-linear endomorphism of `ℂ^n` by `conjC`: `f ↦ conjC ∘ f ∘ conjC`. -/
def conjMap (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n) :=
  (conjC n).comp (f.comp (conjC n))

theorem conjMap_apply (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) : conjMap n f v = conjC n (f (conjC n v)) := rfl

theorem conjMap_conjMap (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :
    conjMap n (conjMap n f) = f := by
  ext v
  simp only [conjMap_apply, conjC_involutive]

theorem conjMap_add (n : ℕ) (f g : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :
    conjMap n (f + g) = conjMap n f + conjMap n g := by
  ext v
  simp only [conjMap_apply, LinearMap.add_apply, map_add]

theorem conjMap_smul (n : ℕ) (r : ℝ)
    (f : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :
    conjMap n (r • f) = r • conjMap n f := by
  ext v
  simp only [conjMap_apply, LinearMap.smul_apply, map_smul]

/-- A complex-linear endomorphism commutes with `cxMulI`. -/
theorem cxMulI_eq_smul (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    cxMulI v = Complex.I • v := by
  ext i
  rfl

theorem clm_cxMulI (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) : f (cxMulI v) = cxMulI (f v) := by
  have h1 : cxMulI v = Complex.I • v := cxMulI_eq_smul n v
  have h2 : Complex.I • f v = cxMulI (f v) := (cxMulI_eq_smul n (f v)).symm
  rw [h1, map_smul, h2]

theorem conjMap_cxMulI (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))
    (hf : ∀ v, f (cxMulI v) = cxMulI (f v)) (v : EuclideanSpace ℂ (Fin n)) :
    conjMap n f (cxMulI v) = cxMulI (conjMap n f v) := by
  rw [conjMap_apply, conjMap_apply, conjC_cxMulI, map_neg, hf, map_neg, conjC_cxMulI, neg_neg]

/-- **The conjugate of a complex-linear endomorphism**: `f ↦ conjC ∘ f ∘ conjC`, which is again
`ℂ`-linear (the conjugation is anti-linear and appears twice). -/
def conjCLM (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    (toCxLinear (conjMap n f.toLinearMap)
      (conjMap_cxMulI n f.toLinearMap (fun v => clm_cxMulI n f v)))

@[simp] theorem conjCLM_apply (n : ℕ) (f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) : conjCLM n f v = conjC n (f (conjC n v)) := rfl

@[simp] theorem conjCLM_one (n : ℕ) :
    conjCLM n (1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = 1 := by
  ext v
  simp only [conjCLM_apply, ContinuousLinearMap.one_apply, conjC_involutive]

theorem conjCLM_comp (n : ℕ)
    (f g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    conjCLM n (g.comp f) = (conjCLM n g).comp (conjCLM n f) := by
  ext v
  simp only [conjCLM_apply, ContinuousLinearMap.comp_apply, conjC_involutive]

theorem conjCLM_add (n : ℕ)
    (f g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    conjCLM n (f + g) = conjCLM n f + conjCLM n g := by
  ext v
  simp only [conjCLM_apply, ContinuousLinearMap.add_apply, map_add]

theorem conjCLM_conjCLM (n : ℕ)
    (f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    conjCLM n (conjCLM n f) = f := by
  ext v
  simp only [conjCLM_apply, conjC_involutive]

/-- Conjugation of endomorphisms as an `ℝ`-linear map. -/
def conjCLMLM (n : ℕ) :
    (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) where
  toFun := conjCLM n
  map_add' f g := conjCLM_add n f g
  map_smul' r f := by
    ext v
    simp only [conjCLM_apply, ContinuousLinearMap.smul_apply, map_smul, RingHom.id_apply]

/-- **Conjugation of endomorphisms is continuous** (it is `ℝ`-linear between finite-dimensional
spaces). -/
theorem continuous_conjCLM (n : ℕ) : Continuous (conjCLM n) :=
  (conjCLMLM n).continuous_of_finiteDimensional

theorem continuousOn_conjCLM (n : ℕ) {α : Type*} [TopologicalSpace α] {s : Set α}
    {f : α → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hf : ContinuousOn f s) :
    ContinuousOn (fun x => conjCLM n (f x)) s :=
  (continuous_conjCLM n).comp_continuousOn hf

/-! ## The conjugate bundle -/

/-- **The conjugate bundle** `Ē`: the same cover, the same index map, and the conjugated transition
functions `conj ∘ g_{ij} ∘ conj`. -/
def conjCore {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := conjCLM m (Z.coordChange i j x)
  coordChange_self i x hx v := by
    have h1 : Z.coordChange i i x = 1 :=
      ContinuousLinearMap.ext (fun w => Z.coordChange_self i x hx w)
    rw [h1, conjCLM_one]
    rfl
  continuousOn_coordChange i j :=
    continuousOn_conjCLM m (Z.continuousOn_coordChange i j)
  coordChange_comp i j k x hx v := by
    have hcomp : (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
      ContinuousLinearMap.ext (fun w => Z.coordChange_comp i j k x hx w)
    rw [← hcomp, conjCLM_comp]
    rfl

@[simp] theorem conjCore_baseSet {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) :
    (conjCore Z).baseSet i = Z.baseSet i := rfl

@[simp] theorem conjCore_indexAt {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (x : B) :
    (conjCore Z).indexAt x = Z.indexAt x := rfl

@[simp] theorem conjCore_coordChange {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι) (x : B) :
    (conjCore Z).coordChange i j x = conjCLM m (Z.coordChange i j x) := rfl

/-- **The conjugate of the conjugate bundle is the bundle itself.** -/
theorem conjCore_conjCore {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    conjCore (conjCore Z) = Z := by
  refine bundleCore_ext rfl rfl (fun i j x => ?_)
  rw [conjCore_coordChange, conjCore_coordChange, conjCLM_conjCLM]

/-- **The conjugate of the pullback is the pullback of the conjugate.** -/
theorem conjCore_bundleComap {m : ℕ} {B' : Type} [TopologicalSpace B']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    conjCore (bundleComap Z f) = bundleComap (conjCore Z) f := by
  refine bundleCore_ext rfl rfl (fun i j x => ?_)
  rw [conjCore_coordChange, bundleComap_coordChange, bundleComap_coordChange, conjCore_coordChange]

/-- The conjugate of a trivial bundle is trivial. -/
theorem conjCore_trivial {m : ℕ} (ι₀ : Type) [Inhabited ι₀] :
    conjCore (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₀)
      = trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₀ := by
  refine bundleCore_ext rfl rfl (fun i j x => ?_)
  rw [conjCore_coordChange]
  have htriv : (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι₀).coordChange i j x
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := rfl
  rw [htriv]
  ext v
  simp [conjCLM_apply]

end

end Work.Whitney
