import Mathlib
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.realification

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The complexification `E ⊗_ℝ ℂ` of a real vector bundle (gluing-data model)

The complexification of a real vector bundle with model fibre `EuclideanSpace ℝ (Fin k)` is the
complex vector bundle with model fibre `EuclideanSpace ℂ (Fin k)` whose transition functions are the
`ℂ`-linear extensions `g ⊗ id_ℂ` of the transition functions of `Z`.

The complexification of a single continuous ℝ-linear map `T` is, on the level of the *(real and
imaginary parts)* identification
`EuclideanSpace ℂ (Fin k) ≃ᵣ EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)`,
the map `(x, y) ↦ (T x, T y)`; on `ℂ^k` it is characterised by
`(T ⊗ id)(cxOfReal u) = cxOfReal (T u)`, where `cxOfReal` embeds `ℝ^k` as the real part of `ℂ^k`.
That characterisation, together with the two facts that `1 ⊗ id = 1` and `(T ∘ S) ⊗ id =
(T ⊗ id) ∘ (S ⊗ id)`, is all that is needed for the cocycle condition; the continuity of the
transition functions is inherited from `Z` because `T ↦ T ⊗ id` is ℝ-linear and between
finite-dimensional spaces, hence continuous.

This is rung 5 of ADDENDUM 14 of `Submission/Work/Thom/README.md`, and the input of the
Pontryagin classes `p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)`.
-/

open scoped RealInnerProductSpace

namespace Work.Thom

noncomputable section

/-! ## The real and imaginary parts of `ℂ^k`, and the real inclusion `ℝ^k → ℂ^k` -/

section Complexify

variable {k : ℕ}

/-- The real inclusion `ℝ^k → ℂ^k`, `u ↦ u + 0 i`. -/
def cxOfReal : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℂ (Fin k) where
  toFun u := WithLp.toLp 2 (fun t => ((u t : ℝ) : ℂ))
  map_add' u v := by ext t; simp
  map_smul' c u := by ext t; simp

/-- The real part `ℂ^k → ℝ^k`. -/
def cxRePart : EuclideanSpace ℂ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun v := WithLp.toLp 2 (fun t => ((v t).re : ℝ))
  map_add' u v := by ext t; simp
  map_smul' c u := by ext t; simp

/-- The imaginary part `ℂ^k → ℝ^k`. -/
def cxImPart : EuclideanSpace ℂ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun v := WithLp.toLp 2 (fun t => ((v t).im : ℝ))
  map_add' u v := by ext t; simp
  map_smul' c u := by ext t; simp

/-- Multiplication by `i` on `ℂ^k`, as an ℝ-linear map. -/
def cxMulI : EuclideanSpace ℂ (Fin k) →ₗ[ℝ] EuclideanSpace ℂ (Fin k) where
  toFun v := WithLp.toLp 2 (fun t => Complex.I * (v t))
  map_add' u v := by ext t; simp [mul_add]
  map_smul' c u := by ext t; simp [mul_left_comm]

@[simp] lemma cxRePart_cxOfReal (u : EuclideanSpace ℝ (Fin k)) : cxRePart (cxOfReal u) = u := by
  ext t; simp [cxRePart, cxOfReal]

@[simp] lemma cxImPart_cxOfReal (u : EuclideanSpace ℝ (Fin k)) : cxImPart (cxOfReal u) = 0 := by
  ext t; simp [cxImPart, cxOfReal]

@[simp] lemma cxRePart_cxMulI (v : EuclideanSpace ℂ (Fin k)) : cxRePart (cxMulI v) = - cxImPart v := by
  ext t; simp [cxMulI, cxRePart, cxImPart]

@[simp] lemma cxImPart_cxMulI (v : EuclideanSpace ℂ (Fin k)) : cxImPart (cxMulI v) = cxRePart v := by
  ext t; simp [cxMulI, cxRePart, cxImPart]

@[simp] lemma cxMulI_zero : cxMulI (0 : EuclideanSpace ℂ (Fin k)) = 0 := map_zero ..

lemma cxMulI_cxMulI (v : EuclideanSpace ℂ (Fin k)) : cxMulI (cxMulI v) = -v := by
  ext t
  simp only [cxMulI, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_neg, Pi.neg_apply]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- The decomposition `v = cxRePart v + i · cxImPart v` of a complex vector into real and imaginary
parts. -/
lemma cxOfReal_cxRePart_add_cxMulI_cxImPart (v : EuclideanSpace ℂ (Fin k)) :
    cxOfReal (cxRePart v) + cxMulI (cxOfReal (cxImPart v)) = v := by
  ext t
  simp only [cxOfReal, cxRePart, cxImPart, cxMulI, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_add,
    Pi.add_apply]
  rw [mul_comm Complex.I ((v t).im : ℂ)]
  exact Complex.re_add_im (v t)

/-- The decomposition of the ℂ-action in terms of the ℝ-action and `cxMulI`:
`c • v = c.re • v + c.im • (i · v)`. -/
lemma cx_complex_smul_eq (c : ℂ) (v : EuclideanSpace ℂ (Fin k)) :
    c • v = c.re • v + c.im • cxMulI v := by
  ext t
  simp only [cxMulI, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply]
  rw [smul_eq_mul, Complex.real_smul, Complex.real_smul]
  nth_rewrite 1 [← Complex.re_add_im c]
  rw [add_mul, mul_assoc]

/-! ## The complexification of a real-linear map -/

/-- The complexification of an ℝ-linear endomorphism `T` of `ℝ^k`, as an ℝ-linear endomorphism of
`ℂ^k`: on `x + i y` it is `x + i y ↦ T x + i T y`. -/
def cxMap (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℂ (Fin k) →ₗ[ℝ] EuclideanSpace ℂ (Fin k) :=
  cxOfReal.comp (T.comp cxRePart) + cxMulI.comp (cxOfReal.comp (T.comp cxImPart))

lemma cxMap_apply (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (v : EuclideanSpace ℂ (Fin k)) :
    cxMap T v = cxOfReal (T (cxRePart v)) + cxMulI (cxOfReal (T (cxImPart v))) := rfl

/-- `cxMap T` commutes with `i`, hence is `ℂ`-linear. -/
lemma cxMap_cxMulI (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    (v : EuclideanSpace ℂ (Fin k)) : cxMap T (cxMulI v) = cxMulI (cxMap T v) := by
  rw [cxMap_apply, cxMap_apply, cxRePart_cxMulI, cxImPart_cxMulI, map_add, cxMulI_cxMulI]
  simp only [map_neg]
  abel

/-- Upgrade an ℝ-linear endomorphism of `ℂ^k` commuting with `i` to a ℂ-linear endomorphism. -/
def toCxLinear (f : EuclideanSpace ℂ (Fin k) →ₗ[ℝ] EuclideanSpace ℂ (Fin k))
    (h : ∀ v, f (cxMulI v) = cxMulI (f v)) :
    EuclideanSpace ℂ (Fin k) →ₗ[ℂ] EuclideanSpace ℂ (Fin k) where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [cx_complex_smul_eq c v, cx_complex_smul_eq c (f v)]
    simp only [map_add, map_smul, h]

/-- **The complexification of a continuous ℝ-linear endomorphism** of `EuclideanSpace ℝ (Fin k)`:
the `ℂ`-linear endomorphism `T ⊗ id_ℂ` of `EuclideanSpace ℂ (Fin k)`. -/
def cxTrans (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
  LinearMap.toContinuousLinearMap (toCxLinear (cxMap T.toLinearMap) (cxMap_cxMulI T.toLinearMap))

lemma cxTrans_apply (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (v : EuclideanSpace ℂ (Fin k)) :
    cxTrans T v = cxOfReal (T (cxRePart v)) + cxMulI (cxOfReal (T (cxImPart v))) := rfl

/-- The defining property of the complexification: on the real part it is `T`. -/
lemma cxTrans_cxOfReal (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (u : EuclideanSpace ℝ (Fin k)) : cxTrans T (cxOfReal u) = cxOfReal (T u) := by
  simp only [cxTrans_apply, cxRePart_cxOfReal, cxImPart_cxOfReal, map_zero, add_zero]

lemma cxTrans_one :
    cxTrans (1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [cxTrans_apply]
  exact cxOfReal_cxRePart_add_cxMulI_cxImPart v

lemma cxTrans_pair (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (x y : EuclideanSpace ℝ (Fin k)) :
    cxTrans T (cxOfReal x + cxMulI (cxOfReal y)) = cxOfReal (T x) + cxMulI (cxOfReal (T y)) := by
  rw [cxTrans_apply]
  simp only [map_add, cxRePart_cxOfReal, cxImPart_cxOfReal, cxRePart_cxMulI, cxImPart_cxMulI, neg_zero,
    add_zero, zero_add]

/-- `T ↦ T ⊗ id_ℂ` is a functor: `(T ∘ S) ⊗ id = (T ⊗ id) ∘ (S ⊗ id)`. -/
lemma cxTrans_comp (T S : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    cxTrans (T.comp S) = (cxTrans T).comp (cxTrans S) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply]
  conv_rhs => rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart v]
  rw [cxTrans_pair, cxTrans_pair]
  rfl

/-! ## Continuity of the complexification of a transition function -/

/-- `T ↦ T ⊗ id_ℂ` is ℝ-linear. -/
def cxTransLM :
    (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →ₗ[ℝ]
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) where
  toFun := cxTrans
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cxTrans_apply, add_apply, map_add]
    abel
  map_smul' r T := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cxTrans_apply, smul_apply, map_smul, smul_add, RingHom.id_apply]

/-- `T ↦ T ⊗ id_ℂ` is continuous, being linear between finite-dimensional spaces. -/
lemma continuous_cxTrans :
    Continuous (cxTrans : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))) :=
  cxTransLM.continuous_of_finiteDimensional

end Complexify

/-! ## The complexification of a real vector bundle -/

section Bundle

variable {B : Type} [TopologicalSpace B] {k : ℕ} {ι : Type}

/-- **The complexification `E ⊗_ℝ ℂ` of a real bundle**, as a named gluing datum: the same cover
and index map as `Z`, and the transition functions `g_{ij} ⊗ id_ℂ` of `Z`.  It is the witness of
`Work.Thom.complexification`. -/
def complexificationCore (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j b := cxTrans (Z.coordChange i j b)
  coordChange_self i x hx v := by
    have h1 : Z.coordChange i i x = 1 :=
      ContinuousLinearMap.ext (fun w => Z.coordChange_self i x hx w)
    rw [h1, cxTrans_one]
    rfl
  continuousOn_coordChange i j :=
    continuous_cxTrans.comp_continuousOn (Z.continuousOn_coordChange i j)
  coordChange_comp i j l x hx v := by
    have hcomp : (Z.coordChange j l x).comp (Z.coordChange i j x) = Z.coordChange i l x :=
      ContinuousLinearMap.ext (fun w => Z.coordChange_comp i j l x hx w)
    rw [← hcomp, cxTrans_comp, ContinuousLinearMap.comp_apply]

/-- **The complexification `E ⊗_ℝ ℂ` of a real bundle.**  For a real vector bundle `Z` over `B` with
model fibre `EuclideanSpace ℝ (Fin k)`, the complexification is a *complex* vector bundle with model
fibre `EuclideanSpace ℂ (Fin k)` whose transition functions are the `ℂ`-linear extensions of the
transition functions of `Z` (i.e. `g_{ij} ⊗ id_ℂ`): the real parts of its transition functions are the
transition functions of `Z`, which is the conjunct below (`u : EuclideanSpace ℝ (Fin k)` is sent to
the complex vector with those real coordinates via `WithLp.toLp 2 (fun t => ((u t : ℝ) : ℂ))`).

This is rung 5 of ADDENDUM 14, and the input of the Pontryagin classes
`p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)`.  The complex model fibre `EuclideanSpace ℂ (Fin k)` carries all
the required instances already, and the identification `EuclideanSpace ℂ (Fin k) ≃ₗ[ℝ]
EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)` (real and imaginary parts) supplies the
complexification of a linear map; the cocycle condition is inherited from that of `Z`, since
`g ↦ g ⊗ id_ℂ` is a functor on linear maps.  Follow the pattern of
`Work.Thom.exists_underlyingReal` / `Work.Thom.realification` (`Submission/Work/Thom/realification.lean`)
if a named definition is wanted alongside the existence statement. -/
theorem complexification {B : Type} [TopologicalSpace B] {k : ℕ} {ι : Type}
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    ∃ Zc : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι,
      Zc.baseSet = Z.baseSet ∧ Zc.indexAt = Z.indexAt ∧
      (∀ i j (b : B) (u : EuclideanSpace ℝ (Fin k)),
        (Zc.coordChange i j b) (WithLp.toLp 2 (fun t => ((u t : ℝ) : ℂ))) =
          WithLp.toLp 2 (fun t => (((Z.coordChange i j b u) t : ℝ) : ℂ))) :=
  ⟨complexificationCore Z, rfl, rfl, fun i j b u => cxTrans_cxOfReal (Z.coordChange i j b) u⟩

theorem complexificationCore_baseSet
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    (complexificationCore Z).baseSet = Z.baseSet := rfl

theorem complexificationCore_indexAt
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    (complexificationCore Z).indexAt = Z.indexAt := rfl

theorem complexificationCore_coordChange
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i j : ι) (b : B) :
    ⇑((complexificationCore Z).coordChange i j b) = ⇑(cxTrans (Z.coordChange i j b)) := rfl

/-- The computation rule of the complexification on the real part of the fibre: it is the transition
function of `Z`. -/
theorem complexificationCore_coordChange_cxOfReal
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i j : ι) (b : B)
    (u : EuclideanSpace ℝ (Fin k)) :
    (complexificationCore Z).coordChange i j b
        (WithLp.toLp 2 (fun t => ((u t : ℝ) : ℂ))) =
      WithLp.toLp 2 (fun t => (((Z.coordChange i j b u) t : ℝ) : ℂ)) :=
  cxTrans_cxOfReal (Z.coordChange i j b) u

/-- The complexified transition function acts on real and imaginary parts separately, by the
transition function of `Z`. -/
theorem complexificationCore_coordChange_cxRePart
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i j : ι) (b : B)
    (v : EuclideanSpace ℂ (Fin k)) :
    cxRePart ((complexificationCore Z).coordChange i j b v) =
      Z.coordChange i j b (cxRePart v) := by
  conv_lhs => rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart v]
  rw [complexificationCore_coordChange, cxTrans_pair]
  simp

/-- The complexified transition function acts on real and imaginary parts separately, by the
transition function of `Z`. -/
theorem complexificationCore_coordChange_cxImPart
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i j : ι) (b : B)
    (v : EuclideanSpace ℂ (Fin k)) :
    cxImPart ((complexificationCore Z).coordChange i j b v) =
      Z.coordChange i j b (cxImPart v) := by
  conv_lhs => rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart v]
  rw [complexificationCore_coordChange, cxTrans_pair]
  simp

end Bundle

end

end Work.Thom
