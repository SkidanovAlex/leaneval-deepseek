import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.projImmersion

/-!
# The data of the chart perturbation `Ξ` of the capping space

`Work.Drive.ChartPert Q m Ξ` (`Submission/Work/Drive/sideGerm.lean`) asks for a smooth `m`-parameter
family of self-maps of the capping space `Y = Work.Drive.CappingSpace` with `Ξ 0 = id` whose
parameter-derivative at every parameter and every point is onto.  This file builds the family.

The capping space is the product `(0,∞) × ℝP³` in the coordinates of the concrete homeomorphism
`Work.Drive.cappingSpaceHomeoProj`; the family acts on the two factors as

* `r ↦ exp (exp⁻¹ r + t 0)` on the level `(0,∞)` (one parameter, the derivative in `t 0` is the
  identity of `ℝ` in the exponential chart),
* `[v] ↦ [(1 + L (t)) v]` on the class `ℝP³ ≅ ℍ/±1`, where `L (t)` is *left multiplication by the
  imaginary quaternion* `t 1 i + t 2 j + t 3 k` (three parameters).

The two algebraic facts about `L` that the construction rests on are

* `classGen_classGen` — `L (t) ∘ L (t) = -‖t‖² · 1` (whence `1 + L (t)` is invertible, with the
  explicit inverse `(1 + ‖t‖²)⁻¹ (1 - L (t))`), and
* `classGen_inner_zero` — `⟪L (t) v, v⟫ = 0`, i.e. `L (t)` is antisymmetric, so that the range of
  `t ↦ L (t) v` is the orthogonal complement of `v` — a complement of the line of the image point.
-/

namespace Work.Drive

noncomputable section

open scoped Manifold ContDiff LinearAlgebra.Projectivization

/-! ## The three quaternionic generators -/

/-- The `i`-th coordinate projection of `ℝ⁴`. -/
def cproj (i : Fin 4) : Eucl 3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

/-- The identification `(Fin 4 → ℝ) ≃L ℝ⁴`. -/
def toLp4 : (Fin 4 → ℝ) →L[ℝ] Eucl 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm

/-- Quaternionic left multiplication by `i`, in real coordinates `(x,y,z,w) ↦ (-y, x, -w, z)`. -/
def genI : Eucl 3 →L[ℝ] Eucl 3 :=
  toLp4.comp (ContinuousLinearMap.pi (![-cproj 1, cproj 0, -cproj 3, cproj 2] :
    Fin 4 → (Eucl 3 →L[ℝ] ℝ)))

/-- Quaternionic left multiplication by `j`, in real coordinates `(x,y,z,w) ↦ (-z, w, x, -y)`. -/
def genJ : Eucl 3 →L[ℝ] Eucl 3 :=
  toLp4.comp (ContinuousLinearMap.pi (![-cproj 2, cproj 3, cproj 0, -cproj 1] :
    Fin 4 → (Eucl 3 →L[ℝ] ℝ)))

/-- Quaternionic left multiplication by `k`, in real coordinates `(x,y,z,w) ↦ (-w, -z, y, x)`. -/
def genK : Eucl 3 →L[ℝ] Eucl 3 :=
  toLp4.comp (ContinuousLinearMap.pi (![-cproj 3, -cproj 2, cproj 1, cproj 0] :
    Fin 4 → (Eucl 3 →L[ℝ] ℝ)))

@[simp] lemma genI_apply_0 (v : Eucl 3) : (genI v).ofLp 0 = -(v.ofLp 1) := by
  simp [genI, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genI_apply_1 (v : Eucl 3) : (genI v).ofLp 1 = v.ofLp 0 := by
  simp [genI, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genI_apply_2 (v : Eucl 3) : (genI v).ofLp 2 = -(v.ofLp 3) := by
  simp [genI, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genI_apply_3 (v : Eucl 3) : (genI v).ofLp 3 = v.ofLp 2 := by
  simp [genI, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genJ_apply_0 (v : Eucl 3) : (genJ v).ofLp 0 = -(v.ofLp 2) := by
  simp [genJ, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genJ_apply_1 (v : Eucl 3) : (genJ v).ofLp 1 = v.ofLp 3 := by
  simp [genJ, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genJ_apply_2 (v : Eucl 3) : (genJ v).ofLp 2 = v.ofLp 0 := by
  simp [genJ, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genJ_apply_3 (v : Eucl 3) : (genJ v).ofLp 3 = -(v.ofLp 1) := by
  simp [genJ, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genK_apply_0 (v : Eucl 3) : (genK v).ofLp 0 = -(v.ofLp 3) := by
  simp [genK, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genK_apply_1 (v : Eucl 3) : (genK v).ofLp 1 = -(v.ofLp 2) := by
  simp [genK, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genK_apply_2 (v : Eucl 3) : (genK v).ofLp 2 = v.ofLp 1 := by
  simp [genK, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]
@[simp] lemma genK_apply_3 (v : Eucl 3) : (genK v).ofLp 3 = v.ofLp 0 := by
  simp [genK, toLp4, cproj, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply,
    WithLp.ofLp_toLp]

/-! ## The class generator -/

/-- **The class generator**: quaternionic left multiplication by the imaginary quaternion with
coordinates `(t 1, t 2, t 3)`. -/
def classGen (t : Eucl 3) : Eucl 3 →L[ℝ] Eucl 3 :=
  (t 1) • genI + (t 2) • genJ + (t 3) • genK

lemma classGen_apply (t v : Eucl 3) :
    classGen t v = (t 1) • genI v + (t 2) • genJ v + (t 3) • genK v := by
  simp [classGen]

@[simp] lemma classGen_ofLp_0 (t v : Eucl 3) :
    (classGen t v).ofLp 0 = -(t 1) * v.ofLp 1 - (t 2) * v.ofLp 2 - (t 3) * v.ofLp 3 := by
  rw [classGen_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, genI_apply_0, genJ_apply_0,
    genK_apply_0]
  ring
@[simp] lemma classGen_ofLp_1 (t v : Eucl 3) :
    (classGen t v).ofLp 1 = (t 1) * v.ofLp 0 + (t 2) * v.ofLp 3 - (t 3) * v.ofLp 2 := by
  rw [classGen_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, genI_apply_1, genJ_apply_1,
    genK_apply_1]
  ring
@[simp] lemma classGen_ofLp_2 (t v : Eucl 3) :
    (classGen t v).ofLp 2 = -(t 1) * v.ofLp 3 + (t 2) * v.ofLp 0 + (t 3) * v.ofLp 1 := by
  rw [classGen_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, genI_apply_2, genJ_apply_2,
    genK_apply_2]
  ring
@[simp] lemma classGen_ofLp_3 (t v : Eucl 3) :
    (classGen t v).ofLp 3 = (t 1) * v.ofLp 2 - (t 2) * v.ofLp 1 + (t 3) * v.ofLp 0 := by
  rw [classGen_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, genI_apply_3, genJ_apply_3,
    genK_apply_3]
  ring

/-- The class norm square `‖t 1 i + t 2 j + t 3 k‖²`. -/
def classNormSq (t : Eucl 3) : ℝ := (t 1) ^ 2 + (t 2) ^ 2 + (t 3) ^ 2

lemma classNormSq_nonneg (t : Eucl 3) : 0 ≤ classNormSq t := by
  simp only [classNormSq]; positivity

/-- **The square of the class generator**: `L (t) ∘ L (t) = -‖t‖² · 1`. -/
theorem classGen_classGen (t v : Eucl 3) :
    classGen t (classGen t v) = -(classNormSq t) • v := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show ((classGen t) ((classGen t) v)).ofLp (0 : Fin 4) =
      ((-(classNormSq t)) • v).ofLp (0 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      classNormSq, PiLp.smul_apply, smul_eq_mul]
    ring
  case «1» =>
    show ((classGen t) ((classGen t) v)).ofLp (1 : Fin 4) =
      ((-(classNormSq t)) • v).ofLp (1 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      classNormSq, PiLp.smul_apply, smul_eq_mul]
    ring
  case «2» =>
    show ((classGen t) ((classGen t) v)).ofLp (2 : Fin 4) =
      ((-(classNormSq t)) • v).ofLp (2 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      classNormSq, PiLp.smul_apply, smul_eq_mul]
    ring
  case «3» =>
    show ((classGen t) ((classGen t) v)).ofLp (3 : Fin 4) =
      ((-(classNormSq t)) • v).ofLp (3 : Fin 4)
    simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
      classNormSq, PiLp.smul_apply, smul_eq_mul]
    ring

/-- **The class generator is antisymmetric**: `⟪L (t) v, v⟫ = 0`. -/
theorem classGen_inner_zero (t v : Eucl 3) : inner ℝ (classGen t v) v = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [classGen_ofLp_0, classGen_ofLp_1, classGen_ofLp_2, classGen_ofLp_3,
    Real.inner_apply]
  ring

/-- The class generator depends only on the last three coordinates of the parameter. -/
theorem classGen_congr {s t : Eucl 3} (h1 : s 1 = t 1) (h2 : s 2 = t 2) (h3 : s 3 = t 3) :
    classGen s = classGen t := by
  simp only [classGen, h1, h2, h3]

/-! ## The class equivalence `1 + L (t)` -/

/-- **The composite `(1 - L) ∘ (1 + L)` is the scalar `1 + ‖t‖²`.** -/
theorem classGen_sub_mul (t v : Eucl 3) :
    ((1 - classGen t : Eucl 3 →L[ℝ] Eucl 3)) ((1 + classGen t) v)
      = (1 + classNormSq t) • v := by
  have h1 : ((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3)) v = v + classGen t v := rfl
  have h2 : ((1 - classGen t : Eucl 3 →L[ℝ] Eucl 3)) (v + classGen t v)
      = (v + classGen t v) - classGen t (v + classGen t v) := rfl
  rw [h1, h2, map_add, classGen_classGen]
  module

/-- **The composite `(1 + L) ∘ (1 - L)` is the scalar `1 + ‖t‖²`.** -/
theorem classGen_mul_sub (t v : Eucl 3) :
    ((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3)) ((1 - classGen t) v)
      = (1 + classNormSq t) • v := by
  have h1 : ((1 - classGen t : Eucl 3 →L[ℝ] Eucl 3)) v = v - classGen t v := rfl
  have h2 : ((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3)) (v - classGen t v)
      = (v - classGen t v) + classGen t (v - classGen t v) := rfl
  rw [h1, h2, map_sub, classGen_classGen]
  module

theorem classEquiv_add_injective (t : Eucl 3) :
    Function.Injective ((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3) : Eucl 3 → Eucl 3) := by
  intro v w hvw
  have hpos : (0 : ℝ) < 1 + classNormSq t := by
    have := classNormSq_nonneg t; linarith
  have hzero : ((1 - classGen t : Eucl 3 →L[ℝ] Eucl 3))
      ((1 + classGen t) (v - w)) = 0 := by
    rw [map_sub, hvw, sub_self, map_zero]
  rw [classGen_sub_mul] at hzero
  have := congrArg (fun x => (1 + classNormSq t)⁻¹ • x) hzero
  simp only [smul_smul, smul_zero, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] at this
  simpa using sub_eq_zero.mp this

theorem classEquiv_add_surjective (t : Eucl 3) :
    Function.Surjective ((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3) : Eucl 3 → Eucl 3) := by
  intro w
  have hpos : (0 : ℝ) < 1 + classNormSq t := by
    have := classNormSq_nonneg t; linarith
  refine ⟨(1 + classNormSq t)⁻¹ • ((1 - classGen t) w), ?_⟩
  have hcomp : (1 + classGen t) ((1 + classNormSq t)⁻¹ • ((1 - classGen t) w))
      = (1 + classNormSq t)⁻¹ • ((1 + classGen t) ((1 - classGen t) w)) :=
    map_smul _ _ _
  rw [hcomp, classGen_mul_sub]
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul]

/-- **The class equivalence**: `1 + L (t)`, i.e. `v ↦ v + (t 1 i + t 2 j + t 3 k) v`. -/
def classEquiv (t : Eucl 3) : Eucl 3 ≃L[ℝ] Eucl 3 :=
  (LinearEquiv.ofBijective ((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3)
    ⟨classEquiv_add_injective t, classEquiv_add_surjective t⟩).toContinuousLinearEquiv

@[simp] lemma classEquiv_apply (t v : Eucl 3) : classEquiv t v = v + classGen t v := rfl

@[simp] lemma classGen_zero : classGen (0 : Eucl 3) = 0 := by
  ext v
  simp [classGen]

@[simp] lemma classEquiv_zero (v : Eucl 3) : classEquiv 0 v = v := by
  simp [classEquiv_apply]

lemma classEquiv_injective (t : Eucl 3) : Function.Injective (classEquiv t) :=
  (classEquiv t).injective

lemma classEquiv_ne_zero {t : Eucl 3} {v : Eucl 3} (hv : v ≠ 0) : classEquiv t v ≠ 0 :=
  fun h => hv ((classEquiv t).injective (by simpa using h))

/-- **The class map on `ℝP³`**: the projectivisation of `1 + L (t)`. -/
def classMap (t : Eucl 3) : Projectivization ℝ (Eucl 3) → Projectivization ℝ (Eucl 3) :=
  Projectivization.map ((classEquiv t : Eucl 3 →L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3)
    (classEquiv t).injective

lemma classMap_mk (t : Eucl 3) (v : Eucl 3) (hv : v ≠ 0) :
    classMap t (Projectivization.mk ℝ v hv)
      = Projectivization.mk ℝ (classEquiv t v) (classEquiv_ne_zero hv) :=
  Projectivization.map_mk _ _ v hv

@[simp] lemma classMap_zero (p : Projectivization ℝ (Eucl 3)) : classMap 0 p = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [classMap_mk]
    exact (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr ⟨1, by simp⟩


/-! ## The class generator as a linear map in the parameter -/

/-- The first basis vector `(1,0,0,0)`. -/
def e0 : Eucl 3 := WithLp.toLp 2 ![1, 0, 0, 0]

@[simp] lemma e0_ofLp_zero : (e0 : Eucl 3).ofLp 0 = 1 := by
  simp [e0, WithLp.ofLp_toLp]
@[simp] lemma e0_ofLp_one : (e0 : Eucl 3).ofLp 1 = 0 := by
  simp [e0, WithLp.ofLp_toLp]
@[simp] lemma e0_ofLp_two : (e0 : Eucl 3).ofLp 2 = 0 := by
  simp [e0, WithLp.ofLp_toLp]
@[simp] lemma e0_ofLp_three : (e0 : Eucl 3).ofLp 3 = 0 := by
  simp [e0, WithLp.ofLp_toLp]

lemma e0_ne_zero : (e0 : Eucl 3) ≠ 0 := by
  intro h
  have h0 : (e0 : Eucl 3).ofLp 0 = (0 : Eucl 3).ofLp 0 := by rw [h]
  simpa using h0

/-- **The class generator as a linear map of the parameter.** -/
def classEval (v : Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3 :=
  (cproj 1).smulRight (genI v) + (cproj 2).smulRight (genJ v) + (cproj 3).smulRight (genK v)

lemma classEval_apply (v s : Eucl 3) : classEval v s = classGen s v := by
  simp only [classEval, LinearMap.add_apply, LinearMap.smulRight_apply,
    ContinuousLinearMap.coe_coe, LinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  simp only [classGen, add_apply, smul_apply]
  rfl

/-- The class evaluation kills the first coordinate: it only sees `s 1`, `s 2`, `s 3`. -/
lemma classEval_smul_e0 (v : Eucl 3) (a : ℝ) : classEval v (a • e0) = 0 := by
  rw [classEval_apply]
  have h1 : (a • (e0 : Eucl 3)) 1 = 0 := by simp
  have h2 : (a • (e0 : Eucl 3)) 2 = 0 := by simp
  have h3 : (a • (e0 : Eucl 3)) 3 = 0 := by simp
  rw [classGen_apply, h1, h2, h3]
  simp

/-- A vector whose last three coordinates vanish is a multiple of `e0`. -/
lemma eq_smul_e0_of_tail_zero {s : Eucl 3} (h1 : s 1 = 0) (h2 : s 2 = 0) (h3 : s 3 = 0) :
    s = s 0 • (e0 : Eucl 3) := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  case «0» =>
    show s.ofLp (0 : Fin 4) = (s 0 • (e0 : Eucl 3)).ofLp (0 : Fin 4)
    simp
  case «1» =>
    show s.ofLp (1 : Fin 4) = (s 0 • (e0 : Eucl 3)).ofLp (1 : Fin 4)
    simp [h1]
  case «2» =>
    show s.ofLp (2 : Fin 4) = (s 0 • (e0 : Eucl 3)).ofLp (2 : Fin 4)
    simp [h2]
  case «3» =>
    show s.ofLp (3 : Fin 4) = (s 0 • (e0 : Eucl 3)).ofLp (3 : Fin 4)
    simp [h3]

/-- **The kernel of the class evaluation is the line of the first coordinate.** -/
lemma classEval_ker {v : Eucl 3} (hv : v ≠ 0) :
    LinearMap.ker (classEval v) = ℝ ∙ (e0 : Eucl 3) := by
  ext s
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hs
    have hs' : classGen s v = 0 := by rw [← classEval_apply]; exact hs
    have hsq : classNormSq s = 0 := by
      have h := classGen_classGen s v
      rw [hs', map_zero] at h
      have h2 : (classNormSq s) • v = 0 := by
        have h' : (-(classNormSq s)) • v = 0 := h.symm
        rw [neg_smul] at h'
        exact neg_eq_zero.mp h'
      exact (smul_eq_zero.mp h2).resolve_right hv
    have h1 : s 1 = 0 := by
      have : (s 1) ^ 2 + (s 2) ^ 2 + (s 3) ^ 2 = 0 := by simpa [classNormSq] using hsq
      nlinarith [sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have h2 : s 2 = 0 := by
      have : (s 1) ^ 2 + (s 2) ^ 2 + (s 3) ^ 2 = 0 := by simpa [classNormSq] using hsq
      nlinarith [sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have h3 : s 3 = 0 := by
      have : (s 1) ^ 2 + (s 2) ^ 2 + (s 3) ^ 2 = 0 := by simpa [classNormSq] using hsq
      nlinarith [sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    exact ⟨s 0, (eq_smul_e0_of_tail_zero h1 h2 h3).symm⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact classEval_smul_e0 v a

/-! ## The class derivative is surjective -/

/-- The class evaluation as a continuous linear map. -/
def classEvalCLM (v : Eucl 3) : Eucl 3 →L[ℝ] Eucl 3 :=
  (cproj 1).smulRight (genI v) + (cproj 2).smulRight (genJ v) + (cproj 3).smulRight (genK v)

@[simp] lemma classEvalCLM_apply (v s : Eucl 3) : classEvalCLM v s = classGen s v := by
  simp only [classEvalCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply]
  simp only [classGen_apply]
  rfl

/-- The class family `s ↦ classEquiv s v` is affine in the parameter, with linear part the class
evaluation. -/
lemma hasFDerivAt_classEquiv (t v : Eucl 3) :
    HasFDerivAt (fun s : Eucl 3 => classEquiv s v) (classEvalCLM v) t := by
  have h : HasFDerivAt (fun s : Eucl 3 => v + classEvalCLM v s) (classEvalCLM v) t :=
    HasFDerivAt.const_add v ((classEvalCLM v).hasFDerivAt (x := t))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
  simp only [classEquiv_apply, classEvalCLM_apply, add_comm]

/-- **The class derivative is onto.**  The parameter derivative of the class family at `t`, read in
the projective chart `j` at the image point `classEquiv t v`, is surjective: the class directions
span a complement of the line of the image point. -/
theorem classDeriv_surjective {v : Eucl 3} (hv : v ≠ 0) (t : Eucl 3) (j : Fin 4)
    (hj : (classEquiv t v).ofLp j ≠ 0) :
    Function.Surjective (fun s : Eucl 3 =>
      projCoordFunDerivE j (classEquiv t v) (classGen s v)) := by
  classical
  set w : Eucl 3 := classEquiv t v with hw
  set fL : Eucl 3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (projCoordFunDerivE j w : Eucl 3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) with hfL
  have hfL_apply : ∀ x : Eucl 3, fL x = projCoordFunDerivE j w x := fun x => rfl
  set U : Submodule ℝ (Eucl 3) := LinearMap.range (classEval v) with hU
  -- the class evaluation's kernel is the line of `e0`, so its range has dimension three
  have hker : LinearMap.ker (classEval v) = ℝ ∙ (e0 : Eucl 3) := classEval_ker hv
  have hfinU : Module.finrank ℝ U = 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker (classEval v)
    rw [hU]
    rw [hker, finrank_span_singleton e0_ne_zero] at h
    have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
    rw [h4] at h
    omega
  -- every element of `U` is orthogonal to `v`
  have hUorth : ∀ x ∈ U, inner ℝ x v = 0 := by
    intro x hx
    obtain ⟨s, hs⟩ := hx
    rw [← hs, classEval_apply]
    exact classGen_inner_zero s v
  -- the image point is not orthogonal to `v`, so it is not in `U`
  have hwv : inner ℝ w v = ‖v‖ ^ 2 := by
    rw [hw, classEquiv_apply, inner_add_left, classGen_inner_zero, add_zero,
      real_inner_self_eq_norm_sq]
  have hvn : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hwU : w ∉ U := by
    intro hwmem
    have := hUorth w hwmem
    rw [hwv] at this
    exact absurd this (ne_of_gt hvn)
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hwv
    exact absurd hwv.symm (ne_of_gt hvn)
  -- the kernel of the chart derivative is the line of `w`
  have hjw : w.ofLp j ≠ 0 := hj
  have hkerf : LinearMap.ker fL = ℝ ∙ w := by
    ext x
    rw [LinearMap.mem_ker, hfL_apply, projCoordFunDerivE_eq_zero_iff hjw x]
  have hkerf_fin : Module.finrank ℝ (LinearMap.ker fL) = 1 := by
    rw [hkerf, finrank_span_singleton hw0]
  -- `U` and `ker f` meet in `0` and together span everything
  have hUinf : U ⊓ LinearMap.ker fL = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxk⟩ := hx
    have hxlin : x ∈ ℝ ∙ w := by rw [← hkerf]; exact hxk
    rw [Submodule.mem_span_singleton] at hxlin
    obtain ⟨a, ha⟩ := hxlin
    have haU : a • w ∈ U := by rw [ha]; exact hxU
    have ha0 : a = 0 := by
      by_contra hane
      exact hwU ((Submodule.smul_mem_iff U hane).mp haU)
    rw [ha0, zero_smul] at ha
    exact ha.symm
  have hsup : U ⊔ LinearMap.ker fL = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker fL)
    rw [hUinf, hfinU, hkerf_fin] at h
    have hb : Module.finrank ℝ (↥(⊥ : Submodule ℝ (Eucl 3))) = 0 := by simp
    rw [hb] at h
    have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
    rw [h4]
    omega
  -- the chart derivative is onto
  have hmap_top : Submodule.map fL (⊤ : Submodule ℝ (Eucl 3)) = ⊤ := by
    rw [Submodule.map_top]
    refine Submodule.eq_top_of_finrank_eq ?_
    have h := LinearMap.finrank_range_add_finrank_ker fL
    rw [hkerf_fin] at h
    have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
    rw [h4] at h
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hfr : Module.finrank ℝ ↥fL.range = 3 := by omega
    rw [hfr, h3]
  have hkerbot : Submodule.map fL (LinearMap.ker fL) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨k, hk, hkx⟩ := hx
    rw [← hkx]
    exact LinearMap.mem_ker.mp hk
  have hmapU : Submodule.map fL U = ⊤ := by
    have h1 : Submodule.map fL (U ⊔ LinearMap.ker fL) = Submodule.map fL U := by
      rw [Submodule.map_sup, hkerbot, sup_bot_eq]
    rw [← h1, hsup, hmap_top]
  -- conclude
  intro y
  have hy : y ∈ Submodule.map fL U := by rw [hmapU]; trivial
  obtain ⟨x, hxU, hxy⟩ := hy
  obtain ⟨s, hs⟩ := hxU
  refine ⟨s, ?_⟩
  show projCoordFunDerivE j w (classGen s v) = y
  rw [← classEval_apply, hs, ← hfL_apply]
  exact hxy

/-! ## The family -/

/-- The unit vector of `ℝ¹ = EuclideanSpace ℝ (Fin 1)`. -/
def e1 : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))

/-- The level scaling `r ↦ exp (exp⁻¹ r + t 0)`. -/
def levelScale (t : Eucl 3) (r : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  expHomeo (expHomeo.symm r + (t 0) • (e1 : EuclideanSpace ℝ (Fin 1)))

@[simp] lemma levelScale_zero (r : Set.Ioi (0 : ℝ)) : levelScale 0 r = r := by
  simp [levelScale]

@[simp] lemma expHomeo_symm_levelScale (t : Eucl 3) (r : Set.Ioi (0 : ℝ)) :
    expHomeo.symm (levelScale t r)
      = expHomeo.symm r + (t 0) • (e1 : EuclideanSpace ℝ (Fin 1)) := by
  simp [levelScale]

/-- The derivative of the level scaling, read in the exponential chart: it is `s ↦ s 0`. -/
lemma fderiv_expHomeo_symm_levelScale (t : Eucl 3) (r : Set.Ioi (0 : ℝ)) :
    fderiv ℝ (fun s : Eucl 3 => expHomeo.symm (levelScale s r)) t
      = (cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1)) := by
  have hfun : (fun s : Eucl 3 => expHomeo.symm (levelScale s r))
      = fun s : Eucl 3 =>
          expHomeo.symm r + (cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1)) s := by
    funext s
    rw [expHomeo_symm_levelScale]
    simp only [ContinuousLinearMap.smulRight_apply, cproj, PiLp.proj_apply]
  rw [hfun]
  exact (HasFDerivAt.const_add (expHomeo.symm r)
    ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))).hasFDerivAt).fderiv

/-- The coordinate family on `(0,∞) × ℝP³`: scale the level, act on the class. -/
def coordFam (t : Eucl 3) (x : Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3)) :
    Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3) :=
  (levelScale t x.1, classMap t x.2)

@[simp] lemma coordFam_zero (x : Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3)) :
    coordFam 0 x = x := by
  simp [coordFam]

@[simp] lemma coordFam_fst (t : Eucl 3) (x : Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3)) :
    (coordFam t x).1 = levelScale t x.1 := rfl

@[simp] lemma coordFam_snd (t : Eucl 3) (x : Set.Ioi (0 : ℝ) × Projectivization ℝ (Eucl 3)) :
    (coordFam t x).2 = classMap t x.2 := rfl

/-- **The chart perturbation family of the capping space.** -/
def chartPert (t : Eucl 3) (p : CappingSpace) : CappingSpace :=
  cappingSpaceHomeoProj.symm (coordFam t (cappingSpaceHomeoProj p))

@[simp] lemma chartPert_zero (p : CappingSpace) : chartPert 0 p = p := by
  simp [chartPert]

@[simp] lemma cappingSpaceHomeoProj_chartPert (t : Eucl 3) (p : CappingSpace) :
    cappingSpaceHomeoProj (chartPert t p) = coordFam t (cappingSpaceHomeoProj p) := by
  simp [chartPert]

end

end Work.Drive
