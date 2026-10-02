import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Agree.s4Cohomology
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.Gysin
import Submission.Work.Cohomology.SphDefs
import Submission.Work.Cohomology.Degree
import Submission.Work.CharacteristicClasses.Powers
import Submission.Work.CharacteristicClasses.Degree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# SUBPROJECT TRANSGRESSION: the vocabulary

This module fixes the vocabulary of the subproject `Submission/Work/Transgression/`, whose target is

> the Euler class of a rank-`n` real bundle over `Sⁿ` given by a two-chart clutching
> `f : S^{n-1} → GL⁺(n)` is `± deg(ev ∘ f)` times the generator of `Hⁿ(Sⁿ;ℤ)`,

and, as the concrete instance the paper's core theorem consumes, `Work.Agree.EulerClutch`
(`Submission/Work/Agree/crux.lean`):

> for all `a b : ℤ` and every Thom class `T` of `clutchBundle a b`,
> `π^*(T.eulerClass) = ± (a + b) · tauD`  (`π = Work.TangentClasses.discProj`).

## Contents

* `GLend n`, `GLpos n` — the invertible, resp. orientation-preserving invertible, endomorphisms of
  `ℝⁿ` (the structure group of a rank-`n` bundle, resp. its orientation-preserving subgroup);
* `baseVec`, `evalVec`, `sphSelfDegree`, `clutchDegreeN` — the evaluation map `GL⁺(n) → S^{n-1}` at a
  fixed unit vector, and the **degree of a clutching function** `S^{n-1} → GL⁺(n)`;
* `baseVec4`, `evalGL4`, `evalAt`, `clutchDegree` — the same in the quaternionic model
  `S³ = Sp(1)`, `ℍ = ℝ⁴`, which is the model of the workspace's `CharacteristicClasses` chapter
  (where `Work.CharacteristicClasses.chern2` *is* the degree of a self-map of `S³`);
* `qTwistGL`, `evalGL4_qTwist`, `clutchDegree_qTwist` — the clutching function `q ↦ (v ↦ qᵃ v qᵇ)`
  of `clutchBundle a b`, the fundamental computation **`ev₁ ∘ (qTwist a b) = (q ↦ q^{a+b})`**, and the
  deliverable's item (2), **`deg (q ↦ qᵃ v qᵇ) = a + b`**.
-/

namespace Work.Transgression

open Work.TangentClasses

noncomputable section

/-- **`S⁴` is path connected** (it is homeomorphic to the standard sphere).  This instance is
provided by the chapter because the degree-`0` cohomology statement
`Work.Cohomology.exists_smul_oneH` needs it, and the `Agree` modules state it only for the theorems
that use it. -/
instance instPathConnectedSpaceS4 : PathConnectedSpace Work.Agree.S4 := by
  have hpc : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (h := by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num)
        (0 : EuclideanSpace ℝ (Fin 5)) (by norm_num))
  exact Work.Agree.homeoS4Sphere.symm.surjective.pathConnectedSpace
    Work.Agree.homeoS4Sphere.symm.continuous

/-! ## The structure group `GL(n)` and its orientation-preserving part -/

/-- The invertible continuous linear endomorphisms of `ℝⁿ` (`GL(n)`), as a topological space (the
subspace topology of the norm topology on continuous linear maps). -/
abbrev GLend (n : ℕ) : Type :=
  {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) // Function.Bijective A}

instance instCoeFunGLend (n : ℕ) :
    CoeFun (GLend n) (fun _ => EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
  ⟨fun A => fun x => A.1 x⟩

/-- The **orientation-preserving** invertible continuous linear endomorphisms of `ℝⁿ`: `GL⁺(n)`. -/
abbrev GLpos (n : ℕ) : Type :=
  {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) //
    Function.Bijective A ∧ 0 < A.det}

instance instCoeFunGLpos (n : ℕ) :
    CoeFun (GLpos n) (fun _ => EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
  ⟨fun A => fun x => A.1 x⟩

/-- `GL⁺(n) ⊆ GL(n)`: forgetting the positivity of the determinant. -/
def GLpos.toGL {n : ℕ} (A : GLpos n) : GLend n := ⟨A.1, A.2.1⟩

lemma continuous_GLpos_toGL (n : ℕ) : Continuous (GLpos.toGL (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val

/-- An invertible linear map is nonzero on nonzero vectors. -/
lemma GLend.map_ne_zero {n : ℕ} (A : GLend n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    A.1 x ≠ 0 := by
  intro h
  refine hx (A.2.1 ?_)
  rw [h, map_zero]

/-! ## The evaluation map `GL(n) → S^{n-1}` -/

/-- The base vector `e₀ ∈ ℝⁿ` at which clutching functions are evaluated. -/
def baseVec (n : ℕ) (hn : 1 ≤ n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single ⟨0, hn⟩ 1

lemma baseVec_ne_zero (n : ℕ) (hn : 1 ≤ n) : baseVec n hn ≠ 0 := by
  intro h
  have h1 : (baseVec n hn) ⟨0, hn⟩ = (0 : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩ := by rw [h]
  rw [baseVec, PiLp.single_apply, if_pos rfl] at h1
  simp at h1

/-- The normalisation `x ↦ ‖x‖⁻¹ • x` is continuous away from the origin. -/
lemma continuousOn_normalize (m : ℕ) :
    ContinuousOn (fun x : EuclideanSpace ℝ (Fin m) => (‖x‖)⁻¹ • x) {x | x ≠ 0} := by
  have hc : ContinuousOn (fun x : EuclideanSpace ℝ (Fin m) => (‖x‖)⁻¹) {x | x ≠ 0} :=
    continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr hx)
  exact hc.smul continuousOn_id

/-- The evaluation of an invertible linear map at the base vector, normalised to a unit vector:
`A ↦ ‖A e₀‖⁻¹ • A e₀ ∈ S^{n-1}`. -/
def evalVec (n : ℕ) (hn : 1 ≤ n) (A : GLend n) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨(‖A (baseVec n hn)‖)⁻¹ • A (baseVec n hn), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have hpos : 0 < ‖A (baseVec n hn)‖ :=
      norm_pos_iff.mpr (GLend.map_ne_zero A (baseVec_ne_zero n hn))
    rw [abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hpos)]⟩

@[simp] lemma evalVec_coe (n : ℕ) (hn : 1 ≤ n) (A : GLend n) :
    ((evalVec n hn A : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n))
      = (‖A (baseVec n hn)‖)⁻¹ • A (baseVec n hn) := rfl

/-- The evaluation map `evalVec n hn` is continuous. -/
lemma continuous_evalVec (n : ℕ) (hn : 1 ≤ n) :
    Continuous fun A : GLend n => (‖A (baseVec n hn)‖)⁻¹ • A (baseVec n hn) := by
  have hA : Continuous fun A : GLend n => A.1 (baseVec n hn) :=
    (continuous_subtype_val).clm_apply continuous_const
  have hnorm : Continuous fun A : GLend n => ‖A (baseVec n hn)‖ := by
    simpa using hA.norm
  exact (hnorm.inv₀ (fun A => ne_of_gt (norm_pos_iff.mpr
    (GLend.map_ne_zero A (baseVec_ne_zero n hn))))).smul hA

lemma continuous_evalVec' (n : ℕ) (hn : 1 ≤ n) : Continuous (evalVec n hn) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_evalVec n hn

/-! ## The degree of a self-map of a sphere -/

/-- The **degree of a self-map of `S^m`** (`S^m = Metric.sphere (0 : ℝ^{m+1}) 1`), in the
normalisation of `Work.Cohomology.sphereSelfDegree`: the integer `d` with `f_* [S^m] = d • [S^m]`
on top homology. -/
def sphSelfDegree (m : ℕ) (hm : 1 ≤ m)
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) : ℤ :=
  Work.Cohomology.sphereSelfDegree m hm (TopCat.ofHom g)

/-! ## The degree of a clutching function (general rank) -/

/-- **The degree of a clutching function** `f : S^{n-1} → GL⁺(n)`: the degree of the evaluation
`q ↦ ‖f q · e₀‖⁻¹ • (f q · e₀)`, a self-map of `S^{n-1}`.

By the transgression theorem (`Work.Transgression.TwoChartEuler`) this is the number that the Euler
class of the corresponding rank-`n` bundle computes, up to sign. -/
def clutchDegreeN (m : ℕ) (hm : 1 ≤ m)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, GLpos (m + 1))) : ℤ :=
  sphSelfDegree m hm ⟨fun x => evalVec (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    (GLpos.toGL (f x)),
    (continuous_evalVec' (m + 1) (Nat.succ_le_succ (Nat.zero_le m))).comp
      ((continuous_GLpos_toGL (m + 1)).comp f.continuous)⟩

/-! ## The quaternionic rank-4 model (`S³ = Sp(1)`, the fibre `ℍ ≅ ℝ⁴`) -/

/-- The base unit vector of the fibre `ℝ⁴ ≅ ℍ` at which the clutching functions of the chapter are
evaluated: the quaternion `1`. -/
def baseVec4 : EuclideanSpace ℝ (Fin 4) := Work.Agree.ofQ 1

lemma baseVec4_ne_zero : baseVec4 ≠ 0 := by
  intro h
  have h1 : Work.Agree.toQ baseVec4 = 0 := by rw [h]; exact map_zero _
  rw [baseVec4, Work.Agree.toQ_ofQ] at h1
  exact one_ne_zero h1

lemma norm_toQ (v : EuclideanSpace ℝ (Fin 4)) : ‖Work.Agree.toQ v‖ = ‖v‖ :=
  LinearIsometryEquiv.norm_map Quaternion.linearIsometryEquivTuple.symm v

lemma norm_ofQ (w : Quaternion ℝ) : ‖Work.Agree.ofQ w‖ = ‖w‖ :=
  LinearIsometryEquiv.norm_map Quaternion.linearIsometryEquivTuple w

/-- The evaluation of an invertible linear map of `ℝ⁴ ≅ ℍ` at the unit vector `1`, normalised:
`A ↦ ‖A 1‖⁻¹ • A 1`, read as a unit quaternion. -/
def evalGL4 (A : GLend 4) : Work.CharacteristicClasses.S3 :=
  ⟨Work.Agree.toQ ((‖A baseVec4‖)⁻¹ • A baseVec4), by
    rw [Metric.mem_sphere, dist_zero_right, norm_toQ, norm_smul, Real.norm_eq_abs]
    have hpos : 0 < ‖A baseVec4‖ := norm_pos_iff.mpr (GLend.map_ne_zero A baseVec4_ne_zero)
    rw [abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hpos)]⟩

@[simp] lemma evalGL4_coe (A : GLend 4) :
    ((evalGL4 A : Work.CharacteristicClasses.S3) : Quaternion ℝ)
      = Work.Agree.toQ ((‖A baseVec4‖)⁻¹ • A baseVec4) := rfl

lemma continuous_evalGL4 : Continuous (evalGL4 : GLend 4 → Work.CharacteristicClasses.S3) := by
  refine Continuous.subtype_mk ?_ _
  exact (Work.Agree.toQ.continuous.comp_continuousOn (continuousOn_normalize 4)).comp_continuous
    (by
      have hA : Continuous fun A : GLend 4 => A.1 baseVec4 :=
        (continuous_subtype_val).clm_apply continuous_const
      simpa using hA)
    (fun A => GLend.map_ne_zero A baseVec4_ne_zero)

/-- **The evaluation of a clutching function** `f : S³ → GL(4)` at the unit quaternion `1 ∈ ℍ`:
the self-map `q ↦ ‖f q 1‖⁻¹ • (f q 1)` of `S³`. -/
def evalAt (f : C(Work.CharacteristicClasses.S3, GLend 4)) :
    C(Work.CharacteristicClasses.S3, Work.CharacteristicClasses.S3) :=
  ⟨fun q => evalGL4 (f q), continuous_evalGL4.comp f.continuous⟩

@[simp] lemma evalAt_apply (f : C(Work.CharacteristicClasses.S3, GLend 4))
    (q : Work.CharacteristicClasses.S3) : evalAt f q = evalGL4 (f q) := rfl

/-- **The degree of a clutching function** `f : S³ → GL(4)`, in the workspace's quaternionic
model: the degree `chern2` of the evaluation `q ↦ f q · 1`. -/
def clutchDegree (f : C(Work.CharacteristicClasses.S3, GLend 4)) : ℤ :=
  Work.CharacteristicClasses.chern2 (evalAt f)

/-- The unit direction `uDir p ∈ S³` of a point of `S⁴`, as an element of the model `S³ = Sp(1)`
(`Work.Agree.uDir` is the same quaternion, coerced to `ℍ`). -/
def uDirS3 (p : S4) : Work.CharacteristicClasses.S3 :=
  ⟨Work.Agree.uDir p, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact Submission.Milnor.norm_coe (Submission.Milnor.unitDir (Work.Agree.coord0 p))⟩

@[simp] lemma uDirS3_coe (p : S4) :
    ((uDirS3 p : Work.CharacteristicClasses.S3) : Quaternion ℝ) = Work.Agree.uDir p := rfl

lemma coe_ne_zero_of_s3 {q : Work.CharacteristicClasses.S3} : (q : Quaternion ℝ) ≠ 0 := by
  intro h
  have hnorm : ‖(q : Quaternion ℝ)‖ = 1 := Submission.Milnor.norm_coe q
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-! ## The clutching function of `clutchBundle a b` -/

lemma bijective_qTwist (a b : ℤ) {q : Quaternion ℝ} (hq : q ≠ 0) :
    Function.Bijective (Work.Agree.qTwist a b q) := by
  have h1 := Work.Agree.qTwist_inv a b q hq
  have h2 := Work.Agree.qTwist_inv (-a) (-b) q hq
  rw [show (-(-a) : ℤ) = a from neg_neg a, show (-(-b) : ℤ) = b from neg_neg b] at h2
  refine ⟨fun x y hxy => ?_, fun y => ⟨Work.Agree.qTwist (-a) (-b) q y, ?_⟩⟩
  · have hx : Work.Agree.qTwist (-a) (-b) q (Work.Agree.qTwist a b q x) = x :=
      congrArg (fun f : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) => f x) h2
    have hy : Work.Agree.qTwist (-a) (-b) q (Work.Agree.qTwist a b q y) = y :=
      congrArg (fun f : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) => f y) h2
    rw [← hx, ← hy, hxy]
  · exact congrArg (fun f : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) => f y) h1

/-- **The clutching function of `clutchBundle a b`**, as a continuous map into `GL(4)`:
`q ↦ (v ↦ qᵃ v qᵇ)`. -/
def qTwistGL (a b : ℤ) : C(Work.CharacteristicClasses.S3, GLend 4) :=
  ⟨fun q => ⟨Work.Agree.qTwist a b (q : Quaternion ℝ), bijective_qTwist a b coe_ne_zero_of_s3⟩, by
    refine Continuous.subtype_mk ?_ _
    exact (Work.Agree.continuousOn_qTwist a b).comp_continuous continuous_subtype_val
      (fun q => coe_ne_zero_of_s3)⟩

@[simp] lemma qTwistGL_apply (a b : ℤ) (q : Work.CharacteristicClasses.S3) :
    (qTwistGL a b q).1 = Work.Agree.qTwist a b (q : Quaternion ℝ) := rfl

/-- **The evaluation of the `qTwist`-clutching is the power map**: evaluating `v ↦ qᵃ v qᵇ` at the
unit vector `1 ∈ ℍ` gives the unit quaternion `q^{a+b}`,

  `ev₁ ∘ (qTwist a b) = (q ↦ q^{a+b})`.

This is the `n = 4` instance of the general fact that the evaluation of the clutching at a unit
vector computes the sum of the exponents. -/
theorem evalGL4_qTwist (a b : ℤ) (q : Work.CharacteristicClasses.S3) :
    evalGL4 (qTwistGL a b q) = Work.CharacteristicClasses.s3ZPowCm (a + b) q := by
  apply Subtype.ext
  rw [evalGL4_coe, Work.CharacteristicClasses.s3ZPowCm_coe]
  have hq : (q : Quaternion ℝ) ≠ 0 := coe_ne_zero_of_s3
  have hval : qTwistGL a b q baseVec4
      = Work.Agree.ofQ ((q : Quaternion ℝ) ^ a * 1 * (q : Quaternion ℝ) ^ b) := by
    simp only [qTwistGL_apply]
    rw [Work.Agree.qTwist_apply, baseVec4, Work.Agree.toQ_ofQ]
  rw [hval, show (q : Quaternion ℝ) ^ a * 1 * (q : Quaternion ℝ) ^ b
      = (q : Quaternion ℝ) ^ (a + b) from by rw [mul_one, ← zpow_add₀ hq]]
  have hnorm : ‖(q : Quaternion ℝ) ^ (a + b)‖ = 1 := by
    rw [norm_zpow, Submission.Milnor.norm_coe q, one_zpow]
  rw [norm_ofQ, hnorm]
  simp

/-- **The degree of the clutching function of `clutchBundle a b` is `a + b`** — the deliverable's
item (2): `deg (q ↦ qᵃ · 1 · qᵇ) = deg (q ↦ q^{a+b}) = a + b`. -/
theorem clutchDegree_qTwist (a b : ℤ) : clutchDegree (qTwistGL a b) = a + b := by
  rw [clutchDegree]
  have h : evalAt (qTwistGL a b) = Work.CharacteristicClasses.s3ZPowCm (a + b) := by
    apply ContinuousMap.ext
    intro q
    exact evalGL4_qTwist a b q
  rw [h]
  exact Work.CharacteristicClasses.chern2_zPowCm (a + b)

end

end Work.Transgression
