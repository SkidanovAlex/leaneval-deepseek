import Mathlib
import Submission.Work.ThomBordism.Signs.coordChangeO_ogFlip_mul_flipMat
import Submission.Work.ThomBordism.Signs.coordEval_flipMat
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The tautological bundle is invariant under the orientation reversal

Let `X = G̃r_k(ℝ^{k+m})` be the oriented Grassmannian and `τ` the tautological oriented rank-`k`
bundle over it (`Work.ThomBordism.Grassmann.tautologicalBundle`, with orientation-corrected
transition functions `coordChangeO`).  The orientation reversal `ogFlip k m` right-multiplies
frames by `flipMat k = diag(-1,1,…,1)`; it preserves the underlying plane and reverses its
orientation (`_gtd/P1.lean`), and it is a continuous involution.

This module proves that the pullback of `τ` along `ogFlip` is isomorphic to `τ`:

`Work.ThomBordism.Grassmann.ogFlipComapIso`.

## The isomorphism

The transition functions of the pullback `X := ogFlip^* τ` are `c^X_{ij}(b) = c_{ij}(ogFlip b)`
(`coordChangeO` evaluated at the flipped point), while those of `τ` are `c_{ij}(b)`.  The two are
related by the flip matrix: `c_{ij}(ogFlip b) = F ∘ c_{ij}(b) ∘ F` where `F = matLin (flipMat k)`
(`coordChangeO_ogFlip_eq`).  The fibrewise maps

`flipHom b = c_{Q P}(b) ∘ F`,  `flipInv b = F ∘ c_{P Q}(b)`,  `P = chartCover b`,
`Q = chartCover (ogFlip b)`,

are mutually inverse (`c_{PQ} c_{QP} = c_{QQ} = 1` and `F² = 1`), and they make the induced maps of
total spaces continuous: in the charts `i₁` (source) and `i₂` (target) the chart matrix of
`flipHom` is

`c_{P i₂}(b) ∘ c_{QP}(b) ∘ F ∘ c_{i₁ Q}(ogFlip b) = c_{P i₂}(b) ∘ c_{QP}(b) ∘ c_{i₁ Q}(b) ∘ F
    = c_{i₁ i₂}(b) ∘ F`

(using `F ∘ c_{i₁Q}(ogFlip b) = c_{i₁Q}(b) ∘ F` and the cocycle identities), which is an explicit
continuous function of `b`; symmetrically for `flipInv`, whose chart matrix is `F ∘ c_{i₁ i₂}(b)`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## The flip matrix is invertible, and the flip preserves the charts -/

/-- The orientation-reversing matrix `diag(-1,1,…,1)` is invertible (it is an involution). -/
theorem flipMat_det_ne_zero (k : ℕ) : (flipMat k).det ≠ 0 :=
  isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_left_inverse (flipMat_transpose_mul k))

/-- **The orientation flip does not change the charts**: `ogFlip x` lies in `baseSet S` exactly
when `x` does (the determinant of the `S`-minor changes sign, hence stays nonzero). -/
theorem ogFlip_mem_baseSet_iff (S : ChartIdx k m) (x : OG k m) :
    ogFlip k m x ∈ baseSet S ↔ x ∈ baseSet S := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk, mem_baseSet_iff, mem_baseSet_iff, mem_chartSet, mem_chartSet,
    det_frameMatrix_soActFun]
  exact mul_ne_zero_iff_right (flipMat_det_ne_zero k)

/-- The preimage of a chart under the orientation flip is the chart itself. -/
theorem ogFlip_preimage_baseSet (S : ChartIdx k m) :
    ogFlip k m ⁻¹' baseSet S = baseSet S := by
  ext x
  exact ogFlip_mem_baseSet_iff S x

/-- The chart of the flipped point contains the point. -/
theorem mem_baseSet_chartCover_ogFlip (b : OG k m) :
    b ∈ baseSet (chartCover (ogFlip k m b)) :=
  (ogFlip_mem_baseSet_iff _ b).mp (mem_baseSet_chartCover (ogFlip k m b))

/-! ## The transition functions in `ContinuousLinearMap` form -/

/-- The cocycle of the corrected transition functions, as an identity of continuous linear maps. -/
theorem coordChangeO_linear_comp (i j l : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet i ∩ baseSet j ∩ baseSet l) :
    (coordChangeO j l x).comp (coordChangeO i j x) = coordChangeO i l x := by
  exact VectorBundleCore.coordChange_linear_comp (tautologicalBundle k m) i j l x hx

/-- The corrected transition function from a chart to itself is the identity, as a continuous
linear map. -/
theorem coordChangeO_self_clm (i : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet i) :
    coordChangeO i i x = 1 :=
  ContinuousLinearMap.ext fun v => coordChangeO_self i x hx v

/-- The flip matrix as a continuous linear endomorphism of `Amb k` is an involution. -/
theorem matLin_flipMat_comp_self (k : ℕ) :
    (matLin (flipMat k)).comp (matLin (flipMat k)) = 1 := by
  rw [← matLin_mul, flipMat_mul_self, matLin_one]

/-- The flip matrix as a continuous linear endomorphism of `Amb k` is an involution, pointwise. -/
theorem matLin_flipMat_apply_self (k : ℕ) (v : Amb k) :
    matLin (flipMat k) (matLin (flipMat k) v) = v := by
  have hh : ((matLin (flipMat k)).comp (matLin (flipMat k))) v = v := by
    rw [matLin_flipMat_comp_self k]
    rfl
  rwa [ContinuousLinearMap.comp_apply] at hh

/-- **`coordChangeO` at the flipped point is the conjugate of `coordChangeO` by the flip matrix.** -/
theorem coordChangeO_ogFlip_eq (S T : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet S ∩ baseSet T) :
    coordChangeO S T (ogFlip k m x)
      = (matLin (flipMat k)).comp ((coordChangeO S T x).comp (matLin (flipMat k))) := by
  have h := Work.ThomBordism.Signs.coordChangeO_ogFlip_mul_flipMat S T hx
  have hF := matLin_flipMat_comp_self k
  calc coordChangeO S T (ogFlip k m x)
      = (coordChangeO S T (ogFlip k m x)).comp
          ((matLin (flipMat k)).comp (matLin (flipMat k))) := by
          rw [hF]
          ext v; rfl
    _ = ((coordChangeO S T (ogFlip k m x)).comp (matLin (flipMat k))).comp
          (matLin (flipMat k)) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = ((matLin (flipMat k)).comp (coordChangeO S T x)).comp (matLin (flipMat k)) := by
          rw [h]
    _ = (matLin (flipMat k)).comp ((coordChangeO S T x).comp (matLin (flipMat k))) :=
          ContinuousLinearMap.comp_assoc _ _ _

/-! ## The fibrewise linear maps realising the isomorphism -/

/-- The fibre map of `ogFlip^*τ → τ` in the charts `chartCover (ogFlip b)` (source) and
`chartCover b` (target): the transition function `c_{QP}(b)` followed by the flip `F`. -/
def flipHom (k m : ℕ) (b : OG k m) : Amb k →L[ℝ] Amb k :=
  (coordChangeO (chartCover (ogFlip k m b)) (chartCover b) b).comp (matLin (flipMat k))

/-- The inverse of `flipHom`: the flip followed by `c_{PQ}(b)`. -/
def flipInv (k m : ℕ) (b : OG k m) : Amb k →L[ℝ] Amb k :=
  (matLin (flipMat k)).comp (coordChangeO (chartCover b) (chartCover (ogFlip k m b)) b)

/-- The two fibrewise maps are mutually inverse: `flipInv b (flipHom b x) = x`. -/
theorem flipInv_apply_flipHom (k m : ℕ) (b : OG k m) (x : Amb k) :
    flipInv k m b (flipHom k m b x) = x := by
  have hbP : b ∈ baseSet (chartCover b) := mem_baseSet_chartCover b
  have hbQ : b ∈ baseSet (chartCover (ogFlip k m b)) := mem_baseSet_chartCover_ogFlip b
  have hcyc : ∀ w : Amb k,
      coordChangeO (chartCover b) (chartCover (ogFlip k m b)) b
        (coordChangeO (chartCover (ogFlip k m b)) (chartCover b) b w) = w := by
    intro w
    have h := congrArg (fun (f : Amb k →L[ℝ] Amb k) => f w)
      (coordChangeO_linear_comp (chartCover (ogFlip k m b)) (chartCover b)
        (chartCover (ogFlip k m b)) b ⟨⟨hbQ, hbP⟩, hbQ⟩)
    rw [ContinuousLinearMap.comp_apply] at h
    rw [h, coordChangeO_self _ b hbQ]
  simp only [flipInv, flipHom, ContinuousLinearMap.comp_apply]
  rw [hcyc, matLin_flipMat_apply_self]

/-- The two fibrewise maps are mutually inverse: `flipHom b (flipInv b y) = y`. -/
theorem flipHom_apply_flipInv (k m : ℕ) (b : OG k m) (y : Amb k) :
    flipHom k m b (flipInv k m b y) = y := by
  have hbP : b ∈ baseSet (chartCover b) := mem_baseSet_chartCover b
  have hbQ : b ∈ baseSet (chartCover (ogFlip k m b)) := mem_baseSet_chartCover_ogFlip b
  have hcyc : ∀ w : Amb k,
      coordChangeO (chartCover (ogFlip k m b)) (chartCover b) b
        (coordChangeO (chartCover b) (chartCover (ogFlip k m b)) b w) = w := by
    intro w
    have h := congrArg (fun (f : Amb k →L[ℝ] Amb k) => f w)
      (coordChangeO_linear_comp (chartCover b) (chartCover (ogFlip k m b))
        (chartCover b) b ⟨⟨hbP, hbQ⟩, hbP⟩)
    rw [ContinuousLinearMap.comp_apply] at h
    rw [h, coordChangeO_self _ b hbP]
  simp only [flipHom, flipInv, ContinuousLinearMap.comp_apply]
  rw [matLin_flipMat_apply_self k (coordChangeO (chartCover b) (chartCover (ogFlip k m b)) b y)]
  rw [hcyc]

/-! ## The chart expressions of the two maps -/

/-- **The chart expression of `flipHom`**: in the source chart `i₁` and target chart `i₂` its
matrix is `c_{i₁ i₂}(b) ∘ F`, an explicit continuous function of `b`. -/
theorem flipHom_chart_expr (i₁ i₂ : ChartIdx k m) (b : OG k m)
    (h₁ : ogFlip k m b ∈ baseSet i₁) (h₂ : b ∈ baseSet i₂) :
    (coordChangeO (chartCover b) i₂ b).comp
        ((flipHom k m b).comp (coordChangeO i₁ (chartCover (ogFlip k m b)) (ogFlip k m b)))
      = (coordChangeO i₁ i₂ b).comp (matLin (flipMat k)) := by
  have hbP : b ∈ baseSet (chartCover b) := mem_baseSet_chartCover b
  have hbQ : b ∈ baseSet (chartCover (ogFlip k m b)) := mem_baseSet_chartCover_ogFlip b
  have hb1 : b ∈ baseSet i₁ := (ogFlip_mem_baseSet_iff i₁ b).mp h₁
  have hA := coordChangeO_ogFlip_eq i₁ (chartCover (ogFlip k m b)) b ⟨hb1, hbQ⟩
  have hB : (coordChangeO (chartCover b) i₂ b).comp
      (coordChangeO (chartCover (ogFlip k m b)) (chartCover b) b)
      = coordChangeO (chartCover (ogFlip k m b)) i₂ b :=
    coordChangeO_linear_comp (chartCover (ogFlip k m b)) (chartCover b) i₂ b
      ⟨⟨hbQ, hbP⟩, h₂⟩
  have hC : (coordChangeO (chartCover (ogFlip k m b)) i₂ b).comp
      (coordChangeO i₁ (chartCover (ogFlip k m b)) b)
      = coordChangeO i₁ i₂ b :=
    coordChangeO_linear_comp i₁ (chartCover (ogFlip k m b)) i₂ b ⟨⟨hb1, hbQ⟩, h₂⟩
  have hstep : ∀ v : Amb k,
      matLin (flipMat k) (coordChangeO i₁ (chartCover (ogFlip k m b)) (ogFlip k m b) v)
        = coordChangeO i₁ (chartCover (ogFlip k m b)) b (matLin (flipMat k) v) := by
    intro v
    rw [hA]
    simp only [ContinuousLinearMap.comp_apply, matLin_flipMat_apply_self]
  have hB' : ∀ w : Amb k, (coordChangeO (chartCover b) i₂ b)
      (coordChangeO (chartCover (ogFlip k m b)) (chartCover b) b w)
      = coordChangeO (chartCover (ogFlip k m b)) i₂ b w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, hB]
  have hC' : ∀ w : Amb k, (coordChangeO (chartCover (ogFlip k m b)) i₂ b)
      (coordChangeO i₁ (chartCover (ogFlip k m b)) b w) = coordChangeO i₁ i₂ b w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, hC]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [flipHom, ContinuousLinearMap.comp_apply]
  rw [hstep, hB', hC']

/-- **The chart expression of `flipInv`**: in the source chart `i₁` (of `τ`) and target chart `i₂`
(of `ogFlip^*τ`) its matrix is `F ∘ c_{i₁ i₂}(b)`, again an explicit continuous function. -/
theorem flipInv_chart_expr (i₁ i₂ : ChartIdx k m) (b : OG k m)
    (h₁ : b ∈ baseSet i₁) (h₂ : ogFlip k m b ∈ baseSet i₂) :
    (coordChangeO (chartCover (ogFlip k m b)) i₂ (ogFlip k m b)).comp
        ((flipInv k m b).comp (coordChangeO i₁ (chartCover b) b))
      = (matLin (flipMat k)).comp (coordChangeO i₁ i₂ b) := by
  have hbP : b ∈ baseSet (chartCover b) := mem_baseSet_chartCover b
  have hbQ : b ∈ baseSet (chartCover (ogFlip k m b)) := mem_baseSet_chartCover_ogFlip b
  have hb2 : b ∈ baseSet i₂ := (ogFlip_mem_baseSet_iff i₂ b).mp h₂
  have hA := coordChangeO_ogFlip_eq (chartCover (ogFlip k m b)) i₂ b ⟨hbQ, hb2⟩
  have hB : (coordChangeO (chartCover (ogFlip k m b)) i₂ b).comp
      (coordChangeO (chartCover b) (chartCover (ogFlip k m b)) b)
      = coordChangeO (chartCover b) i₂ b :=
    coordChangeO_linear_comp (chartCover b) (chartCover (ogFlip k m b)) i₂ b
      ⟨⟨hbP, hbQ⟩, hb2⟩
  have hC : (coordChangeO (chartCover b) i₂ b).comp (coordChangeO i₁ (chartCover b) b)
      = coordChangeO i₁ i₂ b :=
    coordChangeO_linear_comp i₁ (chartCover b) i₂ b ⟨⟨h₁, hbP⟩, hb2⟩
  have hstep : ∀ v : Amb k,
      coordChangeO (chartCover (ogFlip k m b)) i₂ (ogFlip k m b) (matLin (flipMat k) v)
        = matLin (flipMat k) (coordChangeO (chartCover (ogFlip k m b)) i₂ b v) := by
    intro v
    rw [hA]
    simp only [ContinuousLinearMap.comp_apply, matLin_flipMat_apply_self]
  have hB' : ∀ w : Amb k, (coordChangeO (chartCover (ogFlip k m b)) i₂ b)
      (coordChangeO (chartCover b) (chartCover (ogFlip k m b)) b w)
      = coordChangeO (chartCover b) i₂ b w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, hB]
  have hC' : ∀ w : Amb k, (coordChangeO (chartCover b) i₂ b)
      (coordChangeO i₁ (chartCover b) b w) = coordChangeO i₁ i₂ b w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, hC]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [flipInv, ContinuousLinearMap.comp_apply]
  rw [hstep, hB', hC']

/-! ## Continuity of the induced maps of total spaces -/

theorem continuous_flipHom_totalMap (k m : ℕ) :
    Continuous (fun p : (Work.Thom.bundleComap (tautologicalBundle k m) (ogFlipCM k m)).TotalSpace =>
      (⟨p.proj, flipHom k m p.proj p.snd⟩ : (tautologicalBundle k m).TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm_gen _ _ (ContinuousMap.id (OG k m))
    (flipHom k m) ?_
  intro i₁ i₂
  rw [show (⇑(ContinuousMap.id (OG k m)) : OG k m → OG k m) = id from rfl, Set.preimage_id]
  have hbase : (Work.Thom.bundleComap (tautologicalBundle k m) (ogFlipCM k m)).baseSet i₁
      = (tautologicalBundle k m).baseSet i₁ := ogFlip_preimage_baseSet i₁
  rw [hbase]
  refine ContinuousOn.congr (f := fun b : OG k m =>
    ((tautologicalBundle k m).coordChange i₁ i₂ b).comp (matLin (flipMat k))) ?_ ?_
  · exact ((tautologicalBundle k m).continuousOn_coordChange i₁ i₂).clm_comp continuousOn_const
  · intro b hb
    exact flipHom_chart_expr i₁ i₂ b ((ogFlip_mem_baseSet_iff i₁ b).mpr hb.1) hb.2

theorem continuous_flipInv_totalMap (k m : ℕ) :
    Continuous (fun p : (tautologicalBundle k m).TotalSpace =>
      (⟨p.proj, flipInv k m p.proj p.snd⟩ :
        (Work.Thom.bundleComap (tautologicalBundle k m) (ogFlipCM k m)).TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm_gen _ _ (ContinuousMap.id (OG k m))
    (flipInv k m) ?_
  intro i₁ i₂
  rw [show (⇑(ContinuousMap.id (OG k m)) : OG k m → OG k m) = id from rfl, Set.preimage_id]
  have hbase : (Work.Thom.bundleComap (tautologicalBundle k m) (ogFlipCM k m)).baseSet i₂
      = (tautologicalBundle k m).baseSet i₂ := ogFlip_preimage_baseSet i₂
  rw [hbase]
  refine ContinuousOn.congr (f := fun b : OG k m =>
    (matLin (flipMat k)).comp ((tautologicalBundle k m).coordChange i₁ i₂ b)) ?_ ?_
  · exact continuousOn_const.clm_comp ((tautologicalBundle k m).continuousOn_coordChange i₁ i₂)
  · intro b hb
    exact flipInv_chart_expr i₁ i₂ b hb.1 ((ogFlip_mem_baseSet_iff i₂ b).mpr hb.2)

/-! ## The bundle isomorphism -/

theorem ogFlipComapIso (k m : ℕ) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k m)
        (Work.ThomBordism.Grassmann.ogFlipCM k m))
      (Work.ThomBordism.Grassmann.tautologicalBundle k m)) := by
  refine ⟨{ hom := fun b => (flipHom k m b).toLinearMap
            inv := fun b => (flipInv k m b).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    exact flipInv_apply_flipHom k m b x
  · intro b y
    exact flipHom_apply_flipInv k m b y
  · exact continuous_flipHom_totalMap k m
  · exact continuous_flipInv_totalMap k m

end

end Work.ThomBordism.Grassmann
