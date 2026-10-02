import Mathlib
import Submission.Work.ThomBordism.Signs.coordChangeO_ogFlip_mul_flipMat
import Submission.Work.ThomBordism.Signs.coordEval_flipMat
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.IncidenceVector
import Submission.Work.Thom.coreMorphism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The orientation-reversing automorphism of the tautological bundle

`Work.ThomBordism.Grassmann.ogFlip k m` reverses the orientation of a plane of
`G̃r_k(ℝ^{k+m})` without changing the plane itself (`projOfPlane_ogFlip`).  The present module
lifts this involution of the base to a map of the total space of the tautological bundle: the map
`flipFun k m` keeps the vector of the plane (`evalVec (flipFun p) = evalVec p`, `evalVec_flipFun`)
and sends the fibre over `P` to the fibre over `ogFlip k m P`.

The construction is the one forced by the geometry: a point of the total space is a pair
(plane, vector of the plane), and the flip keeps the vector.  In the chart `S` of the plane the map
reads `(P, v) ↦ (ogFlip P, flipMat k · v)`; the compatibility of these local formulas over overlaps
is *exactly* the equivariance statement `coordChangeO_ogFlip_mul_flipMat` proved in the companion
module.  We formalise the map by giving the fibre coordinate in the chart `indexAt P` of the
*source* point, and get continuity from `Work.Thom.continuous_totalSpaceMap_clm`.

The statement `flipMap` is the exact form needed by the Thom-class comparison
(`Work.ThomBordism.gtdThomClass_flipPairs`).
-/

namespace Work.ThomBordism.Signs

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The flip does not change the charts -/

/-- The orientation-reversing matrix `flipMat k` is invertible. -/
theorem flipMat_det_ne_zero (k : ℕ) : (flipMat k).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (flipMat_mul_self k)
  rw [Matrix.det_mul, Matrix.det_one, h, mul_zero] at h1
  exact one_ne_zero h1.symm

/-- **The chart membership of a plane is orientation-blind**: the underlying (unoriented) plane of
`ogFlip k m x` is that of `x`, so `x` lies in the chart `U_S` exactly when `ogFlip k m x` does. -/
theorem mem_baseSet_ogFlip (S : ChartIdx k m) (x : OG k m) :
    ogFlip k m x ∈ baseSet S ↔ x ∈ baseSet S := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk, mem_baseSet_iff, mem_baseSet_iff, mem_chartSet, mem_chartSet,
    frameMatrix_soActFun, Matrix.det_mul]
  exact ⟨fun h hf => h (by rw [hf, zero_mul]),
    fun h => mul_ne_zero h (flipMat_det_ne_zero k)⟩

/-! ## Bridge lemmas: the gluing data of the tautological bundle in the coordinate language -/

/-- The transition function of the tautological bundle *is* `coordChangeO` (the definitional
unfolding of its gluing data). -/
@[simp] theorem taut_coordChange (k m : ℕ) (i j : ChartIdx k m) (x : OG k m) :
    (tautologicalBundle k m).coordChange i j x = coordChangeO i j x := rfl

/-- **The fibre coordinate of the tautological bundle in a chart**, as a transition function:
Mathlib's `VectorBundleCore.localTriv_apply` with the gluing data unfolded. -/
theorem localTriv_snd_eq (S : ChartIdx k m) (p : (tautologicalBundle k m).TotalSpace) :
    (show Amb k from ((tautologicalBundle k m).localTriv S p).2)
      = coordChangeO ((tautologicalBundle k m).indexAt p.1) S p.1 p.2 :=
  congrArg (fun q : OG k m × Amb k => q.2)
    (VectorBundleCore.localTriv_apply (tautologicalBundle k m) (i := S) p)

/-- The transition function of a chart with itself is the identity. -/
theorem coordChangeO_self' (S : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S) (v : Amb k) :
    coordChangeO S S x v = v :=
  VectorBundleCore.coordChange_self (tautologicalBundle k m) S x hx v

/-- The cocycle condition for the transition functions of the tautological bundle, as an identity
of continuous linear maps. -/
theorem coordChangeO_linear_comp (i j l : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet i ∩ baseSet j ∩ baseSet l) :
    (coordChangeO j l x).comp (coordChangeO i j x) = coordChangeO i l x :=
  VectorBundleCore.coordChange_linear_comp (tautologicalBundle k m) i j l x hx

/-! ## Conjugation by the flip matrix -/

/-- The flip matrix conjugates the sign gauge to itself: `flipMat * D * flipMat = D` (both are
diagonal with entries `±1` and the entries of `flipMat` square to `1`). -/
theorem flipMat_orientMat_flipMat (S : ChartIdx k m) (x : OG k m) :
    flipMat k * orientMat S x * flipMat k = orientMat S x := by
  rw [CoordFlip.orientMat_diagonal, flipMat, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_diagonal_iff]
  intro i
  by_cases hi : (i : ℕ) = 0 <;> simp only [hi, if_true, if_false] <;> ring

/-- **The key algebraic identity**: the gauge at the flipped point multiplied by the flip matrix is
the gauge at the point. -/
theorem orientMat_ogFlip_mul_flipMat (S : ChartIdx k m) (x : OG k m) :
    orientMat S (ogFlip k m x) * flipMat k = orientMat S x := by
  rw [CoordFlip.orientMat_ogFlip, flipMat_orientMat_flipMat]

/-! ## The frame obtained by the orientation-reversing change of basis -/

/-- The frame obtained from `f` by right-multiplication with the orientation-reversing matrix
`flipMat k`; it represents the same plane as `f`, with the opposite orientation. -/
def flipFrame (k m : ℕ) (f : Stiefel k m) : Stiefel k m :=
  ⟨soActFun (flipMat k) f.1, orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩

/-- The orientation flip sends the plane of `f` to the plane of `flipFrame f`. -/
theorem ogFlip_mk' (k m : ℕ) (f : Stiefel k m) :
    ogFlip k m (Quotient.mk'' f) = Quotient.mk'' (flipFrame k m f) := ogFlip_mk f

/-- The chart evaluation is invariant under the orientation-reversing change of frame: it only
sees the *plane*, and the flip does not change the plane. -/
theorem coordEval_flipFrame (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S)
    (v : Amb k) : coordEval S (flipFrame k m f) v = coordEval S f v :=
  coordEval_flipMat S f hf v

/-! ## The map of total spaces -/

/-- **The fibre coordinate of the flip**, in the chart `indexAt P` of the source point: it is the
`indexAt (ogFlip P)`-coordinate of the vector belonging to the same plane point as the
`indexAt P`-coordinate `v`. -/
noncomputable def flipFibre (k m : ℕ) (x : OG k m) : Amb k →L[ℝ] Amb k :=
  (coordChangeO ((tautologicalBundle k m).indexAt x)
    ((tautologicalBundle k m).indexAt (ogFlip k m x)) (ogFlip k m x)).comp (matLin (flipMat k))

/-- **The orientation flip of the total space of the tautological bundle**: the plane is
orientation-reversed, the vector of the plane is kept. -/
noncomputable def flipFun (k m : ℕ) :
    (tautologicalBundle k m).TotalSpace → (tautologicalBundle k m).TotalSpace :=
  fun p => ⟨ogFlip k m p.1, flipFibre k m p.1 p.2⟩

theorem flipFun_apply (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    flipFun k m p = ⟨ogFlip k m p.1, flipFibre k m p.1 p.2⟩ := rfl

/-- **Continuity of the flip.**  On the chart of the source point the flip is
`(P, v) ↦ (ogFlip P, flipMat k · v)`; the compatibility of these local formulas over overlaps is
the equivariance `coordChangeO_ogFlip_mul_flipMat`, which is what makes the chart expression
`coordChangeO (indexAt (ogFlip b)) i₂ (ogFlip b) ∘ flipMat ∘ coordChangeO i₁ (indexAt b)` reduce to
`flipMat ∘ coordChangeO i₁ i₂`. -/
theorem continuous_flipFun (k m : ℕ) : Continuous (flipFun k m) := by
  have hT : ∀ (i₁ i₂ : ChartIdx k m), ContinuousOn (fun b : OG k m =>
      ((tautologicalBundle k m).coordChange
        ((tautologicalBundle k m).indexAt (ogFlip k m b)) i₂ (ogFlip k m b)).comp
        ((flipFibre k m b).comp
          ((tautologicalBundle k m).coordChange i₁ ((tautologicalBundle k m).indexAt b) b)))
      ((tautologicalBundle k m).baseSet i₁ ∩ ogFlip k m ⁻¹' (tautologicalBundle k m).baseSet i₂) := by
    intro i₁ i₂
    have hcont : ContinuousOn (fun b : OG k m =>
        (matLin (flipMat k)).comp (coordChangeO i₁ i₂ b)) (baseSet i₁ ∩ baseSet i₂) :=
      continuousOn_const.clm_comp (continuousOn_coordChangeO i₁ i₂)
    have hpoint : ∀ b ∈ (tautologicalBundle k m).baseSet i₁
        ∩ ogFlip k m ⁻¹' (tautologicalBundle k m).baseSet i₂,
        (((tautologicalBundle k m).coordChange
          ((tautologicalBundle k m).indexAt (ogFlip k m b)) i₂ (ogFlip k m b)).comp
          ((flipFibre k m b).comp
            ((tautologicalBundle k m).coordChange i₁ ((tautologicalBundle k m).indexAt b) b)))
        = (matLin (flipMat k)).comp ((tautologicalBundle k m).coordChange i₁ i₂ b) := by
      intro b hb
      simp only [taut_coordChange]
      obtain ⟨hb₁, hb₂'⟩ := hb
      have hb₂ : b ∈ baseSet i₂ := (mem_baseSet_ogFlip i₂ b).mp hb₂'
      have hb₀ : b ∈ baseSet ((tautologicalBundle k m).indexAt b) :=
        (tautologicalBundle k m).mem_baseSet_at b
      have hy'T' : ogFlip k m b ∈ baseSet ((tautologicalBundle k m).indexAt (ogFlip k m b)) :=
        (tautologicalBundle k m).mem_baseSet_at _
      have hy'S₀ : ogFlip k m b ∈ baseSet ((tautologicalBundle k m).indexAt b) :=
        (mem_baseSet_ogFlip ((tautologicalBundle k m).indexAt b) b).mpr hb₀
      have hA : (coordChangeO ((tautologicalBundle k m).indexAt (ogFlip k m b)) i₂
              (ogFlip k m b)).comp
            (coordChangeO ((tautologicalBundle k m).indexAt b)
              ((tautologicalBundle k m).indexAt (ogFlip k m b)) (ogFlip k m b))
          = coordChangeO ((tautologicalBundle k m).indexAt b) i₂ (ogFlip k m b) :=
        VectorBundleCore.coordChange_linear_comp (tautologicalBundle k m)
          ((tautologicalBundle k m).indexAt b) ((tautologicalBundle k m).indexAt (ogFlip k m b)) i₂
          (ogFlip k m b) ⟨⟨hy'S₀, hy'T'⟩, hb₂'⟩
      have hB : (coordChangeO ((tautologicalBundle k m).indexAt b) i₂ (ogFlip k m b)).comp
            (matLin (flipMat k))
          = (matLin (flipMat k)).comp (coordChangeO ((tautologicalBundle k m).indexAt b) i₂ b) :=
        coordChangeO_ogFlip_mul_flipMat ((tautologicalBundle k m).indexAt b) i₂ ⟨hb₀, hb₂⟩
      have hC : (coordChangeO ((tautologicalBundle k m).indexAt b) i₂ b).comp
            (coordChangeO i₁ ((tautologicalBundle k m).indexAt b) b)
          = coordChangeO i₁ i₂ b :=
        VectorBundleCore.coordChange_linear_comp (tautologicalBundle k m) i₁
          ((tautologicalBundle k m).indexAt b) i₂ b ⟨⟨hb₁, hb₀⟩, hb₂⟩
      rw [flipFibre, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hA, hB,
        ContinuousLinearMap.comp_assoc, hC]
    exact (hcont.mono (fun b hb => ⟨hb.1, (mem_baseSet_ogFlip i₂ b).mp hb.2⟩)).congr hpoint
  exact (Work.Thom.continuous_totalSpaceMap_clm (tautologicalBundle k m) (tautologicalBundle k m)
    (ogFlipCM k m) (flipFibre k m) hT).congr (fun p => rfl)

/-! ## The evaluation of the flip -/

/-- **The flip keeps the vector of the plane.**  Both sides are read in the chart of the flipped
point; the equality of the two fibre coordinates is `orientMat_ogFlip_mul_flipMat` (the gauge
correction) together with the equivariance `coordChangeO_ogFlip_mul_flipMat` of the transition
functions. -/
theorem evalVec_flipFun (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    evalVec (flipFun k m p) = evalVec p := by
  obtain ⟨f, hf0⟩ := Quotient.exists_rep p.1
  have hf : (Quotient.mk'' f : OG k m) = p.1 := hf0
  -- the two charts and the frames
  have hS0 : p.1 ∈ baseSet ((tautologicalBundle k m).indexAt p.1) :=
    (tautologicalBundle k m).mem_baseSet_at p.1
  have hyT : ogFlip k m p.1 ∈ baseSet ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) :=
    (tautologicalBundle k m).mem_baseSet_at _
  have hxT : p.1 ∈ baseSet ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) :=
    (mem_baseSet_ogFlip _ p.1).mp hyT
  have hfT : f ∈ chartSet ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) :=
    (mem_baseSet_iff _ f).mp (hf ▸ hxT)
  have hog : ogFlip k m p.1 = Quotient.mk'' (flipFrame k m f) :=
    (congrArg (ogFlip k m) hf).symm.trans (ogFlip_mk' k m f)
  have hgT : flipFrame k m f ∈ chartSet ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) :=
    (mem_baseSet_iff _ _).mp (hog ▸ hyT)
  -- the value of `evalVec` at the flipped point, read in the chart of the flipped point
  have key₁ : evalVec (flipFun k m p) =
      coordEval ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) f
        (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (ogFlip k m p.1))
          (flipFibre k m p.1 p.2)) := by
    have hl : (show Amb k from ((tautologicalBundle k m).localTriv
        ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (flipFun k m p)).2)
        = flipFibre k m p.1 p.2 :=
      (localTriv_snd_eq ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (flipFun k m p)).trans
        (coordChangeO_self' _ (ogFlip k m p.1) hyT (flipFibre k m p.1 p.2))
    calc evalVec (flipFun k m p)
        = evalChartO ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
            ⟨ogFlip k m p.1, hyT⟩
            (show Amb k from ((tautologicalBundle k m).localTriv
              ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (flipFun k m p)).2) :=
          evalVec_apply_chart (flipFun k m p) _ hyT
      _ = evalChart ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
            (⟨ogFlip k m p.1, hyT⟩,
              matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
                (ogFlip k m p.1))
                (show Amb k from ((tautologicalBundle k m).localTriv
                  ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (flipFun k m p)).2)) := rfl
      _ = evalChart ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
            (⟨ogFlip k m p.1, hyT⟩,
              matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
                (ogFlip k m p.1)) (flipFibre k m p.1 p.2)) :=
          congrArg (fun w => evalChart ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
            (⟨ogFlip k m p.1, hyT⟩,
              matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
                (ogFlip k m p.1)) w)) hl
      _ = coordEval ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (flipFrame k m f)
            (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
              (ogFlip k m p.1)) (flipFibre k m p.1 p.2)) :=
          evalChart_spec _ ⟨ogFlip k m p.1, hyT⟩ (flipFrame k m f) hgT hog _
      _ = coordEval ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) f
            (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
              (ogFlip k m p.1)) (flipFibre k m p.1 p.2)) :=
          coordEval_flipFrame _ f hfT _
  -- the value of `evalVec` at the point, read in the same chart
  have key₂ : evalVec p =
      coordEval ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) f
        (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1)
          (coordChangeO ((tautologicalBundle k m).indexAt p.1)
            ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1 p.2)) := by
    have hl : (show Amb k from ((tautologicalBundle k m).localTriv
        ((tautologicalBundle k m).indexAt p.1) p).2) = p.2 :=
      (localTriv_snd_eq ((tautologicalBundle k m).indexAt p.1) p).trans
        (coordChangeO_self' _ p.1 hS0 p.2)
    calc evalVec p
        = evalChartO ((tautologicalBundle k m).indexAt p.1) ⟨p.1, hS0⟩
            (show Amb k from ((tautologicalBundle k m).localTriv
              ((tautologicalBundle k m).indexAt p.1) p).2) :=
          evalVec_apply_chart p _ hS0
      _ = evalChartO ((tautologicalBundle k m).indexAt p.1) ⟨p.1, hS0⟩ p.2 :=
          congrArg (fun w => evalChartO ((tautologicalBundle k m).indexAt p.1) ⟨p.1, hS0⟩ w) hl
      _ = evalChartO ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) ⟨p.1, hxT⟩
            (coordChangeO ((tautologicalBundle k m).indexAt p.1)
              ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1 p.2) :=
          evalChartO_glue _ _ p.1 ⟨hS0, hxT⟩ p.2
      _ = evalChart ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
            (⟨p.1, hxT⟩,
              matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1)
                (coordChangeO ((tautologicalBundle k m).indexAt p.1)
                  ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1 p.2)) := rfl
      _ = coordEval ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) f
            (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1)
              (coordChangeO ((tautologicalBundle k m).indexAt p.1)
                ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1 p.2)) :=
          evalChart_spec _ ⟨p.1, hxT⟩ f hfT hf.symm _
  -- the two arguments of the chart evaluation agree
  have hE1 : (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
        (ogFlip k m p.1))).comp (matLin (flipMat k))
      = matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1) := by
    rw [← matLin_mul, orientMat_ogFlip_mul_flipMat]
  have hE2 : (coordChangeO ((tautologicalBundle k m).indexAt p.1)
        ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (ogFlip k m p.1)).comp
        (matLin (flipMat k))
      = (matLin (flipMat k)).comp (coordChangeO ((tautologicalBundle k m).indexAt p.1)
          ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1) :=
    coordChangeO_ogFlip_mul_flipMat _ _ ⟨hS0, hxT⟩
  have hC : matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
        (ogFlip k m p.1)) (flipFibre k m p.1 p.2)
      = matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1)
        (coordChangeO ((tautologicalBundle k m).indexAt p.1)
          ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1 p.2) := by
    have hCLM : (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
          (ogFlip k m p.1))).comp (flipFibre k m p.1)
        = (matLin (orientMat ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1)).comp
          (coordChangeO ((tautologicalBundle k m).indexAt p.1)
            ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) p.1) := by
      rw [flipFibre, hE2, ← ContinuousLinearMap.comp_assoc, hE1]
    exact congrArg (fun F : Amb k →L[ℝ] Amb k => F p.2) hCLM
  exact key₁.trans
    ((congrArg (coordEval ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) f) hC).trans
      key₂.symm)

/-- **The orientation-reversing automorphism of the tautological bundle.**  There is a continuous
map of the total space of the tautological oriented bundle over `G̃r_k(ℝ^{k+m})` which reverses the
orientation of the plane and keeps the vector of the plane; in particular it preserves the zero
section and therefore the zero complement, and it is a map over `ogFlip k m`. -/
theorem flipMap (k m : ℕ) :
    ∃ F : C((Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace,
           (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace),
      (∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k m).proj (F p)
        = Work.ThomBordism.Grassmann.ogFlip k m ((Work.ThomBordism.Grassmann.tautologicalBundle k m).proj p)) ∧
      (∀ p, Work.ThomBordism.Grassmann.evalVec (F p) = Work.ThomBordism.Grassmann.evalVec p) ∧
      (∀ p, p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m) →
        F p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) := by
  refine ⟨⟨flipFun k m, continuous_flipFun k m⟩, fun p => rfl, fun p => evalVec_flipFun k m p, ?_⟩
  intro p hp
  have hp2 : (show Amb k from p.2) ≠ 0 := (Work.Thom.mem_zeroComplement p).mp hp
  have hE : evalVec p ≠ 0 := fun h => hp2 ((evalVec_eq_zero_iff p).mp h)
  have hF : evalVec (flipFun k m p) ≠ 0 := by
    rw [evalVec_flipFun k m p]
    exact hE
  exact (Work.Thom.mem_zeroComplement (flipFun k m p)).mpr
    (fun h => hF ((evalVec_eq_zero_iff (flipFun k m p)).mpr h))

end

end Work.ThomBordism.Signs
