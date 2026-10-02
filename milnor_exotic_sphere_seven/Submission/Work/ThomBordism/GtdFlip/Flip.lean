import Mathlib
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.PlaneAct
import Submission.Work.ThomBordism.Grassmann.tautTotalMap
import Submission.Work.ThomBordism.Grassmann.probePlane
import Submission.Work.Thom.ChartOrientation
import Submission.Work.ThomBordism.Grassmann.PlaneCoord
import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.ThomBordism.Signs.coordChangeO_ogFlip_mul_flipMat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The orientation flip of the tautological bundle

`Work.ThomBordism.Grassmann.ogFlip` reverses the orientation of an oriented plane; it acts on frames
by right multiplication with `flipMat k = diag(-1,1,…,1)`.  This module lifts it to the
*tautological bundle* as a continuous map `ogFlipTotal k m : C(γ, γ)` that keeps the vector of the
plane.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## Membership in a plane is invariant under the orientation flip -/

theorem memPlane_ogFlip (k m : ℕ) (P : OG k m) (w : Amb (k + m)) :
    memPlane (ogFlip k m P) w ↔ memPlane P w := by
  rw [← Work.PTGeometric.projOfPlane_fixed_iff, ← Work.PTGeometric.projOfPlane_fixed_iff,
    projOfPlane_ogFlip]


/-- **The orientation flip preserves each chart cell** `baseSet S`: the determinant of the `S`-minor
of a frame is multiplied by `det (flipMat k) = ±1`. -/
theorem ogFlip_mem_baseSet_iff (S : ChartIdx k m) (x : OG k m) :
    ogFlip k m x ∈ baseSet S ↔ x ∈ baseSet S := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = x := Quotient.exists_rep x
  rw [← hf, ogFlip_mk]
  rw [mem_baseSet_iff, mem_baseSet_iff, mem_chartSet, mem_chartSet,
    frameMatrix_soActFun]
  by_cases hk : k = 0
  · subst hk
    have : flipMat 0 = (1 : Matrix (Fin 0) (Fin 0) ℝ) := Subsingleton.elim _ _
    rw [this, Matrix.mul_one]
  · rw [Matrix.det_mul, Work.ThomBordism.Signs.CoordFlip.flipMat_det (Nat.pos_of_ne_zero hk)]
    constructor
    · intro h h0; exact h (by rw [h0, zero_mul])
    · intro h; exact mul_ne_zero h (by norm_num)

/-! ## The explicit chart evaluation of a bundled vector -/

/-- **The fibre coordinate of the chart evaluation.** -/
theorem toECoordAt_evalChartO_gen (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S)
    (x : ↥(baseSet S)) (v : Amb k) :
    toECoordAt S P (evalChartO S x v) = matLin (orientMat S P) (matLin (orientMat S x) v) := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = (x : OG k m) := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  have hspec : evalChartO S x v = coordEval S f (matLin (orientMat S (x : OG k m)) v) := by
    rw [evalChartO]
    exact evalChart_spec S x f hfc hf.symm (matLin (orientMat S (x : OG k m)) v)
  rw [hspec, toECoordAt]
  rw [coordProj_coordEval S f (matLin (orientMat S (x : OG k m)) v) hfc]

/-! ## The flip of the total space -/

/-- **The orientation flip of the tautological bundle**: the continuous map `γ → γ` covering
`ogFlip` and keeping the vector of the plane. -/
noncomputable def ogFlipTotal (k m : ℕ) :
    C((tautologicalBundle k m).TotalSpace, (tautologicalBundle k m).TotalSpace) :=
  ⟨fun p => mkTotal (ogFlip k m p.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (ogFlip k m p.1) (evalVec p)),
    ((continuousOn_mkTotal_toECoordAt (k := k) (m := m)).comp_continuous
      (((continuous_ogFlip k m).comp (tautologicalBundle k m).continuous_proj).prodMk
        continuous_evalVec)
      (fun p => (memPlane_ogFlip k m p.1 (evalVec p)).mpr (evalVec_memPlane p))).congr
      (fun p => rfl)⟩

theorem ogFlipTotal_apply (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    ogFlipTotal k m p = mkTotal (ogFlip k m p.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (ogFlip k m p.1)
        (evalVec p)) := rfl

theorem ogFlipTotal_proj (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    (ogFlipTotal k m p).1 = ogFlip k m p.1 := rfl

theorem ogFlipTotal_evalVec (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    evalVec (ogFlipTotal k m p) = evalVec p := by
  rw [ogFlipTotal_apply, evalVec_mkTotal]
  exact evalChartO_toECoordAt _ _ _ _ (memPlane_ogFlip k m p.1 (evalVec p) |>.mpr
    (evalVec_memPlane p))

/-! ## The pair `(proj, evalVec)` determines a point -/

/-- **Reconstruction of a point of the tautological bundle from its plane and its vector.** -/
theorem mkTotal_toECoordAt_evalVec_eq (p : (tautologicalBundle k m).TotalSpace) :
    mkTotal p.1 (toECoordAt ((tautologicalBundle k m).indexAt p.1) p.1 (evalVec p)) = p := by
  cases p with
  | mk a b =>
    show mkTotal a (toECoordAt ((tautologicalBundle k m).indexAt a) a
      (evalVec (mkTotal a b))) = mkTotal a b
    congr 1
    rw [evalVec_mkTotal]
    exact toECoordAt_evalChartO _ _ _ b

/-- **Two points of the total space over the same plane with the same vector coincide.** -/
theorem evalVec_injective_of_proj_eq {p q : (tautologicalBundle k m).TotalSpace}
    (h : p.1 = q.1) (h2 : evalVec p = evalVec q) : p = q := by
  rw [← mkTotal_toECoordAt_evalVec_eq p, ← mkTotal_toECoordAt_evalVec_eq q, h, h2]

theorem evalVec_injective_on_fibre (k m : ℕ) :
    ∀ p q : (tautologicalBundle k m).TotalSpace, p.1 = q.1 → evalVec p = evalVec q → p = q :=
  fun _ _ h h2 => evalVec_injective_of_proj_eq h h2

/-! ## The flip is an involution and preserves the zero section complement -/

theorem ogFlipTotal_involutive (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    ogFlipTotal k m (ogFlipTotal k m p) = p :=
  evalVec_injective_of_proj_eq
    (by rw [ogFlipTotal_proj, ogFlipTotal_proj, ogFlip_idem])
    (by rw [ogFlipTotal_evalVec, ogFlipTotal_evalVec])

theorem ogFlipTotal_mem (k m : ℕ) :
    ∀ p ∈ Work.Thom.zeroComplement (tautologicalBundle k m),
      ogFlipTotal k m p ∈ Work.Thom.zeroComplement (tautologicalBundle k m) := by
  intro p hp
  rw [Work.Thom.mem_zeroComplement] at hp ⊢
  intro h0
  have h2 : evalVec (ogFlipTotal k m p) = 0 := (evalVec_eq_zero_iff _).mpr h0
  rw [ogFlipTotal_evalVec] at h2
  exact hp ((evalVec_eq_zero_iff p).mp h2)

/-! ## The chart description of the flip -/

/-- **The flip in the chart `S`**: on the piece over `baseSet S` (which the flip maps to itself) the
fibre coordinate is multiplied by `flipMat k`. -/
theorem localTriv_snd_eq (S : ChartIdx k m) (p : (tautologicalBundle k m).TotalSpace) :
    ((tautologicalBundle k m).localTriv S p).2
      = (tautologicalBundle k m).coordChange ((tautologicalBundle k m).indexAt p.1) S p.1 p.2 := by
  rw [VectorBundleCore.localTriv_apply]

/-- **The flip in the chart `S`**: on the piece over `baseSet S` (which the flip maps to itself) the
fibre coordinate is multiplied by `flipMat k`. -/
theorem localTriv_ogFlipTotal (S : ChartIdx k m) (p : (tautologicalBundle k m).TotalSpace)
    (hpS : p.1 ∈ (tautologicalBundle k m).baseSet S) :
    ((tautologicalBundle k m).localTriv S (ogFlipTotal k m p)).2
      = matLin (flipMat k) (((tautologicalBundle k m).localTriv S p).2) := by
  have hpS' : p.1 ∈ baseSet S := hpS
  have hflipS : (ogFlipTotal k m p).1 ∈ (tautologicalBundle k m).baseSet S := by
    rw [ogFlipTotal_proj]
    exact (ogFlip_mem_baseSet_iff S p.1).mpr hpS
  have hflipS' : ogFlip k m p.1 ∈ baseSet S := hflipS
  rw [localTriv_snd_eq S (ogFlipTotal k m p), localTriv_snd_eq S p, ogFlipTotal_proj,
    ogFlipTotal_apply]
  have hmk : (mkTotal (ogFlip k m p.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (ogFlip k m p.1)) (ogFlip k m p.1)
        (evalVec p))).2
      = toECoordAt ((tautologicalBundle k m).indexAt (ogFlip k m p.1))
          (ogFlip k m p.1) (evalVec p) := rfl
  rw [hmk]
  rw [coordChange_toECoordAt S (ogFlip k m p.1) hflipS' (evalVec p)
    ((memPlane_ogFlip k m p.1 (evalVec p)).mpr (evalVec_memPlane p))]
  rw [evalVec_apply_chart p S hpS]
  rw [toECoordAt_evalChartO_gen S (ogFlip k m p.1) hflipS' ⟨p.1, hpS'⟩
    ((tautologicalBundle k m).localTriv S p).2]
  rw [← localTriv_snd_eq S p]
  have hmat : (matLin (orientMat S (ogFlip k m p.1)))
      = (matLin (flipMat k)).comp (matLin (orientMat S p.1)) := by
    rw [Work.ThomBordism.Signs.CoordFlip.orientMat_ogFlip]
    exact matLin_mul (flipMat k) (orientMat S p.1)
  rw [hmat, ContinuousLinearMap.comp_apply]
  congr 1
  exact orientMat_involutive S p.1 hpS' ((tautologicalBundle k m).localTriv S p).2


/-! ## The flip of a piece over a chart -/

/-- **The flip restricts to each piece over a chart** (`ogFlip` preserves the chart cells
`baseSet S`), as a continuous map of the piece. -/
noncomputable def ogFlipPiece (k m : ℕ) (S : ChartIdx k m) :
    C(↥((tautologicalBundle k m).proj ⁻¹' baseSet S),
      ↥((tautologicalBundle k m).proj ⁻¹' baseSet S)) :=
  let h : ∀ p : ↥((tautologicalBundle k m).proj ⁻¹' baseSet S),
      ogFlipTotal k m (p : (tautologicalBundle k m).TotalSpace)
        ∈ (tautologicalBundle k m).proj ⁻¹' baseSet S :=
    fun p => by
      show ogFlip k m (p : (tautologicalBundle k m).TotalSpace).1 ∈ baseSet S
      rw [← ogFlipTotal_proj]
      exact (ogFlip_mem_baseSet_iff S _).mpr p.2
  ⟨fun p => ⟨ogFlipTotal k m (p : (tautologicalBundle k m).TotalSpace), h p⟩,
    Continuous.subtype_mk ((ogFlipTotal k m).continuous.comp continuous_subtype_val) h⟩

/-- The flip of a piece preserves the zero complement of the piece. -/
theorem ogFlipPiece_mem (k m : ℕ) (S : ChartIdx k m) :
    ∀ p ∈ Work.Thom.pieceZero (tautologicalBundle k m) (baseSet S),
      ogFlipPiece k m S p ∈ Work.Thom.pieceZero (tautologicalBundle k m) (baseSet S) := by
  intro p hp
  exact ogFlipTotal_mem k m _ hp

/-- The flip of a piece is the restriction of the flip to the piece. -/
theorem subtypeMap_comp_ogFlipPiece (k m : ℕ) (S : ChartIdx k m) :
    (Work.Thom.subtypeMap ((tautologicalBundle k m).proj ⁻¹' baseSet S)).comp
        (ogFlipPiece k m S)
      = (ogFlipTotal k m).comp
        (Work.Thom.subtypeMap ((tautologicalBundle k m).proj ⁻¹' baseSet S)) := by
  apply ContinuousMap.ext
  intro p
  rfl

end

end Work.ThomBordism.Grassmann
