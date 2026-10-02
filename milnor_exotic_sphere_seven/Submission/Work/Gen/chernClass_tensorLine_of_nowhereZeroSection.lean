import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.continuousOn_chartExpressionCLM
import Submission.Work.Whitney.SectionStability
import Submission.Work.Whitney.TautSection
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.NowhereZeroChart
import Submission.Work.Gen.chernClass_one_whitneySum_eq_tensorLine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# `c₁(V ⊗ W) = c₁(W)` when `V` has a nowhere-zero section

The main theorem of this file is `Work.Gen.chernClass_tensorLine_of_nowhereZeroSection`.  Its
mathematical content is that a complex **line** bundle with a continuous nowhere-zero section is
trivial (in rank one the section itself is a global frame), so that it can be peeled off from a
tensor product.

The trivialisation is `nonempty_bundleIso_tensorLine_of_nowhereZeroSection`: for a complex line
bundle `V` with a continuous nowhere-zero section `σ` and any complex line bundle `W`, there is an
isomorphism `V ⊗ W ≅ W` given fibrewise by `v ⊗ w ↦ λ(v) w`, where `λ : V_b → ℂ` is the unique
linear form with `λ (σ b) = 1`.  Everything is proved with the gauge construction
`Work.Thom.nonempty_bundleIso_of_gauge`, so that the continuity of the total-space maps is reduced
to continuity of the chart expressions and the compatibility conditions become the cocycle
identities of the transition functions.

The chart coordinate `secCoord V σ i b` of the section in the chart `i` is the basic tool: it is
continuous on `V.baseSet i` and non-zero there, and it transforms by
`secCoord i b = scl (V.coordChange (V.indexAt b) i b) * secCoord (V.indexAt b) b`.
-/

namespace Work.Gen

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The scalar of a rank-one transition function -/

/-- **The scalars of transition functions of a complex line bundle multiply along compositions.**
For `x` in the intersection of the three base sets,
`scl (Z.coordChange i k x) = scl (Z.coordChange i j x) * scl (Z.coordChange j k x)`. -/
theorem scl_cc_comp {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (i j k : ι) (x : B) (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
    scl (Z.coordChange i k x)
      = scl (Z.coordChange i j x) * scl (Z.coordChange j k x) := by
  rw [← Z.coordChange_linear_comp i j k x hx, scl_comp, mul_comm]

/-- **The scalars of reciprocal transition functions of a complex line bundle are reciprocal.** -/
theorem scl_cc_recip {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (i j : ι) (x : B) (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    scl (Z.coordChange j i x) * scl (Z.coordChange i j x) = 1 := by
  have h := scl_cc_comp Z i j i x ⟨⟨hi, hj⟩, hi⟩
  have hself : Z.coordChange i i x = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    apply ContinuousLinearMap.ext
    intro v
    exact Z.coordChange_self i x hi v
  rw [hself, scl_id] at h
  rw [mul_comm]
  exact h.symm

/-- **The inverse of the scalar of a transition function is the scalar of the reciprocal
transition function.** -/
theorem scl_cc_inv {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (i j : ι) (x : B) (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    (scl (Z.coordChange i j x))⁻¹ = scl (Z.coordChange j i x) :=
  inv_eq_of_mul_eq_one_left (scl_cc_recip Z i j x hi hj)

/-- The composite of "multiplication by `c`" with "multiplication by `d`" is multiplication by
`c * d` — with the scalar of the *first* (outer) factor on the right. -/
theorem comp_smul_id (c d : ℂ) :
    (d • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))).comp
        (c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      = (c * d) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, smul_smul, mul_comm]

/-- The scalar of the identity of `ℂ¹`, in the form of the unit of the endomorphism ring. -/
theorem scl_one : scl (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) = 1 := by
  rw [show (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) from rfl, scl_id]

/-! ## The trivial core -/

/-- The trivial core has all base sets `univ`. -/
theorem trivialCore_baseSet {ι : Type} [Inhabited ι] (i : ι) :
    (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι).baseSet i = Set.univ := rfl

/-- The trivial core has identically the identity transition function. -/
theorem trivialCore_coordChange {ι : Type} [Inhabited ι] (i j : ι) (b : B) :
    (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι).coordChange i j b
      = 1 := rfl

/-- The scalar of a transition function of the trivial core is `1`. -/
theorem scl_trivialCore {ι : Type} [Inhabited ι] (i j : ι) (b : B) :
    scl ((trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι).coordChange i j b) = 1 := by
  rw [trivialCore_coordChange, scl_one]

/-- The base sets of `ε ⊗ W` are those of `W`, for `ε` the trivial core. -/
theorem tensorLine_trivial_left_baseSet {ι₀ ι₂ : Type} [Inhabited ι₀]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) (i : ι₀ × ι₂) :
    (tensorLine (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀) W).baseSet i
      = W.baseSet i.2 := by
  rw [tensorLine_baseSet, trivialCore_baseSet, Set.univ_inter]

/-- The transition function of `ε ⊗ W` is that of `W` (as a scalar multiple of the identity). -/
theorem tensorLine_trivial_left_coordChange {ι₀ ι₂ : Type} [Inhabited ι₀]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    (u t : ι₀ × ι₂) (b : B) :
    (tensorLine (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀) W).coordChange u t b
      = (scl (W.coordChange u.2 t.2 b)) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  rw [tensorLine_coordChange, scl_trivialCore, one_mul]

/-! ## The trivial core is a unit for the tensor product -/

/-- **`ε ⊗ W ≅ W`**: tensoring with the trivial core does not change a complex line bundle. -/
theorem nonempty_bundleIso_tensorLine_trivial_left {ι₀ ι₂ : Type} [Inhabited ι₀]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Nonempty (Work.Thom.BundleIso
      (tensorLine (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀) W) W) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (tensorLine (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀) W) W
    (fun u q b => scl (W.coordChange u.2 q b) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    (fun u q b => scl (W.coordChange q u.2 b) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u q
    rw [tensorLine_trivial_left_baseSet]
    exact (continuous_scl.comp_continuousOn (W.continuousOn_coordChange u.2 q)).smul
      (continuousOn_const :
        ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)
  · intro u q
    rw [tensorLine_trivial_left_baseSet]
    exact ((continuous_scl.comp_continuousOn (W.continuousOn_coordChange q u.2)).mono
      (fun b hb => ⟨hb.2, hb.1⟩)).smul
      (continuousOn_const :
        ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)
  · intro u t t' b hu ht ht'
    rw [tensorLine_trivial_left_baseSet] at hu
    rw [scl_smul_id (W.coordChange t t' b), comp_smul_id,
      ← scl_cc_comp W u.2 t t' b ⟨⟨hu, ht⟩, ht'⟩]
  · intro u t u' b hu hu' ht
    rw [tensorLine_trivial_left_baseSet] at hu hu'
    rw [tensorLine_trivial_left_coordChange, comp_smul_id,
      ← scl_cc_comp W u'.2 u.2 t b ⟨⟨hu', hu⟩, ht⟩]
  · intro u t t' b hu ht ht'
    rw [tensorLine_trivial_left_baseSet] at hu
    rw [scl_smul_id (W.coordChange t' t b), comp_smul_id,
      ← scl_cc_comp W t' t u.2 b ⟨⟨ht', ht⟩, hu⟩]
  · intro u t u' b hu hu' ht
    rw [tensorLine_trivial_left_baseSet] at hu hu'
    rw [tensorLine_trivial_left_coordChange, comp_smul_id,
      ← scl_cc_comp W t u.2 u'.2 b ⟨⟨ht, hu⟩, hu'⟩]
  · intro u q b x ⟨hu, hq⟩
    rw [tensorLine_trivial_left_baseSet] at hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, smul_smul,
      scl_cc_recip W u.2 q b hu hq]
    simp
  · intro u q b y ⟨hu, hq⟩
    rw [tensorLine_trivial_left_baseSet] at hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, smul_smul,
      scl_cc_recip W q u.2 b hq hu]
    simp

/-! ## The chart coordinate of a nowhere-zero section -/

/-- The point `σ b` of the total space of the realification of `V` (where the section takes its
values). -/
noncomputable def secSPt {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (b : B) :
    (Work.Thom.realification V).TotalSpace :=
  ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
    (Work.Thom.realification V).TotalSpace)

/-- The base point of `secSPt`. -/
theorem secSPt_proj {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (b : B) :
    (secSPt V σ b).proj = b := hσ b

/-- The vector of the section `σ` at `b`, as a vector of the model fibre. -/
noncomputable def secVec {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (b : B) :
    EuclideanSpace ℂ (Fin 1) :=
  (secSPt V σ b).2

/-- The section vector is non-zero. -/
theorem secVec_ne_zero {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (b : B) :
    secVec V σ b ≠ 0 := (σ b).2

/-- The section point, as a point of the total space of the realification whose base point is `b`
*definitionally*.  This is what makes the chart computations below reduce. -/
noncomputable def secPt {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (b : B) :
    (Work.Thom.realification V).TotalSpace :=
  ⟨b, secVec V σ b⟩

/-- The section point read in the chart `i` of `V`, as a vector of the model fibre. -/
noncomputable def secChartVec {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (i : ι₁) (b : B) :
    EuclideanSpace ℂ (Fin 1) :=
  ((Work.Thom.realification V).localTriv i (secSPt V σ b)).2

/-- The defining equation of `secChartVec`. -/
theorem secChartVec_apply {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (i : ι₁) (b : B) :
    secChartVec V σ i b
      = ((Work.Thom.realification V).localTriv i (secSPt V σ b)).2 := rfl

/-- The chart vector of the section, read in the chart `i` of `V` itself (rather than in the
realification). -/
theorem secChartVec_eq_localTriv {ι₁ : Type}
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (i : ι₁) (b : B) :
    secChartVec V σ i b = ((V.localTriv i (secPt V σ b)).2) := by
  rw [secChartVec_apply, Work.Thom.localTriv_snd_eq (Z := V) i (secSPt V σ b),
    VectorBundleCore.localTriv_apply (Z := V) (i := i) (secSPt V σ b),
    VectorBundleCore.localTriv_apply (Z := V) (i := i) (secPt V σ b),
    secSPt_proj V σ hσ b]
  rfl

/-- The coordinate of the section point `σ b` in the chart `i`. -/
noncomputable def secCoord {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (i : ι₁) (b : B) : ℂ :=
  (secChartVec V σ i b).ofLp 0

/-- The defining equation of `secCoord`. -/
theorem secCoord_apply {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V)))) (i : ι₁) (b : B) :
    secCoord V σ i b = (secChartVec V σ i b).ofLp 0 := rfl

/-- In the *preferred* chart, the coordinate of the section point is the section vector itself. -/
theorem secCoord_indexAt {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (b : B) :
    secCoord V σ (V.indexAt b) b = (secVec V σ b).ofLp 0 := by
  rw [secCoord_apply, secChartVec_eq_localTriv V σ hσ (V.indexAt b) b,
    VectorBundleCore.localTriv_apply (Z := V) (i := V.indexAt b) (secPt V σ b)]
  show (V.coordChange (V.indexAt b) (V.indexAt b) b (secVec V σ b)).ofLp 0
      = (secVec V σ b).ofLp 0
  rw [V.coordChange_self (V.indexAt b) b (V.mem_baseSet_at b)]

/-- **The transformation rule of the section coordinate**: the coordinate in the chart `i` is the
transition scalar from the preferred chart to the chart `i`, times the coordinate in the preferred
chart. -/
theorem secCoord_scl {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (i : ι₁) (b : B) :
    secCoord V σ i b
      = scl (V.coordChange (V.indexAt b) i b) * secCoord V σ (V.indexAt b) b := by
  rw [secCoord_indexAt V σ hσ b, secCoord_apply, secChartVec_eq_localTriv V σ hσ i b,
    VectorBundleCore.localTriv_apply (Z := V) (i := i) (secPt V σ b)]
  show (V.coordChange (V.indexAt b) i b (secVec V σ b)).ofLp 0
      = scl (V.coordChange (V.indexAt b) i b) * (secVec V σ b).ofLp 0
  rw [oneVec_apply (secVec V σ b), map_smul, Work.Gen.scl_apply, smul_smul]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, Work.Gen.oneVec_ofLp_zero, smul_eq_mul, mul_one]
  ring

/-- **The transformation rule of the section coordinate from one chart to another.** -/
theorem secCoord_cc {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b)
    (i i' : ι₁) (b : B) (hb : b ∈ V.baseSet i ∩ V.baseSet i') :
    secCoord V σ i' b = scl (V.coordChange i i' b) * secCoord V σ i b := by
  have h1 := secCoord_scl V σ hσ i' b
  have h2 := secCoord_scl V σ hσ i b
  rw [h1, h2, scl_cc_comp V (V.indexAt b) i i' b ⟨⟨V.mem_baseSet_at b, hb.1⟩, hb.2⟩]
  ring

/-- **The reciprocal transformation rule of the section coordinate.** -/
theorem secCoord_cc_inv {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b)
    (i i' : ι₁) (b : B) (hb : b ∈ V.baseSet i ∩ V.baseSet i') :
    (secCoord V σ i' b)⁻¹ = scl (V.coordChange i' i b) * (secCoord V σ i b)⁻¹ := by
  rw [secCoord_cc V σ hσ i i' b hb, mul_inv_rev, scl_cc_inv V i i' b hb.1 hb.2]
  ring

/-- **Continuity of the section point read in a chart.** -/
theorem continuousOn_secChartVec {ι₁ : Type}
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (i : ι₁) :
    ContinuousOn (secChartVec V σ i) (V.baseSet i) := by
  have hσ' : Work.Whitney.NZ.IsSection σ := fun b => hσ b
  exact Work.Whitney.NZ.continuousOn_localTriv_snd_sec (V := V) (σ := σ) hσ' i

/-- **Continuity of the section coordinate** in any chart. -/
theorem continuousOn_secCoord {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (i : ι₁) :
    ContinuousOn (secCoord V σ i) (V.baseSet i) := by
  have h := continuousOn_secChartVec V σ hσ i
  have h' : ContinuousOn (fun b : B => (secChartVec V σ i b).ofLp 0) (V.baseSet i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℂ) 0).comp_continuousOn h
  exact h'

/-- **The section coordinate does not vanish** in any chart containing the base point. -/
theorem secCoord_ne_zero {ι₁ : Type} (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) (i : ι₁) (b : B)
    (hb : b ∈ V.baseSet i) : secCoord V σ i b ≠ 0 := by
  intro h
  have h0 : (secChartVec V σ i b).ofLp 0 = 0 := h
  have hc : secChartVec V σ i b = ((V.localTriv i (secPt V σ b)).2) :=
    secChartVec_eq_localTriv V σ hσ i b
  have h1 : ((V.localTriv i (secPt V σ b)).2) = 0 := by
    have h0' : (((V.localTriv i (secPt V σ b)).2)).ofLp 0 = 0 := by
      rw [← hc]
      exact h0
    rw [oneVec_apply ((V.localTriv i (secPt V σ b)).2), h0', zero_smul]
  have hcomp : ((V.localTriv i (secPt V σ b)).2)
      = V.coordChange (V.indexAt b) i b (secVec V σ b) := by
    rw [VectorBundleCore.localTriv_apply (Z := V) (i := i) (secPt V σ b)]
    rfl
  have h2 : V.coordChange (V.indexAt b) i b (secVec V σ b) = 0 := by
    rw [← hcomp]
    exact h1
  have h3 : secVec V σ b = 0 := by
    have hc2 := V.coordChange_comp (V.indexAt b) i (V.indexAt b) b
      ⟨⟨V.mem_baseSet_at b, hb⟩, V.mem_baseSet_at b⟩ (secVec V σ b)
    rw [h2] at hc2
    rw [map_zero] at hc2
    rw [V.coordChange_self (V.indexAt b) b (V.mem_baseSet_at b)] at hc2
    exact hc2.symm
  exact secVec_ne_zero V σ b h3

/-! ## The tensor product with a bundle having a nowhere-zero section -/

/-- **`V ⊗ W ≅ W` when `V` has a nowhere-zero section**: the fibrewise isomorphism is
`v ⊗ w ↦ λ(v) w`, where `λ` is the unique linear form on the fibre of `V` at `b` with
`λ (σ b) = 1`.

In the chart `(i, p)` of `V ⊗ W` and the chart `q` of `W` it is multiplication by
`scl (W.coordChange p q b) * (secCoord V σ i b)⁻¹`. -/
theorem nonempty_bundleIso_tensorLine_of_nowhereZeroSection {ι₁ ι₂ : Type}
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
      (Work.Thom.realification V).TotalSpace).proj = b) :
    Nonempty (Work.Thom.BundleIso (tensorLine V W) W) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge (tensorLine V W) W
    (fun u q b => (scl (W.coordChange u.2 q b) * (secCoord V σ u.1 b)⁻¹) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    (fun u q b => (scl (W.coordChange q u.2 b) * secCoord V σ u.1 b) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u q
    rw [tensorLine_baseSet]
    have h1 : ContinuousOn (fun b : B => scl (W.coordChange u.2 q b))
        ((V.baseSet u.1 ∩ W.baseSet u.2) ∩ W.baseSet q) :=
      (continuous_scl.comp_continuousOn (W.continuousOn_coordChange u.2 q)).mono
        (fun b hb => ⟨hb.1.2, hb.2⟩)
    have h2 : ContinuousOn (fun b : B => (secCoord V σ u.1 b)⁻¹)
        ((V.baseSet u.1 ∩ W.baseSet u.2) ∩ W.baseSet q) :=
      ((continuousOn_secCoord V σ hσ u.1).mono (fun b hb => hb.1.1)).inv₀
        (fun b hb => secCoord_ne_zero V σ hσ u.1 b hb.1.1)
    exact (h1.mul h2).smul
      (continuousOn_const :
        ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)
  · intro u q
    rw [tensorLine_baseSet]
    have h1 : ContinuousOn (fun b : B => scl (W.coordChange q u.2 b))
        ((V.baseSet u.1 ∩ W.baseSet u.2) ∩ W.baseSet q) :=
      (continuous_scl.comp_continuousOn (W.continuousOn_coordChange q u.2)).mono
        (fun b hb => ⟨hb.2, hb.1.2⟩)
    have h2 : ContinuousOn (fun b : B => secCoord V σ u.1 b)
        ((V.baseSet u.1 ∩ W.baseSet u.2) ∩ W.baseSet q) :=
      (continuousOn_secCoord V σ hσ u.1).mono (fun b hb => hb.1.1)
    exact (h1.mul h2).smul
      (continuousOn_const :
        ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)
  · intro u t t' b hu ht ht'
    rw [tensorLine_baseSet] at hu
    have hW : scl (W.coordChange u.2 t' b) =
        scl (W.coordChange u.2 t b) * scl (W.coordChange t t' b) :=
      scl_cc_comp W u.2 t t' b ⟨⟨hu.2, ht⟩, ht'⟩
    rw [scl_smul_id (W.coordChange t t' b), comp_smul_id, hW]
    congr 1
    ring
  · intro u t u' b hu hu' ht
    rw [tensorLine_baseSet] at hu hu'
    have hV : (secCoord V σ u'.1 b)⁻¹
        = scl (V.coordChange u'.1 u.1 b) * (secCoord V σ u.1 b)⁻¹ :=
      secCoord_cc_inv V σ hσ u.1 u'.1 b ⟨hu.1, hu'.1⟩
    have hW : scl (W.coordChange u'.2 t b) =
        scl (W.coordChange u'.2 u.2 b) * scl (W.coordChange u.2 t b) :=
      scl_cc_comp W u'.2 u.2 t b ⟨⟨hu'.2, hu.2⟩, ht⟩
    rw [tensorLine_coordChange, comp_smul_id, hV, hW]
    congr 1
    ring
  · intro u t t' b hu ht ht'
    rw [tensorLine_baseSet] at hu
    have hW : scl (W.coordChange t' u.2 b) =
        scl (W.coordChange t' t b) * scl (W.coordChange t u.2 b) :=
      scl_cc_comp W t' t u.2 b ⟨⟨ht', ht⟩, hu.2⟩
    rw [scl_smul_id (W.coordChange t' t b), comp_smul_id, hW]
    congr 1
    ring
  · intro u t u' b hu hu' ht
    rw [tensorLine_baseSet] at hu hu'
    have hV : secCoord V σ u'.1 b = scl (V.coordChange u.1 u'.1 b) * secCoord V σ u.1 b :=
      secCoord_cc V σ hσ u.1 u'.1 b ⟨hu.1, hu'.1⟩
    have hW : scl (W.coordChange t u'.2 b) =
        scl (W.coordChange t u.2 b) * scl (W.coordChange u.2 u'.2 b) :=
      scl_cc_comp W t u.2 u'.2 b ⟨⟨ht, hu.2⟩, hu'.2⟩
    rw [tensorLine_coordChange, comp_smul_id, hV, hW]
    congr 1
    ring
  · intro u q b x ⟨hu, hq⟩
    rw [tensorLine_baseSet] at hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [show (scl (W.coordChange q u.2 b) * secCoord V σ u.1 b) *
        (scl (W.coordChange u.2 q b) * (secCoord V σ u.1 b)⁻¹) = 1 from by
      rw [show scl (W.coordChange q u.2 b) * secCoord V σ u.1 b *
          (scl (W.coordChange u.2 q b) * (secCoord V σ u.1 b)⁻¹)
          = (scl (W.coordChange q u.2 b) * scl (W.coordChange u.2 q b))
            * (secCoord V σ u.1 b * (secCoord V σ u.1 b)⁻¹) from by ring,
        scl_cc_recip W u.2 q b hu.2 hq,
        mul_inv_cancel₀ (secCoord_ne_zero V σ hσ u.1 b hu.1), mul_one]]
    simp
  · intro u q b y ⟨hu, hq⟩
    rw [tensorLine_baseSet] at hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [show (scl (W.coordChange u.2 q b) * (secCoord V σ u.1 b)⁻¹) *
        (scl (W.coordChange q u.2 b) * secCoord V σ u.1 b) = 1 from by
      rw [show scl (W.coordChange u.2 q b) * (secCoord V σ u.1 b)⁻¹ *
          (scl (W.coordChange q u.2 b) * secCoord V σ u.1 b)
          = (scl (W.coordChange q u.2 b) * scl (W.coordChange u.2 q b))
            * ((secCoord V σ u.1 b)⁻¹ * secCoord V σ u.1 b) from by ring,
        scl_cc_recip W u.2 q b hu.2 hq,
        inv_mul_cancel₀ (secCoord_ne_zero V σ hσ u.1 b hu.1), mul_one]]
    simp

end

/-- **Tensoring with a line bundle that has a nowhere-zero continuous section does not change the
first Chern class**: for a complex line bundle `V` with a nowhere-zero section `σ` (over an
arbitrary topological base — no paracompactness) and any complex line bundle `W`,
`c₁(V ⊗ W) = c₁(W)`.

Consumers: the *divisibility* step of `Work.Gen.tensorLine_c1_additive`
(`Submission/Work/Gen/tensorLine_c1_additive.lean`), applied over the punctured total space of a
line bundle, where the pullback of the bundle to its own punctured total space carries the
tautological nowhere-zero section; and, more generally, every splitting-principle argument in this
workspace that needs to "peel off a line with a section" at the level of the tensor product.

A route: `V` is *trivialized* by `σ` (in rank one the section spans, so `c • σ(b)` is a fibrewise
linear bijection, continuous in `b`), i.e. `Nonempty (BundleIso V ε)` with `ε` the trivial core; the
conclusion then follows from `c₁(ε ⊗ W) = c₁(W)` — which is `Work.Whitney.chernClass_whitneySum_trivial`
combined with the determinant trick `Work.Gen.chernClass_one_whitneySum_eq_tensorLine` and the
commutativity of the Whitney sum (`Work.Whitney.nonempty_bundleIso_whitneySum_comm`). -/
theorem chernClass_tensorLine_of_nowhereZeroSection {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    (σ : C(B, ↥(Work.Thom.zeroComplement (Work.Thom.realification V))))
    (hσ : ∀ b, ((σ b : ↥(Work.Thom.zeroComplement (Work.Thom.realification V))) :
        (Work.Thom.realification V).TotalSpace).proj = b) :
    Work.Thom.chernClass 1 1 (Work.Gen.tensorLine V W)
      = Work.Thom.chernClass 1 1 W := by
  obtain ⟨e⟩ := nonempty_bundleIso_tensorLine_of_nowhereZeroSection (B := B) V W σ hσ
  exact Work.Thom.chernClass_BundleIso (Work.Gen.tensorLine V W) W e

end Work.Gen
