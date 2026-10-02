import Mathlib
import Submission.Work.ThomBordism.Grassmann.PlaneCoord
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.relCohMap_comp
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.relCohMap_id

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The frame reading of the tautological Thom class

For the tautological oriented bundle `γ = tautologicalBundle k 10` over the oriented Grassmannian
`G̃r_k(ℝ^{k+10})` and a frame `σ ∈ V_k(ℝ^{k+10})` (an orthonormal `k`-frame), the map

  `frameEval σ : ℝ^k → γ.TotalSpace`,  `v ↦` the point of the fibre over the plane `ogMk σ` whose
ambient vector is `∑ v_j σ_j`,

is a homeomorphism of pairs `(ℝ^k, ℝ^k∖0) ≅ (γ_{ogMk σ}, γ_{ogMk σ}∖0)`.  Consequently the pullback

  `frameClass σ := (relCohMap (frameEval σ)).hom τ`,   `τ = (tautologicalThomClass k 10).τ`,

is an element of the *standard* pair `H^k(ℝ^k, ℝ^k∖0;ℤ)`, and the whole content of the fibre
comparison of the last mile is that this element is the same for every frame `σ` (and hence is
`±` the standard generator `Work.ThomBordism.stdThomGen`).

This module contains only the definitions and their basic API, so that the statements about
`frameClass` can be delegated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

/-- The ambient vector `∑ v_j • σ_j` of a frame `σ` with coordinate vector `v`, as a linear map. -/
def frameLM (k : ℕ) (σ : Stiefel k 10) : Amb k →ₗ[ℝ] Amb (k + 10) where
  toFun v := ∑ j, v j • σ.1 j
  map_add' a b := by
    simp only [PiLp.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul]
    rw [Finset.smul_sum]
    rfl

theorem frameLM_apply (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    frameLM k σ v = ∑ j, v j • σ.1 j := rfl

theorem inner_frameLM_apply (k : ℕ) (σ : Stiefel k 10) (i : Fin k) (v : Amb k) :
    inner ℝ (σ.1 i) (frameLM k σ v) = v i := by
  rw [frameLM_apply]
  exact Orthonormal.inner_right_fintype σ.2 v i

theorem inner_frameLM_self (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    inner ℝ (frameLM k σ v) (frameLM k σ v) = ∑ j, (v j) ^ 2 := by
  rw [frameLM_apply, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, Orthonormal.inner_right_fintype σ.2 v j]
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem norm_frameLM (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    ‖frameLM k σ v‖ = ‖v‖ := by
  have h1 : ‖frameLM k σ v‖ ^ 2 = ∑ j, (v j) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_frameLM_self]
  have h3 : ‖(v : Amb k)‖ ^ 2 = ∑ j, (v j) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [sq]
  have h2 : ‖frameLM k σ v‖ ^ 2 = ‖(v : Amb k)‖ ^ 2 := by rw [h1, ← h3]
  rw [← Real.sqrt_sq (norm_nonneg (frameLM k σ v)),
    ← Real.sqrt_sq (norm_nonneg (v : Amb k)), h2]

/-- The **frame map of a frame `σ`**: the linear isometry `ℝ^k → ℝ^{k+10}`, `v ↦ ∑ v_j σ_j`. -/
def frameLI (k : ℕ) (σ : Stiefel k 10) : Amb k →ₗᵢ[ℝ] Amb (k + 10) where
  toLinearMap := frameLM k σ
  norm_map' := norm_frameLM k σ

theorem frameLI_apply (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    frameLI k σ v = frameLM k σ v := rfl

theorem frameVec_memPlane (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    memPlane (k := k) (m := 10) (ogMk k 10 σ) (frameLI k σ v) := by
  refine ⟨σ, rfl, ?_⟩
  rw [frameLI_apply, frameLM_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem continuous_frameLM_apply (k : ℕ) :
    Continuous fun q : Stiefel k 10 × Amb k => frameLM k q.1 q.2 := by
  rw [show (fun q : Stiefel k 10 × Amb k => frameLM k q.1 q.2)
      = fun q => ∑ j, q.2 j • q.1.1 j from funext fun q => frameLM_apply k q.1 q.2]
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp continuous_snd).smul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst))

/-! ## The frame evaluation -/

/-- **The point of the tautological bundle over the plane of `σ` with ambient vector
`∑ v_j σ_j`.** -/
def frameEval (k : ℕ) (σ : Stiefel k 10) (v : Amb k) : (tautologicalBundle k 10).TotalSpace :=
  mkTotal (ogMk k 10 σ)
    (toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
      (frameLI k σ v))

theorem frameEval_apply (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    frameEval k σ v = mkTotal (ogMk k 10 σ)
      (toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
        (frameLI k σ v)) := rfl

theorem frameEval_base (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    (frameEval k σ v).1 = ogMk k 10 σ := rfl

theorem evalVec_frameEval (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    evalVec (frameEval k σ v) = frameLI k σ v := by
  rw [frameEval_apply, evalVec_mkTotal]
  exact evalChartO_toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
    ((tautologicalBundle k 10).mem_baseSet_at (ogMk k 10 σ)) _ (frameVec_memPlane k σ v)

/-- Membership in the zero complement of the tautological bundle is non-vanishing of the ambient
vector. -/
theorem mem_zeroComplement_iff_evalVec_ne_zero (k : ℕ)
    (p : (tautologicalBundle k 10).TotalSpace) :
    p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10) ↔ evalVec p ≠ 0 := by
  refine ⟨fun hp h => Work.ThomBordism.Grassmann.evalVec_ne_zero_of_mem_zeroComplement p hp h,
    fun hp => ?_⟩
  rw [Work.Thom.mem_zeroComplement]
  intro h0
  exact hp ((Work.ThomBordism.Grassmann.evalVec_eq_zero_iff p).mpr h0)

theorem frameEval_ne_zero_iff (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    frameEval k σ v ∈ Work.Thom.zeroComplement (tautologicalBundle k 10) ↔ v ≠ 0 := by
  rw [mem_zeroComplement_iff_evalVec_ne_zero, evalVec_frameEval]
  exact ⟨fun h h0 => h (by rw [h0, map_zero]),
    fun hv h0 => hv ((frameLI k σ).injective (by rw [h0, map_zero]))⟩

theorem frameEval_zero (k : ℕ) (σ : Stiefel k 10) :
    frameEval k σ 0 = mkTotal (ogMk k 10 σ)
      (toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ) 0) := by
  rw [frameEval_apply, map_zero]

/-- **Reconstruction of a vector from its coordinates in an orthonormal family.** -/
theorem sum_inner_smul_eq_self_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] (f : ι → E) (hf : Orthonormal ℝ f) {w : E}
    (hw : w ∈ Submodule.span ℝ (Set.range f)) :
    ∑ i, (inner ℝ (f i) w) • f i = w := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := f) (x := w)).mp hw
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Orthonormal.inner_right_fintype hf c i]

/-- **Reconstruction of a vector from its coordinates in an orthonormal frame.** -/
theorem sum_inner_smul_eq_self (k : ℕ) (σ : Stiefel k 10) {w : Amb (k + 10)}
    (hw : w ∈ Submodule.span ℝ (Set.range σ.1)) :
    ∑ j, (inner ℝ (σ.1 j) w) • σ.1 j = w := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := σ.1) (x := w)).mp hw
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Orthonormal.inner_right_fintype σ.2 c i]

/-! ## Continuity -/

/-- **The point `mkTotal P (toECoordAt (indexAt P) P c)` depends continuously on `(P,c)`** on the
incidence set (where `c` really is a vector of the plane `P`). -/
theorem continuousOn_mkTotal_toECoordAt (k : ℕ) :
    ContinuousOn (fun q : OG k 10 × Amb (k + 10) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k 10).indexAt q.1) q.1 q.2))
      {q : OG k 10 × Amb (k + 10) | memPlane q.1 q.2} := by
  intro x hx
  set S := (tautologicalBundle k 10).indexAt x.1 with hS
  let e := (tautologicalBundle k 10).localTriv S
  let U : Set (OG k 10 × Amb (k + 10)) := {q | q.1 ∈ (tautologicalBundle k 10).baseSet S}
  let s : Set (OG k 10 × Amb (k + 10)) := {q | memPlane q.1 q.2}
  have hxS : x.1 ∈ (tautologicalBundle k 10).baseSet S :=
    (tautologicalBundle k 10).mem_baseSet_at x.1
  have hU : U ∈ 𝓝 x := ((isOpen_baseSet S).preimage continuous_fst).mem_nhds hxS
  have hsource : ∀ q : OG k 10 × Amb (k + 10), q.1 ∈ (tautologicalBundle k 10).baseSet S →
      mkTotal q.1 (toECoordAt ((tautologicalBundle k 10).indexAt q.1) q.1 q.2) ∈ e.source := by
    intro q hq
    rw [VectorBundleCore.mem_localTriv_source]
    exact hq
  have htarget : ∀ q : OG k 10 × Amb (k + 10), q.1 ∈ (tautologicalBundle k 10).baseSet S →
      (q.1, toECoordAt S q.1 q.2) ∈ e.target := by
    intro q hq
    rw [VectorBundleCore.mem_localTriv_target]
    exact hq
  have hg : ContinuousOn (fun q : OG k 10 × Amb (k + 10) =>
      e.toOpenPartialHomeomorph.symm (q.1, toECoordAt S q.1 q.2)) U :=
    (OpenPartialHomeomorph.continuousOn_symm e.toOpenPartialHomeomorph).comp
      (continuousOn_fst.prodMk (continuousOn_toECoordAt S)) htarget
  have hfilter : 𝓝[U ∩ s] x = 𝓝[s] x := nhdsWithin_inter_of_mem (nhdsWithin_le_nhds hU)
  have hmain : ContinuousWithinAt (fun q : OG k 10 × Amb (k + 10) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k 10).indexAt q.1) q.1 q.2)) (U ∩ s) x := by
    refine ((hg.continuousWithinAt hxS).mono Set.inter_subset_left).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [← localTriv_mkTotal S q.1 hq.1 q.2 hq.2]
      exact (e.left_inv' (hsource q hq.1)).symm
    · rw [← localTriv_mkTotal S x.1 hxS x.2 hx]
      exact (e.left_inv' (hsource x hxS)).symm
  show Filter.Tendsto (fun q : OG k 10 × Amb (k + 10) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k 10).indexAt q.1) q.1 q.2)) (𝓝[s] x)
      (𝓝 (mkTotal x.1 (toECoordAt ((tautologicalBundle k 10).indexAt x.1) x.1 x.2)))
  rw [← hfilter]
  exact hmain

/-- The frame evaluation is continuous, jointly in the frame and the coordinate. -/
theorem continuous_frameEval (k : ℕ) :
    Continuous fun q : Stiefel k 10 × Amb k => frameEval k q.1 q.2 := by
  have hA : Continuous fun q : Stiefel k 10 × Amb k =>
      (ogMk k 10 q.1, frameLI k q.1 q.2) :=
    (continuous_quotient_mk'.comp continuous_fst).prodMk
      (by
        rw [show (fun q : Stiefel k 10 × Amb k => frameLI k q.1 q.2)
            = fun q => frameLM k q.1 q.2 from funext fun q => frameLI_apply k q.1 q.2]
        exact continuous_frameLM_apply k)
  refine (continuousOn_mkTotal_toECoordAt k).comp_continuous hA ?_
  intro q
  exact frameVec_memPlane k q.1 q.2

theorem continuous_frameEval_snd (k : ℕ) (σ : Stiefel k 10) :
    Continuous fun v : Amb k => frameEval k σ v :=
  (continuous_frameEval k).comp (continuous_const.prodMk continuous_id)

/-! ## The class -/

/-- The punctured standard pair `(ℝ^k, ℝ^k∖0)`.  An `abbrev` so that it is transparent to the
elaborator (it is definitionally the complement of the origin). -/
abbrev framePunct (k : ℕ) : Set (Amb k) := {0}ᶜ

theorem mem_framePunct (k : ℕ) (v : Amb k) : v ∈ framePunct k ↔ v ≠ 0 := Iff.rfl

/-- The frame evaluation as a continuous map of pairs. -/
def frameEvalMap (k : ℕ) (σ : Stiefel k 10) :
    C(Amb k, (tautologicalBundle k 10).TotalSpace) :=
  ⟨fun v => frameEval k σ v, continuous_frameEval_snd k σ⟩

theorem frameEvalMap_apply (k : ℕ) (σ : Stiefel k 10) (v : Amb k) :
    frameEvalMap k σ v = frameEval k σ v := rfl

theorem frameEvalMap_mem (k : ℕ) (σ : Stiefel k 10) :
    ∀ v ∈ framePunct k, frameEvalMap k σ v ∈ Work.Thom.zeroComplement (tautologicalBundle k 10) :=
  fun v hv => (frameEval_ne_zero_iff k σ v).mpr hv

/-- **The frame reading of the tautological Thom class**: the pullback of `τ` along the frame
evaluation, as an element of the standard pair `H^k(ℝ^k, ℝ^k∖0;ℤ)`. -/
def frameClass (k : ℕ) (σ : Stiefel k 10) : Work.Thom.RelCoh ℤ k (Amb k) (framePunct k) :=
  (Work.Thom.relCohMap (frameEvalMap k σ) (framePunct k)
    (Work.Thom.zeroComplement (tautologicalBundle k 10)) (frameEvalMap_mem k σ) ℤ k).hom
    (tautologicalThomClass k 10).τ

end

end Work.ThomBordism
