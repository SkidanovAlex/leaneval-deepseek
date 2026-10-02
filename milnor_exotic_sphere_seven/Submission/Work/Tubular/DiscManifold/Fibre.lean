import Submission.Work.Tubular.DiscManifold.OrthoFrameSmooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-!
# The trivialization of the normal bundle in the coordinates of the fibre disc

The closed fibre disc of the normal disc bundle is `Ball (k-1) ⊆ ℝ^{(k-1)+1}`, while the
trivialization `readF` of `OrthoFrame.lean` lands in `ℝ^k`.  This file transports the trivialization
along the linear isometry `ℝ^k ≃ ℝ^{(k-1)+1}` so that the fibre coordinate is an element of the
ambient space of the disc `Ball (k-1)`.
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- The linear isometry `ℝ^k ≃ ℝ^{(k-1)+1}` (which is the identity on indices when `k ≥ 1`). -/
noncomputable def reindexFibre (k : ℕ) [NeZero k] : Euc k ≃ₗᵢ[ℝ] Euc ((k - 1) + 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finCongr (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne k))).symm)

/-- The reindexing, as a continuous linear map. -/
noncomputable def reindexFibreCLM (k : ℕ) [NeZero k] : Euc k →L[ℝ] Euc ((k - 1) + 1) :=
  (reindexFibre k).toContinuousLinearEquiv.toContinuousLinearMap

/-- The inverse reindexing, as a continuous linear map. -/
noncomputable def reindexFibreCLMsymm (k : ℕ) [NeZero k] : Euc ((k - 1) + 1) →L[ℝ] Euc k :=
  (reindexFibre k).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- **The trivialization**, in the coordinates of the fibre disc `Ball (k-1)`. -/
noncomputable def insFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) : Euc ((k - 1) + 1) →L[ℝ] Euc (8 + k) :=
  (insF C i x).comp (reindexFibreCLMsymm k)

/-- **The inverse trivialization**, in the coordinates of the fibre disc `Ball (k-1)`. -/
noncomputable def readFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) : Euc (8 + k) →L[ℝ] Euc ((k - 1) + 1) :=
  (reindexFibreCLM k).comp (readF C i x)

/-- **The change of trivialization**, in the coordinates of the fibre disc. -/
noncomputable def frameChangeE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) (x : V.pt) : Euc ((k - 1) + 1) →L[ℝ] Euc ((k - 1) + 1) :=
  (readFE C j x).comp (insFE C i x)

theorem insFE_apply {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) (c : Euc ((k - 1) + 1)) :
    insFE C i x c = insF C i x ((reindexFibre k).symm c) := rfl

theorem readFE_apply {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) (v : Euc (8 + k)) :
    readFE C i x v = reindexFibre k (readF C i x v) := rfl

theorem frameChangeE_apply {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) (x : V.pt) (c : Euc ((k - 1) + 1)) :
    frameChangeE C i j x c = reindexFibre k (frameChange C i j x ((reindexFibre k).symm c)) := rfl

theorem readFE_insFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (c : Euc ((k - 1) + 1)) :
    readFE C i x (insFE C i x c) = c := by
  rw [readFE_apply, insFE_apply, readF_insF C i hx]
  exact (reindexFibre k).apply_symm_apply c

theorem insFE_readFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) {v : Euc (8 + k)} (hv : v ∈ normalSpace E x) :
    insFE C i x (readFE C i x v) = v := by
  rw [readFE_apply, insFE_apply, (reindexFibre k).symm_apply_apply]
  exact insF_readF C i hx hv

theorem norm_insFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (c : Euc ((k - 1) + 1)) :
    ‖insFE C i x c‖ = ‖c‖ := by
  rw [insFE_apply, norm_insF C i hx, (reindexFibre k).symm.norm_map]

theorem insFE_mem {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (c : Euc ((k - 1) + 1)) :
    insFE C i x c ∈ normalSpace E x := by
  rw [insFE_apply]
  exact insF_mem C i hx _

theorem norm_readF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) {v : Euc (8 + k)} (hv : v ∈ normalSpace E x) :
    ‖readF C i x v‖ = ‖v‖ := by
  rw [← norm_insF C i hx (readF C i x v), insF_readF C i hx hv]

theorem norm_frameChangeE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) {x : V.pt} (hxi : x ∈ coverBaseSet E.e i)
    (hxj : x ∈ coverBaseSet E.e j) (c : Euc ((k - 1) + 1)) :
    ‖frameChangeE C i j x c‖ = ‖c‖ := by
  rw [frameChangeE_apply, (reindexFibre k).norm_map, frameChange,
    ContinuousLinearMap.comp_apply, norm_readF C j hxj (insF_mem C i hxi _), norm_insF C i hxi,
    (reindexFibre k).symm.norm_map]

/-! ## Smoothness and continuity in the fibre coordinates -/

theorem contDiffOn_readFE_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) (x₀ : V.pt) :
    ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc (8 + k) => readFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2)
      (chartCover E i x₀ ×ˢ Set.univ) :=
  ((reindexFibreCLM k).contDiff.comp_contDiffOn (contDiffOn_readF_chart C i x₀)).congr
    fun p _ => rfl

theorem contDiffOn_insFE_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) (x₀ : V.pt) :
    ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc ((k - 1) + 1) => insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2)
      (chartCover E i x₀ ×ˢ Set.univ) := by
  have hlin : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc ((k - 1) + 1) => (p.1, (reindexFibreCLMsymm k) p.2))
      (chartCover E i x₀ ×ˢ Set.univ) :=
    ((contDiff_fst.prodMk ((reindexFibreCLMsymm k).contDiff.comp contDiff_snd)).contDiffOn).mono
      (Set.subset_univ _)
  exact ((contDiffOn_insF_chart C i x₀).comp hlin (fun p hp => ⟨hp.1, Set.mem_univ _⟩)).congr
    fun p _ => rfl

theorem contDiffOn_readF_insFE_chart {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i j : CoverIdx V k) (x₀ : V.pt) :
    ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc ((k - 1) + 1) =>
        readF C j ((chartAt (Euc 8) x₀).symm p.1)
          (insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2))
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := by
  have hcoord : ∀ l : Fin k, ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc ((k - 1) + 1) =>
        euclCLM k (readF C j ((chartAt (Euc 8) x₀).symm p.1)
          (insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2)) l)
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := by
    intro l
    have hb : ContDiffOn ℝ 1
        (fun p : Euc 8 × Euc ((k - 1) + 1) =>
          ⟪orthTubeFrame C j ((chartAt (Euc 8) x₀).symm p.1) l,
            insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2⟫_ℝ)
        ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) :=
      ((contDiffOn_orthTubeFrame_chart C j x₀ l).comp contDiffOn_fst
        (fun p hp => hp.1.2)).inner ℝ
        ((contDiffOn_insFE_chart C i x₀).mono
          (Set.prod_mono Set.inter_subset_left Set.Subset.rfl))
    exact hb.congr fun p hp =>
      readF_coord C j hp.1.2.2 (insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2) l
  have hpi : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc ((k - 1) + 1) =>
        euclCLM k (readF C j ((chartAt (Euc 8) x₀).symm p.1)
          (insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2)))
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) := contDiffOn_pi' hcoord
  have hcomp : ContDiffOn ℝ 1
      (fun p : Euc 8 × Euc ((k - 1) + 1) =>
        (EuclideanSpace.equiv (Fin k) ℝ).symm
          (euclCLM k (readF C j ((chartAt (Euc 8) x₀).symm p.1)
            (insFE C i ((chartAt (Euc 8) x₀).symm p.1) p.2))))
      ((chartCover E i x₀ ∩ chartCover E j x₀) ×ˢ Set.univ) :=
    ((EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff).contDiffOn.comp hpi
      (fun p _ => Set.mem_univ _)
  exact hcomp.congr fun p _ => (EuclideanSpace.equiv (Fin k) ℝ).symm_apply_apply _

theorem continuousOn_readFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) :
    ContinuousOn (fun p : V.pt × Euc (8 + k) => readFE C i p.1 p.2)
      (coverBaseSet E.e i ×ˢ Set.univ) :=
  ((reindexFibreCLM k).continuous.comp_continuousOn (continuousOn_readF C i)).congr
    fun p _ => rfl

theorem continuousOn_insFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) :
    ContinuousOn (fun p : V.pt × Euc ((k - 1) + 1) => insFE C i p.1 p.2)
      (coverBaseSet E.e i ×ˢ Set.univ) := by
  have hlin : Continuous (fun p : V.pt × Euc ((k - 1) + 1) =>
      (p.1, (reindexFibreCLMsymm k) p.2)) :=
    continuous_fst.prodMk ((reindexFibreCLMsymm k).continuous.comp continuous_snd)
  exact ((continuousOn_insF C i).comp hlin.continuousOn
    (fun p hp => ⟨hp.1, Set.mem_univ _⟩)).congr fun p _ => rfl

end

end Work.Tubular
