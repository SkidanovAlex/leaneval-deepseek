import Submission.Work.Tubular.DiscManifold.TubeFrame
import Submission.Work.Tubular.DiscManifold.contDiffOn_gramSchmidtNormed

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The orthonormal normal frame and the trivialization of the normal bundle
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-! ## The orthonormal frame -/

/-- **The orthonormal normal frame**: Gram–Schmidt applied to the normal frame `tubeFrame`. -/
def orthTubeFrame {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) : Fin k → Euc (8 + k) :=
  fun l => InnerProductSpace.gramSchmidtNormed ℝ (tubeFrame C i x) l

theorem orthTubeFrame_orthonormal {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ coverBaseSet E.e i) :
    Orthonormal ℝ (orthTubeFrame C i x) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal (tubeFrame_linearIndependent C i hx)

theorem orthTubeFrame_span {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ coverBaseSet E.e i) :
    Submodule.span ℝ (Set.range (orthTubeFrame C i x)) = normalSpace E x := by
  rw [show Set.range (orthTubeFrame C i x)
      = InnerProductSpace.gramSchmidtNormed ℝ (tubeFrame C i x) '' Set.univ from
    Set.image_univ.symm]
  rw [InnerProductSpace.span_gramSchmidtNormed, Set.image_univ]
  rw [InnerProductSpace.span_gramSchmidt]
  exact tubeFrame_span C i hx

theorem orthTubeFrame_mem {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (l : Fin k) :
    orthTubeFrame C i x l ∈ normalSpace E x := by
  rw [← orthTubeFrame_span C i hx]
  exact Submodule.subset_span ⟨l, rfl⟩

/-! ## Coordinates on `ℝⁿ` -/

/-- The canonical continuous linear map `ℝⁿ → (Fin n → ℝ)`. -/
def euclCLM (n : ℕ) : Euc n →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

theorem euclCLM_apply (n : ℕ) (x : Euc n) : euclCLM n x = x.ofLp := rfl

theorem euclCLM_injective (n : ℕ) : Function.Injective (euclCLM n) := fun a b h =>
  (EuclideanSpace.equiv (Fin n) ℝ).injective h

theorem euclCLM_single (m : ℕ) (l : Fin m) :
    euclCLM m (EuclideanSpace.single l (1 : ℝ)) = Pi.single l (1 : ℝ) := by
  funext j
  rw [euclCLM_apply, EuclideanSpace.single_apply, Pi.single_apply]

/-- The `l`-th coordinate functional is the inner product with the `l`-th standard basis vector. -/
theorem euclCLM_eq_inner_single {m : ℕ} (w : Euc m) (l : Fin m) :
    euclCLM m w l = ⟪EuclideanSpace.single l (1 : ℝ), w⟫_ℝ := by
  rw [euclCLM_apply, EuclideanSpace.inner_single_left]
  simp

/-! ## The trivialization of the normal bundle -/

/-- **The trivialization of the normal bundle**: the linear map which sends the standard basis of
`ℝ^k` to the orthonormal frame of `ν_x`. -/
def insF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) (x : V.pt) :
    Euc k →L[ℝ] Euc (8 + k) :=
  ∑ l : Fin k, ((ContinuousLinearMap.proj l).comp (euclCLM k)).smulRight
    (orthTubeFrame C i x l)

/-- **The inverse trivialization**, defined as the adjoint of `insF`. -/
def readF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k) (x : V.pt) :
    Euc (8 + k) →L[ℝ] Euc k :=
  (insF C i x)†

theorem insF_apply {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) (c : Euc k) :
    insF C i x c = ∑ l : Fin k, euclCLM k c l • orthTubeFrame C i x l := by
  simp only [insF, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, euclCLM_apply]

theorem insF_single {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (x : V.pt) (l : Fin k) :
    insF C i x (EuclideanSpace.single l (1 : ℝ)) = orthTubeFrame C i x l := by
  rw [insF_apply]
  rw [Finset.sum_congr rfl (fun m _ => by rw [euclCLM_single, Pi.single_apply])]
  rw [Finset.sum_eq_single l]
  · simp
  · intro m _ hm
    rw [if_neg hm, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

theorem insF_mem {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (c : Euc k) :
    insF C i x c ∈ normalSpace E x := by
  rw [insF_apply]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (orthTubeFrame_mem C i hx l)

theorem readF_coord {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (v : Euc (8 + k)) (l : Fin k) :
    euclCLM k (readF C i x v) l = ⟪orthTubeFrame C i x l, v⟫_ℝ :=
  calc euclCLM k (readF C i x v) l
      = ⟪EuclideanSpace.single l (1 : ℝ), readF C i x v⟫_ℝ := euclCLM_eq_inner_single _ _
    _ = ⟪readF C i x v, EuclideanSpace.single l (1 : ℝ)⟫_ℝ := real_inner_comm _ _
    _ = ⟪v, insF C i x (EuclideanSpace.single l (1 : ℝ))⟫_ℝ := by
          rw [readF]; exact ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪v, orthTubeFrame C i x l⟫_ℝ := by rw [insF_single]
    _ = ⟪orthTubeFrame C i x l, v⟫_ℝ := real_inner_comm _ _

theorem readF_insF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (c : Euc k) :
    readF C i x (insF C i x c) = c := by
  apply euclCLM_injective k
  funext l
  rw [readF_coord C i hx, insF_apply,
    (orthTubeFrame_orthonormal C i hx).inner_right_fintype (fun m => euclCLM k c m) l]

theorem insF_readF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) {v : Euc (8 + k)} (hv : v ∈ normalSpace E x) :
    insF C i x (readF C i x v) = v := by
  have hspan : v ∈ Submodule.span ℝ (Set.range (orthTubeFrame C i x)) := by
    rw [orthTubeFrame_span C i hx]; exact hv
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← insF_single C i x m, readF_insF C i hx, insF_single]

theorem inner_insF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (a b : Euc k) :
    ⟪insF C i x a, insF C i x b⟫_ℝ = ⟪a, b⟫_ℝ := by
  rw [insF_apply, insF_apply,
    (orthTubeFrame_orthonormal C i hx).inner_sum (fun l => euclCLM k a l)
      (fun m => euclCLM k b m) Finset.univ]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [euclCLM_apply, euclCLM_apply, starRingEnd_apply, star_trivial, Real.inner_apply]

theorem norm_insF {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) (c : Euc k) :
    ‖insF C i x c‖ = ‖c‖ := by
  have h1 : ⟪insF C i x c, insF C i x c⟫_ℝ = ⟪c, c⟫_ℝ := inner_insF C i hx c c
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

end

end Work.Tubular
