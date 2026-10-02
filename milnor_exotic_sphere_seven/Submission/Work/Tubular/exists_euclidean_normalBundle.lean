import Mathlib
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Rank
import Submission.Work.Tubular.normalTotalIso
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion
import Submission.Work.ThomBordism.PontryaginThom.Frames
import Submission.Work.ThomBordism.PontryaginThom.Orthogonal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The normal bundle of an embedded manifold as a Euclidean real bundle

For a compact smooth `8`-manifold `V` embedded in `ℝ^{8+k}` (`E : EmbeddingData V (8 + k)`), the
concrete normal bundle `Work.Tubular.NormalTotal E ⊆ V.pt × ℝ^{8+k}` of the embedding is the total
space of a **Euclidean real vector bundle of rank `k`**: there is a real bundle `ν` over `V.pt`
with fibre `Euc k = ℝ^k` whose transition functions preserve the fibre norm
(`Work.Thom.IsEuclidean ν`), together with a homeomorphism `ν.TotalSpace ≃ₜ NormalTotal E` that
preserves the fibrewise norms.

This is the bridge recorded in `Submission/Work/Tubular/README.md` §9: it makes the `Work.Thom`
disc/sphere/Thom-class machinery (stated for gluing-data bundles with a Euclidean structure)
applicable to the normal bundle of an embedded manifold.  In particular the repair of
`Work.Tubular.fibreNorm_not_continuous` is implemented here: the bundle is built from *isometric*
trivialisations, so that `Work.Thom.fibreNorm` really is the pullback of `normalNorm E`.

## The construction

* `chartVecLM` — the linear parametrisation `v ↦ orthInj (frame i x) (I i x v)` of the normal space
  `ν_x` in the chart `(i,S)` of the cover of `NormalData` (the map underlying
  `Work.Tubular.normalChartVec`), with `range_chartVecLM : range = ν_x`;
* `rawFrame` / `orthFrame` — the associated frame and its Gram–Schmidt orthonormalisation: an
  orthonormal frame of `ν_x` depending continuously on `x` (`orthFrame_orthonormal`,
  `continuousOn_orthFrame`, `span_orthFrame`, `orthFrame_mem`);
* `insCLM` / `readCLM` — the isometric insertion `Euc k → ν_x ⊆ ℝ^{8+k}` and its inverse
  (`readCLM_insCLM`, `insCLM_readCLM_of_mem`), both norm-preserving (`norm_insCLM`,
  `readCLM_norm_of_mem`) and continuous in the base point (`continuousOn_insCLM`,
  `continuousOn_readCLM`);
* `normalBundle` — the bundle whose transition functions are
  `coordChange i j x = readCLM j x ∘ insCLM i x`, Euclidean because both factors are isometries
  (`isEuclidean_normalBundle`);
* `eucNormalHomeomorph` — the norm-preserving homeomorphism `ν.TotalSpace ≃ₜ NormalTotal E`
  (`fibreNorm_eq_normalNorm`).

Two Mathlib gaps the construction needs are proved at the top of the file:
`continuousOn_gramSchmidtNormed` (Gram–Schmidt is continuous along a family that is everywhere
linearly independent) and `sum_inner_smul_eq_self_of_mem_span` (the Fourier expansion of a vector
of the span of an orthonormal family).
-/

open scoped Manifold ContDiff Topology
open Function Topology

namespace Work.Tubular

open Work.ThomBordism.PontryaginThom
open Work.TangentClasses

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Mathlib gaps used by the construction -/

theorem continuousOn_gramSchmidt {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ι → E}
    (hf : ∀ i, ContinuousOn (fun x => f x i) s)
    (hlin : ∀ x ∈ s, LinearIndependent 𝕜 (f x)) (n : ι) :
    ContinuousOn (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) n) s := by
  refine (wellFounded_lt.induction (C := fun m => ContinuousOn (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) m) s) n) ?_
  intro n ih
  have hstep : (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) n) =
      fun x => f x n - ∑ i ∈ Finset.Iio n, (𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 (f x) i).starProjection (f x n) := by
    funext x
    rw [InnerProductSpace.gramSchmidt_def]
  rw [hstep]
  refine ContinuousOn.sub (hf n) ?_
  refine continuousOn_finsetSum _ fun i hi => ?_
  have hi' : i < n := Finset.mem_Iio.mp hi
  have hGi : ContinuousOn (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) i) s := ih i hi'
  have hGne : ∀ x ∈ s, InnerProductSpace.gramSchmidt 𝕜 (f x) i ≠ 0 := fun x hx =>
    InnerProductSpace.gramSchmidt_ne_zero_coe (𝕜 := 𝕜) (f := f x) i
      (LinearIndependent.comp (hlin x hx) _ Subtype.coe_injective)
  rw [show (fun x => (𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 (f x) i).starProjection (f x n))
      = fun x => (inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i) (f x n)
          / (↑(‖InnerProductSpace.gramSchmidt 𝕜 (f x) i‖ ^ 2) : 𝕜)) • InnerProductSpace.gramSchmidt 𝕜 (f x) i from by
    funext x; rw [Submodule.starProjection_singleton]]
  have hnum : ContinuousOn (fun x => inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i) (f x n)) s :=
    ContinuousOn.inner hGi (hf n)
  have hden : ContinuousOn (fun x => (↑(‖InnerProductSpace.gramSchmidt 𝕜 (f x) i‖ ^ 2) : 𝕜)) s :=
    RCLike.continuous_ofReal.comp_continuousOn (hGi.norm.pow 2)
  have hdenne : ∀ x ∈ s, (↑(‖InnerProductSpace.gramSchmidt 𝕜 (f x) i‖ ^ 2) : 𝕜) ≠ 0 := by
    intro x hx h
    have h1 : ‖InnerProductSpace.gramSchmidt 𝕜 (f x) i‖ ^ 2 = 0 :=
      RCLike.ofReal_injective (by rw [h]; simp)
    have h2 : ‖InnerProductSpace.gramSchmidt 𝕜 (f x) i‖ = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    exact hGne x hx (norm_eq_zero.mp h2)
  exact (hnum.div hden hdenne).smul hGi

theorem continuousOn_gramSchmidtNormed {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ι → E}
    (hf : ∀ i, ContinuousOn (fun x => f x i) s)
    (hlin : ∀ x ∈ s, LinearIndependent 𝕜 (f x)) (n : ι) :
    ContinuousOn (fun x => InnerProductSpace.gramSchmidtNormed 𝕜 (f x) n) s := by
  have hG : ContinuousOn (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) n) s :=
    continuousOn_gramSchmidt hf hlin n
  have hGne : ∀ x ∈ s, InnerProductSpace.gramSchmidt 𝕜 (f x) n ≠ 0 := fun x hx =>
    InnerProductSpace.gramSchmidt_ne_zero_coe (𝕜 := 𝕜) (f := f x) n
      (LinearIndependent.comp (hlin x hx) _ Subtype.coe_injective)
  rw [show (fun x => InnerProductSpace.gramSchmidtNormed 𝕜 (f x) n)
      = fun x => (↑(‖InnerProductSpace.gramSchmidt 𝕜 (f x) n‖) : 𝕜)⁻¹
          • InnerProductSpace.gramSchmidt 𝕜 (f x) n from by
    funext x; rw [InnerProductSpace.gramSchmidtNormed]]
  refine ContinuousOn.smul ?_ hG
  refine ContinuousOn.inv₀ (RCLike.continuous_ofReal.comp_continuousOn hG.norm) ?_
  intro x hx h
  exact hGne x hx (norm_eq_zero.mp (RCLike.ofReal_injective (by rw [h]; simp)))

theorem sum_inner_smul_eq_self_of_mem_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] {u : ι → E} (hu : Orthonormal ℝ u) {w : E}
    (hw : w ∈ Submodule.span ℝ (Set.range u)) :
    ∑ i, inner ℝ (u i) w • u i = w := by
  classical
  refine Submodule.span_induction (p := fun w _ => ∑ i, inner ℝ (u i) w • u i = w) ?_ ?_ ?_ ?_ hw
  · rintro y ⟨j, rfl⟩
    rw [Finset.sum_eq_single j]
    · rw [orthonormal_iff_ite.mp hu j j, if_pos rfl, one_smul]
    · intro i _ hij
      rw [orthonormal_iff_ite.mp hu i j, if_neg hij, zero_smul]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · rw [Finset.sum_eq_zero]
    intro i _
    rw [inner_zero_right, zero_smul]
  · intro x y hx hy ihx ihy
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, ihx, ihy]
  · intro c x hx ih
    rw [show (∑ i, inner ℝ (u i) (c • x) • u i)
        = c • (∑ i, inner ℝ (u i) x • u i) from by
      simp_rw [inner_smul_right]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul], ih]

theorem norm_map_eq_of_orthonormal_single {k : ℕ} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : EuclideanSpace ℝ (Fin k) →L[ℝ] F)
    (hT : Orthonormal ℝ (fun j : Fin k => T (EuclideanSpace.single j 1)))
    (v : EuclideanSpace ℝ (Fin k)) : ‖T v‖ = ‖v‖ := by
  have hb : Orthonormal ℝ ⇑(EuclideanSpace.basisFun (Fin k) ℝ).toBasis :=
    OrthonormalBasis.orthonormal (EuclideanSpace.basisFun (Fin k) ℝ)
  have hf : Orthonormal ℝ ((T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] F)
      ∘ ⇑(EuclideanSpace.basisFun (Fin k) ℝ).toBasis) := by
    have htop : ((T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] F)
        ∘ ⇑(EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        = fun j : Fin k => T (EuclideanSpace.single j 1) := by
      funext j
      simp only [Function.comp_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      rfl
    rw [htop]
    exact hT
  exact LinearIsometry.norm_map (LinearMap.isometryOfOrthonormal (𝕜 := ℝ)
    (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] F) hb hf) v

/-- **Continuity of a map into a subtype, from an equality with an ambient-valued map.**  This
is the `ContinuousOn` version of `Continuous.subtype_mk`. -/
theorem continuousOn_subtype_of_eqOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : Y → Prop} {f : X → Y} {s : Set X} (g : X → Subtype p)
    (hf : ContinuousOn f s) (hg : ∀ x ∈ s, (g x : Y) = f x) : ContinuousOn g s := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_induced_rng]
  exact hf.domRestrict.congr (fun x => (hg x.1 x.2).symm)

/-! ## The frame of the normal space in a chart -/

/-- The parametrisation of the normal space `ν_x` in the chart index `i`, in the coordinates of the
gluing data: `v ↦ orthInj (frame i x) (I i x v)`.  Its linearity (unlike the definitional form of
`normalChartVec`) is what the linear algebra below uses. -/
def chartVecLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : (Fin k → ℝ) →ₗ[ℝ] Euc (8 + k) :=
  (funToEuc (8 + k)).toLinearMap.comp
    ((orthInj (frame E.e (coverChart i) x)).comp ((ND.D.I i x).toLinearMap))

@[simp] theorem chartVecLM_apply (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (v : Fin k → ℝ) :
    chartVecLM E ND i x v = normalChartVec E ND i x v := rfl

/-- The raw frame of `ν_x` in the chart index `i`: the images of the coordinate basis vectors. -/
def rawFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Fin k → Euc (8 + k) :=
  fun j => chartVecLM E ND i x (Pi.single j 1)

/-- The orthonormal frame of `ν_x` in the chart index `i`, by Gram–Schmidt. -/
def orthFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Fin k → Euc (8 + k) :=
  fun j => InnerProductSpace.gramSchmidtNormed ℝ (rawFrame E ND i x) j

theorem chartVecLM_injective (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Function.Injective (chartVecLM E ND i x) := by
  intro u v huv
  have h1 : (ND.D.P i x) (eucToFun (8 + k) (chartVecLM E ND i x u)) = u := by
    rw [chartVecLM_apply, eucToFun_normalChartVec, P_orthInj E ND hx, P_I_apply E ND i x u]
  have h2 : (ND.D.P i x) (eucToFun (8 + k) (chartVecLM E ND i x v)) = v := by
    rw [chartVecLM_apply, eucToFun_normalChartVec, P_orthInj E ND hx, P_I_apply E ND i x v]
  rw [huv] at h1
  rw [h1] at h2
  exact h2

/-- The expansion of a vector of `ℝ^k` in the standard basis. -/
theorem sum_smul_single_eq_self (k : ℕ) (c : Fin k → ℝ) :
    ∑ j : Fin k, c j • (Pi.single j 1 : Fin k → ℝ) = c := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro j _ hj; rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The expansion of a vector of `ℝ^k` in the standard basis of `Euc k`. -/
theorem sum_smul_single_eq_funToEuc (k : ℕ) (c : Fin k → ℝ) :
    ∑ j : Fin k, c j • EuclideanSpace.single j 1 = funToEuc k c := by
  apply eucToFun_injective k
  rw [map_sum, eucToFun_funToEuc]
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, eucToFun_apply, Pi.smul_apply, PiLp.single_apply, if_pos rfl, smul_eq_mul,
      mul_one]
  · intro j _ hj
    rw [map_smul, eucToFun_apply, Pi.smul_apply, PiLp.single_apply, if_neg (Ne.symm hj),
      smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem rawFrame_linIndependent (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    LinearIndependent ℝ (rawFrame E ND i x) := by
  have hinj : Function.Injective (chartVecLM E ND i x) := chartVecLM_injective E ND i hx
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : chartVecLM E ND i x (∑ j : Fin k, c j • (Pi.single j 1 : Fin k → ℝ)) = 0 := by
    rw [map_sum]
    simp only [map_smul]
    rw [show (∑ j : Fin k, c j • chartVecLM E ND i x (Pi.single j 1))
        = ∑ j : Fin k, c j • rawFrame E ND i x j from rfl, hc]
  have h1 : (∑ j : Fin k, c j • (Pi.single j 1 : Fin k → ℝ)) = 0 := hinj (by rw [h0, map_zero])
  rw [sum_smul_single_eq_self k c] at h1
  intro i
  exact congrFun h1 i

theorem range_chartVecLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    LinearMap.range (chartVecLM E ND i x) = normalSpace E x := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, rfl⟩
    rw [chartVecLM_apply]
    exact normalChartVec_mem E ND i hx v
  · intro w hw
    refine ⟨(ND.D.P i x) (eucToFun (8 + k) w), ?_⟩
    rw [chartVecLM_apply]
    refine eucToFun_injective (8 + k) ?_
    rw [eucToFun_normalChartVec, orthInj_I_P E ND hx (eucToFun (8 + k) w)]
    exact (orthInj_eucToFun_eq_self_iff E (coverChart i)
      (ND.baseSet_sub i.1 i.2 x hx) w).mpr hw

theorem span_rawFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Submodule.span ℝ (Set.range (rawFrame E ND i x)) = normalSpace E x := by
  have h : Submodule.span ℝ (Set.range (rawFrame E ND i x))
      = LinearMap.range (chartVecLM E ND i x) := by
    rw [show (rawFrame E ND i x) = fun j : Fin k => chartVecLM E ND i x (Pi.single j 1) from rfl]
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨j, rfl⟩
      exact ⟨Pi.single j 1, rfl⟩
    · rintro _ ⟨v, rfl⟩
      have hv : v = ∑ j, v j • Pi.single j 1 := (sum_smul_single_eq_self k v).symm
      rw [hv, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  rw [h, range_chartVecLM E ND i hx]

theorem orthFrame_orthonormal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Orthonormal ℝ (orthFrame E ND i x) := by
  rw [show orthFrame E ND i x
      = InnerProductSpace.gramSchmidtNormed ℝ (rawFrame E ND i x) from rfl]
  exact InnerProductSpace.gramSchmidtNormed_orthonormal (rawFrame_linIndependent E ND i hx)

theorem span_orthFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Submodule.span ℝ (Set.range (orthFrame E ND i x)) = normalSpace E x := by
  have h1 : Submodule.span ℝ (Set.range (orthFrame E ND i x))
      = Submodule.span ℝ (Set.range (rawFrame E ND i x)) := by
    rw [show (orthFrame E ND i x)
        = InnerProductSpace.gramSchmidtNormed ℝ (rawFrame E ND i x) from rfl,
      InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]
  rw [h1, span_rawFrame E ND i hx]

theorem orthFrame_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (j : Fin k) :
    orthFrame E ND i x j ∈ normalSpace E x := by
  have h : orthFrame E ND i x j ∈ Submodule.span ℝ (Set.range (orthFrame E ND i x)) :=
    Submodule.subset_span (Set.mem_range_self j)
  rwa [span_orthFrame E ND i hx] at h

/-! ## Continuity of the frame -/

theorem continuousOn_rawFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (j : Fin k) :
    ContinuousOn (fun x => rawFrame E ND i x j) (ND.D.baseSet i) := by
  have horth : ContinuousOn (fun x => LinearMap.toContinuousLinearMap
      (orthInj (frame E.e (coverChart i) x))) (ND.D.baseSet i) :=
    (continuousOn_orthInj_frame E (coverChart i)).mono
      (fun x hx => ND.baseSet_sub i.1 i.2 x hx)
  have hI : ContinuousOn (fun x : V.pt => (ND.D.I i x) (Pi.single j 1)) (ND.D.baseSet i) :=
    (ND.D.continuousOn_I i).clm_apply continuousOn_const
  have hmain := horth.clm_apply hI
  have hfin := (funToEuc (8 + k)).continuous.comp_continuousOn hmain
  refine hfin.congr (fun x hx => ?_)
  simp only [Function.comp_apply, rawFrame, chartVecLM, LinearMap.comp_apply]
  rfl

theorem continuousOn_orthFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (j : Fin k) :
    ContinuousOn (fun x => orthFrame E ND i x j) (ND.D.baseSet i) :=
  continuousOn_gramSchmidtNormed (𝕜 := ℝ) (fun j => continuousOn_rawFrame E ND i j)
    (fun x hx => rawFrame_linIndependent E ND i hx) j

/-! ## The isometric insertion and the reading map -/

/-- The isometric insertion `ℝ^k → ν_x ⊆ ℝ^{8+k}` given by the orthonormal frame. -/
def insCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Euc k →L[ℝ] Euc (8 + k) :=
  ∑ j : Fin k, (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (orthFrame E ND i x j)

/-- The reading map `ℝ^{8+k} → ℝ^k`: the coordinates in the orthonormal frame. -/
def readCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Euc (8 + k) →L[ℝ] Euc k :=
  (funToEuc k).comp (∑ j : Fin k, (innerSL ℝ (orthFrame E ND i x j)).smulRight
    (Pi.single j 1 : Fin k → ℝ))

theorem insCLM_apply (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (v : Euc k) :
    insCLM E ND i x v = ∑ j : Fin k, eucToFun k v j • orthFrame E ND i x j := by
  simp only [insCLM, sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
    eucToFun_apply]

theorem readCLM_apply (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (w : Euc (8 + k)) :
    readCLM E ND i x w
      = funToEuc k (fun j : Fin k => inner ℝ (orthFrame E ND i x j) w) := by
  simp only [readCLM, ContinuousLinearMap.comp_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  congr 1
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, innerSL_apply_apply, smul_eq_mul, mul_one]
  · intro l _ hlj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hlj), innerSL_apply_apply, smul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem insCLM_single (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (j : Fin k) :
    insCLM E ND i x (EuclideanSpace.single j 1) = orthFrame E ND i x j := by
  rw [insCLM_apply, Finset.sum_eq_single j]
  · rw [eucToFun_apply, PiLp.single_apply, if_pos rfl, one_smul]
  · intro l _ hlj
    rw [eucToFun_apply, PiLp.single_apply, if_neg hlj, zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem norm_insCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (v : Euc k) :
    ‖insCLM E ND i x v‖ = ‖v‖ := by
  refine norm_map_eq_of_orthonormal_single (insCLM E ND i x) ?_ v
  rw [show (fun j : Fin k => insCLM E ND i x (EuclideanSpace.single j 1))
      = orthFrame E ND i x from funext (fun j => insCLM_single E ND i x j)]
  exact orthFrame_orthonormal E ND i hx

theorem insCLM_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (v : Euc k) :
    insCLM E ND i x v ∈ normalSpace E x := by
  rw [insCLM_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (orthFrame_mem E ND i hx j)

theorem readCLM_insCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (v : Euc k) :
    readCLM E ND i x (insCLM E ND i x v) = v := by
  rw [readCLM_apply, insCLM_apply]
  have h1 : (fun l : Fin k => inner ℝ (orthFrame E ND i x l)
      (∑ j : Fin k, eucToFun k v j • orthFrame E ND i x j)) = eucToFun k v := by
    funext l
    exact (orthFrame_orthonormal E ND i hx).inner_right_fintype (fun j => eucToFun k v j) l
  rw [h1]
  exact funToEuc_eucToFun k v

theorem insCLM_readCLM_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) {w : Euc (8 + k)}
    (hw : w ∈ normalSpace E x) :
    insCLM E ND i x (readCLM E ND i x w) = w := by
  rw [readCLM_apply, insCLM_apply, eucToFun_funToEuc]
  exact sum_inner_smul_eq_self_of_mem_span (orthFrame_orthonormal E ND i hx)
    (by rw [span_orthFrame E ND i hx]; exact hw)

theorem readCLM_norm_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) {w : Euc (8 + k)}
    (hw : w ∈ normalSpace E x) : ‖readCLM E ND i x w‖ = ‖w‖ := by
  rw [← norm_insCLM E ND i hx (readCLM E ND i x w), insCLM_readCLM_of_mem E ND i hx hw]

/-! ## Continuity of the insertion and the reading map -/

theorem continuousOn_insCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x => insCLM E ND i x) (ND.D.baseSet i) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_clm_apply]
  intro v
  have hframe : ∀ j : Fin k, Continuous fun x : ↥(ND.D.baseSet i) =>
      orthFrame E ND i (x : V.pt) j := fun j =>
    (continuousOn_orthFrame E ND i j).comp_continuous continuous_subtype_val (fun x => x.2)
  have hsum : Continuous fun x : ↥(ND.D.baseSet i) =>
      ∑ j : Fin k, eucToFun k v j • orthFrame E ND i (x : V.pt) j :=
    continuous_finsetSum (Finset.univ : Finset (Fin k)) fun j _ =>
      (continuous_const : Continuous fun _ : ↥(ND.D.baseSet i) => eucToFun k v j).smul
        (hframe j)
  refine hsum.congr (fun x => ?_)
  show (∑ j : Fin k, eucToFun k v j • orthFrame E ND i (x : V.pt) j)
      = (insCLM E ND i (x : V.pt)) v
  rw [insCLM_apply]

theorem continuousOn_readCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x => readCLM E ND i x) (ND.D.baseSet i) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_clm_apply]
  intro w
  have hpi : Continuous fun x : ↥(ND.D.baseSet i) =>
      (fun j : Fin k => inner ℝ (orthFrame E ND i (x : V.pt) j) w) :=
    continuous_pi_iff.mpr fun j =>
      Continuous.inner ((continuousOn_orthFrame E ND i j).comp_continuous continuous_subtype_val
        (fun x => x.2)) continuous_const
  have hfun : Continuous fun x : ↥(ND.D.baseSet i) =>
      funToEuc k (fun j : Fin k => inner ℝ (orthFrame E ND i (x : V.pt) j) w) :=
    (funToEuc k).continuous.comp hpi
  refine hfun.congr (fun x => ?_)
  show funToEuc k (fun j : Fin k => inner ℝ (orthFrame E ND i (x : V.pt) j) w)
      = (readCLM E ND i (x : V.pt)) w
  rw [readCLM_apply]

/-! ## The bundle -/

/-- The transition function of the Euclidean normal bundle: from the chart `i` to the chart `j`,
read the insertion in the orthonormal frame of the chart `j`. -/
def transFun (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) (x : V.pt) : Euc k →L[ℝ] Euc k := by
  classical
  exact if x ∈ ND.D.baseSet i ∧ x ∈ ND.D.baseSet j then (readCLM E ND j x).comp (insCLM E ND i x)
    else 0

theorem transFun_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i ∧ x ∈ ND.D.baseSet j) :
    transFun E ND i j x = (readCLM E ND j x).comp (insCLM E ND i x) := by
  classical
  rw [transFun, if_pos hx]

theorem transFun_of_notMem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) (x : V.pt) (hx : ¬ (x ∈ ND.D.baseSet i ∧ x ∈ ND.D.baseSet j)) :
    transFun E ND i j x = 0 := by
  classical
  rw [transFun, if_neg hx]

theorem continuousOn_transFun (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) :
    ContinuousOn (fun x => transFun E ND i j x)
      (ND.D.baseSet i ∩ ND.D.baseSet j) := by
  have hmain : ContinuousOn (fun x => (readCLM E ND j x).comp (insCLM E ND i x))
      (ND.D.baseSet i ∩ ND.D.baseSet j) :=
    ContinuousOn.clm_comp ((continuousOn_readCLM E ND j).mono Set.inter_subset_right)
      ((continuousOn_insCLM E ND i).mono Set.inter_subset_left)
  refine hmain.congr (fun x hx => ?_)
  rw [transFun_of_mem E ND i j x hx]

theorem transFun_self (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) (v : Euc k) :
    transFun E ND i i x v = v := by
  rw [transFun_of_mem E ND i i x ⟨hx, hx⟩, ContinuousLinearMap.comp_apply,
    readCLM_insCLM E ND i hx v]

theorem transFun_comp (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j l : CoverIdx V k) (x : V.pt)
    (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j ∩ ND.D.baseSet l) (v : Euc k) :
    transFun E ND j l x (transFun E ND i j x v) = transFun E ND i l x v := by
  have hx1 : x ∈ ND.D.baseSet i := hx.1.1
  have hx2 : x ∈ ND.D.baseSet j := hx.1.2
  have hx3 : x ∈ ND.D.baseSet l := hx.2
  rw [transFun_of_mem E ND j l x ⟨hx2, hx3⟩, transFun_of_mem E ND i j x ⟨hx1, hx2⟩,
    transFun_of_mem E ND i l x ⟨hx1, hx3⟩, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [insCLM_readCLM_of_mem E ND j hx2 (insCLM_mem E ND i hx1 v)]

/-- The **Euclidean real bundle** of the normal bundle of the embedding, with fibre `ℝ^k`. -/
def normalBundle (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    RealBundle V.pt (Euc k) (CoverIdx V k) where
  baseSet := ND.D.baseSet
  isOpen_baseSet := ND.D.isOpen_baseSet
  indexAt := ND.D.indexAt
  mem_baseSet_at := ND.D.mem_baseSet_at
  coordChange := transFun E ND
  coordChange_self i x hx v := transFun_self E ND i x hx v
  continuousOn_coordChange i j := continuousOn_transFun E ND i j
  coordChange_comp i j l x hx v := transFun_comp E ND i j l x hx v

theorem normalBundle_coordChange (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) (x : V.pt) :
    (normalBundle E ND).coordChange i j x = transFun E ND i j x := rfl

theorem normalBundle_indexAt (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (x : V.pt) : (normalBundle E ND).indexAt x = ND.D.indexAt x := rfl

theorem normalBundle_baseSet (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) : (normalBundle E ND).baseSet i = ND.D.baseSet i := rfl

theorem isEuclidean_normalBundle (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Work.Thom.IsEuclidean (normalBundle E ND) := by
  intro i j x hx v
  rw [normalBundle_coordChange, transFun_of_mem E ND i j x hx, ContinuousLinearMap.comp_apply,
    readCLM_norm_of_mem E ND j hx.2 (insCLM_mem E ND i hx.1 v), norm_insCLM E ND i hx.1 v]

/-! ## The identification with the concrete normal total space -/

theorem bundleToNormal_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (p : (normalBundle E ND).TotalSpace) :
    insCLM E ND ((normalBundle E ND).indexAt p.1) p.1 p.2 ∈ normalSpace E p.1 :=
  insCLM_mem E ND _ (ND.D.mem_baseSet_at p.1) p.2

/-- The homeomorphism-in-waiting from the total space of the Euclidean normal bundle to the concrete
normal total space: in the preferred chart of the base point, apply the isometric insertion. -/
def bundleToNormal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    (normalBundle E ND).TotalSpace → NormalTotal E :=
  fun p => ⟨(p.1, insCLM E ND ((normalBundle E ND).indexAt p.1) p.1 p.2),
    bundleToNormal_mem E ND p⟩

/-- The inverse direction: read the normal vector in the orthonormal frame of the preferred chart. -/
def normalToBundle (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    NormalTotal E → (normalBundle E ND).TotalSpace :=
  fun q => ⟨q.1.1, readCLM E ND ((normalBundle E ND).indexAt q.1.1) q.1.1 q.1.2⟩

theorem bundleToNormal_normalToBundle (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (q : NormalTotal E) : bundleToNormal E ND (normalToBundle E ND q) = q := by
  refine NormalTotal.ext (Prod.ext rfl ?_)
  exact insCLM_readCLM_of_mem E ND _ (ND.D.mem_baseSet_at q.1.1) q.2

theorem normalToBundle_bundleToNormal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (p : (normalBundle E ND).TotalSpace) : normalToBundle E ND (bundleToNormal E ND p) = p := by
  show (⟨p.1, readCLM E ND ((normalBundle E ND).indexAt p.1) p.1
      (insCLM E ND ((normalBundle E ND).indexAt p.1) p.1 p.2)⟩ :
        (normalBundle E ND).TotalSpace) = p
  rw [readCLM_insCLM E ND ((normalBundle E ND).indexAt p.1) (ND.D.mem_baseSet_at p.1) p.2]

theorem bundleToNormal_apply_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {q : (normalBundle E ND).TotalSpace} (hq : q.1 ∈ ND.D.baseSet i) :
    ((bundleToNormal E ND q : NormalTotal E) : V.pt × Euc (8 + k))
      = (q.1, insCLM E ND i q.1 (((normalBundle E ND).localTriv i) q).2) := by
  refine Prod.ext rfl ?_
  show insCLM E ND ((normalBundle E ND).indexAt q.1) q.1 (show Euc k from q.2)
      = insCLM E ND i q.1 (show Euc k from (((normalBundle E ND).localTriv i) q).2)
  simp only [VectorBundleCore.localTriv_apply]
  have hcoord : (normalBundle E ND).coordChange ((normalBundle E ND).indexAt q.1) i q.1
        (show Euc k from q.2)
      = readCLM E ND i q.1 (insCLM E ND ((normalBundle E ND).indexAt q.1) q.1
          (show Euc k from q.2)) := by
    show transFun E ND (ND.D.indexAt q.1) i q.1 (show Euc k from q.2)
      = readCLM E ND i q.1 (insCLM E ND (ND.D.indexAt q.1) q.1 (show Euc k from q.2))
    rw [transFun_of_mem E ND (ND.D.indexAt q.1) i q.1
      ⟨(ND.D.mem_baseSet_at q.1 : q.1 ∈ ND.D.baseSet (ND.D.indexAt q.1)), hq⟩]
    rfl
  show insCLM E ND ((normalBundle E ND).indexAt q.1) q.1 (show Euc k from q.2)
      = insCLM E ND i q.1 ((normalBundle E ND).coordChange ((normalBundle E ND).indexAt q.1)
          i q.1 (show Euc k from q.2))
  exact (insCLM_readCLM_of_mem E ND i hq
    (insCLM_mem E ND _ (ND.D.mem_baseSet_at q.1) q.2)).symm.trans
      (congrArg (insCLM E ND i q.1) hcoord.symm)

theorem continuousOn_bundleToNormal_local (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ContinuousOn (bundleToNormal E ND)
      {q : (normalBundle E ND).TotalSpace | q.1 ∈ ND.D.baseSet i} := by
  have htriv : ContinuousOn (fun q : (normalBundle E ND).TotalSpace =>
      ((normalBundle E ND).localTriv i) q)
      {q : (normalBundle E ND).TotalSpace | q.1 ∈ ND.D.baseSet i} :=
    (Bundle.Trivialization.continuousOn ((normalBundle E ND).localTriv i)).mono
      (fun q hq => hq)
  have hsnd : ContinuousOn (fun q : (normalBundle E ND).TotalSpace =>
      (((normalBundle E ND).localTriv i) q).2)
      {q : (normalBundle E ND).TotalSpace | q.1 ∈ ND.D.baseSet i} := htriv.snd
  have hbase : ContinuousOn (fun q : (normalBundle E ND).TotalSpace => (q.1 : V.pt))
      {q : (normalBundle E ND).TotalSpace | q.1 ∈ ND.D.baseSet i} := htriv.fst
  have hIns : ContinuousOn (fun z : V.pt × Euc k => insCLM E ND i z.1 z.2)
      (ND.D.baseSet i ×ˢ Set.univ) :=
    ((continuousOn_insCLM E ND i).comp continuousOn_fst (fun z hz => hz.1)).clm_apply
      continuousOn_snd
  have hpair : ContinuousOn (fun q : (normalBundle E ND).TotalSpace =>
      ((q.1, insCLM E ND i q.1 (((normalBundle E ND).localTriv i) q).2) :
        V.pt × Euc (8 + k)))
      {q : (normalBundle E ND).TotalSpace | q.1 ∈ ND.D.baseSet i} :=
    ContinuousOn.prodMk hbase
      (((continuousOn_insCLM E ND i).comp hbase (fun q hq => hq)).clm_apply hsnd)
  refine continuousOn_subtype_of_eqOn
    (p := fun z : V.pt × Euc (8 + k) => z.2 ∈ normalSpace E z.1)
    (f := fun q : (normalBundle E ND).TotalSpace =>
      ((q.1, insCLM E ND i q.1 (((normalBundle E ND).localTriv i) q).2) : V.pt × Euc (8 + k)))
    (g := bundleToNormal E ND) hpair (fun q hq => ?_)
  exact bundleToNormal_apply_of_mem E ND i hq

theorem continuous_bundleToNormal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Continuous (bundleToNormal E ND) := by
  rw [continuous_iff_continuousAt]
  intro p
  refine (continuousOn_bundleToNormal_local E ND (ND.D.indexAt p.1)).continuousAt ?_
  exact (((normalBundle E ND).localTriv (ND.D.indexAt p.1)).open_source).mem_nhds
    (ND.D.mem_baseSet_at p.1)

theorem normalToBundle_eq_localTriv (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {q : NormalTotal E} (hq : q.1.1 ∈ ND.D.baseSet i) :
    normalToBundle E ND q
      = ⟨q.1.1, ((normalBundle E ND).localTriv i).symm q.1.1 (readCLM E ND i q.1.1 q.1.2)⟩ := by
  show (⟨q.1.1, readCLM E ND ((normalBundle E ND).indexAt q.1.1) q.1.1 q.1.2⟩ :
      (normalBundle E ND).TotalSpace)
    = ⟨q.1.1, ((normalBundle E ND).localTriv i).symm q.1.1 (readCLM E ND i q.1.1 q.1.2)⟩
  rw [VectorBundleCore.localTriv_symm_apply (normalBundle E ND) i hq, normalBundle_indexAt,
    normalBundle_coordChange,
    transFun_of_mem E ND i _ q.1.1 ⟨hq, ND.D.mem_baseSet_at q.1.1⟩,
    ContinuousLinearMap.comp_apply, insCLM_readCLM_of_mem E ND i hq q.2]

theorem continuousOn_normalToBundle_local (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ContinuousOn (normalToBundle E ND) {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} := by
  have hCLM : ContinuousOn (fun q : NormalTotal E => readCLM E ND i q.1.1)
      {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} :=
    (continuousOn_readCLM E ND i).comp continuous_subtype_val.fst.continuousOn
      (fun q hq => hq)
  have hz : ContinuousOn (fun q : NormalTotal E =>
      ((q.1.1, readCLM E ND i q.1.1 q.1.2) : V.pt × Euc k))
      {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} :=
    ContinuousOn.prodMk (continuous_subtype_val.fst.continuousOn)
      (hCLM.clm_apply ((continuous_subtype_val.snd.continuousOn).mono (Set.subset_univ _)))
  have hcomp : ContinuousOn (fun q : NormalTotal E =>
      (⟨q.1.1, ((normalBundle E ND).localTriv i).symm q.1.1 (readCLM E ND i q.1.1 q.1.2)⟩ :
        (normalBundle E ND).TotalSpace))
      {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} :=
    (Bundle.Trivialization.continuousOn_symm ((normalBundle E ND).localTriv i)).comp hz
      (fun q hq => ⟨hq, Set.mem_univ _⟩)
  refine hcomp.congr (fun q hq => ?_)
  exact normalToBundle_eq_localTriv E ND i hq

theorem continuous_normalToBundle (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Continuous (normalToBundle E ND) := by
  rw [continuous_iff_continuousAt]
  intro q
  refine (continuousOn_normalToBundle_local E ND (ND.D.indexAt q.1.1)).continuousAt ?_
  exact (((ND.D.isOpen_baseSet (ND.D.indexAt q.1.1)).preimage
    (continuous_subtype_val.fst)).mem_nhds (ND.D.mem_baseSet_at q.1.1))

/-- **The homeomorphism between the total space of the Euclidean normal bundle and the concrete
normal total space**: in the preferred chart of the base point, apply the isometric insertion. -/
noncomputable def eucNormalHomeomorph (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    (normalBundle E ND).TotalSpace ≃ₜ NormalTotal E where
  toFun := bundleToNormal E ND
  invFun := normalToBundle E ND
  left_inv := normalToBundle_bundleToNormal E ND
  right_inv := bundleToNormal_normalToBundle E ND
  continuous_toFun := continuous_bundleToNormal E ND
  continuous_invFun := continuous_normalToBundle E ND

@[simp] theorem eucNormalHomeomorph_apply (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (p : (normalBundle E ND).TotalSpace) :
    eucNormalHomeomorph E ND p = bundleToNormal E ND p := rfl

theorem fibreNorm_eq_normalNorm (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (p : (normalBundle E ND).TotalSpace) :
    Work.Thom.fibreNorm (normalBundle E ND) p = normalNorm E (bundleToNormal E ND p) := by
  have h := norm_insCLM E ND ((normalBundle E ND).indexAt p.1) (ND.D.mem_baseSet_at p.1) p.2
  simpa only [Work.Thom.fibreNorm, normalNorm, bundleToNormal] using h.symm

/-! ## The target statement -/

theorem exists_euclidean_normalBundle {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ (ι : Type) (nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι),
      Work.Thom.IsEuclidean nu ∧
      ∃ phi : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E,
        ∀ p : nu.TotalSpace,
          Work.Thom.fibreNorm nu p = Work.Tubular.normalNorm E (phi p) := by
  obtain ⟨ND⟩ := exists_normalData_of_immersion E.e (E.smooth.of_le (by simp)) E.injective_mfderiv
  refine ⟨CoverIdx V k, normalBundle E ND, isEuclidean_normalBundle E ND,
    eucNormalHomeomorph E ND, ?_⟩
  intro p
  rw [eucNormalHomeomorph_apply]
  exact fibreNorm_eq_normalNorm E ND p

end

end Work.Tubular
