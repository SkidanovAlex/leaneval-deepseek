import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped Manifold ContDiff
open Topology Filter

/-!
# Reduction of the compact case of Whitney's strong embedding theorem to the connected case

This file proves `Work.Embedding.exists_embedding_of_components`: if every *connected* compact open
subset of a compact smooth `n`-manifold `M` (`n ≥ 1`) admits a smooth embedding into `ℝ^{2n}` with
injective manifold derivative, then `M` itself does.

The proof is a disjoint-union assembly.

* A compact smooth manifold is locally connected, hence has finitely many connected components, and
  each component is clopen (open because `M` is locally connected, closed in any topological
  space), so compact.  We index the components by `Fin k` through `ConnectedComponents M` and
  `Fintype.equivFin`, obtaining a family `U : Fin k → Opens M` of pairwise disjoint connected
  compact open sets covering `M`, together with an index map `idx : M → Fin k` with
  `x ∈ U (idx x)`.

* Applying the hypothesis to each `U i` produces a smooth embedding `E i : ↥(U i) → ℝ^{2n}` with
  injective derivative.  Its image is compact, hence bounded; composing with `y ↦ c i + lam i • y`
  for suitable `lam i > 0` moves it into a ball of radius `1/4` around a point `c i`, where the
  points `c i` are pairwise at distance at least `2`.  Consequently the placed images are pairwise
  disjoint.

* The individual maps are then extended to `M` (by `0` outside `U i`) and *summed*; since the
  `U i` are pairwise disjoint, at every point at most one summand is nonzero and `e` agrees
  locally with the placed embedding of the component, which gives smoothness, injectivity and
  injectivity of `mfderiv` (using `mfderiv_comp_subtype_val` for the derivative of a map
  restricted to an open subset).  Finally a continuous injective map from the compact space `M` to
  the Hausdorff space `ℝ^{2n}` is an embedding.
-/

namespace Work.Embedding

/-! ## Auxiliary lemmas -/

section Components

variable {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]

/-- The connected component of `M` corresponding to a point of `ConnectedComponents M`, as an
open subset. -/
noncomputable def compOpens (C : ConnectedComponents M) : TopologicalSpace.Opens M :=
  ⟨ConnectedComponents.mk ⁻¹' {C}, (isOpen_discrete {C}).preimage ConnectedComponents.continuous_coe⟩

lemma mem_compOpens (C : ConnectedComponents M) (x : M) :
    x ∈ compOpens C ↔ ConnectedComponents.mk x = C := Iff.rfl

lemma compOpens_eq_iff {C D : ConnectedComponents M} :
    compOpens C = compOpens D ↔ C = D := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    exact (mem_compOpens D x).mp (h ▸ (mem_compOpens (ConnectedComponents.mk x) x).mpr rfl)
  · rintro rfl
    rfl

lemma isConnected_compOpens (C : ConnectedComponents M) : IsConnected (compOpens C : Set M) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [show ((compOpens (ConnectedComponents.mk x) : TopologicalSpace.Opens M) : Set M)
      = connectedComponent x from connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

lemma isClosed_compOpens (C : ConnectedComponents M) : IsClosed (compOpens C : Set M) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [show ((compOpens (ConnectedComponents.mk x) : TopologicalSpace.Opens M) : Set M)
      = connectedComponent x from connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

lemma isCompact_compOpens [CompactSpace M] (C : ConnectedComponents M) :
    IsCompact (compOpens C : Set M) :=
  (isClosed_compOpens C).isCompact

lemma disjoint_compOpens {C D : ConnectedComponents M} (h : C ≠ D) :
    Disjoint (compOpens C : Set M) (compOpens D : Set M) := by
  rw [Set.disjoint_left]
  intro x hxC hxD
  exact h (((mem_compOpens C x).mp hxC).symm.trans ((mem_compOpens D x).mp hxD))

lemma iUnion_compOpens : (⋃ C : ConnectedComponents M, (compOpens C : Set M)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨ConnectedComponents.mk x, (mem_compOpens _ x).mpr rfl⟩

end Components

/-- Two distinct natural numbers differ by at least `2` after the map `a ↦ 2 a + 1`. -/
theorem two_le_abs_two_mul_add_one_sub {a d : ℕ} (h : a ≠ d) :
    2 ≤ |(2 * (a : ℝ) + 1) - (2 * (d : ℝ) + 1)| := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : (a : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_of_neg (by linarith)]
    linarith
  · have h1 : (d : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_of_pos (by linarith)]
    linarith

/-- Multiplication by a nonzero scalar on a real vector space is injective. -/
theorem injective_smul_of_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E] {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (fun x : E => a • x) := by
  intro x y h
  have h2 := congrArg (fun w : E => a⁻¹ • w) h
  simpa [smul_smul, inv_mul_cancel₀ ha] using h2

/-- Multiplication by a nonzero scalar, as a continuous linear map, is injective. -/
theorem injective_smul_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (a • ContinuousLinearMap.id ℝ E) := by
  intro x y h
  refine injective_smul_of_ne_zero ha ?_
  simpa using h

/-- The manifold derivative of `z ↦ c + a • z` is multiplication by `a`. -/
theorem mfderiv_const_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) (a : ℝ) (y : E) :
    mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) (fun z : E => c + a • z) y
      = a • ContinuousLinearMap.id ℝ E := by
  rw [mfderiv_eq_fderiv]
  have h1 : HasFDerivAt (fun z : E => a • z) (a • ContinuousLinearMap.id ℝ E) y := by
    have h := ContinuousLinearMap.hasFDerivAt (a • ContinuousLinearMap.id ℝ E) (x := y)
    have hfun : (⇑(a • ContinuousLinearMap.id ℝ E) : E → E) = fun z : E => a • z := by
      funext z
      simp
    rwa [hfun] at h
  rw [show (fun z : E => c + a • z) = (fun z : E => c + (fun w : E => a • w) z) from rfl,
    fderiv_const_add]
  exact h1.fderiv

/-- **The derivative of a smooth map restricted to an open subset.**  The inclusion of an open
subset of a manifold has the identity as its manifold derivative, so restricting a smooth map to an
open subset does not change its derivative. -/
theorem mfderiv_comp_subtype_val {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {M' : Type*} [TopologicalSpace M']
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) M']
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞) M']
    {f : M → M'} (U : TopologicalSpace.Opens M) (x : U)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) (fun y : U => f ↑y) x =
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) f ↑x := by
  let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
  let J := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
  have hmd1 : MDifferentiableAt I J (fun y : U => f ↑y) x :=
    (((hf.comp contMDiff_subtype_val).contMDiffAt)).mdifferentiableAt (by simp)
  have hmd2 : MDifferentiableAt I J f (↑x) := hf.mdifferentiableAt (by simp)
  rw [MDifferentiableAt.mfderiv hmd1, MDifferentiableAt.mfderiv hmd2]
  have hfun : ⇑(extChartAt I x) = ⇑(extChartAt I ↑x) ∘ (Subtype.val : U → M) := by
    funext y
    simp only [extChartAt_coe, Function.comp_apply, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict]
  have hpt : (extChartAt I x) x = (extChartAt I ↑x) ↑x := congrFun hfun x
  rw [← hpt]
  have hsec : ∀ y ∈ (extChartAt I x).target,
      (Subtype.val : U → M) ((extChartAt I x).symm y) = (extChartAt I ↑x).symm y := by
    intro y hy
    have h1 : (extChartAt I ↑x) (((extChartAt I x).symm y)).val = y := by
      have h := congrFun hfun ((extChartAt I x).symm y)
      simp only [Function.comp_apply] at h
      rw [← h]
      exact (extChartAt I x).right_inv hy
    have hsrc : (((extChartAt I x).symm y)).val ∈ (extChartAt I ↑x).source := by
      have hmem : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
        (extChartAt I x).mapsTo_symm hy
      rw [extChartAt_source] at hmem ⊢
      rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source] at hmem
      exact hmem
    conv_rhs => rw [← h1]
    exact (PartialEquiv.left_inv (e := extChartAt I ↑x)
      (x := (((extChartAt I x).symm y)).val) hsrc).symm
  have hev : ((Subtype.val : U → M) ∘ (extChartAt I x).symm)
      =ᶠ[𝓝 ((extChartAt I x) x)] (extChartAt I ↑x).symm :=
    Filter.eventually_of_mem (extChartAt_target_mem_nhds x) hsec
  have hev2 : writtenInExtChartAt I J x (fun y : U => f ↑y)
      =ᶠ[𝓝[Set.range I] ((extChartAt I x) x)] writtenInExtChartAt I J ↑x f :=
    ((hev.filter_mono inf_le_left).fun_comp f).fun_comp (extChartAt J (f ↑x))
  refine Filter.EventuallyEq.fderivWithin_eq hev2 ?_
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [hsec ((extChartAt I x) x) (mem_extChartAt_target x)]

/-- **Reduction of the compact case to the connected one.**  If every connected compact open
subset of a compact smooth `n`-manifold `M` (`n ≥ 1`) admits a smooth embedding into `ℝ^{2n}` with
injective derivative, then so does `M`: the finitely many connected components are embedded
separately, their images are moved into pairwise disjoint balls, and the resulting map is glued. -/
theorem exists_embedding_of_components {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hconn : ∀ U : TopologicalSpace.Opens M, IsConnected (U : Set M) → IsCompact (U : Set M) →
      ∃ e : U → EuclideanSpace ℝ (Fin (2 * n)),
        ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
        Topology.IsEmbedding e ∧
        ∀ x : U, Function.Injective
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) := by
  classical
  haveI hLC : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  haveI hFinite : Finite (ConnectedComponents M) := inferInstance
  haveI hFintype : Fintype (ConnectedComponents M) := Fintype.ofFinite _
  let k := Fintype.card (ConnectedComponents M)
  let eqv : Fin k ≃ ConnectedComponents M := (Fintype.equivFin (ConnectedComponents M)).symm
  let U : Fin k → TopologicalSpace.Opens M := fun i => compOpens (eqv i)
  let idx : M → Fin k := fun x => Fintype.equivFin (ConnectedComponents M) (ConnectedComponents.mk x)
  have hidx : ∀ x : M, eqv (idx x) = ConnectedComponents.mk x := fun x => Equiv.apply_symm_apply _ _
  have hmemU : ∀ x : M, x ∈ (U (idx x) : Set M) := by
    intro x
    show x ∈ (compOpens (eqv (idx x)) : Set M)
    rw [hidx x]
    exact (mem_compOpens _ x).mpr rfl
  have hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (U i : Set M) (U j : Set M) :=
    fun i j hij => disjoint_compOpens fun h => hij (eqv.injective h)
  -- per-component embeddings
  have hcomp : ∀ i : Fin k, ∃ e : (↥(U i)) → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      Topology.IsEmbedding e ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) :=
    fun i => hconn (U i) (isConnected_compOpens (eqv i)) (isCompact_compOpens (eqv i))
  let E : (i : Fin k) → (↥(U i)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun i => Classical.choose (hcomp i)
  have hE : ∀ i, ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (E i) ∧
      Topology.IsEmbedding (E i) ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) (E i) x) :=
    fun i => Classical.choose_spec (hcomp i)
  -- a norm bound for each image
  have hbdd : ∀ i : Fin k, ∃ R : ℝ, 1 ≤ R ∧ ∀ z : ↥(U i), ‖E i z‖ ≤ R := by
    intro i
    haveI : CompactSpace ↥(U i) := isCompact_iff_compactSpace.mp (isCompact_compOpens (eqv i))
    obtain ⟨R₀, hR₀⟩ := (isCompact_range (hE i).1.continuous).isBounded.exists_norm_le
    refine ⟨max 1 (|R₀| + 1), le_max_left _ _, fun z => ?_⟩
    refine le_trans (hR₀ (E i z) (Set.mem_range_self z)) ?_
    exact le_trans (le_trans (le_abs_self R₀) (le_add_of_nonneg_right zero_le_one)) (le_max_right _ _)
  let R : Fin k → ℝ := fun i => Classical.choose (hbdd i)
  have hR1 : ∀ i, 1 ≤ R i := fun i => (Classical.choose_spec (hbdd i)).1
  have hR2 : ∀ i z, ‖E i z‖ ≤ R i := fun i => (Classical.choose_spec (hbdd i)).2
  have hRpos : ∀ i, 0 < R i := fun i => lt_of_lt_of_le zero_lt_one (hR1 i)
  let lam : Fin k → ℝ := fun i => 1 / (4 * R i)
  have hlam_apply : ∀ i, lam i = 1 / (4 * R i) := fun i => rfl
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    rw [hlam_apply]
    have := hRpos i
    positivity
  have hlam_bound : ∀ i (z : ↥(U i)), ‖lam i • E i z‖ ≤ 1 / 4 := by
    intro i z
    have hRne : R i ≠ 0 := ne_of_gt (hRpos i)
    have key : lam i * R i = 1 / 4 := by
      rw [hlam_apply]
      field_simp
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (hlam_pos i))]
    calc lam i * ‖E i z‖ ≤ lam i * R i := mul_le_mul_of_nonneg_left (hR2 i z) (le_of_lt (hlam_pos i))
      _ = 1 / 4 := key
  -- the separation points
  let b : EuclideanSpace ℝ (Fin (2 * n)) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ)
  have hb : ‖b‖ = 1 := by
    have h : b = PiLp.single 2 (⟨0, by omega⟩ : Fin (2 * n)) (1 : ℝ) := rfl
    rw [h, PiLp.norm_single, norm_one]
  let c : Fin k → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun i => ((2 * ((i : ℕ) : ℝ)) + 1) • b
  have hc_apply : ∀ i, c i = ((2 * ((i : ℕ) : ℝ)) + 1) • b := fun i => rfl
  have hc : ∀ i j : Fin k, i ≠ j → 2 ≤ ‖c i - c j‖ := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rw [hc_apply i, hc_apply j, ← sub_smul, norm_smul, hb, mul_one, Real.norm_eq_abs]
    exact two_le_abs_two_mul_add_one_sub hne
  -- the maps
  let psi : (i : Fin k) → EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun i y => c i + lam i • y
  have hpsi_apply : ∀ i y, psi i y = c i + lam i • y := fun i y => rfl
  let G : (i : Fin k) → M → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun i x => if h : x ∈ (U i : Set M) then psi i (E i ⟨x, h⟩) else 0
  have hG_apply : ∀ i x, G i x =
      (if h : x ∈ (U i : Set M) then psi i (E i ⟨x, h⟩) else 0) := fun i x => rfl
  have hG_pos : ∀ i (x : M) (hx : x ∈ (U i : Set M)), G i x = psi i (E i ⟨x, hx⟩) := by
    intro i x hx
    rw [hG_apply]
    exact dif_pos (c := x ∈ (U i : Set M)) hx
  have hG_neg : ∀ i (x : M), x ∉ (U i : Set M) → G i x = 0 := by
    intro i x hx
    rw [hG_apply]
    exact dif_neg (c := x ∈ (U i : Set M)) hx
  let e : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => ∑ i : Fin k, G i x
  have he_apply : ∀ x, e x = ∑ i : Fin k, G i x := fun x => rfl
  have hpsi_smooth : ∀ i, ContMDiff (𝓡 (2 * n)) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (psi i) := by
    intro i
    have h1 : ContMDiff (𝓡 (2 * n)) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) => z + c i) := contMDiff_id.add contMDiff_const
    have h2 : ContMDiff (𝓡 (2 * n)) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) => lam i • y) := by
      have h := ContinuousLinearMap.contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        ((lam i) • (1 : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))))
      have hfun : (⇑((lam i) • (1 : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))) : EuclideanSpace ℝ (Fin (2 * n)) →
          EuclideanSpace ℝ (Fin (2 * n))) = fun y => lam i • y := by
        funext y
        simp
      rwa [hfun] at h
    refine (h1.comp h2).congr fun y => ?_
    simp only [Function.comp_apply, hpsi_apply]
    exact add_comm _ _
  have hpsi_inj : ∀ i, Function.Injective (psi i) := by
    intro i a d hab
    rw [hpsi_apply] at hab
    exact injective_smul_of_ne_zero (ne_of_gt (hlam_pos i)) (add_left_cancel hab)
  have hG_smooth : ∀ i : Fin k, ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (G i) := by
    intro i
    have hsub1 : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ↥(U i) => G i ↑z) := by
      have heq : (fun z : ↥(U i) => G i ↑z) = (fun z => psi i (E i z)) := by
        funext z
        rw [hG_pos i ↑z z.2]
      rw [heq]
      exact (hpsi_smooth i).comp (hE i).1
    have h1 : ∀ y ∈ (U i : Set M), ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (G i) y :=
      fun y hy => contMDiffAt_subtype_iff.mp (hsub1.contMDiffAt (x := ⟨y, hy⟩))
    have h2 : ∀ y ∉ (U i : Set M), ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (G i) y := by
      intro y hy
      have hcompl : (((U i : TopologicalSpace.Opens M) : Set M))ᶜ ∈ 𝓝 y :=
        (isClosed_compOpens (eqv i)).isOpen_compl.mem_nhds hy
      have hev : G i =ᶠ[𝓝 y] (fun _ : M => (0 : EuclideanSpace ℝ (Fin (2 * n)))) := by
        refine Filter.eventually_of_mem hcompl fun z hz => ?_
        exact hG_neg i z hz
      exact (contMDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin (2 * n))))).congr_of_eventuallyEq hev
    intro y
    by_cases hy : y ∈ (U i : Set M)
    · exact h1 y hy
    · exact h2 y hy
  have hG_inj : ∀ i, Set.InjOn (G i) (U i : Set M) := by
    intro i x hx y hy hxy
    rw [hG_pos i x hx, hG_pos i y hy] at hxy
    have h2 : E i ⟨x, hx⟩ = E i ⟨y, hy⟩ := hpsi_inj i hxy
    have h3 : (⟨x, hx⟩ : ↥(U i)) = ⟨y, hy⟩ := (hE i).2.1.injective h2
    exact congrArg Subtype.val h3
  -- the glued map agrees with one piece near each point
  have hev : ∀ x : M, e =ᶠ[𝓝 x] G (idx x) := by
    intro x
    refine Filter.eventually_of_mem ((U (idx x)).2.mem_nhds (hmemU x)) fun y hy => ?_
    show (∑ i : Fin k, G i y) = G (idx x) y
    refine Finset.sum_eq_single (idx x) ?_ ?_
    · intro i _ hi
      exact hG_neg i y fun hyi => (Set.disjoint_left.mp (hdisj i (idx x) hi) hyi) hy
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  have he_eval : ∀ x : M, e x = G (idx x) x := fun x => (hev x).eq_of_nhds
  have he_smooth : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) e := by
    have h := ContMDiff.sum (t := Finset.univ) (f := G) fun i _ => hG_smooth i
    refine h.congr fun x => ?_
    rw [he_apply]
  have he_inj : Function.Injective e := by
    intro x y hxy
    have hmain : G (idx x) x = G (idx y) y := by rw [← he_eval x, ← he_eval y]; exact hxy
    rcases eq_or_ne (idx x) (idx y) with hid | hid
    · have hUeq : (U (idx x) : Set M) = (U (idx y) : Set M) := by rw [hid]
      have hx' : x ∈ (U (idx y) : Set M) := hUeq ▸ hmemU x
      refine hG_inj (idx y) hx' (hmemU y) ?_
      rw [hid] at hmain
      exact hmain
    · exfalso
      have hdist : 2 ≤ dist (c (idx x)) (c (idx y)) := by
        rw [dist_eq_norm]
        exact hc (idx x) (idx y) hid
      have hxb : dist (c (idx x)) (e x) ≤ 1 / 4 := by
        rw [dist_comm, dist_eq_norm, he_eval x, hG_pos (idx x) x (hmemU x), hpsi_apply,
          add_sub_cancel_left]
        exact hlam_bound (idx x) ⟨x, hmemU x⟩
      have hyb : dist (c (idx y)) (e y) ≤ 1 / 4 := by
        rw [dist_comm, dist_eq_norm, he_eval y, hG_pos (idx y) y (hmemU y), hpsi_apply,
          add_sub_cancel_left]
        exact hlam_bound (idx y) ⟨y, hmemU y⟩
      have hmid : dist (e x) (c (idx y)) = dist (c (idx y)) (e y) := by rw [hxy, dist_comm]
      have htri : dist (c (idx x)) (c (idx y)) ≤ dist (c (idx x)) (e x) + dist (c (idx y)) (e y) := by
        calc dist (c (idx x)) (c (idx y)) ≤ dist (c (idx x)) (e x) + dist (e x) (c (idx y)) :=
              dist_triangle _ _ _
          _ = dist (c (idx x)) (e x) + dist (c (idx y)) (e y) := by rw [hmid]
      linarith
  have he_deriv : ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
    intro x
    have hx : x ∈ (U (idx x) : Set M) := hmemU x
    rw [(hev x).mfderiv_eq]
    have hkey := mfderiv_comp_subtype_val (U := U (idx x)) (x := ⟨x, hx⟩) (f := G (idx x))
      (hG_smooth (idx x))
    rw [← hkey]
    have heq : (fun z : ↥(U (idx x)) => G (idx x) ↑z)
        = (psi (idx x) ∘ E (idx x)) := by
      funext z
      rw [hG_pos (idx x) ↑z z.2]
      rfl
    rw [heq]
    rw [mfderiv_comp (x := ⟨x, hx⟩) (f := E (idx x)) (g := psi (idx x))
      ((hpsi_smooth (idx x)).mdifferentiableAt (by simp))
      ((hE (idx x)).1.mdifferentiableAt (by simp))]
    rw [mfderiv_const_add_smul (c (idx x)) (lam (idx x)) (E (idx x) ⟨x, hx⟩)]
    exact Function.Injective.comp
      (f := ⇑(mfderiv (𝓡 n) (𝓡 (2 * n)) (E (idx x)) ⟨x, hx⟩))
      (g := ⇑((lam (idx x)) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2 * n)))))
      (injective_smul_id (E := EuclideanSpace ℝ (Fin (2 * n))) (ne_of_gt (hlam_pos (idx x))))
      ((hE (idx x)).2.2 ⟨x, hx⟩)
  refine ⟨e, he_smooth, ?_, he_deriv⟩
  exact (IsClosedEmbedding.of_continuous_injective_isClosedMap he_smooth.continuous he_inj
    (fun s hs => (hs.isCompact.image he_smooth.continuous).isClosed)).isEmbedding

end Work.Embedding
