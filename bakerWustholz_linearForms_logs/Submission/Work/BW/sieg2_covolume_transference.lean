import Mathlib
import Submission.Work.BW.covolume_isometry_map_volume
import Submission.Work.BW.covolume_eq_abs_det_orthonormalBasis
import Submission.Work.BW.det_toMatrix_sq_eq_det_comp_adjoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covolume transference along a surjective linear map

`Work.BW.sieg2_covolume_transference` : for `f : V →L[ℝ] W` surjective between
finite-dimensional real inner product spaces, a `ℤ`-lattice `L ⊆ V` with
`Λ = L ∩ ker f` and `M = f L`,

  `covol Λ · covol M = covol L · √det (f ∘ f†)`,

where `covol Λ` is taken with respect to the Lebesgue measure of `ker f`
inherited from `V` (pinned through the isometry `e`).

The proof decomposes `V = ker f ⊕ (ker f)ᗮ` isometrically, chooses an
orthonormal basis adapted to this splitting and `ℤ`-bases of `Λ`, `M`, builds a
`ℤ`-basis of `L` adapted to the exact sequence `0 → Λ → L → M → 0`, and
computes all three covolumes as absolute values of determinants of the
corresponding coordinate matrices, which are block triangular.
-/

set_option linter.style.haveILetI false

namespace Work.BW

theorem sieg2_covolume_transference {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
    (f : V →L[ℝ] W) (hf : Function.Surjective f) {k : ℕ}
    (e : EuclideanSpace ℝ (Fin k) ≃ᵢ ↥(LinearMap.ker (f : V →ₗ[ℝ] W)))
    (L : Submodule ℤ V) [DiscreteTopology ↥L] [IsZLattice ℝ L]
    (Λ : Submodule ℤ ↥(LinearMap.ker (f : V →ₗ[ℝ] W)))
    (hΛ : ∀ x : ↥(LinearMap.ker (f : V →ₗ[ℝ] W)), x ∈ Λ ↔ (x : V) ∈ L)
    [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ]
    (M : Submodule ℤ W) (hM : ∀ y : W, y ∈ M ↔ ∃ x ∈ L, f x = y)
    [DiscreteTopology ↥M] [IsZLattice ℝ M] :
    ZLattice.covolume Λ (MeasureTheory.Measure.map e MeasureTheory.volume) * ZLattice.covolume M
      = ZLattice.covolume L *
        Real.sqrt (LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W)) := by
  let KK : Submodule ℝ V := LinearMap.ker (f : V →ₗ[ℝ] W)
  have hKK : KK = LinearMap.ker (f : V →ₗ[ℝ] W) := rfl
  haveI : KK.HasOrthogonalProjection := inferInstance
  -- finrank facts
  have hfrK : Module.finrank ℝ ↥(LinearMap.ker (f : V →ₗ[ℝ] W)) = k := by
    have h := finrank_eq_of_isometryEquiv e
    rw [finrank_euclideanSpace_fin] at h
    exact h.symm
  have hker : Module.finrank ℝ ↥(LinearMap.ker (f : V →ₗ[ℝ] W)) + Module.finrank ℝ W
      = Module.finrank ℝ V := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (f : V →ₗ[ℝ] W)
    rw [LinearMap.range_eq_top.mpr hf, finrank_top] at h1
    omega
  have hfrP : Module.finrank ℝ ↥(KKᗮ) = Module.finrank ℝ W := by
    have h1 := Submodule.finrank_add_finrank_orthogonal KK
    rw [hKK] at h1
    exact Nat.add_left_cancel (h1.trans hker.symm)
  have hfrV : Module.finrank ℝ V = k + Module.finrank ℝ W := by
    rw [← hker, hfrK]
  -- the measure on the kernel
  have hvol : MeasureTheory.Measure.map e MeasureTheory.volume
      = (MeasureTheory.volume : MeasureTheory.Measure ↥KK) := covolume_isometry_map_volume e
  -- ONBs
  let bK : OrthonormalBasis (Fin k) ℝ ↥KK := (stdOrthonormalBasis ℝ ↥KK).reindex (finCongr hfrK)
  let bP : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ ↥(KKᗮ) :=
    (stdOrthonormalBasis ℝ ↥(KKᗮ)).reindex (finCongr hfrP)
  let bW : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ W := stdOrthonormalBasis ℝ W
  let bV : OrthonormalBasis (Fin k ⊕ Fin (Module.finrank ℝ W)) ℝ V :=
    (bK.prod bP).map (KK.orthogonalDecomposition.symm)
  have hbV_inl (i : Fin k) : bV (Sum.inl i) = ((bK i : ↥KK) : V) := by
    simp [bV, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Submodule.orthogonalDecomposition_symm_apply]
  have hbV_inr (j : Fin (Module.finrank ℝ W)) : bV (Sum.inr j) = ((bP j : ↥(KKᗮ)) : V) := by
    simp [bV, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Submodule.orthogonalDecomposition_symm_apply]
  -- Z-bases and the splitting family
  have hrankΛ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = k := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ Λ, ZLattice.rank ℝ Λ]
    exact hfrK
  let cΛ : Module.Basis (Fin k) ℤ Λ :=
    (Module.Free.chooseBasis ℤ Λ).reindex
      (Fintype.equivOfCardEq (by rw [hrankΛ]; exact (Fintype.card_fin k).symm))
  have hrankM : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = Module.finrank ℝ W := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ M, ZLattice.rank ℝ M]
  let cM : Module.Basis (Fin (Module.finrank ℝ W)) ℤ M :=
    (Module.Free.chooseBasis ℤ M).reindex
      (Fintype.equivOfCardEq (by rw [hrankM]; exact (Fintype.card_fin _).symm))
  have hlift : ∀ j : Fin (Module.finrank ℝ W), ∃ x : L, f (x : V) = (cM j : W) := by
    intro j
    have hmem : (cM j : W) ∈ M := (cM j).2
    rw [hM] at hmem
    obtain ⟨x, hxL, hfx⟩ := hmem
    exact ⟨⟨x, hxL⟩, hfx⟩
  let w : Fin (Module.finrank ℝ W) → L := fun j => (hlift j).choose
  have hw (j : Fin (Module.finrank ℝ W)) : f ((w j : L) : V) = (cM j : W) :=
    (hlift j).choose_spec
  let fam : Fin k ⊕ Fin (Module.finrank ℝ W) → L := fun ij =>
    match ij with
    | Sum.inl i => ⟨(((cΛ i : Λ) : ↥KK) : V), (hΛ ((cΛ i : Λ) : ↥KK)).mp (cΛ i).2⟩
    | Sum.inr j => w j
  have hfam_inl (i : Fin k) : ((fam (Sum.inl i) : L) : V) = (((cΛ i : Λ) : ↥KK) : V) := rfl
  have hfam_inr (j : Fin (Module.finrank ℝ W)) : ((fam (Sum.inr j) : L) : V) = ((w j : L) : V) := rfl
  -- The exact sequence 0 -> Λ -> L -> M -> 0 of Z-modules
  let fL : L →ₗ[ℤ] W := ((f : V →ₗ[ℝ] W).restrictScalars ℤ).comp (Submodule.subtype L)
  have hfL_apply (x : L) : fL x = f (x : V) := rfl
  let π : L →ₗ[ℤ] M := fL.codRestrict M fun x =>
    (hM (fL x)).mpr ⟨(x : V), x.2, (hfL_apply x).symm⟩
  have hπ_apply (x : L) : ((π x : M) : W) = f (x : V) := rfl
  let ιΛ : Λ →ₗ[ℤ] L :=
    { toFun := fun a => ⟨(((a : Λ) : ↥(LinearMap.ker (f : V →ₗ[ℝ] W))) : V),
        (hΛ ((a : Λ) : ↥(LinearMap.ker (f : V →ₗ[ℝ] W)))).mp a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun n a => Subtype.ext (by simp) }
  have hιΛ_apply (a : Λ) : ((ιΛ a : L) : V)
      = (((a : Λ) : ↥(LinearMap.ker (f : V →ₗ[ℝ] W))) : V) := rfl
  have hιΛ_inj : Function.Injective ιΛ := by
    intro a b hab
    refine Subtype.ext (Subtype.ext ?_)
    exact congrArg (fun z : L => (z : V)) hab
  have hπ_ιΛ (a : Λ) : π (ιΛ a) = 0 := by
    refine Subtype.ext ?_
    rw [hπ_apply, hιΛ_apply]
    exact LinearMap.mem_ker.mp (Subtype.property ((a : Λ) : ↥(LinearMap.ker (f : V →ₗ[ℝ] W))))
  let wM : M →ₗ[ℤ] L := cM.constr ℤ fun j => w j
  have hwM_cM (j : Fin (Module.finrank ℝ W)) : wM (cM j) = w j :=
    Module.Basis.constr_basis cM ℤ (fun j => w j) j
  have hπ_wM (m : M) : π (wM m) = m := by
    have h : π.comp wM = LinearMap.id := by
      refine cM.ext fun j => ?_
      rw [LinearMap.comp_apply, hwM_cM]
      exact Subtype.ext (hw j)
    have := LinearMap.congr_fun h m
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at this
  let Ψ : Λ × M →ₗ[ℤ] L :=
    (ιΛ.comp (LinearMap.fst ℤ Λ M)) + (wM.comp (LinearMap.snd ℤ Λ M))
  have hΨ_apply (ab : Λ × M) : Ψ ab = ιΛ ab.1 + wM ab.2 := rfl
  have hΨ_bij : Function.Bijective Ψ := by
    constructor
    · intro ab cd h
      have hπ : π (wM ab.2) = π (wM cd.2) := by
        have hh := congrArg π h
        simp only [hΨ_apply, map_add, hπ_ιΛ, zero_add] at hh
        exact hh
      have hπ' : ab.2 = cd.2 := by
        rw [hπ_wM ab.2, hπ_wM cd.2] at hπ
        exact hπ
      have hι : ιΛ ab.1 = ιΛ cd.1 := by
        have h2 : ιΛ ab.1 + wM ab.2 = ιΛ cd.1 + wM cd.2 := by
          rw [← hΨ_apply, h, hΨ_apply]
        rw [hπ'] at h2
        exact add_right_cancel h2
      exact Prod.ext (hιΛ_inj hι) hπ'
    · intro x
      let y : L := x - wM (π x)
      have hyL : (y : V) ∈ L := by
        show ((x - wM (π x) : L) : V) ∈ L
        rw [Submodule.coe_sub]
        exact Submodule.sub_mem L x.2 (wM (π x)).2
      have hyker : (y : V) ∈ LinearMap.ker (f : V →ₗ[ℝ] W) := by
        rw [LinearMap.mem_ker]
        show f ((x - wM (π x) : L) : V) = 0
        have h1 : f ((wM (π x) : L) : V) = f (x : V) := by
          rw [← hπ_apply (wM (π x)), hπ_wM (π x), hπ_apply x]
        rw [Submodule.coe_sub, map_sub, h1, sub_self]
      refine ⟨(⟨⟨(y : V), hyker⟩, (hΛ ⟨(y : V), hyker⟩).mpr hyL⟩, π x), ?_⟩
      rw [hΨ_apply]
      have hthis : ιΛ ⟨⟨(y : V), hyker⟩, (hΛ ⟨(y : V), hyker⟩).mpr hyL⟩ = y :=
        Subtype.ext rfl
      rw [hthis]
      exact sub_add_cancel x (wM (π x))
  let bfam : Module.Basis (Fin k ⊕ Fin (Module.finrank ℝ W)) ℤ L :=
    (cΛ.prod cM).map (LinearEquiv.ofBijective Ψ hΨ_bij)
  have hbfam_inl (i : Fin k) : (bfam (Sum.inl i) : L) = fam (Sum.inl i) := by
    have h1 : (cΛ.prod cM) (Sum.inl i) = (cΛ i, 0) := by simp
    rw [Module.Basis.map_apply, h1]
    change Ψ (cΛ i, 0) = fam (Sum.inl i)
    rw [hΨ_apply, map_zero, add_zero]
    exact Subtype.ext rfl
  have hbfam_inr (j : Fin (Module.finrank ℝ W)) : (bfam (Sum.inr j) : L) = fam (Sum.inr j) := by
    have h1 : (cΛ.prod cM) (Sum.inr j) = (0, cM j) := by simp
    rw [Module.Basis.map_apply, h1]
    change Ψ (0, cM j) = fam (Sum.inr j)
    rw [hΨ_apply, map_zero, zero_add, hwM_cM]
  -- ===== inner-product / projection helper facts =====
  have hdecomp (x : V) : ((KK.orthogonalProjectionOnto x : ↥KK) : V)
      + ((KKᗮ.orthogonalProjectionOnto x : ↥(KKᗮ)) : V) = x := by
    conv_rhs => rw [← KK.orthogonalDecomposition.symm_apply_apply x]
    rw [Submodule.orthogonalDecomposition_apply, Submodule.orthogonalDecomposition_symm_apply]
    simp
  have hprojK_mem (x : ↥KK) : KK.orthogonalProjectionOnto (x : V) = x := by
    have h := Submodule.eq_starProjection_of_mem_orthogonal (K := KK) (u := (x : V)) (v := (x : V))
      x.2 (by simp)
    simpa [Submodule.starProjection_apply] using h
  have hprojP_mem (x : ↥(KKᗮ)) : KKᗮ.orthogonalProjectionOnto (x : V) = x := by
    have h := Submodule.eq_starProjection_of_mem_orthogonal (K := KKᗮ) (u := (x : V)) (v := (x : V))
      x.2 (by simp)
    simpa [Submodule.starProjection_apply] using h
  have hf_projK (x : V) : f ((KK.orthogonalProjectionOnto x : ↥KK) : V) = 0 :=
    LinearMap.mem_ker.mp (Subtype.property (KK.orthogonalProjectionOnto x))
  have hf_projP (x : V) : f ((KKᗮ.orthogonalProjectionOnto x : ↥(KKᗮ)) : V) = f x := by
    conv_rhs => rw [← hdecomp x]
    rw [map_add, hf_projK, zero_add]
  have hinnerK (u : ↥KK) (x : V) :
      inner ℝ (u : V) x = inner ℝ u (KK.orthogonalProjectionOnto x) := by
    conv_lhs => rw [← hdecomp x]
    rw [inner_add_right]
    have hzero : inner ℝ (u : V) ((KKᗮ.orthogonalProjectionOnto x : ↥(KKᗮ)) : V) = 0 := by
      rw [inner_eq_zero_symm]
      exact Submodule.inner_left_of_mem_orthogonal (K := KK) u.2
        (Submodule.coe_mem (KKᗮ.orthogonalProjectionOnto x))
    rw [hzero, add_zero]
    exact (Submodule.coe_inner KK u (KK.orthogonalProjectionOnto x)).symm
  have hinnerP (u : ↥(KKᗮ)) (x : V) :
      inner ℝ (u : V) x = inner ℝ u (KKᗮ.orthogonalProjectionOnto x) := by
    conv_lhs => rw [← hdecomp x]
    rw [inner_add_right]
    have hzero : inner ℝ (u : V) ((KK.orthogonalProjectionOnto x : ↥KK) : V) = 0 :=
      Submodule.inner_left_of_mem_orthogonal (K := KK) (Subtype.property (KK.orthogonalProjectionOnto x)) u.2
    rw [hzero, zero_add]
    exact (Submodule.coe_inner (KKᗮ) u (KKᗮ.orthogonalProjectionOnto x)).symm
  have hBRv (x : V) (t : Fin k ⊕ Fin (Module.finrank ℝ W)) :
      bV.toBasis.repr x t = inner ℝ (bV t) x := by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hBRK (x : ↥KK) (i : Fin k) : bK.toBasis.repr x i = inner ℝ (bK i) x := by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hBRP (x : ↥(KKᗮ)) (j : Fin (Module.finrank ℝ W)) :
      bP.toBasis.repr x j = inner ℝ (bP j) x := by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hBRW (x : W) (j : Fin (Module.finrank ℝ W)) :
      bW.toBasis.repr x j = inner ℝ (bW j) x := by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  -- ===== matrices =====
  let hKP : ↥(KKᗮ) →ₗ[ℝ] W := (f : V →ₗ[ℝ] W).comp (Submodule.subtype (KKᗮ))
  have hKP_apply (x : ↥(KKᗮ)) : hKP x = f ((x : ↥(KKᗮ)) : V) := rfl
  let Cm : Matrix (Fin k) (Fin k) ℝ := bK.toBasis.toMatrix (fun i => ((cΛ i : Λ) : ↥KK))
  let Dm : Matrix (Fin k) (Fin (Module.finrank ℝ W)) ℝ :=
    bK.toBasis.toMatrix (fun j => KK.orthogonalProjectionOnto ((w j : L) : V))
  let E : Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ W)) ℝ :=
    bP.toBasis.toMatrix (fun j => KKᗮ.orthogonalProjectionOnto ((w j : L) : V))
  let A : Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ W)) ℝ :=
    LinearMap.toMatrix bP.toBasis bW.toBasis hKP
  let B : Matrix (Fin k ⊕ Fin (Module.finrank ℝ W)) (Fin k ⊕ Fin (Module.finrank ℝ W)) ℝ :=
    bV.toBasis.toMatrix (fun z => ((bfam z : L) : V))
  let Mmat : Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ W)) ℝ :=
    bW.toBasis.toMatrix (fun j => ((cM j : M) : W))
  have hKP_w (j : Fin (Module.finrank ℝ W)) :
      hKP (KKᗮ.orthogonalProjectionOnto ((w j : L) : V)) = (cM j : W) := by
    have h1 : hKP (KKᗮ.orthogonalProjectionOnto ((w j : L) : V)) = f ((w j : L) : V) :=
      hf_projP ((w j : L) : V)
    rw [h1, hw j]
  have hB_decomp : B = Matrix.fromBlocks Cm Dm 0 E := by
    ext ij ij'
    rcases ij with i' | j' <;> rcases ij' with i | j
    · change bV.toBasis.repr ((bfam (Sum.inl i) : L) : V) (Sum.inl i')
        = bK.toBasis.repr ((cΛ i : Λ) : ↥KK) i'
      rw [hbfam_inl, hfam_inl, hBRv, hbV_inl, hinnerK, hprojK_mem, ← hBRK]
    · change bV.toBasis.repr ((bfam (Sum.inr j) : L) : V) (Sum.inl i')
        = bK.toBasis.repr (KK.orthogonalProjectionOnto ((w j : L) : V)) i'
      rw [hbfam_inr, hfam_inr, hBRv, hbV_inl, hinnerK, ← hBRK]
    · change bV.toBasis.repr ((bfam (Sum.inl i) : L) : V) (Sum.inr j') = 0
      rw [hbfam_inl, hfam_inl, hBRv, hbV_inr]
      exact Submodule.inner_left_of_mem_orthogonal (K := KK)
        (Subtype.property ((cΛ i : Λ) : ↥KK)) (Submodule.coe_mem (bP j'))
    · change bV.toBasis.repr ((bfam (Sum.inr j) : L) : V) (Sum.inr j')
        = bP.toBasis.repr (KKᗮ.orthogonalProjectionOnto ((w j : L) : V)) j'
      rw [hbfam_inr, hfam_inr, hBRv, hbV_inr, hinnerP, ← hBRP]
  have hEM : A * E = Mmat := by
    ext i j
    have hmv := LinearMap.toMatrix_mulVec_repr bP.toBasis bW.toBasis hKP
      (KKᗮ.orthogonalProjectionOnto ((w j : L) : V))
    rw [Matrix.mul_apply]
    have hcoef : ∀ l, A i l * E l j = A i l
        * (bP.toBasis.repr (KKᗮ.orthogonalProjectionOnto ((w j : L) : V))) l := fun l => rfl
    rw [Finset.sum_congr rfl (fun l _ => hcoef l)]
    change (A.mulVec (bP.toBasis.repr (KKᗮ.orthogonalProjectionOnto ((w j : L) : V)))) i
      = (bW.toBasis.repr ((cM j : M) : W)) i
    rw [congrFun hmv i, hKP_w j]
  have hιadj : LinearMap.adjoint (Submodule.subtype (KKᗮ)) = (KKᗮ).orthogonalProjectionOnto := by
    have h := ContinuousLinearMap.adjoint_toLinearMap (Submodule.subtypeL (KKᗮ))
    rw [Submodule.adjoint_subtypeL] at h
    exact h
  have hcomp0 : hKP.comp (LinearMap.adjoint (Submodule.subtype (KKᗮ))) = (f : V →ₗ[ℝ] W) := by
    rw [hιadj]
    ext v
    rw [LinearMap.comp_apply, hKP_apply]
    exact hf_projP v
  have hι_adj : ∀ y : W, (Submodule.subtype (KKᗮ)) (LinearMap.adjoint hKP y) = f.adjoint y := by
    have h1 := congrArg LinearMap.adjoint hcomp0
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_toLinearMap] at h1
    intro y
    have h2 := LinearMap.congr_fun h1 y
    simpa [LinearMap.comp_apply] using h2
  have hAdet : A.det ^ 2 = LinearMap.det ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W) := by
    have hε := det_toMatrix_sq_eq_det_comp_adjoint bP bW hKP
    have hcomp : hKP.comp (LinearMap.adjoint hKP)
        = ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W) := by
      ext y
      have h1 : ((f.comp f.adjoint : W →L[ℝ] W) : W →ₗ[ℝ] W) y = f (f.adjoint y) := by
        show (f.comp f.adjoint) y = f (f.adjoint y)
        exact ContinuousLinearMap.comp_apply f f.adjoint y
      rw [LinearMap.comp_apply, h1, ← hι_adj y, hKP_apply]
      rfl
    rw [hcomp] at hε
    exact hε
  -- ===== covolumes =====
  have hdet_Λ : ZLattice.covolume Λ (MeasureTheory.Measure.map e MeasureTheory.volume)
      = |Cm.det| := by
    rw [hvol, covolume_eq_abs_det_orthonormalBasis Λ cΛ bK, Module.Basis.det_apply]
  have hdet_M : ZLattice.covolume M MeasureTheory.volume = |Mmat.det| := by
    rw [covolume_eq_abs_det_orthonormalBasis M cM bW, Module.Basis.det_apply]
  have hdet_L : ZLattice.covolume L MeasureTheory.volume = |B.det| := by
    rw [covolume_eq_abs_det_orthonormalBasis L bfam bV, Module.Basis.det_apply]
  rw [hdet_Λ, hdet_M, hdet_L, hB_decomp, Matrix.det_fromBlocks_zero₂₁]
  rw [← hEM, Matrix.det_mul]
  rw [abs_mul, abs_mul, ← hAdet, Real.sqrt_sq_eq_abs]
  ring

end Work.BW
