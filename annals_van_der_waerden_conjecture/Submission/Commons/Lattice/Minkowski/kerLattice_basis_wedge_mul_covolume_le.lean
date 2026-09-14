import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.covol_span_wedge_gen
import Submission.Commons.Analysis.InnerProductSpace.sq_norm_iMulti_eq_det_transpose_mul
import Submission.Commons.Lattice.Minkowski.covolume_le_covolume_of_le
import Submission.Commons.Lattice.Minkowski.covolume_zeroDim_dim0
import Submission.Commons.LinearAlgebra.Matrix.det_transpose_mul_le_of_kernel
import Submission.Commons.Lattice.Discrete.discreteTopology_quotLattice
import Submission.Commons.LinearAlgebra.ExteriorPower.norm_iMulti_eq_of_span_eq
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero
import Submission.Commons.Lattice.Module.exists_basis_subtype_kernel
import Submission.Commons.Lattice.Module.basis_extension_pure_rank
import Submission.Commons.Lattice.Minkowski.exists_basis_subtype_kernel_real

open Module

noncomputable section

namespace Commons.Lattice.Minkowski

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real matrix `A` acting on `ℝ^N` as a linear map to `EuclideanSpace ℝ ι`. -/
private def matLin (A : Matrix ι (Fin N) ℝ) : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp A.mulVecLin

private lemma matLin_apply (A : Matrix ι (Fin N) ℝ) (x : Fin N → ℝ) :
    matLin A x = WithLp.toLp 2 (A.mulVec x) := by
  simp [matLin, WithLp.linearEquiv]

private lemma matLin_apply_coord (A : Matrix ι (Fin N) ℝ) (x : Fin N → ℝ) (l : ι) :
    (matLin A x).ofLp l = ∑ i, A l i * x i := by
  rw [matLin_apply]
  rfl

private lemma matLin_add (A : Matrix ι (Fin N) ℝ) (x y : Fin N → ℝ) :
    matLin A (x + y) = matLin A x + matLin A y := by
  rw [matLin_apply, matLin_apply, matLin_apply, Matrix.mulVec_add, WithLp.toLp_add]

private lemma matLin_smul (A : Matrix ι (Fin N) ℝ) (c : ℝ) (x : Fin N → ℝ) :
    matLin A (c • x) = c • matLin A x := by
  rw [matLin_apply, matLin_apply, Matrix.mulVec_smul, WithLp.toLp_smul]

/-- The same map, but on the integer lattice `ℤ^N` (as a `ℤ`-linear map). -/
private def matLinZ (A : Matrix ι (Fin N) ℝ) : (Fin N → ℤ) →ₗ[ℤ] EuclideanSpace ℝ ι where
  toFun x := matLin A (fun i => (x i : ℝ))
  map_add' x y := by
    rw [show (fun i : Fin N => ((x + y) i : ℝ)) = (fun i => (x i : ℝ)) + (fun i => (y i : ℝ)) by
      ext i; simp]
    rw [matLin_add]
  map_smul' m x := by
    rw [show (fun i : Fin N => (((m : ℤ) • x) i : ℝ)) = (m : ℝ) • (fun i => (x i : ℝ)) by
      ext i; simp [Int.cast_smul_eq_zsmul]]
    rw [matLin_smul]
    simp [Int.cast_smul_eq_zsmul]

private lemma matLinZ_apply_coord (A : Matrix ι (Fin N) ℝ) (x : Fin N → ℤ) (l : ι) :
    (matLinZ A x).ofLp l = ∑ i, A l i * (x i : ℝ) := by
  show (matLin A fun i => ((x i : ℤ) : ℝ)).ofLp l = _
  rw [matLin_apply_coord]

private lemma matLinZ_apply_cast (A : Matrix ι (Fin N) ℝ) (x : Fin N → ℤ) :
    matLinZ A x = matLin A (fun i => (x i : ℝ)) := rfl

/-- The integer kernel of `A`. -/
private def kerZ (A : Matrix ι (Fin N) ℝ) : Submodule ℤ (Fin N → ℤ) := LinearMap.ker (matLinZ A)

private lemma mem_kerZ {A : Matrix ι (Fin N) ℝ} {x : Fin N → ℤ} :
    x ∈ kerZ A ↔ ∀ l, ∑ i, A l i * (x i : ℝ) = 0 := by
  rw [kerZ, LinearMap.mem_ker, WithLp.ext_iff]
  constructor
  · intro h l
    have := congrFun h l
    rwa [matLinZ_apply_coord] at this
  · intro h
    ext l
    rw [matLinZ_apply_coord, h l]
    rfl

section Surj
variable (A : Matrix ι (Fin N) ℝ)

private lemma matLin_basisFun (i : Fin N) :
    matLin A (Pi.basisFun ℝ (Fin N) i) = WithLp.toLp 2 (fun l => A l i) := by
  rw [matLin_apply]
  congr 1
  ext l
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [Pi.basisFun_apply, Pi.single_eq_same, mul_one]
  · intro j _ hj
    have hz : (Pi.basisFun ℝ (Fin N) i) j = 0 := by
      simpa using Pi.single_eq_of_ne (M := fun _ : Fin N => ℝ) hj (1 : ℝ)
    rw [hz, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma range_matLin_eq_top
    (hA : LinearIndependent ℝ (fun l : ι => fun i : Fin N => A l i)) :
    LinearMap.range (matLin A) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff]
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hcol : ∀ i : Fin N, ∑ l, A l i * y.ofLp l = 0 := by
    intro i
    have h1 : inner ℝ y (matLin A (Pi.basisFun ℝ (Fin N) i)) = 0 :=
      (Submodule.mem_orthogonal' _ y).mp hy _ ⟨Pi.basisFun ℝ (Fin N) i, rfl⟩
    rw [matLin_basisFun, PiLp.inner_apply] at h1
    simpa using h1
  have hzero : ∑ l, y.ofLp l • (fun i : Fin N => A l i) = 0 := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hcol i]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hfin := (Fintype.linearIndependent_iff.mp hA) (fun l => y.ofLp l) hzero
  apply WithLp.ofLp_injective
  ext l
  rw [hfin l]
  rfl

end Surj

/-- Any real vector is a real combination of integer vectors. -/
private lemma span_range_intCast_top :
    Submodule.span ℝ (Set.range (fun x : Fin N → ℤ => (fun i : Fin N => (x i : ℝ)))) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hbs : ∀ i : Fin N, (Pi.basisFun ℝ (Fin N) i) ∈
      Submodule.span ℝ (Set.range (fun x : Fin N → ℤ => (fun i : Fin N => (x i : ℝ)))) := by
    intro i
    apply Submodule.subset_span
    refine ⟨Pi.basisFun ℤ (Fin N) i, ?_⟩
    ext j
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hv : v = ∑ i, v i • (Pi.basisFun ℝ (Fin N) i) := by
    conv_lhs => rw [← Basis.sum_repr (Pi.basisFun ℝ (Fin N)) v]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.basisFun_repr]
  rw [hv]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hbs i))

section KernelDetEq

open Commons.LinearAlgebra.Matrix in
/-- Equality version of the bordered Gram determinant identity. -/
private lemma det_transpose_mul_eq_of_kernel {d n : ℕ}
    (B : Matrix (Fin n) (Fin d ⊕ Fin n) ℝ)
    (Em : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hE : Em.det = 1 ∨ Em.det = -1)
    (hBE : ∀ (l : Fin n) (a : Fin d ⊕ Fin n),
      (B * Em) l a = Sum.elim (fun _ : Fin d => (0 : ℝ)) (fun j : Fin n => S l j) a) :
    (B * Matrix.transpose B).det =
      ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det * S.det ^ 2 := by
  have hkey := Commons.LinearAlgebra.Matrix.det_transpose_mul_mul_sq B Em S hBE
  have hdetEsq : Em.det ^ 2 = 1 := by rcases hE with h | h <;> rw [h] <;> norm_num
  rw [hdetEsq, mul_one] at hkey
  have hG11pos : 0 < ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det := by
    have hCdet : ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl) =
        Matrix.transpose (Em.submatrix id Sum.inl) * (Em.submatrix id Sum.inl) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    rw [hCdet]
    have hpsd : (Matrix.transpose (Em.submatrix id Sum.inl) * (Em.submatrix id Sum.inl)).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self (Em.submatrix id Sum.inl)
    have hnn : 0 ≤ (Matrix.transpose (Em.submatrix id Sum.inl) * (Em.submatrix id Sum.inl)).det :=
      hpsd.det_nonneg
    have hne : (Matrix.transpose (Em.submatrix id Sum.inl) * (Em.submatrix id Sum.inl)).det ≠ 0 := by
      have hunit : IsUnit Em := by
        rw [Matrix.isUnit_iff_isUnit_det]
        rcases hE with h | h
        · rw [h]; exact ⟨1, rfl⟩
        · rw [h]; exact ⟨-1, rfl⟩
      have hcolE : LinearIndependent ℝ Em.col := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
      have hcolC : LinearIndependent ℝ (Em.submatrix id Sum.inl).col := by
        have hcomp := hcolE.comp Sum.inl Sum.inl_injective
        convert hcomp using 1
        ext j i
        simp [Matrix.col_apply, Matrix.submatrix_apply]
      have hgram : Matrix.transpose (Em.submatrix id Sum.inl) * (Em.submatrix id Sum.inl) =
          Matrix.gram ℝ (fun j : Fin d =>
            WithLp.toLp 2 (fun i : Fin d ⊕ Fin n => (Em.submatrix id Sum.inl) i j)) := by
        ext i j
        rw [Matrix.gram_apply, PiLp.inner_apply]
        simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, mul_comm]
      rw [hgram]
      refine Matrix.det_gram_ne_zero_iff_linearIndependent.mpr ?_
      refine hcolC.map' (WithLp.linearEquiv 2 ℝ (Fin d ⊕ Fin n → ℝ)).symm.toLinearMap ?_
      rw [LinearMap.ker_eq_bot]
      exact (WithLp.linearEquiv 2 ℝ (Fin d ⊕ Fin n → ℝ)).symm.injective
    exact lt_of_le_of_ne' hnn hne
  have hcancel : ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det *
      (B * Matrix.transpose B).det =
      ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det *
        (((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det * S.det ^ 2) := by
    rw [hkey]; ring
  exact mul_left_cancel₀ (ne_of_gt hG11pos) hcancel

end KernelDetEq

section Unimodular

/-- The coordinate matrix of a `ℤ`-basis of `ℤ^N` in the standard basis is unimodular. -/
private lemma det_basis_coordMatrix_eq_pm_one (e : Basis (Fin N) ℤ (Fin N → ℤ)) :
    ((Matrix.of (fun (i j : Fin N) => e j i)).map (fun z : ℤ => (z : ℝ))).det = 1 ∨
      ((Matrix.of (fun (i j : Fin N) => e j i)).map (fun z : ℤ => (z : ℝ))).det = -1 := by
  set É : Matrix (Fin N) (Fin N) ℤ := Matrix.of (fun i j => e j i) with hÉ
  have hsymm : ∀ j : Fin N, e.equivFun.symm (Pi.basisFun ℤ (Fin N) j) = e j := by
    intro j
    rw [Basis.equivFun_symm_apply]
    rw [Finset.sum_eq_single j]
    · rw [Pi.basisFun_apply, Pi.single_eq_same, one_smul]
    · intro k _ hk
      have hz : (Pi.basisFun ℤ (Fin N) j) k = 0 := by
        rw [Pi.basisFun_apply]
        exact Pi.single_eq_of_ne (M := fun _ : Fin N => ℤ) hk (1 : ℤ)
      rw [hz, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hmat : LinearMap.toMatrix (Pi.basisFun ℤ (Fin N)) (Pi.basisFun ℤ (Fin N))
      (e.equivFun.symm.toLinearMap) = É := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    rw [show (e.equivFun.symm.toLinearMap) (Pi.basisFun ℤ (Fin N) j) = e j from hsymm j]
    rw [Pi.basisFun_repr, hÉ, Matrix.of_apply]
  have hunit : IsUnit É.det := by
    have h1 : É.det = ((LinearEquiv.det e.equivFun.symm : ℤˣ) : ℤ) := by
      rw [← hmat, LinearMap.det_toMatrix, ← LinearEquiv.coe_det]
    exact ⟨LinearEquiv.det e.equivFun.symm, h1.symm⟩
  have h2 : É.det = 1 ∨ É.det = -1 := Int.isUnit_iff.mp hunit
  have h3 : ((Int.castRingHom ℝ).mapMatrix É).det = (É.det : ℝ) := by
    rw [← RingHom.map_det (Int.castRingHom ℝ) É]
    rfl
  have h4 : (Matrix.of (fun (i j : Fin N) => e j i)).map (fun z : ℤ => (z : ℝ)) =
      (Int.castRingHom ℝ).mapMatrix É := by
    rw [hÉ]
    ext i j
    rfl
  rcases h2 with h | h
  · left
    rw [h4, h3, h]
    norm_num
  · right
    rw [h4, h3, h]
    norm_num

end Unimodular

section Form

variable (A : Matrix ι (Fin N) ℝ)

private lemma matLinZ_eq_hL_form (x : Fin N → ℤ) :
    matLinZ A x = (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) := by
  apply WithLp.ofLp_injective
  ext l
  rw [matLinZ_apply_coord]
  rfl

private lemma sum_single_smul_basis (e : Basis (Fin N) ℤ (Fin N → ℤ)) {c : ℕ} (h : c ≤ N) (j : Fin c) :
    ∑ j' : Fin c, (Pi.single j (1 : ℤ) : Fin c → ℤ) j' • e (Fin.castLE h j') =
      e (Fin.castLE h j) := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    have hz : (Pi.single j (1 : ℤ) : Fin c → ℤ) j' = 0 :=
      Pi.single_eq_of_ne (M := fun _ : Fin c => ℤ) hj' (1 : ℤ)
    rw [hz, zero_smul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form


section MainTheorem

/- **Covolume bound for the lattice of integer relations of a real matrix.**
Let `A : Matrix ι (Fin N) ℝ` have `ℝ`-linearly independent rows, let `L` be a `ℤ`-lattice in
`EuclideanSpace ℝ ι` containing the image lattice `A ℤ^N` (i.e. `A` applied to every integer
vector lies in `L`), and let `R ≥ 0` bound the wedge norm of the rows via
`(A * Aᵀ).det ≤ R^2`. Then the integer kernel `Λ = {x : Fin N → ℤ // ∀ l, ∑ i, A l i * x i = 0}`
has a `ℤ`-basis `v` of `N - card ι` elements whose exterior product has norm at most
`R / covolume L`; equivalently `covolume Λ * covolume L ≤ R`.

Mathematical route: `covolume Λ * covolume (A ℤ^N) = ‖wedge of the rows of A‖` (the
kernel–image formula: the wedge of a kernel basis is the Hodge dual of the wedge of a basis of
the row space, and the image lattice `A ℤ^N` accounts for the index), and
`covolume L ≤ covolume (A ℤ^N)` by monotonicity of covolume under inclusion. -/
theorem kerLattice_basis_wedge_mul_covolume_le
    {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι (Fin N) ℝ)
    (hA : LinearIndependent ℝ (fun l : ι => fun i : Fin N => A l i))
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ x : Fin N → ℤ, (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) ∈ L)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : (A * A.transpose).det ≤ R ^ 2) :
    ∃ v : Fin (N - Fintype.card ι) → (Fin N → ℤ),
      LinearIndependent ℤ v ∧
      (∀ x : Fin N → ℤ, (∀ l, ∑ i, A l i * (x i : ℝ) = 0) →
        ∃ a : Fin (N - Fintype.card ι) → ℤ, x = ∑ j, a j • v j) ∧
      ‖exteriorPower.ιMulti ℝ (N - Fintype.card ι)
          (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => ((v j i : ℤ) : ℝ)))‖ *
        ZLattice.covolume L ≤ R := by
  classical
  set k : ℕ := Fintype.card ι with hk
  have hk_le_N : k ≤ N := by
    have h1 := hA.fintype_card_le_finrank (R := ℝ)
    rw [Module.finrank_fin_fun] at h1
    simpa [hk] using h1
  set d : ℕ := N - k with hd
  have hdk : d + k = N := by rw [hd, hk]; exact Nat.sub_add_cancel hk_le_N
  have hLimg : ∀ x : Fin N → ℤ, matLinZ A x ∈ L := fun x => by
    rw [matLinZ_eq_hL_form]; exact hL x
  obtain ⟨e, he⟩ := exists_basis_subtype_kernel_real A hA L hL
  -- block equivalence
  let φ : Fin d ⊕ Fin k ≃ Fin N := finSumFinEquiv.trans (finCongr hdk)
  have hφ_inl : ∀ j : Fin d, φ (Sum.inl j) = Fin.castLE (Nat.sub_le N k) j := by
    intro j
    apply Fin.ext
    simp [φ, finSumFinEquiv, finCongr]
  -- the kernel basis family
  let v : Fin d → (Fin N → ℤ) := fun j => e (Fin.castLE (Nat.sub_le N k) j)
  -- the image family
  let w : Fin k → EuclideanSpace ℝ ι := fun j => matLinZ A (e (φ (Sum.inr j)))
  -- the image lattice
  set L0 : Submodule ℤ (EuclideanSpace ℝ ι) := LinearMap.range (matLinZ A) with hL0
  have hL0_le : L0 ≤ L := by
    rintro y ⟨x, rfl⟩
    exact hLimg x
  haveI hL0disc : DiscreteTopology L0 := by
    have hdis : IsDiscrete (L : Set (EuclideanSpace ℝ ι)) :=
      (SetLike.isDiscrete_iff_discreteTopology (s := L)).2 inferInstance
    have hmono : IsDiscrete (L0 : Set (EuclideanSpace ℝ ι)) :=
      hdis.mono (fun x hx => hL0_le hx)
    exact (SetLike.isDiscrete_iff_discreteTopology (s := L0)).1 hmono
  have hrangeZ : Set.range (matLinZ A) =
      matLin A '' Set.range (fun x : Fin N → ℤ => (fun i : Fin N => (x i : ℝ))) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, (matLinZ_apply_cast A x).symm⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (matLinZ_apply_cast A x).symm⟩
  have hL0span : Submodule.span ℝ (L0 : Set (EuclideanSpace ℝ ι)) = ⊤ := by
    have h1 : (L0 : Set (EuclideanSpace ℝ ι)) = Set.range (matLinZ A) := rfl
    rw [h1, hrangeZ, ← Submodule.map_span (matLin A)
      (Set.range (fun x : Fin N → ℤ => (fun i : Fin N => (x i : ℝ)))),
      span_range_intCast_top, Submodule.map_top]
    exact range_matLin_eq_top A hA
  haveI hL0lat : IsZLattice ℝ L0 := ⟨hL0span⟩
  have hcovle : ZLattice.covolume L ≤ ZLattice.covolume L0 :=
    covolume_le_covolume_of_le L0 L hL0_le
  -- the image lattice is spanned by `w`
  have hL0_eq_w : L0 = Submodule.span ℤ (Set.range w) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [← Basis.sum_repr e x, map_sum]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [map_zsmul]
      obtain ⟨a, rfl⟩ := φ.surjective i
      rcases a with j | j
      · have hker : matLinZ A (e (φ (Sum.inl j))) = 0 := by
          rw [hφ_inl]
          exact LinearMap.mem_ker.mp ((mem_kerZ (A := A)).mpr ((he _).mpr
            ⟨Pi.single j (1 : ℤ), (sum_single_smul_basis e (Nat.sub_le N k) j).symm⟩))
        rw [hker, smul_zero]
        exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · exact Submodule.span_le.mpr (fun y hy => by
        rcases hy with ⟨j, rfl⟩
        exact ⟨e (φ (Sum.inr j)), rfl⟩)
  -- the wedge family
  let vv : Fin d → EuclideanSpace ℝ (Fin N) :=
    fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => ((v j i : ℤ) : ℝ))
  -- matrices for the determinant identity
  let ψ : ι ≃ Fin k := Fintype.equivFin ι
  let B : Matrix (Fin k) (Fin d ⊕ Fin k) ℝ := fun l a => A (ψ.symm l) (φ a)
  let Em : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) ℝ := fun a b => ((e (φ b)) (φ a) : ℝ)
  let S : Matrix (Fin k) (Fin k) ℝ := fun l j => (w j).ofLp (ψ.symm l)
  have hkerCastLE : ∀ j : Fin d, matLinZ A (e (Fin.castLE (Nat.sub_le N k) j)) = 0 := by
    intro j
    exact LinearMap.mem_ker.mp ((mem_kerZ (A := A)).mpr ((he _).mpr
      ⟨Pi.single j (1 : ℤ), (sum_single_smul_basis e (Nat.sub_le N k) j).symm⟩))
  have hBE : ∀ (l : Fin k) (a : Fin d ⊕ Fin k),
      (B * Em) l a = Sum.elim (fun _ : Fin d => (0 : ℝ)) (fun j : Fin k => S l j) a := by
    intro l a
    have hsum : (B * Em) l a = (matLinZ A (e (φ a))).ofLp (ψ.symm l) := by
      rw [Matrix.mul_apply]
      simp only [B, Em]
      rw [Equiv.sum_comp φ (fun i : Fin N => A (ψ.symm l) i * ((e (φ a)) i : ℝ))]
      rw [← matLin_apply_coord]
      rfl
    rw [hsum]
    rcases a with j | j
    · rw [hφ_inl, hkerCastLE]
      rfl
    · rfl
  have hEmdet : Em.det = 1 ∨ Em.det = -1 := by
    have hEq : Em = ((Matrix.of (fun (i j : Fin N) => e j i)).map
        (fun z : ℤ => (z : ℝ))).submatrix φ φ := by
      ext a b
      simp [Em, Matrix.submatrix_apply, Matrix.map_apply]
    rw [hEq, Matrix.det_submatrix_equiv_self]
    exact det_basis_coordMatrix_eq_pm_one e
  have hkey := det_transpose_mul_eq_of_kernel B Em S hEmdet hBE
  have hBB : (B * Matrix.transpose B).det = (A * A.transpose).det := by
    have h1 : B * Matrix.transpose B = (A * A.transpose).submatrix ψ.symm ψ.symm := by
      ext l l'
      have hsum : (B * Matrix.transpose B) l l' =
          ∑ x : Fin d ⊕ Fin k, A (ψ.symm l) (φ x) * A (ψ.symm l') (φ x) := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [show B l x = A (ψ.symm l) (φ x) from rfl,
          show B.transpose x l' = A (ψ.symm l') (φ x) from by rw [Matrix.transpose_apply]]
      have hrhs : (A * A.transpose) (ψ.symm l) (ψ.symm l') =
          ∑ i : Fin N, A (ψ.symm l) i * A (ψ.symm l') i := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.transpose_apply]
      rw [hsum, Equiv.sum_comp φ (fun i : Fin N => A (ψ.symm l) i * A (ψ.symm l') i),
        Matrix.submatrix_apply, hrhs]
    rw [h1, Matrix.det_submatrix_equiv_self]
  have hG : ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det =
      ‖exteriorPower.ιMulti ℝ d vv‖ ^ 2 := by
    set C : Matrix (Fin N) (Fin d) ℤ := fun i j => e (Fin.castLE (Nat.sub_le N k) j) i with hC
    have h1 := Commons.Analysis.InnerProductSpace.sq_norm_iMulti_eq_det_transpose_mul C
    have hnorm : (fun j : Fin d => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun i => ((C i j : ℤ) : ℝ))) = vv := by
      funext j
      rfl
    have hdetG : ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl).det =
        ((Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ))).det := by
      congr 1
      ext j j'
      have hL : ((Matrix.transpose Em * Em).submatrix Sum.inl Sum.inl) j j' =
          ∑ x : Fin d ⊕ Fin k,
            ((e (φ (Sum.inl j))) (φ x) : ℝ) * ((e (φ (Sum.inl j'))) (φ x) : ℝ) := by
        rw [Matrix.submatrix_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Matrix.transpose_apply]
      have hR : ((Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ))) j j' =
          ∑ i : Fin N, ((e (Fin.castLE (Nat.sub_le N k) j)) i : ℝ) *
            ((e (Fin.castLE (Nat.sub_le N k) j')) i : ℝ) := by
        rw [Matrix.map_apply, Matrix.mul_apply]
        push_cast
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.transpose_apply, hC]
      rw [hL, hR, Equiv.sum_comp φ (fun i : Fin N =>
        ((e (φ (Sum.inl j))) i : ℝ) * ((e (φ (Sum.inl j'))) i : ℝ)), hφ_inl j, hφ_inl j']
    rw [hdetG, ← h1, hnorm]
  have hS : S.det ^ 2 = ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 := by
    have hgram : Matrix.transpose S * S = Matrix.gram ℝ w := by
      ext j j'
      have hL : (Matrix.transpose S * S) j j' = ∑ l : Fin k, S l j * S l j' := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Matrix.transpose_apply]
      have hR : Matrix.gram ℝ w j j' = ∑ i : ι, (w j).ofLp i * (w j').ofLp i := by
        rw [Matrix.gram_apply, PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        ring
      rw [hL, hR]
      simp only [S]
      rw [Equiv.sum_comp ψ.symm (fun i : ι => (w j).ofLp i * (w j').ofLp i)]
    have hdet : (Matrix.transpose S * S).det = S.det ^ 2 := by
      rw [Matrix.det_mul, Matrix.det_transpose]; ring
    rw [← hdet, hgram, ← exteriorPower.inner_ιMulti_self w, real_inner_self_eq_norm_sq]
  have hdetmain : (A * A.transpose).det = ‖exteriorPower.ιMulti ℝ d vv‖ ^ 2 *
      ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 := by
    rw [← hBB, hkey, hG, hS]
  -- positive definiteness of the Gram matrix of the rows
  have hdetpos : 0 < (A * A.transpose).det := by
    have hgram : A * A.transpose = Matrix.gram ℝ (fun l : ι =>
        WithLp.toLp 2 (fun i : Fin N => A l i)) := by
      ext l l'
      have hL : (A * A.transpose) l l' = ∑ i : Fin N, A l i * A l' i := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.transpose_apply]
      have hR : Matrix.gram ℝ (fun l : ι => WithLp.toLp 2 (fun i : Fin N => A l i)) l l' =
          ∑ i : Fin N, A l i * A l' i := by
        rw [Matrix.gram_apply, PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        ring
      rw [hL, hR]
    rw [hgram]
    have hne : (Matrix.gram ℝ (fun l : ι => WithLp.toLp 2 (fun i : Fin N => A l i))).det ≠ 0 := by
      refine Matrix.det_gram_ne_zero_iff_linearIndependent.mpr ?_
      refine hA.map' (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap ?_
      rw [LinearMap.ker_eq_bot]
      exact (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.injective
    exact ((Matrix.posSemidef_gram ℝ
      (fun l : ι => WithLp.toLp 2 (fun i : Fin N => A l i))).posDef_iff_det_ne_zero.mpr hne).det_pos
  -- the image family is independent
  have hw_li : LinearIndependent ℝ w := by
    have hpos : 0 < ‖exteriorPower.ιMulti ℝ k w‖ := by
      have hprod : 0 < ‖exteriorPower.ιMulti ℝ d vv‖ ^ 2 *
          ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 := by
        rw [← hdetmain]; exact hdetpos
      have hA : (0 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ d vv‖ ^ 2 := sq_nonneg _
      have hBpos : 0 < ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 := by
        rcases mul_pos_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h1 (not_lt.mpr hA)
      have hBne : ‖exteriorPower.ιMulti ℝ k w‖ ≠ 0 := by
        intro h
        rw [h] at hBpos
        norm_num at hBpos
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hBne)
    exact Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero w
      (norm_pos_iff.mp hpos)
  have hw_span : Submodule.span ℝ (Set.range w) = ⊤ :=
    hw_li.span_eq_top_of_card_eq_finrank' (by simp [hk])
  let bb : Basis (Fin k) ℝ (EuclideanSpace ℝ ι) :=
    Basis.mk hw_li (le_of_eq hw_span.symm)
  have hcovw : ZLattice.covolume L0 = ‖exteriorPower.ιMulti ℝ k w‖ := by
    have hb := Commons.Analysis.InnerProductSpace.covol_span_wedge_gen bb
    rw [Basis.coe_mk] at hb
    rw [← hL0_eq_w] at hb
    exact hb
  refine ⟨v, ?_, ?_, ?_⟩
  · exact e.linearIndependent.comp (Fin.castLE (Nat.sub_le N k)) (Fin.castLE_injective _)
  · intro x hx
    exact (he x).mp hx
  · have h1 : ‖exteriorPower.ιMulti ℝ d vv‖ * ZLattice.covolume L ≤
        ‖exteriorPower.ιMulti ℝ d vv‖ * ZLattice.covolume L0 :=
      mul_le_mul_of_nonneg_left hcovle (norm_nonneg _)
    have h2 : ‖exteriorPower.ιMulti ℝ d vv‖ * ZLattice.covolume L0 =
        ‖exteriorPower.ιMulti ℝ d vv‖ * ‖exteriorPower.ιMulti ℝ k w‖ := by rw [hcovw]
    have h3 : ‖exteriorPower.ιMulti ℝ d vv‖ * ‖exteriorPower.ιMulti ℝ k w‖ =
        Real.sqrt ((A * A.transpose).det) := by
      rw [← Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      congr 1
      rw [hdetmain]
      ring
    have h4 : Real.sqrt ((A * A.transpose).det) ≤ R := by
      rw [← Real.sqrt_sq hR0]
      exact Real.sqrt_le_sqrt hR
    calc ‖exteriorPower.ιMulti ℝ d vv‖ * ZLattice.covolume L
        ≤ ‖exteriorPower.ιMulti ℝ d vv‖ * ZLattice.covolume L0 := h1
      _ = ‖exteriorPower.ιMulti ℝ d vv‖ * ‖exteriorPower.ιMulti ℝ k w‖ := h2
      _ = Real.sqrt ((A * A.transpose).det) := h3
      _ ≤ R := h4

end MainTheorem

end Commons.Lattice.Minkowski
