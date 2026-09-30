import Mathlib
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The kernel of `PhiE a` is isometric to `ℝ^{d·(N-M)}`

For a number field `F` of degree `d = [F : ℚ]`, `M < N`, and `F`-linearly independent rows
`a : Fin M → Fin N → F`, the `ℝ`-linear map

`PhiE a : ℝ^{d·N} → ℝ^{d·M}`

(multiplication by the `M × N` matrix of mixed images of the `a i j`, expressed in the
orthonormal coordinates of the mixed space) is surjective, so its kernel is a real inner product
space of dimension `d·N − d·M = d·(N − M)`.  Every finite-dimensional real inner product space of
dimension `k` is isometric to `EuclideanSpace ℝ (Fin k)`, hence the kernel of `PhiE a` is
isometric to `EuclideanSpace ℝ (Fin (d·(N − M)))`.

The file is self-contained: it only needs the vocabulary of `sieg2KernelDefs` (`KE`, `meK`,
`mulK`, `Phi`, `PhiMat`, `PhiE`), and it re-derives the few auxiliary facts it needs (the
coordinate equivalence `psiAssemble` between `(KE F)^N` and the orthonormal coordinates
`ℝ^{N × index F}`, and the algebra of `mulK`), so that it does not depend on a module that other
members of the team are still editing.

The proof has the following shape.
* `siegKernel_card_index` : `|index F| = [F : ℚ]`.
* `siegKernel_Phi_surjective` : `Phi a` is surjective when the rows are `F`-independent.  Row rank
  `M` over `F` gives a right inverse `b` of the matrix (`siegKernel_exists_rightInverse`), and the
  same formula, read in the mixed space, is a right inverse of `Phi a`.
* `siegKernel_psiAssemble_mulVec` : the matrix model `PhiMat a` and the mixed-space model `Phi a`
  agree under the coordinate equivalence, because `PhiMat a` *is* the matrix of `Phi a` in the
  orthonormal basis.
* `siegKernel_PhiE_surjective` : surjectivity of `PhiE a`, transferred from `Phi a`.
* `siegKernel_finrank_ker` : rank–nullity, using `finrank ℝ (ℝ^{d·N}) = d·N`; and
  `siegKernel_kernel_isometry` : the standard orthonormal-basis isometry onto
  `EuclideanSpace ℝ (Fin k)`.
-/

set_option linter.unusedVariables false

open NumberField
open scoped Classical

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ## The coordinate equivalence `(KE F)^N ≅ ℝ^{N × index F}` -/

/-- Assemble coordinates `(j, c) ↦ ℝ` into a tuple of `N` vectors of the Euclidean mixed space,
expanding in the orthonormal basis `mixedEmbedding.euclidean.stdOrthonormalBasis F`. -/
def siegKernel_psiAssemble (N : ℕ) :
    (Fin N × NumberField.mixedEmbedding.index F → ℝ) →ₗ[ℝ] (Fin N → KE F) where
  toFun x := fun j =>
    ∑ c, x (j, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]

/-- The coordinates of a tuple of mixed-space vectors in the orthonormal basis. -/
def siegKernel_psiAssembleInv (N : ℕ) :
    (Fin N → KE F) →ₗ[ℝ] (Fin N × NumberField.mixedEmbedding.index F → ℝ) where
  toFun y := fun p =>
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr (y p.1) p.2
  map_add' y z := by
    ext p
    simp only [Pi.add_apply, map_add, WithLp.ofLp_add]
  map_smul' r y := by
    ext p
    simp only [Pi.smul_apply, map_smul, WithLp.ofLp_smul, RingHom.id_apply]

@[simp]
theorem siegKernel_psiAssemble_apply (N : ℕ)
    (x : Fin N × NumberField.mixedEmbedding.index F → ℝ) (j : Fin N) :
    siegKernel_psiAssemble (F := F) N x j =
      ∑ c, x (j, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c := rfl

@[simp]
theorem siegKernel_psiAssembleInv_apply (N : ℕ) (y : Fin N → KE F)
    (p : Fin N × NumberField.mixedEmbedding.index F) :
    siegKernel_psiAssembleInv (F := F) N y p =
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr (y p.1) p.2 := rfl

theorem siegKernel_psiAssembleInv_psiAssemble (N : ℕ)
    (x : Fin N × NumberField.mixedEmbedding.index F → ℝ) :
    siegKernel_psiAssembleInv (F := F) N (siegKernel_psiAssemble (F := F) N x) = x := by
  ext p
  simp only [siegKernel_psiAssemble_apply, siegKernel_psiAssembleInv_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, Pi.smul_apply, WithLp.ofLp_smul, OrthonormalBasis.repr_self,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem siegKernel_psiAssemble_psiAssembleInv (N : ℕ) (y : Fin N → KE F) :
    siegKernel_psiAssemble (F := F) N (siegKernel_psiAssembleInv (F := F) N y) = y := by
  ext j
  simp only [siegKernel_psiAssemble_apply, siegKernel_psiAssembleInv_apply]
  exact OrthonormalBasis.sum_repr
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) (y j)

theorem siegKernel_psiAssemble_injective (N : ℕ) :
    Function.Injective (siegKernel_psiAssemble (F := F) N) := by
  intro x y h
  have h' := congrArg (siegKernel_psiAssembleInv (F := F) N) h
  rwa [siegKernel_psiAssembleInv_psiAssemble, siegKernel_psiAssembleInv_psiAssemble] at h'

theorem siegKernel_psiAssemble_single (N : ℕ)
    (q : Fin N × NumberField.mixedEmbedding.index F) :
    siegKernel_psiAssemble (F := F) N (Pi.single q 1) =
      Pi.single q.1 (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F q.2) := by
  ext j
  rw [siegKernel_psiAssemble_apply]
  by_cases h : j = q.1
  · subst h
    rw [Finset.sum_eq_single q.2]
    · simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne (show (q.1, c) ≠ (q.1, q.2) from fun hh => hc (Prod.mk.inj hh).2)]
      simp
    · intro hh; exact absurd (Finset.mem_univ q.2) hh
  · rw [Pi.single_eq_of_ne h]
    exact Finset.sum_eq_zero (fun c _ => by
      rw [Pi.single_eq_of_ne (show (j, c) ≠ q from fun hh => h (Prod.mk.inj hh).1)]
      simp)

/-! ## The algebra of `mulK` -/

theorem siegKernel_mulK_add (x y : F) : mulK (x + y) = mulK x + mulK y := by
  ext z
  simp only [LinearMap.add_apply, mulK_apply, map_add, add_mul]

theorem siegKernel_mulK_mul (x y : F) : mulK (x * y) = (mulK x).comp (mulK y) := by
  ext z
  simp [mulK]

theorem siegKernel_mulK_zero : mulK (0 : F) = 0 := by
  ext z
  simp [mulK]

theorem siegKernel_mulK_sum {ι : Type*} (s : Finset ι) (f : ι → F) (y : KE F) :
    mulK (∑ i ∈ s, f i) y = ∑ i ∈ s, mulK (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [siegKernel_mulK_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, siegKernel_mulK_add, LinearMap.add_apply, ih]

/-! ## The matrix of `Phi a` in the orthonormal basis -/

theorem siegKernel_Phi_single {M N : ℕ} (a : Fin M → Fin N → F) (j : Fin N) (v : KE F)
    (i : Fin M) :
    Phi a (Pi.single j v) i = mulK (a i j) v := by
  rw [Phi_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem siegKernel_PhiMat_apply_coe {M N : ℕ} (a : Fin M → Fin N → F) (i : Fin M)
    (c : NumberField.mixedEmbedding.index F) (j : Fin N)
    (c' : NumberField.mixedEmbedding.index F) :
    PhiMat a (i, c) (j, c') =
      inner ℝ (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c)
        (mulK (a i j) (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c')) := by
  simp only [PhiMat, Phi_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The matrix model agrees with the mixed-space model -/

theorem siegKernel_psiAssemble_mulVec_lin {M N : ℕ} (a : Fin M → Fin N → F) :
    (siegKernel_psiAssemble (F := F) M).comp (Matrix.mulVecLin (PhiMat a)) =
      (Phi (F := F) a).comp (siegKernel_psiAssemble (F := F) N) := by
  refine Module.Basis.ext (Pi.basisFun ℝ (Fin N × NumberField.mixedEmbedding.index F)) fun q => ?_
  obtain ⟨j, c'⟩ := q
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one, siegKernel_psiAssemble_single]
  ext i
  rw [siegKernel_Phi_single, siegKernel_psiAssemble_apply]
  simp only [Matrix.col_apply, siegKernel_PhiMat_apply_coe]
  exact OrthonormalBasis.sum_repr'
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F)
    (mulK (a i j) (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c'))

theorem siegKernel_psiAssemble_mulVec {M N : ℕ} (a : Fin M → Fin N → F)
    (x : Fin N × NumberField.mixedEmbedding.index F → ℝ) :
    siegKernel_psiAssemble (F := F) M ((PhiMat a).mulVec x)
      = Phi (F := F) a (siegKernel_psiAssemble (F := F) N x) := by
  have h := LinearMap.congr_fun (siegKernel_psiAssemble_mulVec_lin (F := F) a) x
  simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply] using h

/-! ## Surjectivity of `Phi a` -/

/-- If the rows of `a` are `F`-linearly independent then there are coefficients `b` with
`∑ j, a i j * b j i' = δ_{i i'}`. -/
theorem siegKernel_exists_rightInverse {M N : ℕ} (a : Fin M → Fin N → F)
    (hli : LinearIndependent F a) :
    ∃ b : Fin N → Fin M → F, ∀ i i', ∑ j, a i j * b j i' = if i = i' then 1 else 0 := by
  classical
  have hrow : LinearIndependent F (Matrix.of a).row := hli
  have hrank : (Matrix.of a).rank = M := by
    rw [LinearIndependent.rank_matrix hrow, Fintype.card_fin]
  have hfin : Module.finrank F (LinearMap.range (Matrix.of a).mulVecLin) = M := by
    rw [← Matrix.rank, hrank]
  have htop : LinearMap.range (Matrix.of a).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨S, hS⟩ := LinearMap.exists_rightInverse_of_surjective (Matrix.of a).mulVecLin htop
  have hS' : ∀ v, (Matrix.of a).mulVecLin (S v) = v := fun v => by
    have h := LinearMap.congr_fun hS v
    simpa using h
  refine ⟨fun j i' => S (Pi.single i' (1 : F)) j, fun i i' => ?_⟩
  have h := congrFun (hS' (Pi.single i' (1 : F))) i
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply, dotProduct] at h
  simpa [Matrix.row, Pi.single_apply] using h

/-- If the rows of `a` are `F`-linearly independent then `Phi a` is surjective. -/
theorem siegKernel_Phi_surjective {M N : ℕ} (a : Fin M → Fin N → F)
    (hli : LinearIndependent F a) :
    Function.Surjective (Phi (F := F) a) := by
  classical
  obtain ⟨b, hb⟩ := siegKernel_exists_rightInverse (F := F) a hli
  let Φinv : (Fin M → KE F) →ₗ[ℝ] (Fin N → KE F) :=
    { toFun := fun v j => ∑ i', mulK (b j i') (v i')
      map_add' := by
        intro v w
        ext j
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext j
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply] }
  refine fun v => ⟨Φinv v, ?_⟩
  ext i
  rw [Phi_apply]
  show (∑ j, mulK (a i j) (Φinv v j)) = v i
  have hΦ : ∀ j, Φinv v j = ∑ i', mulK (b j i') (v i') := fun j => rfl
  calc ∑ j, mulK (a i j) (Φinv v j)
      = ∑ j, ∑ i', mulK (a i j) (mulK (b j i') (v i')) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΦ j, map_sum]
    _ = ∑ j, ∑ i', mulK (a i j * b j i') (v i') := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [siegKernel_mulK_mul]
        rfl
    _ = ∑ i', ∑ j, mulK (a i j * b j i') (v i') := Finset.sum_comm
    _ = ∑ i', mulK (∑ j, a i j * b j i') (v i') := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [siegKernel_mulK_sum]
    _ = ∑ i', mulK (if i = i' then 1 else 0) (v i') :=
        Finset.sum_congr rfl fun i' _ => by rw [hb i i']
    _ = mulK (1 : F) (v i) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          have hij : ¬ (i = j) := fun h => hj h.symm
          simp [hij, siegKernel_mulK_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
    _ = v i := by rw [mulK_one]; rfl

/-! ## Dimension of the coordinate spaces -/

theorem siegKernel_card_index (F : Type*) [Field F] [NumberField F] :
    Fintype.card (NumberField.mixedEmbedding.index F) = Module.finrank ℚ F := by
  have h1 := Module.finrank_eq_card_basis
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).toBasis
  exact h1.symm.trans (NumberField.mixedEmbedding.euclidean.finrank F)

theorem siegKernel_finrank_eucl (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F))
      = Module.finrank ℚ F * N := by
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, siegKernel_card_index]
  ring

/-! ## Surjectivity of `PhiE a`, the dimension of its kernel, and the isometry -/

theorem siegKernel_PhiE_surjective {M N : ℕ} (a : Fin M → Fin N → F)
    (hli : LinearIndependent F a) : Function.Surjective (PhiE a) := by
  intro x
  obtain ⟨y, hy⟩ :=
    siegKernel_Phi_surjective (F := F) a hli (siegKernel_psiAssemble (F := F) M x.ofLp)
  refine ⟨WithLp.toLp 2 (siegKernel_psiAssembleInv (F := F) N y), ?_⟩
  have h1 : (PhiE a (WithLp.toLp 2 (siegKernel_psiAssembleInv (F := F) N y))).ofLp
      = (PhiMat a).mulVec (siegKernel_psiAssembleInv (F := F) N y) := by
    rw [PhiE, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  have h2 : siegKernel_psiAssemble (F := F) M
        ((PhiMat a).mulVec (siegKernel_psiAssembleInv (F := F) N y))
      = siegKernel_psiAssemble (F := F) M x.ofLp := by
    rw [siegKernel_psiAssemble_mulVec, siegKernel_psiAssemble_psiAssembleInv]
    exact hy
  have h3 : (PhiMat a).mulVec (siegKernel_psiAssembleInv (F := F) N y) = x.ofLp :=
    siegKernel_psiAssemble_injective (F := F) M h2
  exact (WithLp.equiv 2 (Fin M × NumberField.mixedEmbedding.index F → ℝ)).injective
    (h1.trans h3)

theorem siegKernel_finrank_ker {M N : ℕ} (a : Fin M → Fin N → F)
    (hsurj : Function.Surjective (PhiE a)) :
    Module.finrank ℝ ↥(LinearMap.ker (PhiE a :
      EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))
      = Module.finrank ℚ F * (N - M) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  rw [finrank_top, siegKernel_finrank_eucl F N, siegKernel_finrank_eucl F M] at h
  have hexp : Module.finrank ℚ F * (N - M)
      = Module.finrank ℚ F * N - Module.finrank ℚ F * M := Nat.mul_sub_left_distrib _ _ _
  rw [hexp]
  omega

theorem siegKernel_kernel_isometry {M N : ℕ} (a : Fin M → Fin N → F)
    (hsurj : Function.Surjective (PhiE a)) :
    Nonempty (EuclideanSpace ℝ (Fin (Module.finrank ℚ F * (N - M))) ≃ᵢ
      ↥(LinearMap.ker (PhiE a :
        EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))) := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :=
    LinearMap.ker (PhiE a)
  have hdim : Module.finrank ℝ K = Module.finrank ℚ F * (N - M) :=
    siegKernel_finrank_ker (F := F) a hsurj
  exact ⟨(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim).symm).trans
    (stdOrthonormalBasis ℝ K).repr.symm |>.toIsometryEquiv⟩

end

end Work.BW

namespace Work.BW

theorem sieg2_kernel_isometry {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    Nonempty (EuclideanSpace ℝ (Fin (Module.finrank ℚ F * (N - M))) ≃ᵢ
      ↥(LinearMap.ker (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))) :=
  siegKernel_kernel_isometry (F := F) a (siegKernel_PhiE_surjective (F := F) a hli)

end Work.BW
