import Mathlib
import Submission.Commons.Lattice.Module.exists_basis_subtype_kernel
import Submission.Commons.Lattice.Minkowski.kerLattice_basis_wedge_le
import Submission.Commons.Lattice.Minkowski.covol_span_wedge
import Submission.Commons.Lattice.Minkowski.covolume_le_covolume_of_le
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_eq_abs_det
import Submission.Commons.Analysis.InnerProductSpace.sq_norm_iMulti_eq_det_transpose_mul
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
import Submission.Commons.LinearAlgebra.Matrix.det_transpose_mul_le_of_kernel
import Submission.Commons.NumberTheory.NumberField.exists_uniform_ringOfIntegers_basis_house_le
import Submission.Commons.Lattice.Minkowski.exists_short_independent_of_basis
set_option maxHeartbeats 1000000
open Module NumberField MeasureTheory
open NumberField.mixedEmbedding
open scoped NumberField BigOperators NNReal ENNReal Classical Real
namespace Commons.NumberTheory.NumberField

open Module NumberField
open scoped NumberField BigOperators



variable (K : Type*) [Field K] [NumberField K]

/-- The coordinate matrix of the tuple `y` with respect to an integral basis. -/
noncomputable def coordMat (N : ℕ) (y : Fin N → RingOfIntegers K)
    (eci : Fin (Module.finrank ℚ K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    Fin (Module.finrank ℚ K) → Fin N → ℤ :=
  fun i k => (RingOfIntegers.basis K).repr (y k) (eci i)

/-- The relation lattice: integer vectors `x` with `∑ x k • y k = 0`. -/
def relLat (N : ℕ) (y : Fin N → RingOfIntegers K) : Submodule ℤ (Fin N → ℤ) where
  carrier := {x | ∑ k : Fin N, ((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K) = 0}
  add_mem' {x z} hx hz := by
    rw [Set.mem_ofPred_eq] at hx hz ⊢
    rw [show (∑ k : Fin N, (((x + z) k : ℤ) : K) * ((y k : RingOfIntegers K) : K))
        = ∑ k : Fin N, (((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K)
            + ((z k : ℤ) : K) * ((y k : RingOfIntegers K) : K)) from
        Finset.sum_congr rfl (fun k _ => by simp [add_mul])]
    rw [Finset.sum_add_distrib, hx, hz, add_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [show (∑ k : Fin N, (((c • x) k : ℤ) : K) * ((y k : RingOfIntegers K) : K))
        = (c : K) * ∑ k : Fin N, (((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        simp [mul_assoc]]
    rw [hx, mul_zero]

/-- Key computation: the coordinates of `∑ k, c k • y k` in the integral basis. -/
lemma equivFun_sum_coordMat (N : ℕ) (y : Fin N → RingOfIntegers K)
    (eci : Fin (Module.finrank ℚ K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K))
    (c : Fin N → ℚ) :
    ((NumberField.integralBasis K).reindex eci.symm).equivFun
        (∑ k : Fin N, c k • ((y k : RingOfIntegers K) : K))
      = fun i => ∑ k : Fin N, c k * ((coordMat K N y eci i k : ℤ) : ℚ) := by
  classical
  funext i
  have hcoord_i : ∀ (i : Fin (Module.finrank ℚ K)) (k : Fin N),
      ((NumberField.integralBasis K).reindex eci.symm).equivFun
          (((y k : RingOfIntegers K) : K)) i
        = ((RingOfIntegers.basis K).repr (y k) (eci i) : ℚ) := by
    intro i k
    rw [Basis.equivFun_apply, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
    simp only [Equiv.symm_symm]
    rw [NumberField.integralBasis_repr_apply]
    rfl
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [hcoord_i i k]
  rfl

/-- Membership in the relation lattice is the vanishing of all coordinates. -/
lemma relLat_iff_coordMat (N : ℕ) (y : Fin N → RingOfIntegers K)
    (eci : Fin (Module.finrank ℚ K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (x : Fin N → ℤ) :
    x ∈ relLat K N y ↔
      ∀ i : Fin (Module.finrank ℚ K),
        ∑ k : Fin N, coordMat K N y eci i k * x k = 0 := by
  classical
  let bb : Basis (Fin (Module.finrank ℚ K)) ℚ K :=
    (NumberField.integralBasis K).reindex eci.symm
  have haK : (∑ k : Fin N, ((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K))
      = ∑ k : Fin N, (x k : ℚ) • ((y k : RingOfIntegers K) : K) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.smul_def]
    congr 1
    simp
  change (∑ k : Fin N, ((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K)) = 0 ↔ _
  rw [haK]
  have key : (∑ k : Fin N, (x k : ℚ) • ((y k : RingOfIntegers K) : K)) = 0 ↔
      bb.equivFun (∑ k : Fin N, (x k : ℚ) • ((y k : RingOfIntegers K) : K)) = 0 := by
    constructor
    · intro h; rw [h]; simp
    · intro h
      have := congrArg bb.equivFun.symm h
      simpa using this
  rw [key, equivFun_sum_coordMat K N y eci]
  simp only [funext_iff, Pi.zero_apply]
  constructor
  · intro h i
    have hi : (∑ k : Fin N, (x k : ℚ) * ((coordMat K N y eci i k : ℤ) : ℚ)) = 0 := by
      simpa using h i
    have hi' : ((∑ k : Fin N, coordMat K N y eci i k * x k : ℤ) : ℚ) = 0 := by
      push_cast
      rw [← hi]
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact_mod_cast hi'
  · intro h i
    have hi : ((∑ k : Fin N, coordMat K N y eci i k * x k : ℤ) : ℚ) = 0 := by
      rw [show (∑ k : Fin N, coordMat K N y eci i k * x k) = 0 from h i]
      norm_num
    push_cast at hi
    rw [← hi]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- The rows of the coordinate matrix are linearly independent over `ℚ`. -/
lemma coordMat_rows_linearIndependent (N : ℕ) (y : Fin N → RingOfIntegers K)
    (eci : Fin (Module.finrank ℚ K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K))
    (hspan : Submodule.span ℚ (Set.range (fun i : Fin N => ((y i : RingOfIntegers K) : K))) = ⊤) :
    LinearIndependent ℚ
      (fun i : Fin (Module.finrank ℚ K) => fun k : Fin N => ((coordMat K N y eci i k : ℤ) : ℚ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : ∀ k : Fin N,
      ∑ i : Fin (Module.finrank ℚ K), g i * ((coordMat K N y eci i k : ℤ) : ℚ) = 0 := by
    intro k
    have := congrFun hg k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  intro i₀
  set bb := (NumberField.integralBasis K).reindex eci.symm with hbb
  have hmem : (bb i₀) ∈ Submodule.span ℚ
      (Set.range (fun i : Fin N => ((y i : RingOfIntegers K) : K))) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  have hc2 : bb.equivFun (bb i₀)
      = fun i => ∑ k : Fin N, c k * ((coordMat K N y eci i k : ℤ) : ℚ) := by
    rw [← hc]
    exact equivFun_sum_coordMat K N y eci c
  have hdelta : ∀ i : Fin (Module.finrank ℚ K),
      (∑ k : Fin N, c k * ((coordMat K N y eci i k : ℤ) : ℚ)) = if i₀ = i then 1 else 0 := by
    intro i
    rw [← congrFun hc2 i, Basis.equivFun_apply, hbb, Basis.repr_self_apply]
  calc g i₀ = ∑ i : Fin (Module.finrank ℚ K), g i * (if i₀ = i then (1:ℚ) else 0) := by
        symm
        rw [Finset.sum_eq_single i₀ (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero])
          (fun h => absurd (Finset.mem_univ i₀) h)]
        simp
    _ = ∑ i : Fin (Module.finrank ℚ K), g i *
          (∑ k : Fin N, c k * ((coordMat K N y eci i k : ℤ) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdelta i]
    _ = ∑ i : Fin (Module.finrank ℚ K), ∑ k : Fin N,
          g i * (c k * ((coordMat K N y eci i k : ℤ) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ = ∑ k : Fin N, ∑ i : Fin (Module.finrank ℚ K),
          g i * (c k * ((coordMat K N y eci i k : ℤ) : ℚ)) := Finset.sum_comm
    _ = ∑ k : Fin N, c k * (∑ i : Fin (Module.finrank ℚ K),
          g i * ((coordMat K N y eci i k : ℤ) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [hg' k, mul_zero]

/-- **A `ℤ`-basis of `ℤ^N` adapted to the relation lattice.** -/
theorem exists_basis_relLat (N : ℕ) (hnN : Module.finrank ℚ K < N)
    (y : Fin N → RingOfIntegers K)
    (hspan : Submodule.span ℚ (Set.range (fun i : Fin N => ((y i : RingOfIntegers K) : K))) = ⊤) :
    ∃ e : Basis (Fin N) ℤ (Fin N → ℤ), ∀ x : Fin N → ℤ, x ∈ relLat K N y ↔
      ∃ a : Fin (N - Module.finrank ℚ K) → ℤ,
        x = ∑ r, a r • e (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)) r) := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Module.finrank ℚ K := by
    rw [← finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank]
  let eci : Fin (Module.finrank ℚ K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) :=
    (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := Commons.Lattice.Module.exists_basis_subtype_kernel hnN
    (coordMat K N y eci) (coordMat_rows_linearIndependent K N y eci hspan)
  exact ⟨e, fun x => (relLat_iff_coordMat K N y eci x).trans (he x)⟩



open Module NumberField MeasureTheory
open NumberField.mixedEmbedding
open scoped NumberField BigOperators NNReal ENNReal Classical



variable (K : Type*) [Field K] [NumberField K]

/-- The mixed embedding into the Euclidean mixed space (as a plain function). -/
noncomputable def Mex (a : K) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (NumberField.mixedEmbedding K a)

lemma Mex_add (a b : K) : Mex K (a + b) = Mex K a + Mex K b := by
  simp [Mex]

lemma Mex_smul (q : ℚ) (a : K) : Mex K (q • a) = q • Mex K a := by
  have h : NumberField.mixedEmbedding K (q • a) = q • NumberField.mixedEmbedding K a :=
    map_ratCast_smul (NumberField.mixedEmbedding K) ℚ ℝ q a
  rw [Mex, Mex, h]
  exact (euclidean.toMixed K).symm.toLinearEquiv.map_smul q (NumberField.mixedEmbedding K a)

lemma Mex_sum {ι : Type*} [Fintype ι] (f : ι → K) :
    Mex K (∑ i, f i) = ∑ i, Mex K (f i) := by
  simp [Mex]

/-- The `l`-th mixed coordinate of `a`, written as an inner product. -/
noncomputable def mcoord (l : NumberField.mixedEmbedding.index K) (a : K) : ℝ :=
  inner ℝ ((euclidean.stdOrthonormalBasis K) l) (Mex K a)

/-- The coordinate is the corresponding `stdBasis` coordinate. -/
lemma mcoord_eq_stdBasis (l : NumberField.mixedEmbedding.index K) (a : K) :
    mcoord K l a
      = (NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a) l := by
  have h1 : mcoord K l a = ((euclidean.stdOrthonormalBasis K).repr (Mex K a)) l := by
    rw [mcoord, OrthonormalBasis.repr_apply_apply]
  have h2 : ((euclidean.stdOrthonormalBasis K).repr (Mex K a)) l
      = (NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a) l := by
    rw [← NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq K, Basis.map_repr]
    simp [Mex]
  rw [h1, h2]

/-- Each mixed coordinate of an algebraic element is bounded by its house. -/
lemma abs_mcoord_le_house (l : NumberField.mixedEmbedding.index K) (a : K) :
    |mcoord K l a| ≤ NumberField.house a := by
  classical
  rw [mcoord_eq_stdBasis]
  rcases l with w | wj
  · rw [NumberField.mixedEmbedding.stdBasis_apply_isReal]
    simp only [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    rw [show |InfinitePlace.embedding_of_isReal w.prop a| = ‖((InfinitePlace.embedding_of_isReal w.prop a : ℝ) : ℂ)‖
      from (Complex.norm_real _).symm]
    rw [InfinitePlace.embedding_of_isReal_apply]
    exact NumberField.norm_embedding_le_house a (InfinitePlace.embedding w)
  · rcases wj with ⟨w, j⟩
    fin_cases j
    · change |((NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a)) (Sum.inr (w, (0 : Fin 2)))| ≤ NumberField.house a
      rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst]
      simp only [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
      refine (Complex.abs_re_le_norm _).trans ?_
      exact NumberField.norm_embedding_le_house a ((w : InfinitePlace K).embedding)
    · change |((NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a)) (Sum.inr (w, (1 : Fin 2)))| ≤ NumberField.house a
      rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd]
      simp only [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
      refine (Complex.abs_im_le_norm _).trans ?_
      exact NumberField.norm_embedding_le_house a ((w : InfinitePlace K).embedding)



/-- The mixed embedding is additive and ℚ-homogeneous, `ℤ`-sums. -/
lemma sum_smul_mex (N : ℕ) (y : Fin N → RingOfIntegers K) (x : Fin N → ℤ) :
    (∑ t : Fin N, (((x t : ℤ) : ℝ)) • Mex K (((y t : RingOfIntegers K) : K)))
      = Mex K (∑ t : Fin N, (((x t : ℤ) : K)) * (((y t : RingOfIntegers K) : K))) := by
  rw [Mex_sum]
  apply Finset.sum_congr rfl
  intro t _
  have h1 : (((x t : ℤ) : K)) * (((y t : RingOfIntegers K) : K))
      = ((x t : ℚ)) • (((y t : RingOfIntegers K) : K)) := by
    rw [Algebra.smul_def]
    congr 1
    simp
  have h2 : ((x t : ℚ)) • (Mex K (((y t : RingOfIntegers K) : K)))
      = (((x t : ℤ) : ℝ)) • (Mex K (((y t : RingOfIntegers K) : K))) := by
    rfl
  rw [h1, Mex_smul, h2]

/-- Inner product with a mixed coordinate against a combination of the `y k`. -/
lemma inner_sum_mex (N : ℕ) (y : Fin N → RingOfIntegers K)
    (l : NumberField.mixedEmbedding.index K) (x : Fin N → ℝ) :
    inner ℝ ((euclidean.stdOrthonormalBasis K) l)
        (∑ t : Fin N, x t • Mex K (((y t : RingOfIntegers K) : K)))
      = ∑ t : Fin N, x t * mcoord K l (((y t : RingOfIntegers K) : K)) := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [real_inner_smul_right]
  rfl

/-- The `ℤ`-linear map `x ↦ ∑ x k • y k` into the ring of integers. -/
noncomputable def phiInt (N : ℕ) (y : Fin N → RingOfIntegers K) :
    (Fin N → ℤ) →ₗ[ℤ] RingOfIntegers K where
  toFun x := ∑ k, x k • y k
  map_add' x z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Pi.add_apply, add_smul]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Pi.smul_apply, smul_assoc]

/-- Membership in the relation lattice is vanishing of the `ℤ`-linear map `x ↦ ∑ x k • y k`. -/
lemma relLat_eq_ker_phiInt (N : ℕ) (y : Fin N → RingOfIntegers K) :
    relLat K N y = LinearMap.ker (phiInt K N y) := by
  ext x
  rw [LinearMap.mem_ker]
  have h1 : ((phiInt K N y x : RingOfIntegers K) : K)
      = ∑ k, (((x k : ℤ)) : K) * (((y k : RingOfIntegers K) : K)) := by
    show algebraMap (RingOfIntegers K) K (∑ k, x k • y k) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_zsmul, zsmul_eq_mul]
  constructor
  · intro hx
    change (∑ k : Fin N, ((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K)) = 0 at hx
    have h2 : ((phiInt K N y x : RingOfIntegers K) : K) = 0 := by
      rw [h1]; exact hx
    exact Subtype.coe_injective h2
  · intro hx
    change (∑ k : Fin N, ((x k : ℤ) : K) * ((y k : RingOfIntegers K) : K)) = 0
    rw [← h1, hx]
    rfl

/-- **Gram determinant identity for the kernel of a real matrix.** -/
theorem det_gram_eq_of_kernel {d n : ℕ} (hd : 0 < d)
    (B : Matrix (Fin n) (Fin d ⊕ Fin n) ℝ)
    (P : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.det = 1 ∨ P.det = -1)
    (hBP : ∀ (l : Fin n) (a : Fin d ⊕ Fin n),
      (B * P) l a = Sum.elim (fun _ : Fin d => (0 : ℝ)) (fun j : Fin n => S l j) a)
    (hG : ((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det ≠ 0) :
    (B * Matrix.transpose B).det =
      ((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det * S.det ^ 2 := by
  have h := Commons.LinearAlgebra.Matrix.det_transpose_mul_mul_sq (k := d) B P S hBP
  have hP2 : P.det ^ 2 = 1 := by rcases hP with h | h <;> rw [h] <;> norm_num
  rw [hP2, mul_one] at h
  have h2 : ((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det *
      (B * Matrix.transpose B).det =
      ((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det *
        (((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det * S.det ^ 2) := by
    rw [h]; ring
  exact mul_left_cancel₀ hG h2


/-- An integer vector as an element of `EuclideanSpace ℝ (Fin N)`. -/
noncomputable def intVec (N : ℕ) (x : Fin N → ℤ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun k => (x k : ℝ))

lemma intVec_eq_withLp (N : ℕ) (x : Fin N → ℤ) :
    intVec N x = (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (x k : ℝ)) := by
  rw [intVec, WithLp.equiv_symm_apply]

lemma intVec_ofLp (N : ℕ) (x : Fin N → ℤ) (k : Fin N) :
    (intVec N x).ofLp k = (x k : ℝ) := by
  rw [intVec, WithLp.ofLp_toLp]

lemma inner_intVec_intVec (N : ℕ) (x x' : Fin N → ℤ) :
    inner ℝ (intVec N x) (intVec N x') = ∑ k, (x k : ℝ) * (x' k : ℝ) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [intVec_ofLp, intVec_ofLp, RCLike.inner_apply]
  rw [← RCLike.star_def, star_trivial]
  ring

/-- The `ℝ`-linear map `x ↦ ∑ x k • y k` into the mixed space. -/
noncomputable def Amap (N : ℕ) (y : Fin N → RingOfIntegers K) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] euclidean.mixedSpace K where
  toFun x := ∑ k, x.ofLp k • Mex K (((y k : RingOfIntegers K) : K))
  map_add' x z := by
    simp only [WithLp.ofLp_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Pi.add_apply, add_smul]
  map_smul' c x := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ => smul_assoc c (x.ofLp k) (Mex K (((y k : RingOfIntegers K) : K))))

lemma Amap_apply (N : ℕ) (y : Fin N → RingOfIntegers K) (x : EuclideanSpace ℝ (Fin N)) :
    Amap K N y x = ∑ k, x.ofLp k • Mex K (((y k : RingOfIntegers K) : K)) := rfl

lemma Amap_intVec (N : ℕ) (y : Fin N → RingOfIntegers K) (x : Fin N → ℤ) :
    Amap K N y (intVec N x)
      = ∑ k, ((x k : ℤ) : ℝ) • Mex K (((y k : RingOfIntegers K) : K)) := by
  rw [Amap_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [intVec_ofLp]

/-- The inverse of the `WithLp` linear equivalence is `WithLp.toLp`. -/
lemma WithLp_linearEquiv_symm_eq_toLp {p : ℝ≥0∞} {K' V : Type*} [Semiring K'] [AddCommGroup V]
    [Module K' V] (x : V) :
    (WithLp.linearEquiv p K' V).symm x = WithLp.toLp p x := by
  conv_lhs => rw [← WithLp.toLp_ofLp p ((WithLp.linearEquiv p K' V).symm x)]
  congr 1


lemma intVec_add (N : ℕ) (x x' : Fin N → ℤ) :
    intVec N (x + x') = intVec N x + intVec N x' := by
  apply WithLp.ofLp_injective
  ext k
  simp [intVec_ofLp]

lemma intVec_smul (N : ℕ) (c : ℤ) (x : Fin N → ℤ) :
    intVec N (c • x) = (c : ℝ) • intVec N x := by
  apply WithLp.ofLp_injective
  ext k
  simp [intVec_ofLp]

lemma intVec_sum (N : ℕ) {ι : Type*} [Fintype ι] (f : ι → Fin N → ℤ) :
    intVec N (∑ i, f i) = ∑ i, intVec N (f i) := by
  apply WithLp.ofLp_injective
  ext k
  simp only [intVec_ofLp, WithLp.ofLp_sum, Finset.sum_apply]
  push_cast
  rfl

/-- The image under `Amap` of an integer vector, in terms of the coordinates in the adapted
basis `e`. -/
lemma Amap_expand {d n : ℕ} {N : ℕ} (y : Fin N → RingOfIntegers K) (e : Basis (Fin N) ℤ (Fin N → ℤ))
    (σ : Fin d ⊕ Fin n ≃ Fin N) (vv : Fin n → euclidean.mixedSpace K)
    (hker : ∀ r : Fin d, Amap K N y (intVec N (e (σ (Sum.inl r)))) = 0)
    (hvv : ∀ j : Fin n, Amap K N y (intVec N (e (σ (Sum.inr j)))) = vv j)
    (x : Fin N → ℤ) :
    Amap K N y (intVec N x)
      = ∑ j : Fin n, (((e.equivFun x) (σ (Sum.inr j)) : ℤ) : ℝ) • vv j := by
  have hrepr : x = ∑ i, ((e.equivFun x i : ℤ)) • e i := by
    conv_lhs => rw [← e.sum_repr x]
    apply Finset.sum_congr rfl
    intro i _
    rw [Basis.equivFun_apply]
  conv_lhs => rw [hrepr]
  rw [intVec_sum]
  rw [show (∑ i : Fin N, intVec N (((e.equivFun x i : ℤ)) • e i))
      = ∑ i : Fin N, (((e.equivFun x i : ℤ)) : ℝ) • intVec N (e i) from by
    apply Finset.sum_congr rfl
    intro i _
    rw [intVec_smul]]
  rw [map_sum]
  rw [show (∑ i : Fin N, Amap K N y ((((e.equivFun x i : ℤ)) : ℝ) • intVec N (e i)))
      = ∑ i : Fin N, (((e.equivFun x i : ℤ)) : ℝ) • Amap K N y (intVec N (e i)) from by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]]
  rw [← Equiv.sum_comp σ (fun t : Fin N => (((e.equivFun x t : ℤ)) : ℝ) • Amap K N y (intVec N (e t)))]
  rw [Fintype.sum_sum_type]
  simp only [hker, smul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [hvv j]

lemma Mex_injective (K : Type*) [Field K] [NumberField K] : Function.Injective (Mex K) := by
  intro a b h
  have h2 : NumberField.mixedEmbedding K a = NumberField.mixedEmbedding K b := by
    have := congrArg (euclidean.toMixed K) h
    simpa [Mex] using this
  exact NumberField.mixedEmbedding_injective (K := K) h2

/-- The coercion of `phiInt` to `K`. -/
lemma coe_phiInt (N : ℕ) (y : Fin N → RingOfIntegers K) (x : Fin N → ℤ) :
    (((phiInt K N y x : RingOfIntegers K)) : K)
      = ∑ k, (((x k : ℤ)) : K) * (((y k : RingOfIntegers K) : K)) := by
  show algebraMap (RingOfIntegers K) K (∑ k, x k • y k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, zsmul_eq_mul]

lemma Amap_intVec_eq (N : ℕ) (y : Fin N → RingOfIntegers K) (x : Fin N → ℤ) :
    Amap K N y (intVec N x) = Mex K (((phiInt K N y x : RingOfIntegers K) : K)) := by
  rw [Amap_intVec, coe_phiInt, sum_smul_mex]

lemma Amap_intVec_eq_zero_iff (N : ℕ) (y : Fin N → RingOfIntegers K) (x : Fin N → ℤ) :
    Amap K N y (intVec N x) = 0 ↔ x ∈ relLat K N y := by
  rw [Amap_intVec_eq, relLat_eq_ker_phiInt, LinearMap.mem_ker]
  constructor
  · intro h
    have h2 : ((phiInt K N y x : RingOfIntegers K) : K) = 0 := by
      refine Mex_injective K ?_
      rw [h]
      simp [Mex]
    exact Subtype.coe_injective h2
  · intro h
    rw [h]
    simp [Mex]

lemma Mex_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℚ) (f : ι → K) :
    Mex K (∑ i, c i • f i) = ∑ i, c i • Mex K (f i) := by
  rw [Mex_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Mex_smul]

/-- The fundamental domain of an orthonormal basis has real volume `1`. -/
lemma volume_real_fundamentalDomain_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E) :
    MeasureTheory.volume.real (ZSpan.fundamentalDomain b.toBasis) = 1 := by
  have h1 := ZSpan.fundamentalDomain_ae_parallelepiped b.toBasis (volume : Measure E)
  have h2 : volume (ZSpan.fundamentalDomain b.toBasis) = volume (parallelepiped (⇑b)) := by
    have h1' : ZSpan.fundamentalDomain b.toBasis =ᵐ[volume] parallelepiped (⇑b) := by
      convert h1 using 3
      rw [OrthonormalBasis.coe_toBasis]
    exact measure_congr h1'
  rw [show MeasureTheory.volume.real (ZSpan.fundamentalDomain b.toBasis)
      = (volume (ZSpan.fundamentalDomain b.toBasis)).toReal from rfl, h2, b.volume_parallelepiped]
  simp

lemma sqrt_pow_of_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  conv_lhs => rw [← Real.rpow_natCast a n]
  conv_rhs => rw [← Real.rpow_natCast (a ^ (1/2:ℝ)) n]
  rw [← Real.rpow_mul ha, mul_comm, Real.rpow_mul (by positivity)]
/-- Bound on the covolume of the relation lattice, via the geometry of numbers. -/
theorem wedge_le_of_relation_lattice (N : ℕ) (y : Fin N → RingOfIntegers K) (B : ℝ)
    (hB : ∀ i, NumberField.house ((y i : RingOfIntegers K) : K) ≤ B)
    (hspan : Submodule.span ℚ (Set.range (fun i : Fin N => ((y i : RingOfIntegers K) : K))) = ⊤)
    (hnN : Module.finrank ℚ K < N)
    (e : Basis (Fin N) ℤ (Fin N → ℤ))
    (he : ∀ x : Fin N → ℤ, x ∈ relLat K N y ↔ ∃ a : Fin (N - Module.finrank ℚ K) → ℤ,
      x = ∑ r, a r • e (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)) r)) :
    ‖exteriorPower.ιMulti ℝ (N - Module.finrank ℚ K)
        (fun r => intVec N (e (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)) r)))‖
      ≤ (Real.sqrt N * (B + 1)) ^ (Module.finrank ℚ K) := by
  classical
  set n : ℕ := Module.finrank ℚ K with hn
  set d : ℕ := N - n with hd
  have hdpos : 0 < d := Nat.sub_pos_of_lt hnN
  have hdn : d + n = N := Nat.sub_add_cancel hnN.le
  -- `B ≥ 1`
  have hB1 : 1 ≤ B := by
    have hex : ∃ k : Fin N, ((y k : RingOfIntegers K) : K) ≠ 0 := by
      by_contra h
      push Not at h
      have hbot : Submodule.span ℚ (Set.range (fun i : Fin N => ((y i : RingOfIntegers K) : K)))
          = ⊥ := by
        rw [Submodule.span_eq_bot]
        rintro x ⟨i, rfl⟩
        exact h i
      rw [hspan] at hbot
      have h1 : (1 : K) ∈ (⊥ : Submodule ℚ K) := by rw [← hbot]; trivial
      simpa using h1
    obtain ⟨k, hk⟩ := hex
    refine (NumberField.one_le_house_of_isIntegral ?_ hk).trans (hB k)
    exact (IsIntegralClosure.isIntegral_iff (A := RingOfIntegers K) (R := ℤ) (B := K)).mpr ⟨y k, rfl⟩
  -- index equivalences
  have hcard : Fintype.card (NumberField.mixedEmbedding.index K) = n := by
    rw [hn, ← Module.finrank_eq_card_basis (NumberField.mixedEmbedding.stdBasis K)]
    exact NumberField.mixedEmbedding.finrank K
  let ec : Fin n ≃ NumberField.mixedEmbedding.index K := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Fin d ⊕ Fin n ≃ Fin N := Commons.Lattice.Minkowski.kernelSplitEquiv (n := n) hnN.le
  have hσ_inl : ∀ r : Fin d, σ (Sum.inl r) = Fin.castLE (Nat.sub_le N n) r :=
    fun r => Commons.Lattice.Minkowski.kernelSplitEquiv_inl hnN.le r
  -- the row matrix
  let Bm : Matrix (Fin n) (Fin N) ℝ := fun l k => mcoord K (ec l) (((y k : RingOfIntegers K) : K))
  have hBm_le : ∀ l k, |Bm l k| ≤ B := fun l k => (abs_mcoord_le_house K (ec l) _).trans (hB k)
  -- kernel vectors and lifts
  let u : Fin d → (Fin N → ℤ) := fun r => e (Fin.castLE (Nat.sub_le N n) r)
  let zz : Fin n → (Fin N → ℤ) := fun j => e (σ (Sum.inr j))
  -- the mixed images of the standard basis are ℝ-independent
  have hbase_li : LinearIndependent ℝ (fun t : Fin N => intVec N (e t)) := by
    set A : Matrix (Fin N) (Fin N) ℝ := ((Pi.basisFun ℤ (Fin N)).toMatrix e).map
      (fun z : ℤ => (z : ℝ)) with hA
    have hdet : A.det ≠ 0 := by
      rw [hA]
      rcases Commons.Lattice.Minkowski.det_toMatrix_basisFun_eq_one_or_neg_one e with h | h
      · rw [← Int.cast_det, h]; norm_num
      · rw [← Int.cast_det, h]; norm_num
    have hli : LinearIndependent ℝ A.col := by
      rw [Matrix.linearIndependent_cols_iff_isUnit]
      exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hcol : (fun t : Fin N => intVec N (e t))
        = fun t => (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (A.col t) := by
      funext t
      rw [WithLp_linearEquiv_symm_eq_toLp, intVec]
      congr 1
    rw [hcol]
    exact hli.map' _ (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.injective)
  have hu_li : LinearIndependent ℝ (fun r : Fin d => intVec N (u r)) :=
    hbase_li.comp (Fin.castLE (Nat.sub_le N n)) (Fin.castLE_injective _)
  -- the relation `u r` and the vanishing of its image
  have hu_mem : ∀ r : Fin d, u r ∈ relLat K N y := by
    intro r
    refine (he (u r)).mpr ⟨fun r' => if r' = r then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ r) h)]
    simp [u]
  have hu_ker : ∀ r : Fin d, Amap K N y (intVec N (u r)) = 0 := by
    intro r
    rw [Amap_intVec, sum_smul_mex K N y (u r)]
    have h0 : (∑ t : Fin N, (((u r t : ℤ)) : K) * (((y t : RingOfIntegers K) : K))) = 0 := hu_mem r
    rw [h0]
    simp [Mex]
  -- the matrices of the matrix identity
  let P : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ := fun a b => (((e (σ b)) (σ a) : ℤ) : ℝ)
  let BB : Matrix (Fin n) (Fin d ⊕ Fin n) ℝ := fun l a => Bm l (σ a)
  let S : Matrix (Fin n) (Fin n) ℝ := fun l j => (BB * P) l (Sum.inr j)
  have hP_eq : P = (((Pi.basisFun ℤ (Fin N)).toMatrix e).map (fun z : ℤ => (z : ℝ))).submatrix σ σ := by
    ext a b
    simp [P, Matrix.submatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]
  have hPdet : P.det = 1 ∨ P.det = -1 := by
    rw [hP_eq, Matrix.det_submatrix_equiv_self σ, ← Int.cast_det]
    rcases Commons.Lattice.Minkowski.det_toMatrix_basisFun_eq_one_or_neg_one e with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  have hBP : ∀ (l : Fin n) (a : Fin d ⊕ Fin n),
      (BB * P) l a = Sum.elim (fun _ : Fin d => (0 : ℝ)) (fun j : Fin n => S l j) a := by
    intro l a
    cases a with
    | inl r =>
      rw [Sum.elim_inl]
      have hcomp : (BB * P) l (Sum.inl r)
          = ∑ t : Fin N, Bm l t * (((u r) t : ℤ) : ℝ) := by
        rw [Matrix.mul_apply]
        rw [show (∑ a : Fin d ⊕ Fin n, BB l a * P a (Sum.inl r))
            = ∑ a : Fin d ⊕ Fin n, Bm l (σ a) * (((e (σ (Sum.inl r))) (σ a) : ℤ) : ℝ) from rfl]
        rw [Equiv.sum_comp σ (fun t => Bm l t * (((e (σ (Sum.inl r))) t : ℤ) : ℝ))]
        rw [hσ_inl]
      rw [hcomp]
      rw [show (∑ t : Fin N, Bm l t * (((u r) t : ℤ) : ℝ))
          = ∑ t : Fin N, (((u r) t : ℤ) : ℝ) * mcoord K (ec l) (((y t : RingOfIntegers K) : K)) from
        Finset.sum_congr rfl (fun t _ => by simp only [Bm]; ring)]
      rw [← inner_sum_mex K N y (ec l) (fun t => (((u r) t : ℤ) : ℝ))]
      rw [show (∑ t : Fin N, (((u r) t : ℤ) : ℝ) • Mex K (((y t : RingOfIntegers K) : K)))
          = Amap K N y (intVec N (u r)) from (Amap_intVec K N y (u r)).symm]
      rw [hu_ker r, inner_zero_right]
    | inr j => rfl
  have hG11 : ((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det
      = ‖exteriorPower.ιMulti ℝ d (fun r => intVec N (u r))‖ ^ 2 := by
    have hmat : (Matrix.transpose P * P).submatrix Sum.inl Sum.inl
        = Matrix.gram ℝ (fun r : Fin d => intVec N (u r)) := by
      ext r r'
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply]
      rw [show (∑ a : Fin d ⊕ Fin n, P a (Sum.inl r) * P a (Sum.inl r'))
          = ∑ t : Fin N, (((u r) t : ℤ) : ℝ) * (((u r') t : ℤ) : ℝ) from by
        rw [show (∑ a : Fin d ⊕ Fin n, P a (Sum.inl r) * P a (Sum.inl r'))
            = ∑ a : Fin d ⊕ Fin n, (((e (σ (Sum.inl r))) (σ a) : ℤ) : ℝ) *
                (((e (σ (Sum.inl r'))) (σ a) : ℤ) : ℝ) from rfl]
        rw [Equiv.sum_comp σ (fun t => (((e (σ (Sum.inl r))) t : ℤ) : ℝ) *
          (((e (σ (Sum.inl r'))) t : ℤ) : ℝ))]
        rw [hσ_inl]; rfl]
      rw [inner_intVec_intVec]
    rw [hmat, ← exteriorPower.inner_ιMulti_self,
      show inner ℝ (exteriorPower.ιMulti ℝ d (fun r => intVec N (u r)))
          (exteriorPower.ιMulti ℝ d (fun r => intVec N (u r)))
        = ‖exteriorPower.ιMulti ℝ d (fun r => intVec N (u r))‖ ^ 2 from
      (real_inner_self_eq_norm_sq _)]
  have hG : ((Matrix.transpose P * P).submatrix Sum.inl Sum.inl).det ≠ 0 := by
    rw [hG11]
    have hne : exteriorPower.ιMulti ℝ d (fun r => intVec N (u r)) ≠ 0 :=
      Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ hu_li
    simp [hne]
  have hid := det_gram_eq_of_kernel (d := d) (n := n) hdpos BB P S hPdet hBP hG
  -- #### bound on `det (BB * BBᵀ)`
  have hdiag_nonneg : ∀ l : Fin n, 0 ≤ (BB * Matrix.transpose BB) l l := by
    intro l
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun a _ => mul_self_nonneg _)
  have hdiag : ∀ l : Fin n, (BB * Matrix.transpose BB) l l ≤ (N : ℝ) * B ^ 2 := by
    intro l
    rw [Matrix.mul_apply]
    have h1 : ∑ a : Fin d ⊕ Fin n, BB l a * BB l a ≤ ∑ _a : Fin d ⊕ Fin n, B ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      have h2 := hBm_le l (σ a)
      have h3 : BB l a ^ 2 ≤ B ^ 2 := by
        simp only [BB]
        exact sq_le_sq' (by linarith [(abs_le.mp h2).1]) (abs_le.mp h2).2
      simpa [pow_two] using h3
    calc ∑ a : Fin d ⊕ Fin n, BB l a * BB l a
        = ∑ a : Fin d ⊕ Fin n, BB l a ^ 2 := by
          apply Finset.sum_congr rfl; intro a _; ring
      _ ≤ ∑ _a : Fin d ⊕ Fin n, B ^ 2 := by
          apply Finset.sum_le_sum
          intro a _
          have h2 := hBm_le l (σ a)
          have h3 : BB l a ^ 2 ≤ B ^ 2 := by
            simp only [BB]
            exact sq_le_sq' (by linarith [(abs_le.mp h2).1]) (abs_le.mp h2).2
          simpa [pow_two] using h3
      _ = ((N : ℝ) * B ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
            Fintype.card_fin, hdn, nsmul_eq_mul]
  -- the diagonal of `BB * BBᵀ` is the squared norm of a mixed row
  have hdiag_eq : ∀ l : Fin n, (BB * Matrix.transpose BB) l l
      = ∑ k : Fin N, (mcoord K (ec l) (((y k : RingOfIntegers K) : K))) ^ 2 := by
    intro l
    rw [Matrix.mul_apply]
    rw [show (∑ a : Fin d ⊕ Fin n, BB l a * BB.transpose a l)
        = ∑ a : Fin d ⊕ Fin n, BB l a * BB l a from
      Finset.sum_congr rfl (fun a _ => by
        exact congrArg (fun z => BB l a * z) (Matrix.transpose_apply BB a l))]
    simp only [BB]
    rw [Equiv.sum_comp σ (fun t : Fin N => Bm l t * Bm l t)]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Bm, sq]
  have hreal : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w},
      (∑ k : Fin N, (mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K))) ^ 2)
        ≤ (N : ℝ) * B ^ 2 := by
    intro w
    have h1 : ∀ k : Fin N, (mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K))) ^ 2 ≤ B ^ 2 := by
      intro k
      have h3 : |mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K))| ≤ B :=
        (abs_mcoord_le_house K (Sum.inl w) _).trans (hB k)
      nlinarith [abs_nonneg (mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K))),
        abs_le.mp h3, hB1, sq_abs (mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K)))]
    calc (∑ k : Fin N, (mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K))) ^ 2)
        ≤ ∑ _k : Fin N, B ^ 2 := Finset.sum_le_sum (fun k _ => h1 k)
      _ = (N : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcomplex_sum : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
      (∑ k : Fin N, (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
        + (∑ k : Fin N, (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
        ≤ (N : ℝ) * B ^ 2 := by
    intro w
    have h1 : ∀ k : Fin N,
        (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2
          + (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2
        ≤ B ^ 2 := by
      intro k
      have h2 : mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))
          = ((((w : InfinitePlace K).embedding) (((y k : RingOfIntegers K) : K))).re) := by
        rw [mcoord_eq_stdBasis, NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
          NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
      have h3 : mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))
          = ((((w : InfinitePlace K).embedding) (((y k : RingOfIntegers K) : K))).im) := by
        rw [mcoord_eq_stdBasis, NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd,
          NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
      have h4 : ‖((w : InfinitePlace K).embedding) (((y k : RingOfIntegers K) : K))‖ ≤ B :=
        (NumberField.norm_embedding_le_house _ _).trans (hB k)
      rw [h2, h3]
      have h5 : ((((w : InfinitePlace K).embedding) (((y k : RingOfIntegers K) : K))).re) ^ 2
          + ((((w : InfinitePlace K).embedding) (((y k : RingOfIntegers K) : K))).im) ^ 2
          = ‖((w : InfinitePlace K).embedding) (((y k : RingOfIntegers K) : K))‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [h5]
      exact pow_le_pow_left₀ (norm_nonneg _) h4 2
    calc (∑ k : Fin N, (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
          + (∑ k : Fin N, (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
        = ∑ k : Fin N, ((mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2
          + (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2) := by
          rw [Finset.sum_add_distrib]
      _ ≤ ∑ _k : Fin N, B ^ 2 := Finset.sum_le_sum (fun k _ => h1 k)
      _ = (N : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpair : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
      (∑ k : Fin N, (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
        * (∑ k : Fin N, (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
        ≤ ((N : ℝ) * B ^ 2 / 2) ^ 2 := by
    intro w
    have h3 := hcomplex_sum w
    have h4 : (0:ℝ) ≤ (∑ k : Fin N, (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2) :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have h5 : (0:ℝ) ≤ (∑ k : Fin N, (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2) :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    nlinarith [sq_nonneg ((∑ k : Fin N, (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
      - (∑ k : Fin N, (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2))]
  have hprod_le : ∏ l : Fin n, (BB * Matrix.transpose BB) l l
      ≤ (((N : ℝ) * B ^ 2) ^ n) / 4 ^ (NumberField.InfinitePlace.nrComplexPlaces K) := by
    rw [Finset.prod_congr rfl (fun l _ => hdiag_eq l)]
    rw [show (∏ l : Fin n, (∑ k : Fin N, (mcoord K (ec l) (((y k : RingOfIntegers K) : K))) ^ 2))
        = ∏ l : NumberField.mixedEmbedding.index K,
            (∑ k : Fin N, (mcoord K l (((y k : RingOfIntegers K) : K))) ^ 2) from
      Fintype.prod_equiv ec _ _ (fun _ => rfl)]
    rw [Fintype.prod_sum_type]
    have h2 : ∏ a : ({w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} × Fin 2),
        (∑ k : Fin N, (mcoord K (Sum.inr a) (((y k : RingOfIntegers K) : K))) ^ 2)
        ≤ (((N : ℝ) * B ^ 2 / 2) ^ 2) ^ (NumberField.InfinitePlace.nrComplexPlaces K) := by
      rw [Fintype.prod_prod_type (f := fun (a : ({w : InfinitePlace K //
          NumberField.InfinitePlace.IsComplex w} × Fin 2)) =>
        (∑ k : Fin N, (mcoord K (Sum.inr a) (((y k : RingOfIntegers K) : K))) ^ 2))]
      calc ∏ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ∏ j : Fin 2,
            (∑ k : Fin N, (mcoord K (Sum.inr (w, j)) (((y k : RingOfIntegers K) : K))) ^ 2)
          = ∏ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
              ((∑ k : Fin N, (mcoord K (Sum.inr (w, (0 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)
                * (∑ k : Fin N, (mcoord K (Sum.inr (w, (1 : Fin 2))) (((y k : RingOfIntegers K) : K))) ^ 2)) := by
            apply Finset.prod_congr rfl
            intro w _
            rw [Fin.prod_univ_two]
        _ ≤ ∏ _w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
              (((N : ℝ) * B ^ 2 / 2) ^ 2) :=
            Finset.prod_le_prod (fun w _ => mul_nonneg
              (Finset.sum_nonneg (fun k _ => sq_nonneg _))
              (Finset.sum_nonneg (fun k _ => sq_nonneg _))) (fun w _ => hpair w)
        _ = (((N : ℝ) * B ^ 2 / 2) ^ 2) ^ (NumberField.InfinitePlace.nrComplexPlaces K) := by
            rw [Finset.prod_const, Finset.card_univ]
    have h3 : ∏ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w},
        (∑ k : Fin N, (mcoord K (Sum.inl w) (((y k : RingOfIntegers K) : K))) ^ 2)
        ≤ ∏ _w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ((N : ℝ) * B ^ 2) :=
      Finset.prod_le_prod (fun w _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
        (fun w _ => hreal w)
    refine (mul_le_mul h3 h2 (by positivity) (by positivity)).trans ?_
    rw [Finset.prod_const, Finset.card_univ]
    have hcard : NumberField.InfinitePlace.nrRealPlaces K
        + 2 * NumberField.InfinitePlace.nrComplexPlaces K = n := by
      rw [hn, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]
    have h4eq : ((N:ℝ)*B^2/2)^2 = ((N:ℝ)*B^2)^2 / 4 := by ring
    rw [h4eq, div_pow, ← pow_mul, ← mul_div_assoc, ← pow_add, hcard]
  have hdetBB : (BB * Matrix.transpose BB).det
      ≤ (((N : ℝ) * B ^ 2) ^ n) / 4 ^ (NumberField.InfinitePlace.nrComplexPlaces K) := by
    have hpsd : (BB * Matrix.transpose BB).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose BB
    exact (Commons.Analysis.InnerProductSpace.Hadamard.det_le_prod_diag_of_posSemidef _ hpsd).trans hprod_le
  -- #### the lower bound for `det S`
  let aK : Fin n → RingOfIntegers K := fun j => phiInt K N y (zz j)
  let vv : Fin n → euclidean.mixedSpace K := fun j => Mex K ((aK j : RingOfIntegers K) : K)
  have hvv_eq : ∀ j : Fin n, vv j
      = ∑ t : Fin N, (((zz j t : ℤ) : ℝ)) • Mex K (((y t : RingOfIntegers K) : K)) := by
    intro j
    rw [show vv j = Amap K N y (intVec N (zz j)) from (Amap_intVec_eq K N y (zz j)).symm,
      Amap_intVec]
  have hS_apply : ∀ (l j : Fin n), S l j
      = inner ℝ ((euclidean.stdOrthonormalBasis K) (ec l)) (vv j) := by
    intro l j
    rw [hvv_eq j, inner_sum_mex]
    rw [show S l j = ∑ t : Fin N, Bm l t * (((zz j) t : ℤ) : ℝ) from ?_]
    · apply Finset.sum_congr rfl
      intro t _
      ring
    · rw [show S l j = (BB * P) l (Sum.inr j) from rfl, Matrix.mul_apply]
      rw [show (∑ a : Fin d ⊕ Fin n, BB l a * P a (Sum.inr j))
          = ∑ a : Fin d ⊕ Fin n, Bm l (σ a) * (((zz j) (σ a) : ℤ) : ℝ) from rfl]
      rw [Equiv.sum_comp σ (fun t : Fin N => Bm l t * (((zz j) t : ℤ) : ℝ))]
  -- the lift combinations form a lattice
  let Λ : Submodule ℤ (euclidean.mixedSpace K) := Submodule.span ℤ (Set.range vv)
  have hΛ_le : Λ ≤ euclidean.integerLattice K := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    show vv j ∈ euclidean.integerLattice K
    rw [euclidean.integerLattice, ZLattice.comap]
    show (euclidean.toMixed K) (vv j) ∈ mixedEmbedding.integerLattice K
    rw [show (euclidean.toMixed K) (vv j)
        = NumberField.mixedEmbedding K (((aK j : RingOfIntegers K)) : K) from rfl]
    rw [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]
    exact ⟨aK j, rfl⟩
  haveI : DiscreteTopology Λ :=
    Commons.Lattice.Minkowski.flagBasis.discreteTopology_of_le_general hΛ_le
  have hkerA : ∀ r : Fin d, Amap K N y (intVec N (e (σ (Sum.inl r)))) = 0 := by
    intro r
    rw [hσ_inl]
    exact hu_ker r
  have hvvA : ∀ j : Fin n, Amap K N y (intVec N (e (σ (Sum.inr j)))) = vv j := by
    intro j
    rw [Amap_intVec, hvv_eq j]
  have hyk_span : ∀ k : Fin N,
      Mex K (((y k : RingOfIntegers K) : K))
        ∈ Submodule.span ℝ (Λ : Set (euclidean.mixedSpace K)) := by
    intro k
    have h1 : Amap K N y (intVec N (Pi.single k (1 : ℤ)))
        = Mex K (((y k : RingOfIntegers K) : K)) := by
      rw [Amap_intVec]
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    rw [← h1, Amap_expand (d := d) (n := n) (y := y) (e := e) (σ := σ) (vv := vv)
      (hker := hkerA) (hvv := hvvA)]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.subset_span (Set.mem_range_self j)))
  have hΛ_span : Submodule.span ℝ (Λ : Set (euclidean.mixedSpace K)) = ⊤ := by
    refine top_unique ?_
    rw [← (IsZLattice.span_top (L := euclidean.integerLattice K)), Submodule.span_le]
    intro x hx
    rw [euclidean.integerLattice, ZLattice.comap] at hx
    change (euclidean.toMixed K) x ∈ NumberField.mixedEmbedding.integerLattice K at hx
    rw [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range] at hx
    obtain ⟨a, ha⟩ := hx
    have hx' : x = Mex K ((a : RingOfIntegers K) : K) := by
      refine (euclidean.toMixed K).injective ?_
      rw [← ha]
      rfl
    rw [hx']
    have haK : ((a : RingOfIntegers K) : K)
        ∈ Submodule.span ℚ (Set.range (fun i : Fin N => ((y i : RingOfIntegers K) : K))) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp haK
    rw [← hc, Mex_sum_smul]
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (hyk_span k)
  haveI : IsZLattice ℝ Λ := ⟨hΛ_span⟩
  -- the lifts are `ℤ`-independent
  have hvv_zli : LinearIndependent ℤ (fun j : Fin n =>
      (⟨vv j, Submodule.subset_span (Set.mem_range_self j)⟩ : Λ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgF : ∑ j : Fin n, ((g j : ℤ) : ℝ) • vv j = 0 := by
      have h1 : ((∑ j : Fin n, g j •
          (⟨vv j, Submodule.subset_span (Set.mem_range_self j)⟩ : Λ) : Λ) :
          euclidean.mixedSpace K) = 0 := by
        rw [show ((∑ j : Fin n, g j •
            (⟨vv j, Submodule.subset_span (Set.mem_range_self j)⟩ : Λ) : Λ) :
            euclidean.mixedSpace K) = ((0 : Λ) : euclidean.mixedSpace K) from congrArg _ hg]
        rfl
      have h2 : ((∑ j : Fin n, g j •
          (⟨vv j, Submodule.subset_span (Set.mem_range_self j)⟩ : Λ) : Λ) :
          euclidean.mixedSpace K) = ∑ j : Fin n, ((g j : ℤ) : ℝ) • vv j := by
        simp only [Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul]
      rw [h2] at h1
      exact h1
    have hcoeffZ : ∀ j : Fin n,
        e.equivFun (∑ j' : Fin n, g j' • zz j') (σ (Sum.inr j)) = g j := by
      intro j
      have h1 : e.equivFun (∑ j' : Fin n, g j' • zz j')
          = ∑ j' : Fin n, g j' • e.equivFun (zz j') := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j' _
        rw [map_smul]
      have h2 : ∀ b : Fin n, e.equivFun (zz b)
          = Pi.single (σ (Sum.inr b)) (1:ℤ) := by
        intro b
        funext x
        rw [show zz b = e (σ (Sum.inr b)) from rfl, Basis.equivFun_self, Pi.single_apply]
        by_cases h : σ (Sum.inr b) = x
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
      rw [h1, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, h2 j, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, h2 b, Pi.single_apply,
          if_neg (fun hc => hb (Sum.inr.inj (σ.injective hc.symm))), smul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hcoeff : ∀ j : Fin n,
        ((e.equivFun (∑ j' : Fin n, g j' • zz j') (σ (Sum.inr j)) : ℤ) : ℝ) = ((g j : ℤ) : ℝ) :=
      fun j => by rw [hcoeffZ j]
    have hkey : Amap K N y (intVec N (∑ j : Fin n, g j • zz j)) = 0 := by
      rw [Amap_expand (d := d) (n := n) (y := y) (e := e) (σ := σ) (vv := vv)
        (hker := hkerA) (hvv := hvvA), ← hgF]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact hcoeff j
    intro j₀
    have hmem : (∑ j : Fin n, g j • zz j) ∈ relLat K N y :=
      (Amap_intVec_eq_zero_iff K N y _).mp hkey
    obtain ⟨aa, haa⟩ := (he _).mp hmem
    have hc := congrFun (congrArg (fun v => e.equivFun v) haa) (σ (Sum.inr j₀))
    have hlhs : e.equivFun (∑ j : Fin n, g j • zz j) (σ (Sum.inr j₀)) = g j₀ := by
      have h := hcoeff j₀
      exact_mod_cast h
    have hrhs : e.equivFun (∑ r : Fin d, aa r • u r) (σ (Sum.inr j₀)) = 0 := by
      rw [show (∑ r : Fin d, aa r • u r)
          = ∑ r : Fin d, aa r • e (σ (Sum.inl r)) from by
        apply Finset.sum_congr rfl
        intro r _
        rw [hσ_inl]]
      rw [map_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro r _
      have hne : σ (Sum.inl r) ≠ σ (Sum.inr j₀) := by
        intro hc'
        exact Sum.inl_ne_inr (σ.injective hc')
      rw [map_smul]
      simp only [Pi.smul_apply, Basis.equivFun_self]
      rw [if_neg hne, smul_zero]
    rw [hlhs, hrhs] at hc
    exact hc
  have hspanΛ : ⊤ ≤ Submodule.span ℤ (Set.range (fun j : Fin n =>
      (⟨vv j, Submodule.subset_span (Set.mem_range_self j)⟩ : Λ))) := by
    intro y _
    have hy : (y : euclidean.mixedSpace K) ∈ Submodule.span ℤ (Set.range vv) := y.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, hc⟩ := hy
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [← hc]
    simp
  let hbasisΛ : Basis (Fin n) ℤ Λ := Basis.mk hvv_zli hspanΛ
  -- the covolume of `Λ` is `|det S|`
  have hcovΛ : ZLattice.covolume Λ = |S.det| := by
    have h1 := ZLattice.covolume_eq_det_mul_measureReal (L := Λ) (μ := volume) hbasisΛ
      (((euclidean.stdOrthonormalBasis K).reindex ec.symm).toBasis)
    rw [h1]
    have hvol : volume.real (ZSpan.fundamentalDomain
        (((euclidean.stdOrthonormalBasis K).reindex ec.symm).toBasis)) = 1 :=
      volume_real_fundamentalDomain_orthonormal _
    rw [hvol, mul_one]
    have hmat : (((euclidean.stdOrthonormalBasis K).reindex ec.symm).toBasis).det
        ((↑) ∘ ⇑hbasisΛ) = S.det := by
      rw [Basis.det_apply]
      congr 1
      ext i j
      rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_reindex]
      simp only [Equiv.symm_symm, Function.comp_apply]
      rw [show ((hbasisΛ j : Λ) : euclidean.mixedSpace K) = vv j from by
        rw [show hbasisΛ = Basis.mk hvv_zli hspanΛ from rfl, Basis.coe_mk]]
      exact (hS_apply i j).symm
    rw [hmat]
  have hcovge : ZLattice.covolume (euclidean.integerLattice K) ≤ ZLattice.covolume Λ :=
    Commons.Lattice.Minkowski.covolume_le_covolume_of_le Λ (euclidean.integerLattice K) hΛ_le
  have hcovIL : ZLattice.covolume (euclidean.integerLattice K)
      = (2 : ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K) *
          Real.sqrt |((NumberField.discr K : ℤ) : ℝ)| := by
    rw [NumberField.mixedEmbedding.euclidean.integerLattice,
      ZLattice.covolume_comap (NumberField.mixedEmbedding.integerLattice K) volume volume
        (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed K)]
    exact NumberField.mixedEmbedding.covolume_integerLattice K
  have hSdet : (2 : ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K) * Real.sqrt
      |((NumberField.discr K : ℤ) : ℝ)| ≤ |S.det| := by
    rw [← hcovIL, ← hcovΛ]
    exact hcovge
  have hSdet' : (2 : ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K) ≤ |S.det| := by
    refine (le_mul_of_one_le_right (by positivity) ?_).trans hSdet
    rw [← Real.sqrt_one, ← Int.cast_abs]
    exact Real.sqrt_le_sqrt (Commons.NumberTheory.NumberField.SmallBasis.discr_abs_ge_one K)
  -- #### final bound
  set W := ‖exteriorPower.ιMulti ℝ d (fun r => intVec N (u r))‖ with hW
  have hdetS2 : ((2 : ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K)) ^ 2
      ≤ (S.det) ^ 2 := by
    rw [← sq_abs (S.det)]
    exact pow_le_pow_left₀ (by positivity) hSdet' 2
  have hinv : ((2 : ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K)) ^ 2
      = ((4 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces K))⁻¹ := by
    rw [inv_pow (2:ℝ) (NumberField.InfinitePlace.nrComplexPlaces K),
      inv_pow ((2:ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces K)) 2,
      show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have hmain : W ^ 2 ≤ ((N : ℝ) * B ^ 2) ^ n := by
    have h2 : W ^ 2 * (S.det) ^ 2 = (BB * Matrix.transpose BB).det := by
      rw [hW, ← hG11]
      exact hid.symm
    have h3 : W ^ 2 * (((4 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces K))⁻¹)
        ≤ (((N : ℝ) * B ^ 2) ^ n) / 4 ^ (NumberField.InfinitePlace.nrComplexPlaces K) := by
      rw [← hinv]
      exact (mul_le_mul_of_nonneg_left hdetS2 (sq_nonneg W)).trans_eq h2 |>.trans hdetBB
    rw [div_eq_mul_inv] at h3
    have hpos : (0:ℝ) < 4 ^ (NumberField.InfinitePlace.nrComplexPlaces K) := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hpos)
    simp only [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one] at h4
    exact h4
  have hWle : W ≤ (Real.sqrt N * B) ^ n := by
    have h1 := Real.le_sqrt_of_sq_le hmain
    rwa [sqrt_pow_of_nonneg (by positivity) n, Real.sqrt_mul (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (le_trans zero_le_one hB1)] at h1
  calc ‖exteriorPower.ιMulti ℝ (N - Module.finrank ℚ K)
        (fun r => intVec N (e (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)) r)))‖
      = W := by rw [hW]
    _ ≤ (Real.sqrt N * B) ^ n := hWle
    _ ≤ (Real.sqrt N * (B + 1)) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg N)

lemma intVec_basis_linearIndependent (N : ℕ) (e : Basis (Fin N) ℤ (Fin N → ℤ)) :
    LinearIndependent ℝ (fun t : Fin N => intVec N (e t)) := by
  set A : Matrix (Fin N) (Fin N) ℝ := ((Pi.basisFun ℤ (Fin N)).toMatrix e).map
    (fun z : ℤ => (z : ℝ)) with hA
  have hdet : A.det ≠ 0 := by
    rw [hA]
    rcases Commons.Lattice.Minkowski.det_toMatrix_basisFun_eq_one_or_neg_one e with h | h
    · rw [← Int.cast_det, h]; norm_num
    · rw [← Int.cast_det, h]; norm_num
  have hli : LinearIndependent ℝ A.col := by
    rw [Matrix.linearIndependent_cols_iff_isUnit]
    exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hcol : (fun t : Fin N => intVec N (e t))
      = fun t => (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (A.col t) := by
    funext t
    rw [WithLp_linearEquiv_symm_eq_toLp, intVec]
    congr 1
  rw [hcol]
  exact hli.map' _ (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.injective)

lemma norm_intVec_ge_one (N : ℕ) (z : Fin N → ℤ) (hz : z ≠ 0) : 1 ≤ ‖intVec N z‖ := by
  have h1 : ∀ k : Fin N, (0:ℝ) ≤ (z k : ℝ) ^ 2 := fun k => sq_nonneg _
  have hnormsq : ‖intVec N z‖ ^ 2 = ∑ k : Fin N, (z k : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_intVec_intVec]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hne : ∃ k : Fin N, z k ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext fun k => by simpa using h k)
  obtain ⟨k, hk⟩ := hne
  have h2 : (1:ℝ) ≤ (z k : ℝ) ^ 2 := by
    have : (1:ℤ) ≤ (z k) ^ 2 := by
      rcases lt_or_gt_of_ne (by omega : z k ≠ 0) with h | h
      · nlinarith
      · nlinarith
    exact_mod_cast this
  have h3 : (z k : ℝ) ^ 2 ≤ ∑ k' : Fin N, (z k' : ℝ) ^ 2 :=
    Finset.single_le_sum (fun k' _ => h1 k') (Finset.mem_univ k)
  nlinarith [norm_nonneg (intVec N z)]

/-- The norm of a wedge product is invariant under a linear isometry between different
spaces. -/
lemma norm_iMulti_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E ≃ₗᵢ[ℝ] F) {k : ℕ} (b : Fin k → E) :
    ‖exteriorPower.ιMulti ℝ k (fun i => f (b i))‖ = ‖exteriorPower.ιMulti ℝ k b‖ := by
  have h1 : ‖exteriorPower.ιMulti ℝ k (fun i => f (b i))‖ ^ 2
      = (Matrix.gram ℝ (fun i => f (b i))).det := by
    rw [← real_inner_self_eq_norm_sq, exteriorPower.inner_ιMulti_self]
  have h2 : ‖exteriorPower.ιMulti ℝ k b‖ ^ 2 = (Matrix.gram ℝ b).det := by
    rw [← real_inner_self_eq_norm_sq, exteriorPower.inner_ιMulti_self]
  have hgram : Matrix.gram ℝ (fun i => f (b i)) = Matrix.gram ℝ b := by
    ext i j
    rw [Matrix.gram_apply, Matrix.gram_apply, f.inner_map_map]
  have h3 : ‖exteriorPower.ιMulti ℝ k (fun i => f (b i))‖ ^ 2
      = ‖exteriorPower.ιMulti ℝ k b‖ ^ 2 := by
    rw [h1, h2, hgram]
  nlinarith [norm_nonneg (exteriorPower.ιMulti ℝ k (fun i => f (b i))),
    norm_nonneg (exteriorPower.ιMulti ℝ k b)]

lemma norm_iMulti_subtype {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {W : Submodule ℝ E} {k : ℕ} (v : Fin k → W) :
    ‖exteriorPower.ιMulti ℝ k (fun i => (v i : E))‖ = ‖exteriorPower.ιMulti ℝ k v‖ := by
  have h1 : ‖exteriorPower.ιMulti ℝ k (fun i => (v i : E))‖ ^ 2
      = (Matrix.gram ℝ (fun i => (v i : E))).det := by
    rw [← real_inner_self_eq_norm_sq, exteriorPower.inner_ιMulti_self]
  have h2 : ‖exteriorPower.ιMulti ℝ k v‖ ^ 2 = (Matrix.gram ℝ v).det := by
    rw [← real_inner_self_eq_norm_sq (x := exteriorPower.ιMulti ℝ k v)]
    exact exteriorPower.inner_ιMulti_self v
  have hgram : Matrix.gram ℝ (fun i => (v i : E)) = Matrix.gram ℝ v := by
    ext i j
    rw [Matrix.gram_apply, Matrix.gram_apply, Submodule.coe_inner]
  have h3 : ‖exteriorPower.ιMulti ℝ k (fun i => (v i : E))‖ ^ 2
      = ‖exteriorPower.ιMulti ℝ k v‖ ^ 2 := by
    rw [h1, h2, hgram]
  nlinarith [norm_nonneg (exteriorPower.ιMulti ℝ k (fun i => (v i : E))),
    norm_nonneg (exteriorPower.ιMulti ℝ k v)]
/-- **Short integer relations between algebraic integers**, via the geometry of numbers. -/
theorem short_relations_of_relation_lattice (K : Type*) [Field K] [NumberField K] (N : ℕ)
    (y : Fin N → NumberField.RingOfIntegers K) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, NumberField.house (((y i : NumberField.RingOfIntegers K) : K)) ≤ B)
    (hspan : Submodule.span ℚ (Set.range (fun i : Fin N =>
      (((y i : NumberField.RingOfIntegers K) : K)))) = ⊤)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ N - Module.finrank ℚ K) :
    ∃ x : Fin j → (Fin N → ℤ),
      (∀ i, (∑ k : Fin N, (((x i k : ℤ) : K) *
        (((y k : NumberField.RingOfIntegers K) : K)))) = 0) ∧
      LinearIndependent ℝ (fun i =>
        (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (x i k : ℝ))) ∧
      ∀ i, ‖(WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (x i k : ℝ))‖ ≤
        ((4 : ℝ) ^ (N - Module.finrank ℚ K) *
            (Real.sqrt N * (B + 1)) ^ (Module.finrank ℚ K) /
          ENNReal.toReal (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (N - Module.finrank ℚ K))) 1)))
          ^ ((1 : ℝ) / (((N - Module.finrank ℚ K) + 1 - j : ℕ) : ℝ)) + 1 := by
  classical
  have hdpos : 0 < N - Module.finrank ℚ K := by omega
  have hnN : Module.finrank ℚ K < N := by omega
  obtain ⟨e, he⟩ := exists_basis_relLat K N hnN y hspan
  let u : Fin (N - Module.finrank ℚ K) → (Fin N → ℤ) :=
    fun r => e (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)) r)
  have hu_mem : ∀ r, u r ∈ relLat K N y := by
    intro r
    refine (he (u r)).mpr ⟨fun r' => if r' = r then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ r) h)]
    simp [u]
  have hu_int_li : LinearIndependent ℤ u :=
    e.linearIndependent.comp (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)))
      (Fin.castLE_injective _)
  have hu_li : LinearIndependent ℝ (fun r => (WithLp.equiv 2 (Fin N → ℝ)).symm
      (fun k => (u r k : ℝ))) := by
    have h : (fun r => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u r k : ℝ)))
        = (fun r => intVec N (u r)) := by
      funext r; exact (intVec_eq_withLp N (u r)).symm
    rw [h]
    exact (intVec_basis_linearIndependent N e).comp
      (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K))) (Fin.castLE_injective _)
  have hBwedge : ‖exteriorPower.ιMulti ℝ (N - Module.finrank ℚ K)
      (fun r => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u r k : ℝ)))‖
      ≤ (Real.sqrt N * (B + 1)) ^ (Module.finrank ℚ K) := by
    have h : (fun r => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u r k : ℝ)))
        = (fun r => intVec N (e (Fin.castLE (Nat.sub_le N (Module.finrank ℚ K)) r))) := by
      funext r; exact (intVec_eq_withLp N (e _)).symm
    rw [h]
    exact wedge_le_of_relation_lattice K N y B hB hspan hnN e he
  have hmin : ∀ a : Fin (N - Module.finrank ℚ K) → ℤ, a ≠ 0 →
      1 ≤ ‖∑ i, (a i : ℝ) • (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u i k : ℝ))‖ := by
    intro a ha
    have hz : (∑ i, a i • u i) ≠ 0 := fun h0 =>
      ha (funext ((Fintype.linearIndependent_iff.mp hu_int_li a) h0))
    have hsum : (∑ i, (a i : ℝ) •
          (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u i k : ℝ)))
        = intVec N (∑ i, a i • u i) := by
      simp only [← intVec_eq_withLp]
      rw [intVec_sum]
      exact (Finset.sum_congr rfl (fun i _ => intVec_smul N (a i) (u i))).symm
    rw [hsum]
    exact norm_intVec_ge_one N _ hz
  obtain ⟨b, hb_li, hb_bd⟩ :=
    Commons.Lattice.Minkowski.exists_short_independent_of_basis (M := N)
      (D := N - Module.finrank ℚ K) hdpos u hu_li hBwedge (by positivity) hmin j hj hjd
  let xs : Fin j → (Fin N → ℤ) := fun i k => ∑ r, b i r * u r k
  have hxs_eq : ∀ i, xs i = ∑ r, b i r • u r := by
    intro i
    funext k
    simp [xs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hxs_vec : ∀ i, intVec N (xs i) = ∑ r, (b i r : ℝ) • intVec N (u r) := by
    intro i
    rw [hxs_eq i]
    rw [intVec_sum]
    exact Finset.sum_congr rfl (fun r _ => intVec_smul N (b i r) (u r))
  have hfam : (fun i => ∑ r, (b i r : ℝ) • intVec N (u r))
      = (fun i => ∑ r, (b i r : ℝ) •
          (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u r k : ℝ))) := by
    funext i
    apply Finset.sum_congr rfl
    intro r _
    rw [intVec_eq_withLp]
  refine ⟨xs, ?_, ?_, ?_⟩
  · intro i
    have hmem : (∑ r, b i r • u r) ∈ relLat K N y :=
      Submodule.sum_mem _ (fun r _ => Submodule.smul_mem _ (b i r) (hu_mem r))
    have hgt : (∑ k : Fin N, (((xs i k : ℤ) : K) *
          (((y k : NumberField.RingOfIntegers K) : K))))
        = ∑ k : Fin N, ((((∑ r, b i r • u r) k : ℤ) : K) *
          (((y k : NumberField.RingOfIntegers K) : K))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hxs_eq i]
    rw [hgt]
    exact hmem
  · rw [show (fun i => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (xs i k : ℝ)))
        = (fun i => intVec N (xs i)) from by
      funext i; exact (intVec_eq_withLp N (xs i)).symm]
    rw [show (fun i => intVec N (xs i))
        = (fun i => ∑ r, (b i r : ℝ) • intVec N (u r)) from funext hxs_vec]
    rw [hfam]
    exact hb_li
  · intro i
    have h1 : (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (xs i k : ℝ)) = intVec N (xs i) :=
      (intVec_eq_withLp N (xs i)).symm
    rw [h1, hxs_vec i]
    rw [show (∑ r, (b i r : ℝ) • intVec N (u r))
        = ∑ r, (b i r : ℝ) • (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (u r k : ℝ)) from
      Finset.sum_congr rfl (fun r _ => by rw [intVec_eq_withLp])]
    exact hb_bd i
end Commons.NumberTheory.NumberField
