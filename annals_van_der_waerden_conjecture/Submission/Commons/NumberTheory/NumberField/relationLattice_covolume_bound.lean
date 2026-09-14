import Mathlib
import Submission.Commons.Lattice.Minkowski.exists_basis_subtype_kernel_real
import Submission.Commons.Lattice.Minkowski.kerLattice_basis_wedge_mul_covolume_le
import Submission.Commons.Lattice.Minkowski.covol_span_wedge
import Submission.Commons.NumberTheory.NumberField.mixedEmbedding_gram_det_le
import Submission.Commons.NumberTheory.NumberField.span_mixedEmbedding_range_eq_top
import Submission.Commons.Lattice.Minkowski.kerLattice_basis_wedge_mul_covolume_le_iff

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField

open scoped Classical
open Module

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The covolume of the image of the ring of integers in the Euclidean mixed space
`ℝ^{r₁} × ℂ^{r₂}` is `2^{-r₂} √|discr K|`. -/
theorem covolume_euclidean_integerLattice (K : Type*) [Field K] [NumberField K] :
    ZLattice.covolume (NumberField.mixedEmbedding.euclidean.integerLattice K) =
      (2⁻¹ : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)| := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice,
    ZLattice.covolume_comap (NumberField.mixedEmbedding.integerLattice K) MeasureTheory.volume
      MeasureTheory.volume (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed K)]
  exact NumberField.mixedEmbedding.covolume_integerLattice K

/-- Covolume bound for the lattice of integer relations between algebraic integers.
Let K be a number field, y : Fin N → O_K a family of algebraic integers with house ≤ B whose
Q-span is all of K.  Then the relation lattice
  Λ = {x : Fin N → ℤ | ∑_i x_i • y_i = 0}
has a ℤ-basis v (of N - [K:ℚ] elements) such that
  (a) every basis element IS a relation,
  (b) the basis spans Λ over ℤ,
  (c) ‖v_0 ∧ … ∧ v_{d-1}‖ ≤ (√N · (B+1))^[K:ℚ]   (the covolume bound).
Route: the Hodge-duality / kernel-image formula
  covol(Λ) · covol(image lattice A ℤ^N) = ‖wedge of the rows of A‖  (A = mixed embedding matrix)
together with covol(image) ≥ covol(mixed-embedding lattice of O_K) = √|discr| ≥ 1, and
Hadamard's inequality for the rows of A (each of Euclidean norm ≤ √N · B).

Mathematically, the mixed embedding matrix `A` (in an orthonormal basis of `ℝ^{r₁} × ℂ^{r₂}`) has
Gram determinant `≤ ((√N B)^[K:ℚ] / 2^{r₂})²` and the lattice `L` of the image of `𝓞 K` under the
same identification has covolume `2^{-r₂} √|discr K|`, so the kernel–image identity
`covol Λ · covol L ≤ ‖wedge of the rows of A‖` gives the bound. -/
theorem relationLattice_covolume_bound (K : Type*) [Field K] [NumberField K] (N : ℕ)
    (y : Fin N → NumberField.RingOfIntegers K) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, NumberField.house (((y i : NumberField.RingOfIntegers K) : K)) ≤ B)
    (hspan : Submodule.span ℚ (Set.range (fun i : Fin N => (((y i : NumberField.RingOfIntegers K) : K)))) = ⊤) :
    ∃ v : Fin (N - Module.finrank ℚ K) → (Fin N → ℤ),
      LinearIndependent ℤ v ∧
      (∀ j, (∑ i : Fin N, (((v j i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))) = 0) ∧
      (∀ x : Fin N → ℤ,
        (∑ i : Fin N, (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))) = 0 →
        ∃ a : Fin (N - Module.finrank ℚ K) → ℤ, x = ∑ j, a j • v j) ∧
      ‖exteriorPower.ιMulti ℝ (N - Module.finrank ℚ K)
          (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => ((v j i : ℤ) : ℝ)))‖ ≤
        (Real.sqrt N * (B + 1)) ^ (Module.finrank ℚ K) := by
  classical
  have hcn : Fintype.card (NumberField.mixedEmbedding.index K) = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_basis
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).toBasis]
    exact NumberField.mixedEmbedding.euclidean.finrank K
  rw [← hcn]
  set ι := NumberField.mixedEmbedding.index K with hιdef
  set r₂ : ℕ := NumberField.InfinitePlace.nrComplexPlaces K with hr₂
  let b : OrthonormalBasis ι ℝ (NumberField.mixedEmbedding.euclidean.mixedSpace K) :=
    NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K
  let emb : Fin N → NumberField.mixedEmbedding.euclidean.mixedSpace K := fun i =>
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm
      (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K)))
  let A : Matrix ι (Fin N) ℝ := fun l i =>
    inner ℝ ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K)))) (b l)
  let bres : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ]
      NumberField.mixedEmbedding.euclidean.mixedSpace K := b.repr.symm
  let L : Submodule ℤ (EuclideanSpace ℝ ι) :=
    ZLattice.comap ℝ (NumberField.mixedEmbedding.euclidean.integerLattice K)
      bres.toContinuousLinearEquiv.toLinearMap
  -- The matrix `A` is the coordinate matrix of the embedded family in the orthonormal basis `b`.
  have hA_coord : ∀ (l : ι) (i : Fin N), A l i = (b.repr (emb i)).ofLp l := by
    intro l i
    rw [OrthonormalBasis.repr_apply_apply]
    simp only [A, emb, b]
    exact real_inner_comm _ _
  -- The embedded family spans the whole Euclidean mixed space.
  have hemb_span : Submodule.span ℝ (Set.range emb) = ⊤ := by
    have h := Commons.NumberTheory.NumberField.span_mixedEmbedding_range_eq_top K N y hspan
    set f := (NumberField.mixedEmbedding.euclidean.toMixed K).symm.toLinearMap with hf
    have hrange : Set.range emb = f ''
        (Set.range (fun i : Fin N => NumberField.mixedEmbedding K
          (((y i : NumberField.RingOfIntegers K) : K)))) := by
      ext z; constructor
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
    exact (NumberField.mixedEmbedding.euclidean.toMixed K).symm.surjective
  -- The rows of `A` are linearly independent (the embedded family spans).
  have hA : LinearIndependent ℝ (fun l : ι => fun i : Fin N => A l i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set w : NumberField.mixedEmbedding.euclidean.mixedSpace K := ∑ l : ι, g l • b l with hw
    have hinner : ∀ u ∈ Submodule.span ℝ (Set.range emb), inner ℝ w u = 0 := by
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro u ⟨i, rfl⟩
        have h1 : inner ℝ w (emb i) = ∑ l : ι, g l * A l i := by
          rw [hw, sum_inner]
          apply Finset.sum_congr rfl
          intro l _
          rw [real_inner_smul_left, ← OrthonormalBasis.repr_apply_apply b (emb i) l,
            ← hA_coord l i]
        rw [h1]
        have h2 : (∑ l : ι, g l * A l i) = 0 := by
          simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hg i
        exact h2
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx
        rw [inner_smul_right, hx, mul_zero]
    have hw0 : w = 0 := by
      have hww : inner ℝ w w = 0 := hinner w (by rw [hemb_span]; trivial)
      exact inner_self_eq_zero.mp hww
    intro l
    rw [hw] at hw0
    exact Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent g hw0 l
  -- The embedded vector attached to an integer vector `x` is the mixed embedding of the
  -- corresponding algebraic integer combination.
  have hsum_eq : ∀ (x : Fin N → ℤ),
      (∑ i : Fin N, (x i : ℝ) • emb i) = (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K
          (∑ i : Fin N, (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K))))) := by
    intro x
    have h1 : (∑ i : Fin N, (x i : ℝ) • emb i) =
        (NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (∑ i : Fin N, (x i : ℝ) • (NumberField.mixedEmbedding K
            (((y i : NumberField.RingOfIntegers K) : K)))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    have h2 : (∑ i : Fin N, (x i : ℝ) • (NumberField.mixedEmbedding K
            (((y i : NumberField.RingOfIntegers K) : K))))
        = NumberField.mixedEmbedding K
            (∑ i : Fin N, (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Int.cast_smul_eq_zsmul, ← map_zsmul, ← zsmul_eq_mul]
    rw [h1, h2]
  -- The vector `(∑ l, ∑ i, A l i * x i)` in `ℓ²` coordinates is the `repr` of the embedded sum.
  have hrepr_eq : ∀ (x : Fin N → ℤ),
      b.repr (∑ i : Fin N, (x i : ℝ) • emb i) =
        (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) := by
    intro x
    rw [WithLp.ext_iff]
    funext l
    rw [WithLp.equiv_symm_apply, WithLp.ofLp_toLp, OrthonormalBasis.repr_apply_apply]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right, ← OrthonormalBasis.repr_apply_apply b (emb i) l, ← hA_coord l i]
    ring
  -- Description of the kernel of `A` on `ℤ^N`.
  have hker : ∀ x : Fin N → ℤ, (∀ l, ∑ i, A l i * (x i : ℝ) = 0) ↔
      (∑ i : Fin N, (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))) = 0 := by
    intro x
    constructor
    · intro h
      have hV : (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) = 0 := by
        rw [WithLp.ext_iff]
        funext l
        rw [WithLp.equiv_symm_apply, WithLp.ofLp_toLp, h l]
        rfl
      have h0 : b.repr (∑ i : Fin N, (x i : ℝ) • emb i) = 0 := by rw [hrepr_eq x, hV]
      have h1 : (∑ i : Fin N, (x i : ℝ) • emb i) = 0 := by
        have := congrArg b.repr.symm h0
        simpa using this
      have h2 : (NumberField.mixedEmbedding.euclidean.toMixed K).symm
          (NumberField.mixedEmbedding K (∑ i : Fin N,
            (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K))))) = 0 := by
        rw [← hsum_eq x, h1]
      have h3 : (NumberField.mixedEmbedding K (∑ i : Fin N,
          (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K))))) = 0 := by
        have := congrArg (NumberField.mixedEmbedding.euclidean.toMixed K) h2
        simpa using this
      exact (NumberField.mixedEmbedding_injective K) (by rw [h3, map_zero])
    · intro hz l
      have h1 : (∑ i : Fin N, (x i : ℝ) • emb i) = 0 := by
        rw [hsum_eq x, hz, map_zero, map_zero]
      have hV : (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) = 0 := by
        rw [← hrepr_eq x, h1, map_zero]
      have := congrArg (fun v : EuclideanSpace ℝ ι => v.ofLp l) hV
      simpa using this
  -- Membership in the lattice `L` of the image of the ring of integers.
  have hL : ∀ x : Fin N → ℤ,
      (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) ∈ L := by
    intro x
    set V : EuclideanSpace ℝ ι :=
      (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) with hVdef
    have hmemiff : V ∈ L ↔ bres V ∈ (NumberField.mixedEmbedding.euclidean.integerLattice K :
        Submodule ℤ (NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
      show V ∈ (ZLattice.comap ℝ (NumberField.mixedEmbedding.euclidean.integerLattice K)
        bres.toContinuousLinearEquiv.toLinearMap : Set (EuclideanSpace ℝ ι)) ↔ _
      rw [ZLattice.coe_comap, Set.mem_preimage]
      exact Iff.rfl
    have hbres : bres V = (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (∑ i : Fin N,
          (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K))))) := by
      have h1 : b.repr (bres V) = b.repr (∑ i : Fin N, (x i : ℝ) • emb i) := by
        rw [show b.repr (bres V) = V from LinearIsometryEquiv.apply_symm_apply b.repr V,
          hVdef]
        exact (hrepr_eq x).symm
      rw [b.repr.injective h1, hsum_eq x]
    have hmem2iff : (NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (∑ i : Fin N,
          (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))))
        ∈ (NumberField.mixedEmbedding.euclidean.integerLattice K :
            Submodule ℤ (NumberField.mixedEmbedding.euclidean.mixedSpace K)) ↔
        (NumberField.mixedEmbedding K (∑ i : Fin N,
          (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))))
          ∈ (NumberField.mixedEmbedding.integerLattice K :
              Submodule ℤ (NumberField.mixedEmbedding.mixedSpace K)) := by
      show (NumberField.mixedEmbedding.euclidean.toMixed K).symm _ ∈
        (ZLattice.comap ℝ (NumberField.mixedEmbedding.integerLattice K)
          (NumberField.mixedEmbedding.euclidean.toMixed K).toLinearMap :
            Set (NumberField.mixedEmbedding.euclidean.mixedSpace K)) ↔ _
      rw [ZLattice.coe_comap, Set.mem_preimage]
      exact Iff.rfl
    have hmem : (NumberField.mixedEmbedding K (∑ i : Fin N,
        (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K)))))
        ∈ (NumberField.mixedEmbedding.integerLattice K :
            Submodule ℤ (NumberField.mixedEmbedding.mixedSpace K)) := by
      set zO : NumberField.RingOfIntegers K := ∑ i : Fin N, (x i : ℤ) • y i with hzO
      have hzOmap : algebraMap (NumberField.RingOfIntegers K) K zO = ∑ i : Fin N,
          (((x i : ℤ) : K) * (((y i : NumberField.RingOfIntegers K) : K))) := by
        rw [hzO, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_zsmul, zsmul_eq_mul]
      rw [NumberField.mixedEmbedding.integerLattice]
      refine ⟨zO, ?_⟩
      show NumberField.mixedEmbedding K (algebraMap (NumberField.RingOfIntegers K) K zO) = _
      rw [hzOmap]
    rw [hmemiff, hbres, hmem2iff]
    exact hmem
  -- The radius and the Gram determinant bound.
  set R : ℝ := (2⁻¹ : ℝ) ^ r₂ * (Real.sqrt N * B) ^ (Fintype.card ι) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (mul_nonneg (Real.sqrt_nonneg N) hB0) _)
  have hR : (A * A.transpose).det ≤ R ^ 2 := by
    obtain ⟨A', hA', hdet'⟩ := mixedEmbedding_gram_det_le K N y B hB0 hB
    have hAeq : A = A'.submatrix (Fintype.equivFin (NumberField.mixedEmbedding.index K)) id := by
      ext l i
      show A l i = A' ((Fintype.equivFin (NumberField.mixedEmbedding.index K)) l) i
      rw [hA' _ i]
      simp only [A, b]
      congr 1
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
    have hdet : (A * A.transpose).det = (A' * A'.transpose).det := by
      rw [hAeq]
      rw [show (A'.submatrix (Fintype.equivFin (NumberField.mixedEmbedding.index K)) id)
            * (A'.submatrix (Fintype.equivFin (NumberField.mixedEmbedding.index K)) id).transpose
          = (A' * A'.transpose).submatrix (Fintype.equivFin (NumberField.mixedEmbedding.index K))
              (Fintype.equivFin (NumberField.mixedEmbedding.index K)) from by
        ext l l'
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]]
      rw [Matrix.det_submatrix_equiv_self]
    have hReq : ((Real.sqrt N * B) ^ (Fintype.card ι) / 2 ^ r₂) ^ 2 = R ^ 2 := by
      rw [hRdef, div_eq_mul_inv, inv_pow]
      ring
    rw [hdet, ← hReq]
    exact hdet'
  obtain ⟨v, hv_li, hv_ker, hv_wedge⟩ := Commons.Lattice.Minkowski.kerLattice_basis_wedge_mul_covolume_le_iff A hA L hL hR0 hR
  -- Covolume of the image lattice.
  have hcovL : ZLattice.covolume L =
      (2⁻¹ : ℝ) ^ r₂ * Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [show L = ZLattice.comap ℝ (NumberField.mixedEmbedding.euclidean.integerLattice K)
        bres.toContinuousLinearEquiv.toLinearMap from rfl,
      ZLattice.covolume_comap (NumberField.mixedEmbedding.euclidean.integerLattice K)
        MeasureTheory.volume MeasureTheory.volume (LinearIsometryEquiv.measurePreserving bres),
      covolume_euclidean_integerLattice]
  have hcovLpos : 0 < ZLattice.covolume L := by
    rw [hcovL]
    exact mul_pos (pow_pos (by norm_num) _)
      (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))))
  have hdisc1 : (1 : ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
    apply Real.one_le_sqrt.mpr
    have h : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hwedge : ‖exteriorPower.ιMulti ℝ (N - Fintype.card ι)
      (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => ((v j i : ℤ) : ℝ)))‖ ≤
      R / ZLattice.covolume L := (le_div_iff₀ hcovLpos).mpr hv_wedge
  have hmain : ‖exteriorPower.ιMulti ℝ (N - Fintype.card ι)
      (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => ((v j i : ℤ) : ℝ)))‖ ≤
      (Real.sqrt N * (B + 1)) ^ (Fintype.card ι) := by
    refine le_trans hwedge ?_
    have h2 : (2⁻¹ : ℝ) ^ r₂ * (Real.sqrt N * B) ^ (Fintype.card ι) /
        ((2⁻¹ : ℝ) ^ r₂ * Real.sqrt |(NumberField.discr K : ℝ)|)
        = (Real.sqrt N * B) ^ (Fintype.card ι) / Real.sqrt |(NumberField.discr K : ℝ)| := by
      field_simp
    rw [hRdef, hcovL, h2]
    refine le_trans (div_le_self (pow_nonneg (mul_nonneg (Real.sqrt_nonneg N) hB0) _) hdisc1) ?_
    exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg N) hB0)
      (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg N)) _
  refine ⟨v, hv_li, ?_, ?_, hmain⟩
  · intro j
    have h1 : ∃ a : Fin (N - Fintype.card ι) → ℤ, v j = ∑ k, a k • v k := by
      refine ⟨fun k => if k = j then 1 else 0, ?_⟩
      have hsum : (∑ k : Fin (N - Fintype.card ι), (if k = j then (1:ℤ) else 0) • v k) = v j := by
        rw [Finset.sum_eq_single j]
        · rw [if_pos rfl, one_smul]
        · intro k _ hk
          rw [if_neg hk, zero_smul]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      exact hsum.symm
    exact (hker (v j)).mp ((hv_ker (v j)).mpr h1)
  · intro x hx
    exact (hv_ker x).mp ((hker x).mpr hx)

end

end Commons.NumberTheory.NumberField
