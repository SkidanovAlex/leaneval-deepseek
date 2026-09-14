import Mathlib.NumberTheory.NumberField.House
import Submission.Commons.LinearAlgebra.Matrix.det_le_prod_diag_of_posSemidef

open scoped Classical
open Module

namespace Commons.NumberTheory.NumberField

noncomputable section

/-! ## Auxiliary lemmas -/

/-- For a basis `b` and a linear equivalence `f`, the coordinates of `y` with respect to
`b.map f` are the coordinates of `f.symm y` with respect to `b`. -/
private lemma basis_repr_map_symm {ι R M M' : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid M'] [Module R M'] (b : Basis ι R M) (f : M ≃ₗ[R] M') (y : M') :
    (b.map f).repr y = b.repr (f.symm y) := by
  rw [Basis.map]
  change (f.symm.trans b.repr) y = b.repr (f.symm y)
  rw [LinearEquiv.trans_apply]

/-- The coordinates of `toMixed.symm v` in the standard orthonormal basis of the Euclidean
mixed space are the coordinates of `v` in the standard basis of the mixed space. -/
private theorem inner_toMixed_symm_stdOrthonormalBasis (K : Type*) [Field K] [NumberField K]
    (v : NumberField.mixedEmbedding.mixedSpace K) (c : NumberField.mixedEmbedding.index K) :
    inner ℝ ((NumberField.mixedEmbedding.euclidean.toMixed K).symm v)
        ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K) c)
      = (NumberField.mixedEmbedding.stdBasis K).repr v c := by
  rw [real_inner_comm]
  rw [← OrthonormalBasis.repr_apply_apply]
  rw [← OrthonormalBasis.coe_toBasis_repr_apply]
  rw [← NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq K]
  rw [basis_repr_map_symm]
  simp

/-- The value of an infinite place at an element is at most the house of that element. -/
private lemma infinitePlace_apply_le_house (K : Type*) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (x : K) :
    w x ≤ NumberField.house x := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq w x]
  exact NumberField.norm_embedding_le_house x w.embedding

private lemma stdBasis_repr_mixedEmbedding_isReal (K : Type*) [Field K] [NumberField K] (a : K)
    (w : {w : NumberField.InfinitePlace K // w.IsReal}) :
    (NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a) (Sum.inl w)
      = NumberField.InfinitePlace.embedding_of_isReal w.prop a := by
  rw [NumberField.mixedEmbedding.stdBasis_apply_isReal,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]

private lemma stdBasis_repr_mixedEmbedding_isComplex_fst (K : Type*) [Field K] [NumberField K]
    (a : K) (w : {w : NumberField.InfinitePlace K // w.IsComplex}) :
    (NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a)
        (Sum.inr (w, 0))
      = (w.val.embedding a).re := by
  rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]

private lemma stdBasis_repr_mixedEmbedding_isComplex_snd (K : Type*) [Field K] [NumberField K]
    (a : K) (w : {w : NumberField.InfinitePlace K // w.IsComplex}) :
    (NumberField.mixedEmbedding.stdBasis K).repr (NumberField.mixedEmbedding K a)
        (Sum.inr (w, 1))
      = (w.val.embedding a).im := by
  rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]

private lemma embedding_of_isReal_sq (K : Type*) [Field K] [NumberField K] (a : K)
    (w : {w : NumberField.InfinitePlace K // w.IsReal}) :
    (NumberField.InfinitePlace.embedding_of_isReal w.prop a)^2 = (w.val a)^2 := by
  rw [← sq_abs, ← Real.norm_eq_abs, NumberField.InfinitePlace.norm_embedding_of_isReal]

private lemma complex_coord_sq_sum (K : Type*) [Field K] [NumberField K] (a : K)
    (w : {w : NumberField.InfinitePlace K // w.IsComplex}) :
    (w.val.embedding a).re^2 + (w.val.embedding a).im^2 = (w.val a)^2 := by
  have h1 : (w.val.embedding a).re^2 + (w.val.embedding a).im^2
      = ‖w.val.embedding a‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h1, NumberField.InfinitePlace.norm_embedding_eq]

/-- The arithmetic-geometric mean inequality in the form used below. -/
private lemma mul_le_sq_half_add {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    a * b ≤ ((a + b) / 2)^2 := by
  nlinarith [sq_nonneg (a - b)]

private lemma pow_mul_pow_div (C : ℝ) (r₁ r₂ : ℕ) :
    C^r₁ * ((C/2)^2)^r₂ = C^(r₁ + 2*r₂) / (2:ℝ)^(2*r₂) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, ← mul_div_assoc, ← pow_add]

/-- The cardinality of the index type of the mixed embedding. -/
private lemma card_index_eq (K : Type*) [Field K] [NumberField K] :
    Fintype.card (NumberField.mixedEmbedding.index K)
      = NumberField.InfinitePlace.nrRealPlaces K
        + 2 * NumberField.InfinitePlace.nrComplexPlaces K := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

/-- The square-root expression appearing in the statement equals the more convenient
power expression used below. -/
private lemma sqrt_div_sq (N : ℕ) (B : ℝ) (m r : ℕ) :
    ((Real.sqrt (N:ℝ) * B)^m / (2:ℝ)^r)^2 = ((N:ℝ) * B^2)^m / (2:ℝ)^(2*r) := by
  rw [div_pow]
  have hx : ((Real.sqrt (N:ℝ) * B)^m)^2 = ((Real.sqrt (N:ℝ) * B)^2)^m := by
    rw [← pow_mul, ← pow_mul, show m * 2 = 2 * m from Nat.mul_comm m 2]
  have h2 : ((2:ℝ)^r)^2 = (2:ℝ)^(2*r) := by
    rw [← pow_mul, show r * 2 = 2 * r from Nat.mul_comm r 2]
  rw [hx, h2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Hadamard's inequality for the Gram matrix `A * Aᵀ` of the rows of a real matrix. -/
private lemma det_mul_transpose_le_sum_sq {n N : ℕ} (A : Matrix (Fin n) (Fin N) ℝ) :
    (A * A.transpose).det ≤ ∏ l : Fin n, ∑ i : Fin N, (A l i)^2 := by
  have hpsd : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose A)
  calc (A * A.transpose).det ≤ ∏ l : Fin n, (A * A.transpose) l l :=
        Commons.LinearAlgebra.Matrix.det_le_prod_diag_of_posSemidef _ hpsd
    _ = ∏ l : Fin n, ∑ i : Fin N, (A l i)^2 := by
        apply Finset.prod_congr rfl
        intro l _
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp [Matrix.transpose_apply, sq]

/-- **Product of the squared coordinates of the mixed embedding.**  For `y : Fin N → 𝓞 K` whose
elements have house at most `B`, the product over all coordinates of the mixed embedding of the
squared coordinates is at most `(N B²)^{[K:ℚ]} / 2^{2 r₂}`. -/
private lemma prod_sq_coord_le (K : Type*) [Field K] [NumberField K] (N : ℕ)
    (y : Fin N → NumberField.RingOfIntegers K) (B : ℝ) (_hB0 : 0 ≤ B)
    (hB : ∀ i, NumberField.house (((y i : NumberField.RingOfIntegers K) : K)) ≤ B) :
    ∏ c : NumberField.mixedEmbedding.index K,
        ∑ i : Fin N, ((NumberField.mixedEmbedding.stdBasis K).repr
            (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))) c)^2
      ≤ ((N : ℝ) * B^2)^(Fintype.card (NumberField.mixedEmbedding.index K))
          / (2:ℝ)^(2 * NumberField.InfinitePlace.nrComplexPlaces K) := by
  classical
  set C : ℝ := (N:ℝ) * B^2 with hC
  set r₁ : ℕ := NumberField.InfinitePlace.nrRealPlaces K with hr₁
  set r₂ : ℕ := NumberField.InfinitePlace.nrComplexPlaces K with hr₂
  set F : NumberField.mixedEmbedding.index K → ℝ := fun c =>
      ∑ i : Fin N, ((NumberField.mixedEmbedding.stdBasis K).repr
            (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))) c)^2
    with hF
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hFnn : ∀ c : NumberField.mixedEmbedding.index K, 0 ≤ F c := by
    intro c; rw [hF]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hplace : ∀ (w : NumberField.InfinitePlace K),
      ∑ i : Fin N, (w (((y i : NumberField.RingOfIntegers K) : K)))^2 ≤ C := by
    intro w
    rw [hC]
    calc ∑ i : Fin N, (w (((y i : NumberField.RingOfIntegers K) : K)))^2
        ≤ ∑ _i : Fin N, B^2 := by
          apply Finset.sum_le_sum
          intro i _
          exact pow_le_pow_left₀ (apply_nonneg w _)
            (le_trans (infinitePlace_apply_le_house K w _) (hB i)) 2
      _ = (N:ℝ) * B^2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hreal : ∀ w : {w : NumberField.InfinitePlace K // w.IsReal}, F (Sum.inl w) ≤ C := by
    intro w
    have h1 : F (Sum.inl w)
        = ∑ i : Fin N, (w.val (((y i : NumberField.RingOfIntegers K) : K)))^2 := by
      rw [hF]
      apply Finset.sum_congr rfl
      intro i _
      rw [stdBasis_repr_mixedEmbedding_isReal, embedding_of_isReal_sq]
    rw [h1]; exact hplace w.val
  have hcplx : ∀ w : {w : NumberField.InfinitePlace K // w.IsComplex},
      F (Sum.inr (w, 0)) * F (Sum.inr (w, 1)) ≤ (C/2)^2 := by
    intro w
    have h0 : F (Sum.inr (w, 0))
        = ∑ i : Fin N, ((w.val.embedding (((y i : NumberField.RingOfIntegers K) : K))).re)^2 := by
      rw [hF]; apply Finset.sum_congr rfl; intro i _
      rw [stdBasis_repr_mixedEmbedding_isComplex_fst]
    have h1 : F (Sum.inr (w, 1))
        = ∑ i : Fin N, ((w.val.embedding (((y i : NumberField.RingOfIntegers K) : K))).im)^2 := by
      rw [hF]; apply Finset.sum_congr rfl; intro i _
      rw [stdBasis_repr_mixedEmbedding_isComplex_snd]
    have hsum : F (Sum.inr (w, 0)) + F (Sum.inr (w, 1))
        = ∑ i : Fin N, (w.val (((y i : NumberField.RingOfIntegers K) : K)))^2 := by
      rw [h0, h1, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact complex_coord_sq_sum K _ w
    have hnn0 : 0 ≤ F (Sum.inr (w, 0)) := hFnn _
    have hnn1 : 0 ≤ F (Sum.inr (w, 1)) := hFnn _
    calc F (Sum.inr (w, 0)) * F (Sum.inr (w, 1))
        ≤ ((F (Sum.inr (w, 0)) + F (Sum.inr (w, 1)))/2)^2 :=
          mul_le_sq_half_add hnn0 hnn1
      _ ≤ (C/2)^2 := by
          apply pow_le_pow_left₀ (by positivity)
          rw [hsum]
          exact div_le_div_of_nonneg_right (hplace w.val) (by norm_num)
  have hcard : Fintype.card (NumberField.mixedEmbedding.index K) = r₁ + 2 * r₂ := by
    rw [card_index_eq K, ← hr₁, ← hr₂]
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  have h₁ : ∏ w : {w : NumberField.InfinitePlace K // w.IsReal}, F (Sum.inl w)
      ≤ C ^ r₁ := by
    calc ∏ w : {w : NumberField.InfinitePlace K // w.IsReal}, F (Sum.inl w)
        ≤ ∏ _w : {w : NumberField.InfinitePlace K // w.IsReal}, C :=
          Finset.prod_le_prod (fun w _ => hFnn _) (fun w _ => hreal w)
      _ = C ^ r₁ := by
          rw [Finset.prod_const, Finset.card_univ]
  have h₂ : ∏ w : {w : NumberField.InfinitePlace K // w.IsComplex},
        (F (Sum.inr (w, 0)) * F (Sum.inr (w, 1))) ≤ ((C/2)^2) ^ r₂ := by
    calc ∏ w : {w : NumberField.InfinitePlace K // w.IsComplex},
            (F (Sum.inr (w, 0)) * F (Sum.inr (w, 1)))
        ≤ ∏ _w : {w : NumberField.InfinitePlace K // w.IsComplex}, ((C/2)^2) :=
          Finset.prod_le_prod (fun w _ => mul_nonneg (hFnn _) (hFnn _)) (fun w _ => hcplx w)
      _ = ((C/2)^2) ^ r₂ := by
          rw [Finset.prod_const, Finset.card_univ]
  calc (∏ w : {w : NumberField.InfinitePlace K // w.IsReal}, F (Sum.inl w))
        * (∏ w : {w : NumberField.InfinitePlace K // w.IsComplex},
            (F (Sum.inr (w, 0)) * F (Sum.inr (w, 1))))
      ≤ C ^ r₁ * ((C/2)^2) ^ r₂ :=
        mul_le_mul h₁ h₂ (Finset.prod_nonneg fun w _ => mul_nonneg (hFnn _) (hFnn _))
          (pow_nonneg hCnn r₁)
    _ = C ^ (Fintype.card (NumberField.mixedEmbedding.index K))
          / (2:ℝ)^(2 * r₂) := by
        rw [pow_mul_pow_div C r₁ r₂, hcard]

open scoped Classical in
/-- **Gram determinant of the mixed-embedding matrix of house-bounded algebraic integers.**
Let `y : Fin N → 𝓞 K` have `house ≤ B`. Taking `A` to be the matrix of the mixed embedding
`a ↦ toMixed (mixedEmbedding K a)` in an orthonormal basis of the Euclidean mixed space, the
Gram determinant of the rows of `A` is at most `((√N · B)^[K:ℚ] / 2^r₂)^2`, where `r₂` is the
number of complex places of `K`.

Route: `det (A * Aᵀ) ≤ ∏ l, ‖row l‖²` (Hadamard for the positive semidefinite Gram matrix of
the rows); each real place contributes `‖row‖² ≤ N·B²` and each complex place contributes
`‖row_re‖ · ‖row_im‖ ≤ N·B²/2` by AM-GM applied to `Σ_i (re² + im²) = Σ_i ‖σ(y_i)‖² ≤ N·B²`;
finally `card (index K) = r₁ + 2 r₂`. -/
theorem mixedEmbedding_gram_det_le (K : Type*) [Field K] [NumberField K] (N : ℕ)
    (y : Fin N → NumberField.RingOfIntegers K) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i, NumberField.house (((y i : NumberField.RingOfIntegers K) : K)) ≤ B) :
    ∃ A : Matrix (Fin (Fintype.card (NumberField.mixedEmbedding.index K))) (Fin N) ℝ,
      (∀ (l : Fin (Fintype.card (NumberField.mixedEmbedding.index K))) (i : Fin N),
        A l i = inner ℝ ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
            (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))))
          ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).reindex
            (Fintype.equivFin (NumberField.mixedEmbedding.index K)) l)) ∧
      (A * A.transpose).det ≤
        ((Real.sqrt N * B) ^ (Fintype.card (NumberField.mixedEmbedding.index K)) /
          2 ^ (NumberField.InfinitePlace.nrComplexPlaces K)) ^ 2 := by
  classical
  let e := Fintype.equivFin (NumberField.mixedEmbedding.index K)
  let A : Matrix (Fin (Fintype.card (NumberField.mixedEmbedding.index K))) (Fin N) ℝ :=
    fun l i => inner ℝ ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))))
      ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).reindex e l)
  refine ⟨A, fun l i => rfl, ?_⟩
  have hcoord : ∀ (l : Fin (Fintype.card (NumberField.mixedEmbedding.index K))) (i : Fin N),
      A l i = (NumberField.mixedEmbedding.stdBasis K).repr
        (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))) (e.symm l) := by
    intro l i
    change inner ℝ ((NumberField.mixedEmbedding.euclidean.toMixed K).symm
        (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))))
      ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).reindex e l)
      = (NumberField.mixedEmbedding.stdBasis K).repr
        (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))) (e.symm l)
    rw [OrthonormalBasis.reindex_apply]
    exact inner_toMixed_symm_stdOrthonormalBasis K _ _
  have hreindex :
      ∏ l : Fin (Fintype.card (NumberField.mixedEmbedding.index K)), ∑ i : Fin N, (A l i)^2
        = ∏ c : NumberField.mixedEmbedding.index K,
            ∑ i : Fin N, ((NumberField.mixedEmbedding.stdBasis K).repr
              (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))) c)^2 := by
    refine Fintype.prod_equiv e.symm _ _ ?_
    intro l
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord l i]
  calc (A * A.transpose).det
      ≤ ∏ l : Fin (Fintype.card (NumberField.mixedEmbedding.index K)),
          ∑ i : Fin N, (A l i)^2 := det_mul_transpose_le_sum_sq A
    _ = ∏ c : NumberField.mixedEmbedding.index K,
          ∑ i : Fin N, ((NumberField.mixedEmbedding.stdBasis K).repr
            (NumberField.mixedEmbedding K (((y i : NumberField.RingOfIntegers K) : K))) c)^2 :=
        hreindex
    _ ≤ ((N : ℝ) * B^2)^(Fintype.card (NumberField.mixedEmbedding.index K))
          / (2:ℝ)^(2 * NumberField.InfinitePlace.nrComplexPlaces K) :=
        prod_sq_coord_le K N y B hB0 hB
    _ = ((Real.sqrt N * B) ^ (Fintype.card (NumberField.mixedEmbedding.index K)) /
          2 ^ (NumberField.InfinitePlace.nrComplexPlaces K)) ^ 2 := by
        rw [← sqrt_div_sq N B (Fintype.card (NumberField.mixedEmbedding.index K))
          (NumberField.InfinitePlace.nrComplexPlaces K)]

end

end Commons.NumberTheory.NumberField
