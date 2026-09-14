import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Matrix
open Finset

namespace Commons.LinearAlgebra.Matrix

/-- The determinant, in the column-permutation convention: `det M = ∑ σ, sign σ * ∏ i, M i (σ i)`. -/
private lemma det_apply_col {r : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin r) (Fin r) R) :
    M.det = ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  simp [Matrix.transpose_apply]

/-- Expansion of a minor of a product `A * B` as a sum over all functions `Fin r → Fin n` of the
product of the corresponding "row-minor product" of `A` and the minor of `B`; this is the first step
of the proof of Cauchy–Binet. -/
private lemma det_mul_submatrix_expand {R : Type*} [CommRing R] {m n p r : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin p) R)
    (e : Fin r → Fin m) (f : Fin r → Fin p) :
    ((A * B).submatrix e f).det =
      ∑ q : Fin r → Fin n, (∏ i, A (e i) (q i)) * (B.submatrix q f).det := by
  have hdet : ((A * B).submatrix e f).det =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ i, (((A * B).submatrix e f) i (σ i)) := det_apply_col _
  have hBdet : ∀ q : Fin r → Fin n, (B.submatrix q f).det =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) *
        ∏ i, B (q i) (f (σ i)) := fun q => det_apply_col _
  have hLHS : ((A * B).submatrix e f).det =
      ∑ σ : Equiv.Perm (Fin r), ∑ q : Fin r → Fin n,
        ((Equiv.Perm.sign σ : ℤ) : R) *
          ((∏ i, A (e i) (q i)) * ∏ i, B (q i) (f (σ i))) := by
    rw [hdet]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show (∏ i, (((A * B).submatrix e f) i (σ i)))
          = ∏ i, (∑ k, A (e i) k * B k (f (σ i))) by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Matrix.submatrix_apply, Matrix.mul_apply]]
    rw [Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [hLHS, Finset.sum_comm]
  simp_rw [hBdet]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- Summing `∏ i, M i (τ i) * (sign τ * N.det)` over all permutations `τ` gives `M.det * N.det`. -/
private lemma sum_perm_mul_det {r : ℕ} {R : Type*} [CommRing R]
    (M N : Matrix (Fin r) (Fin r) R) :
    (∑ τ : Equiv.Perm (Fin r), (∏ i, M i (τ i)) * (((Equiv.Perm.sign τ : ℤ) : R) * N.det))
      = M.det * N.det := by
  have h : ∀ τ : Equiv.Perm (Fin r),
      (∏ i, M i (τ i)) * (((Equiv.Perm.sign τ : ℤ) : R) * N.det)
        = (((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M i (τ i)) * N.det := fun τ => by ring
  simp_rw [h]
  rw [← Finset.sum_mul]
  congr 1
  exact (det_apply_col M).symm

/-- Reindexing a sum over all functions `Fin r → Fin n` that vanish on non-injective functions, as a
sum over `r`-element subsets `U` of `Fin n` and permutations `τ : Equiv.Perm (Fin r)`, by sending
`(U, τ)` to the injective function `i ↦ U.orderEmbOfFin hU (τ i)`. -/
private theorem sum_injective_eq_sum_orderEmb {r n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin r → Fin n) → M) (hF : ∀ p, ¬ Function.Injective p → F p = 0) :
    (∑ p : Fin r → Fin n, F p) =
      ∑ U : {U : Finset (Fin n) // U.card = r},
        ∑ τ : Equiv.Perm (Fin r), F (fun i => U.1.orderEmbOfFin U.2 (τ i)) := by
  classical
  have h1 : (∑ p : Fin r → Fin n, F p)
      = ∑ p : {p : Fin r → Fin n // Function.Injective p}, F p.1 := by
    rw [← Finset.sum_subset
      (s₁ := Finset.univ.filter fun p : Fin r → Fin n => Function.Injective p)
      (s₂ := Finset.univ) (Finset.filter_subset _ _) (fun p _ hp => hF p (by simpa using hp))]
    exact Finset.sum_subtype _ (fun p => by simp) _
  rw [h1]
  let Ψ : ({U : Finset (Fin n) // U.card = r} × Equiv.Perm (Fin r)) →
      {p : Fin r → Fin n // Function.Injective p} :=
    fun x => ⟨fun i => x.1.1.orderEmbOfFin x.1.2 (x.2 i),
      (x.1.1.orderEmbOfFin x.1.2).injective.comp x.2.injective⟩
  have hΨinj : Function.Injective Ψ := by
    rintro ⟨⟨U, hU⟩, τ⟩ ⟨⟨U', hU'⟩, τ'⟩ hxy
    simp only [Ψ, Subtype.mk.injEq] at hxy
    have hfuneq : (fun i => (U.orderEmbOfFin hU) (τ i))
        = (fun i => (U'.orderEmbOfFin hU') (τ' i)) := hxy
    have hr : Set.range (U.orderEmbOfFin hU) = Set.range (U'.orderEmbOfFin hU') := by
      have e1 : Set.range (fun i => (U.orderEmbOfFin hU) (τ i)) = Set.range (U.orderEmbOfFin hU) := by
        rw [show (fun i => (U.orderEmbOfFin hU) (τ i)) = (U.orderEmbOfFin hU) ∘ τ from rfl,
          Set.range_comp, τ.surjective.range_eq, Set.image_univ]
      have e2 : Set.range (fun i => (U'.orderEmbOfFin hU') (τ' i)) = Set.range (U'.orderEmbOfFin hU') := by
        rw [show (fun i => (U'.orderEmbOfFin hU') (τ' i)) = (U'.orderEmbOfFin hU') ∘ τ' from rfl,
          Set.range_comp, τ'.surjective.range_eq, Set.image_univ]
      rw [← e1, ← e2, hfuneq]
    have hUeq : U = U' := by
      rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, Finset.coe_inj] at hr
      exact hr
    subst hUeq
    have hτeq : τ = τ' := by
      refine Equiv.ext fun i => ?_
      exact (U.orderEmbOfFin hU).injective (congrFun hfuneq i)
    subst hτeq
    rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro p
    let U : Finset (Fin n) := Finset.univ.image p.1
    have hU : U.card = r := by
      rw [Finset.card_image_of_injective _ p.2, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, p.1 i ∈ Set.range (U.orderEmbOfFin hU) := by
      intro i
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    let τ : Fin r → Fin r := fun i => Classical.choose (hmem i)
    have hτ : ∀ i, U.orderEmbOfFin hU (τ i) = p.1 i := fun i => Classical.choose_spec (hmem i)
    have hτinj : Function.Injective τ := by
      intro i j hij
      exact p.2 (by rw [← hτ i, ← hτ j, hij])
    refine ⟨(⟨U, hU⟩, Equiv.ofBijective τ ⟨hτinj, Finite.injective_iff_surjective.mp hτinj⟩), ?_⟩
    refine Subtype.ext ?_
    funext i
    exact hτ i
  have h2 := Fintype.sum_equiv (Equiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩)
    (fun x : ({U : Finset (Fin n) // U.card = r} × Equiv.Perm (Fin r)) =>
      F (fun i => x.1.1.orderEmbOfFin x.1.2 (x.2 i)))
    (fun p : {p : Fin r → Fin n // Function.Injective p} => F p.1)
    (fun x => rfl)
  rw [← h2]
  rw [Fintype.sum_prod_type]

/-- **Cauchy–Binet** for rectangular matrices: the `r × r` minor of a product `A * B` (rows indexed
by a map `e`, columns by a map `f`) is the sum over `r`-element subsets `U` of the intermediate index
set of the product of the corresponding minors of `A` and `B`. -/
theorem cauchy_binet_general {R : Type*} [CommRing R] {m n p r : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin p) R)
    (e : Fin r → Fin m) (f : Fin r → Fin p) :
    ((A * B).submatrix e f).det =
      ∑ U : {U : Finset (Fin n) // U.card = r},
        (A.submatrix e (U.1.orderEmbOfFin U.2)).det *
        (B.submatrix (U.1.orderEmbOfFin U.2) f).det := by
  rw [det_mul_submatrix_expand A B e f]
  rw [sum_injective_eq_sum_orderEmb (fun q => (∏ i, A (e i) (q i)) * (B.submatrix q f).det) ?_]
  · refine Finset.sum_congr rfl fun U _ => ?_
    have hterm : ∀ τ : Equiv.Perm (Fin r),
        ((∏ i, A (e i) ((U.1.orderEmbOfFin U.2) (τ i))) *
          (B.submatrix (fun i => (U.1.orderEmbOfFin U.2) (τ i)) f).det)
        = (∏ i, (A.submatrix e (U.1.orderEmbOfFin U.2)) i (τ i)) *
          (((Equiv.Perm.sign τ : ℤ) : R) * (B.submatrix (U.1.orderEmbOfFin U.2) f).det) := by
      intro τ
      have h1 : (B.submatrix (fun i => (U.1.orderEmbOfFin U.2) (τ i)) f)
          = (B.submatrix (U.1.orderEmbOfFin U.2) f).submatrix τ id := by
        ext i j; rfl
      rw [h1, Matrix.det_permute]
      rfl
    simp_rw [hterm]
    exact sum_perm_mul_det _ _
  · intro q hq
    rw [Function.not_injective_iff] at hq
    obtain ⟨i, j, hij, hne⟩ := hq
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [Matrix.submatrix_apply, hij]),
      mul_zero]

/-- **Cauchy–Binet**.  For matrices `A B : Matrix (Fin N) (Fin N) R` over a commutative ring and
two `r`-element index sets `T`, `S`, the `r × r` minor of `A * B` indexed by `T`, `S` is the sum
over all `r`-element index sets `U` of the product of the corresponding minors of `A` and `B`.
(The submatrices are taken with the increasing enumeration `Finset.orderEmbOfFin` of the index
sets, which is the form in which Cauchy–Binet is stated without signs.) -/
theorem cauchy_binet {R : Type*} [CommRing R] {N r : ℕ} (A B : Matrix (Fin N) (Fin N) R)
    (T S : Finset (Fin N)) (hT : T.card = r) (hS : S.card = r) :
    ((A * B).submatrix (T.orderEmbOfFin hT) (S.orderEmbOfFin hS)).det =
      ∑ U : {U : Finset (Fin N) // U.card = r},
        (A.submatrix (T.orderEmbOfFin hT) (U.1.orderEmbOfFin U.2)).det *
        (B.submatrix (U.1.orderEmbOfFin U.2) (S.orderEmbOfFin hS)).det :=
  cauchy_binet_general A B (T.orderEmbOfFin hT) (S.orderEmbOfFin hS)

end Commons.LinearAlgebra.Matrix