import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Cauchy–Binet for `n × (n+1)` times `(n+1) × n`, and the adjugate expansion of a row-deleted
product minor

We prove

`Matrix.det_succAbove_mul_eq_sum_adjugate`:

for a commutative ring `K`, `N : ℕ`, `L : Matrix (Fin (N+1)) (Fin (N+1)) K`,
`G : Matrix (Fin (N+1)) (Fin N) K` and `k : Fin (N+1)`,

`((L * G).submatrix (Fin.succAbove k) id).det
   = ∑ j, (-1)^(j + k) * L.adjugate j k * (G.submatrix (Fin.succAbove j) id).det`.

The proof goes through the (special case of the) Cauchy–Binet formula
`det_mul_submatrix_succAbove`: the `n × n` minor of a product of an `n × (n+1)` matrix `A` and a
`(n+1) × n` matrix `B` is the sum over the omitted column `j` of the corresponding minors, and the
identity `(-1)^(j+k) * adjugate L j k = det (L with row k and column j removed)`.
-/

open Finset

namespace Commons.LinearAlgebra.Matrix

/-- The map `(j, τ) ↦ (j.succAbove ∘ τ)` is a bijection between
`Fin (n+1) × Equiv.Perm (Fin n)` and the injective maps `Fin n → Fin (n+1)`. -/
private lemma succAbove_comp_perm_bijective (n : ℕ) :
    Function.Bijective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
      (⟨fun a => p.1.succAbove (p.2 a),
        (Fin.succAbove_right_injective (p := p.1)).comp p.2.injective⟩ :
        {t : Fin n → Fin (n + 1) // Function.Injective t})) := by
  constructor
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    simp only [Subtype.mk.injEq] at h
    have h1 : Set.range (fun a => j.succAbove (τ a)) = Set.range j.succAbove := by
      rw [Set.range_comp' (j.succAbove) (τ), τ.surjective.range_eq, Set.image_univ]
    have h2 : Set.range (fun a => j'.succAbove (τ' a)) = Set.range j'.succAbove := by
      rw [Set.range_comp' (j'.succAbove) (τ'), τ'.surjective.range_eq, Set.image_univ]
    have hrange : Set.range j.succAbove = Set.range j'.succAbove := by
      rw [← h1, ← h2, h]
    rw [Fin.range_succAbove, Fin.range_succAbove] at hrange
    have hjj' : j = j' := by
      have hc : ({j} : Set (Fin (n+1))) = {j'} := compl_injective hrange
      have hmem : j ∈ ({j'} : Set (Fin (n+1))) := by rw [← hc]; exact Set.mem_singleton j
      simpa using hmem
    subst hjj'
    have hτ : τ = τ' :=
      Equiv.ext (fun a => Fin.succAbove_right_injective (congr_fun h a))
    subst hτ
    rfl
  · rintro ⟨t, ht⟩
    obtain ⟨j, ⟨_, hjun⟩, _⟩ := Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one
      (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin (n + 1))))
      (f := t) ht.injOn (by intro x _; simp) (by simp)
    have hj : ∀ a, t a ≠ j := by
      intro a ha
      exact hjun (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
    let τ0 : Fin n → Fin n := fun a => Classical.choose (Fin.exists_succAbove_eq (hj a))
    have hτ0 : ∀ a, j.succAbove (τ0 a) = t a :=
      fun a => Classical.choose_spec (Fin.exists_succAbove_eq (hj a))
    have hinj : Function.Injective τ0 := by
      intro a b hab
      apply ht
      rw [← hτ0 a, ← hτ0 b, hab]
    refine ⟨(j, Equiv.ofBijective τ0 ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩), ?_⟩
    simp only [Subtype.mk.injEq]
    funext a
    exact hτ0 a

/-- A sum over all maps `Fin n → Fin (n+1)` of a function vanishing on the non-injective maps can
be re-indexed as a sum over `(j, τ) ↦ (j.succAbove ∘ τ)`. -/
private lemma sum_injective_eq_sum_succAbove {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : (Fin n → Fin (n+1)) → M) (hf : ∀ t, ¬ Function.Injective t → f t = 0) :
    ∑ t, f t = ∑ j : Fin (n+1), ∑ τ : Equiv.Perm (Fin n), f (fun a => j.succAbove (τ a)) := by
  let G₀ : Fin (n+1) × Equiv.Perm (Fin n) → {t : Fin n → Fin (n+1) // Function.Injective t} :=
    fun p => ⟨fun a => p.1.succAbove (p.2 a),
      (Fin.succAbove_right_injective (p := p.1)).comp p.2.injective⟩
  have hbij' : Function.Bijective G₀ := succAbove_comp_perm_bijective n
  have hzero : ∑ t ∈ Finset.univ.filter (fun t : Fin n → Fin (n+1) => ¬ Function.Injective t),
      f t = 0 :=
    Finset.sum_eq_zero (fun t ht => by
      rw [Finset.mem_filter] at ht
      exact hf t ht.2)
  have hA : ∑ t, f t = ∑ x : {t : Fin n → Fin (n+1) // Function.Injective t}, f x.val := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun t : Fin n → Fin (n+1) => Function.Injective t) f]
    rw [hzero, add_zero]
    exact Finset.sum_subtype _ (fun x => by simp) f
  calc ∑ t, f t
      = ∑ x : {t : Fin n → Fin (n+1) // Function.Injective t}, f x.val := hA
    _ = ∑ p : Fin (n+1) × Equiv.Perm (Fin n), f (G₀ p).val :=
        (Fintype.sum_bijective G₀ hbij' (fun p => f (G₀ p).val) (fun x => f x.val)
          (fun p => rfl)).symm
    _ = ∑ j : Fin (n+1), ∑ τ : Equiv.Perm (Fin n), f (fun a => j.succAbove (τ a)) :=
        Fintype.sum_prod_type _

/-- **Cauchy–Binet**, special case: the determinant of the product of an `n × (n+1)` matrix and a
`(n+1) × n` matrix is the sum over the omitted column `j` of the product of the corresponding
maximal minors. -/
private lemma det_mul_submatrix_succAbove {R : Type*} [CommRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin (n+1)) R) (B : Matrix (Fin (n+1)) (Fin n) R) :
    (A * B).det = ∑ j : Fin (n+1), (A.submatrix id (Fin.succAbove j)).det
        * (B.submatrix (Fin.succAbove j) id).det := by
  have key : ∀ (t : Fin n → Fin (n+1)),
      (∑ σ : Equiv.Perm (Fin n), ↑↑(Equiv.Perm.sign σ) * ∏ a, A (σ a) (t a) * B (t a) a)
      = (∏ a, B (t a) a) * (A.submatrix id t).det := by
    intro t
    have hdet : (A.submatrix id t).det = ∑ σ, ↑↑(Equiv.Perm.sign σ) * ∏ a, A (σ a) (t a) := by
      rw [Matrix.det_apply']
      simp only [Matrix.submatrix_apply, id_eq]
    rw [hdet, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.prod_mul_distrib]
    ring
  have hmain : (A*B).det = ∑ t : Fin n → Fin (n+1),
      (∏ a, B (t a) a) * (A.submatrix id t).det := by
    rw [Matrix.det_apply']
    simp only [Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact key t
  rw [hmain]
  rw [sum_injective_eq_sum_succAbove n (fun t => (∏ a, B (t a) a) * (A.submatrix id t).det) ?_]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hdetB : (B.submatrix (Fin.succAbove j) id).det
        = ∑ τ, ↑↑(Equiv.Perm.sign τ) * ∏ a, B (j.succAbove (τ a)) a := by
      rw [Matrix.det_apply']
      simp only [Matrix.submatrix_apply, id_eq]
    have hdetτ : ∀ τ : Equiv.Perm (Fin n),
        (A.submatrix id (fun a => j.succAbove (τ a))).det
        = ↑↑(Equiv.Perm.sign τ) * (A.submatrix id (Fin.succAbove j)).det := fun τ =>
      (by simpa [Matrix.submatrix_submatrix, Function.comp_def]
        using Matrix.det_permute' τ (A.submatrix id (Fin.succAbove j)))
    rw [hdetB, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hdetτ τ]
    ring
  · intro t ht
    rw [Function.not_injective_iff] at ht
    obtain ⟨a, b, hab, hne⟩ := ht
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hab]),
      mul_zero]

theorem det_succAbove_mul_eq_sum_adjugate {K : Type*} [CommRing K] (N : ℕ)
    (L : Matrix (Fin (N+1)) (Fin (N+1)) K) (G : Matrix (Fin (N+1)) (Fin N) K) (k : Fin (N+1)) :
    ((L * G).submatrix (Fin.succAbove k) id).det
      = ∑ j : Fin (N+1),
          (-1 : K) ^ ((j : ℕ) + (k : ℕ)) * L.adjugate j k * (G.submatrix (Fin.succAbove j) id).det := by
  have hL : (L.submatrix (Fin.succAbove k) id) * G = (L * G).submatrix (Fin.succAbove k) id := by
    rw [Matrix.submatrix_mul L G (Fin.succAbove k) id id Function.bijective_id]
    simp
  have h := det_mul_submatrix_succAbove N (L.submatrix (Fin.succAbove k) id) G
  rw [hL] at h
  rw [h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hterm : ((L.submatrix (Fin.succAbove k) id).submatrix id (Fin.succAbove j)).det
      = (-1 : K) ^ ((j : ℕ) + (k : ℕ)) * L.adjugate j k := by
    rw [Matrix.submatrix_submatrix]
    simp only [Function.comp_id, Function.id_comp]
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix L j k]
    have hone : (-1 : K) ^ (((j:ℕ)+(k:ℕ)) + ((k:ℕ)+(j:ℕ))) = 1 := by
      rw [show ((j:ℕ)+(k:ℕ)) + ((k:ℕ)+(j:ℕ)) = 2 * ((j:ℕ)+(k:ℕ)) by ring, pow_mul, neg_one_sq,
        one_pow]
    rw [← mul_assoc, ← pow_add, hone, one_mul]
  rw [hterm]

end Commons.LinearAlgebra.Matrix