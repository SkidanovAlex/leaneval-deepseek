import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.DifferentialRing

open Matrix

namespace Commons.LinearAlgebra.Matrix

/-- **Leibniz rule for a finite product under a derivation.**
For a derivation `D` on a commutative ring and a finite family `f`, the derivative of the product
`∏ i ∈ s, f i` is `∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i)`. -/
lemma deriv_prod_finset {A : Type*} [CommRing A] [Differential A] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → A) :
    Differential.deriv (∏ i ∈ s, f i)
      = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * Differential.deriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h2 : (insert a s).erase a = s := Finset.erase_insert ha
      have h3 : (∏ i ∈ (insert a s), f i) = f a * ∏ i ∈ s, f i := Finset.prod_insert ha
      rw [h3, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul,
        Finset.sum_insert ha, h2, Finset.mul_sum]
      suffices h : ∑ i ∈ s, f a * ((∏ j ∈ s.erase i, f j) * Differential.deriv (f i))
          = ∑ i ∈ s, (∏ j ∈ (insert a s).erase i, f j) * Differential.deriv (f i) by
        rw [h, add_comm]
      apply Finset.sum_congr rfl
      intro i hi
      have h4 : (insert a s).erase i = insert a (s.erase i) := by
        apply Finset.erase_insert_of_ne
        rintro rfl
        exact ha hi
      have h5 : (∏ j ∈ insert a (s.erase i), f j) = f a * ∏ j ∈ s.erase i, f j :=
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))
      rw [h4, h5]
      ring

/-- Expansion of the derivative of a determinant as a sum over permutations: applying the
derivation and then the Leibniz rule for the product `∏ i, M (σ i) i` gives
`∑ σ, sign σ * ∑ k, (∏ i ≠ k, M (σ i) i) * D (M (σ k) k)`. -/
lemma deriv_det_eq {A : Type*} [CommRing A] [Differential A] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι A) :
    Differential.deriv M.det
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, M (σ i) i) * Differential.deriv (M (σ k) k) := by
  classical
  rw [Matrix.det_apply']
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hc : Differential.deriv (((Equiv.Perm.sign σ : ℤ)) : A) = 0 := by simp
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hc, mul_zero, add_zero]
  rw [deriv_prod_finset (Finset.univ) (fun i => M (σ i) i)]

/-- The product `∏ i, (M.updateRow l (single k 1)) (σ i) i` is nonzero exactly when `σ k = l`, and
then equals `∏ i ≠ k, M (σ i) i`: the inserted column `Pi.single k 1` contributes a single `1`. -/
lemma prod_updateRow_eq {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (k l : ι) (σ : Equiv.Perm ι) :
    (∏ i, (M.updateRow l ((Pi.single k (1 : A) : ι → A))) (σ i) i)
      = (if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i := by
  classical
  have hsigma : σ (σ.symm l) = l := Equiv.apply_symm_apply σ l
  have hsingle : (Pi.single k (1 : A) : ι → A) (σ.symm l) = (if σ k = l then 1 else 0) := by
    rw [Pi.single_apply]
    by_cases h : σ k = l
    · rw [if_pos (show σ.symm l = k from by rw [← h, Equiv.symm_apply_apply]), if_pos h]
    · rw [if_neg (fun hh => h (by rw [← hsigma, hh])), if_neg h]
  have hfun : ∀ i, (M.updateRow l ((Pi.single k (1 : A) : ι → A))) (σ i) i
      = (if σ i = l then (Pi.single k (1 : A) : ι → A) i else M (σ i) i) := by
    intro i; rw [Matrix.updateRow_apply]
  simp only [hfun]
  have hprod2 : (∏ i ∈ Finset.univ.erase (σ.symm l),
        (if σ i = l then (Pi.single k (1 : A) : ι → A) i else M (σ i) i))
      = ∏ i ∈ Finset.univ.erase (σ.symm l), M (σ i) i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg]
    intro hsi
    exact Finset.ne_of_mem_erase hi (σ.injective (by rw [hsi, hsigma]))
  rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if σ i = l then (Pi.single k (1 : A) : ι → A) i else M (σ i) i)
        (Finset.mem_univ (σ.symm l)), if_pos hsigma, hsingle, hprod2]
  by_cases h : σ k = l
  · have hak : σ.symm l = k := by rw [← h, Equiv.symm_apply_apply]
    rw [if_pos h, hak]
  · rw [if_neg h, zero_mul, zero_mul]

/-- Evaluation of a `Pi.single`-type sum: only the term `l = σ k` survives. -/
lemma sum_ite_mul_perm {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι) (σ : Equiv.Perm ι) (P : A) (v : ι → A) :
    (∑ l, ((if σ k = l then (1 : A) else 0) * P) * v l) = P * v (σ k) := by
  have h : ∀ l, ((if σ k = l then (1 : A) else 0) * P) * v l
      = (if l = σ k then P * v l else 0) := by
    intro l
    by_cases hl : σ k = l
    · rw [if_pos hl, if_pos hl.symm, one_mul]
    · rw [if_neg hl, if_neg (fun hh => hl hh.symm), zero_mul, zero_mul]
  simp_rw [h]
  rw [Finset.sum_ite_eq' Finset.univ (σ k) (fun l => P * v l)]
  simp

/-- Cofactor expansion of `∑ l, M.adjugate k l * v l` as a sum over permutations, using
`M.adjugate k l = det (M.updateRow l (single k 1))`. -/
lemma adjugate_perm_sum {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (k : ι) (v : ι → A) :
    (∑ l, M.adjugate k l * v l)
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : A) *
          ((∏ i ∈ Finset.univ.erase k, M (σ i) i) * v (σ k)) := by
  classical
  have h : ∀ l, M.adjugate k l = ∑ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ : ℤ) : A) *
        ((if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i) := by
    intro l
    rw [Matrix.adjugate_apply, Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    rw [prod_updateRow_eq]
  calc ∑ l, M.adjugate k l * v l
      = ∑ l, (∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) *
            ((if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i)) * v l := by
          apply Finset.sum_congr rfl; intro l _; rw [h l]
    _ = ∑ l, ∑ σ, (((Equiv.Perm.sign σ : ℤ) : A) *
            ((if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i)) * v l := by
          apply Finset.sum_congr rfl; intro l _; rw [Finset.sum_mul]
    _ = ∑ σ, ∑ l, (((Equiv.Perm.sign σ : ℤ) : A) *
            ((if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i)) * v l :=
          Finset.sum_comm
    _ = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : A) *
          ((∏ i ∈ Finset.univ.erase k, M (σ i) i) * v (σ k)) := by
          apply Finset.sum_congr rfl; intro σ _
          rw [show (∑ l, (((Equiv.Perm.sign σ : ℤ) : A) *
                ((if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i)) * v l)
              = ((Equiv.Perm.sign σ : ℤ) : A) *
                (∑ l, ((if σ k = l then 1 else 0) * ∏ i ∈ Finset.univ.erase k, M (σ i) i) * v l)
              from by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring]
          rw [sum_ite_mul_perm]

/-- **Jacobi's formula for the derivative of a determinant.** Over a commutative ring `A` equipped
with a derivation `D`, the derivative of the determinant of a square matrix `M` is the trace of the
product of the adjugate of `M` with the entrywise derivative of `M`:

`D (M.det) = (M.adjugate * M.map D).trace`.

This is the classical formula
`(det M)' = tr(adjugate M * M')`, valid over any commutative ring (no invertibility of `M`
required). Suggested proof: expand `M.det = ∑ σ, sign σ • ∏ i, M (σ i) i` (`Matrix.det_apply`), use
the Leibniz rule for the finite product (`D (∏ i, f i) = ∑ i, (∏ j ∈ univ.erase i, f j) * D (f i)`,
prove by induction), and compare term by term with the expansion of
`tr(M.adjugate * M.map D)` obtained from
`M.adjugate k l = (M.updateRow l (Pi.single k 1)).det` (`Matrix.adjugate_apply`) and `det_apply`. -/
theorem deriv_det {A : Type*} [CommRing A] [Differential A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) :
    Differential.deriv M.det = (M.adjugate * M.map Differential.deriv).trace := by
  classical
  have hr : (M.adjugate * M.map Differential.deriv).trace
      = ∑ k, ∑ l, M.adjugate k l * Differential.deriv (M l k) := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl; intro k _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.map_apply]
  have hr2 : (∑ k, ∑ l, M.adjugate k l * Differential.deriv (M l k))
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, M (σ i) i) * Differential.deriv (M (σ k) k) := by
    simp_rw [adjugate_perm_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro σ _
    rw [Finset.mul_sum]
  rw [hr, deriv_det_eq M, hr2]

end Commons.LinearAlgebra.Matrix