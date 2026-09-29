/-
Auxiliary definitions and lemmas for `Work.TMC14Core.AdjTrace`.

The mathematical content is the classical expansion of the adjugate of the
characteristic matrix `X • 1 - B` as a polynomial in `B` (the "divided
difference" of the characteristic polynomial):

  adjugate (charmatrix B) = ∑_{i=0}^{q} (charpoly B).coeff i • geom B i

where `geom B i = ∑_{k<i} X^{i-1-k} • B^k`.  The coefficient of `B^{q-1}` is
therefore `(charpoly B).coeff q = 1`.
-/
import Mathlib

namespace Work.TMC14Core

open Polynomial Matrix Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- `geom B i = ∑_{k<i} X^{i-1-k} • B^k`, the geometric (divided-difference)
sum of `X` and `B`, a matrix over `R[X]`. -/
noncomputable def geom {q : ℕ} (B : Matrix (Fin q) (Fin q) R) (i : ℕ) :
    Matrix (Fin q) (Fin q) R[X] :=
  ∑ k ∈ Finset.range i, ((Polynomial.X : R[X]) ^ (i - 1 - k)) • (B.map (Polynomial.C : R →+* R[X])) ^ k

@[simp] lemma geom_zero {q : ℕ} (B : Matrix (Fin q) (Fin q) R) : geom B 0 = 0 := by
  simp [geom]

lemma geom_succ {q : ℕ} (B : Matrix (Fin q) (Fin q) R) (i : ℕ) :
    geom B (i + 1) = (Polynomial.X : R[X]) • geom B i + (B.map (Polynomial.C : R →+* R[X])) ^ i := by
  rw [geom, Finset.sum_range_succ]
  have hlast : ((Polynomial.X : R[X]) ^ ((i + 1) - 1 - i)) • (B.map (Polynomial.C : R →+* R[X])) ^ i
      = (B.map (Polynomial.C : R →+* R[X])) ^ i := by
    rw [show (i + 1) - 1 - i = 0 by omega, pow_zero, one_smul]
  rw [hlast, geom, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < i := Finset.mem_range.mp hk
  have : (i + 1) - 1 - k = (i - 1 - k) + 1 := by omega
  rw [this, pow_succ', smul_smul]

/-- Telescoping (geometric series) identity: `(X - B) · geom B i = X^i - B^i`. -/
lemma geom_telescope {q : ℕ} (B : Matrix (Fin q) (Fin q) R) (i : ℕ) :
    ((Polynomial.X : R[X]) • (1 : Matrix (Fin q) (Fin q) R[X]) - B.map (Polynomial.C : R →+* R[X])) * geom B i
      = ((Polynomial.X : R[X]) ^ i) • (1 : Matrix (Fin q) (Fin q) R[X]) - (B.map (Polynomial.C : R →+* R[X])) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [geom_succ, Matrix.mul_add, Matrix.mul_smul, ih, Matrix.sub_mul, Matrix.smul_mul,
        Matrix.one_mul, smul_sub]
    have hX : (Polynomial.X : R[X]) • (Polynomial.X : R[X]) ^ i • (1 : Matrix (Fin q) (Fin q) R[X])
        = (Polynomial.X : R[X]) ^ (i + 1) • (1 : Matrix (Fin q) (Fin q) R[X]) := by
      rw [smul_smul, ← pow_succ']
    have hB : (B.map (Polynomial.C : R →+* R[X])) * (B.map (Polynomial.C : R →+* R[X])) ^ i
        = (B.map (Polynomial.C : R →+* R[X])) ^ (i + 1) := by
      rw [← pow_succ']
    rw [hX, hB]
    abel

/-- **Adjugate expansion.**  For a matrix `B` over a nontrivial commutative ring,
the adjugate of the characteristic matrix `X • 1 - B` equals
`∑ i ≤ q, (charpoly B).coeff i • geom B i`. -/
theorem adjugate_charmatrix_eq {q : ℕ} [Nontrivial R] (B : Matrix (Fin q) (Fin q) R) :
    (B.charmatrix).adjugate = ∑ i ∈ Finset.range (q + 1), Polynomial.C (B.charpoly.coeff i) • geom B i := by
  have hcharm : B.charmatrix =
      (Polynomial.X : R[X]) • (1 : Matrix (Fin q) (Fin q) R[X]) - B.map (Polynomial.C : R →+* R[X]) := by
    simp only [Matrix.charmatrix, Matrix.scalar_apply, RingHom.mapMatrix_apply]
    rw [← Matrix.smul_one_eq_diagonal]
  have hpnd : B.charpoly.natDegree = q := by simpa using Matrix.charpoly_natDegree_eq_dim B
  have hpsum : (∑ i ∈ Finset.range (q + 1),
      Polynomial.C (B.charpoly.coeff i) * (Polynomial.X : R[X]) ^ i) = B.charpoly := by
    rw [show q + 1 = B.charpoly.natDegree + 1 by rw [hpnd]]
    exact (Polynomial.as_sum_range_C_mul_X_pow B.charpoly).symm
  have hBsum : (∑ i ∈ Finset.range (q + 1),
      Polynomial.C (B.charpoly.coeff i) • (B.map (Polynomial.C : R →+* R[X])) ^ i) = 0 := by
    rw [← Matrix.aeval_self_charpoly (B.map (Polynomial.C : R →+* R[X]))]
    rw [Polynomial.aeval_eq_sum_range]
    rw [show ((B.map (Polynomial.C : R →+* R[X])).charpoly).natDegree = q by
      simpa using Matrix.charpoly_natDegree_eq_dim (B.map (Polynomial.C : R →+* R[X]))]
    apply Finset.sum_congr rfl
    intro i _
    rw [show ((B.map (Polynomial.C : R →+* R[X])).charpoly).coeff i = Polynomial.C (B.charpoly.coeff i) by
      rw [Matrix.charpoly_map, Polynomial.coeff_map]]
  have hAS : ∀ S : Matrix (Fin q) (Fin q) R[X],
      S = ∑ i ∈ Finset.range (q + 1), Polynomial.C (B.charpoly.coeff i) • geom B i →
      B.charmatrix * S = B.charpoly • (1 : Matrix (Fin q) (Fin q) R[X]) := by
    intro S hS
    rw [hcharm, hS, Matrix.mul_sum]
    simp only [Matrix.mul_smul, geom_telescope, smul_sub]
    rw [Finset.sum_sub_distrib]
    have h2 : (∑ i ∈ Finset.range (q + 1), Polynomial.C (B.charpoly.coeff i) •
          (((Polynomial.X : R[X]) ^ i) • (1 : Matrix (Fin q) (Fin q) R[X])))
        = (∑ i ∈ Finset.range (q + 1),
            Polynomial.C (B.charpoly.coeff i) * (Polynomial.X : R[X]) ^ i)
            • (1 : Matrix (Fin q) (Fin q) R[X]) := by
      simp only [smul_smul]
      rw [← Finset.sum_smul]
    rw [h2, hpsum, hBsum, sub_zero]
  have hadj : B.charmatrix * (B.charmatrix).adjugate =
      B.charpoly • (1 : Matrix (Fin q) (Fin q) R[X]) := by
    rw [Matrix.mul_adjugate]
    rfl
  have hreg : IsRegular B.charmatrix :=
    isRegular_of_isLeftRegular_det (A := B.charmatrix)
      (Polynomial.Monic.isRegular (Matrix.charpoly_monic B)).left
  exact (hreg.left (hAS _ rfl |>.trans hadj.symm)).symm

/-- The same geometric sum evaluated at a complex number `z`. -/
noncomputable def geomZ {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (z : ℂ) (i : ℕ) :
    Matrix (Fin q) (Fin q) ℂ :=
  ∑ k ∈ Finset.range i, (z ^ (i - 1 - k)) • B ^ k

lemma geomZ_succ {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (z : ℂ) (i : ℕ) :
    geomZ B z (i + 1) = z • geomZ B z i + B ^ i := by
  rw [geomZ, Finset.sum_range_succ]
  have hlast : (z ^ ((i + 1) - 1 - i)) • B ^ i = B ^ i := by
    rw [show (i + 1) - 1 - i = 0 by omega, pow_zero, one_smul]
  rw [hlast, geomZ, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < i := Finset.mem_range.mp hk
  have : (i + 1) - 1 - k = (i - 1 - k) + 1 := by omega
  rw [this, pow_succ', smul_smul]

lemma map_BC {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (z : ℂ) :
    (B.map (Polynomial.C : ℂ →+* ℂ[X])).map (Polynomial.eval z) = B := by
  rw [Matrix.map_map,
    show (Polynomial.eval z) ∘ (Polynomial.C : ℂ →+* ℂ[X]) = id from funext fun x => Polynomial.eval_C,
    Matrix.map_id]

/-- Evaluating the `R[X]`-valued geometric sum at `z` gives `geomZ`. -/
lemma map_geom {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (z : ℂ) (i : ℕ) :
    (geom B i).map (Polynomial.eval z) = geomZ B z i := by
  induction i with
  | zero => simp [geom, geomZ]
  | succ i ih =>
    rw [geom_succ, geomZ_succ, Matrix.map_add _ (fun a b => by rw [Polynomial.eval_add]),
        Matrix.map_smul' _ _ _ (fun a b => by rw [Polynomial.eval_mul]), ih, Polynomial.eval_X]
    congr 1
    have hpow : (B.map (Polynomial.C : ℂ →+* ℂ[X]) ^ i).map (Polynomial.eval z)
        = ((B.map (Polynomial.C : ℂ →+* ℂ[X])).map (Polynomial.eval z)) ^ i :=
      Matrix.map_pow _ (Polynomial.evalRingHom z) i
    rw [hpow, map_BC]

/-- `Matrix.map` commutes with finite sums. -/
lemma Matrix.map_sum' {ι m n : Type*} {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (f : α → β) (h0 : f 0 = 0) (hf : ∀ a b, f (a + b) = f a + f b) (s : Finset ι)
    (g : ι → Matrix m n α) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Matrix.map_zero f h0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.map_add f hf, ih]

lemma map_charmatrix {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (z : ℂ) :
    B.charmatrix.map (Polynomial.eval z) = z • (1 : Matrix (Fin q) (Fin q) ℂ) - B := by
  have hc : B.charmatrix =
      (Polynomial.X : ℂ[X]) • (1 : Matrix (Fin q) (Fin q) ℂ[X]) - B.map (Polynomial.C : ℂ →+* ℂ[X]) := by
    simp only [Matrix.charmatrix, Matrix.scalar_apply, RingHom.mapMatrix_apply]
    rw [← Matrix.smul_one_eq_diagonal]
  rw [hc, Matrix.map_sub _ (fun a b => by rw [Polynomial.eval_sub]),
      Matrix.map_smul' _ _ _ (fun a b => by rw [Polynomial.eval_mul]), Polynomial.eval_X,
      Matrix.map_one _ Polynomial.eval_zero Polynomial.eval_one, map_BC]

lemma map_geomsum {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (z : ℂ) :
    (∑ i ∈ Finset.range (q + 1), Polynomial.C (B.charpoly.coeff i) • geom B i).map (Polynomial.eval z)
      = ∑ i ∈ Finset.range (q + 1), (B.charpoly.coeff i) • geomZ B z i := by
  rw [Matrix.map_sum' (Polynomial.eval z) (Polynomial.eval_zero (x := z))
      (fun a b => by rw [Polynomial.eval_add])]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.map_smul' (Polynomial.eval z) _ _ (fun a b => by rw [Polynomial.eval_mul]), Polynomial.eval_C,
      map_geom]

end Work.TMC14Core
