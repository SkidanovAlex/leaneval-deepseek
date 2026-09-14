import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_mul_of_pderiv_eq_zero
import Submission.Commons.Algebra.MvPolynomial.linearIndependent_iff_exists_wronskian
import Submission.Subspace.SuccEmbed

/-!
# The Wronskian of a decomposition, in `MvPolynomial` language

Roth's lemma writes `P ∈ K[x_0,…,x_n]` as `P = ∑_r Φ_r Ψ_r` with `Φ_r` involving only
`x_1,…,x_n` and `Ψ_r` only `x_0`, and forms the Wronskian matrix
`W_{ij} = ∂^{μᵢ + j e₀} P`.  Because the two families live in disjoint sets of variables, the
product rule degenerates and one gets the matrix identity `W = B · A` with
`B_{ir} = ∂^{μᵢ} Φ_r` and `A_{rj} = ∂^{j e₀} Ψ_r`.

This file is the `MvPolynomial` counterpart of `Submission.Subspace.Wronskian` (which works in
`Polynomial (MvPolynomial (Fin n) K)`); working in `MvPolynomial` lets the `index` theory
(`Submission.Subspace.Index`, `…IndexDet`, `…RothIndex`, `…IndexRename`) be applied directly.
-/

open scoped BigOperators

namespace Submission.Subspace

open Commons.Algebra.MvPolynomial (pderivIter indexWt)

variable {K : Type*} [CommSemiring K] {n k : ℕ}

/-- Every element of the support of `ν.mapDomain Fin.succ` is a value of `Fin.succ`. -/
lemma exists_eq_succ_of_mem_support_mapDomain_succ {ν : Fin n →₀ ℕ} {x : Fin (n + 1)}
    (hx : x ∈ (ν.mapDomain Fin.succ).support) : ∃ t : Fin n, x = Fin.succ t := by
  obtain ⟨t, -, ht⟩ := Finset.mem_image.mp
    ((Finsupp.mapDomain_support (f := Fin.succ) (s := ν)) hx)
  exact ⟨t, ht.symm⟩

/-- The elements of the support of `j • e₀` are all equal to `0`. -/
lemma eq_zero_of_mem_support_smul_single_zero {j : ℕ} {x : Fin (n + 1)}
    (hx : x ∈ (j • Finsupp.single (0 : Fin (n + 1)) 1).support) : x = 0 := by
  by_contra h
  rw [Finsupp.mem_support_iff, Finsupp.smul_apply, Finsupp.single_eq_of_ne h, smul_zero]
    at hx
  exact hx rfl

/-- `∂^{ν}` (in the `Fin.succ` variables) commutes with multiplication by a polynomial in the
`x_0` variable only. -/
lemma pderivIter_mapDomain_succ_mul {ν : Fin n →₀ ℕ} (A B : MvPolynomial (Fin (n + 1)) K)
    (hB : ∀ t : Fin n, MvPolynomial.pderiv (Fin.succ t) B = 0) :
    pderivIter (ν.mapDomain Fin.succ) (A * B) = pderivIter (ν.mapDomain Fin.succ) A * B := by
  refine Commons.Algebra.MvPolynomial.pderivIter_mul_of_pderiv_eq_zero _ A B ?_
  intro x hx
  obtain ⟨t, rfl⟩ := exists_eq_succ_of_mem_support_mapDomain_succ hx
  exact hB t

/-- `∂^{m}` for `m` supported at `0` commutes with multiplication by a polynomial in the other
variables. -/
lemma pderivIter_mul_smul_single_zero {m : Fin (n + 1) →₀ ℕ}
    (hm : ∀ x ∈ m.support, x = 0) (A B : MvPolynomial (Fin (n + 1)) K)
    (hA : MvPolynomial.pderiv (0 : Fin (n + 1)) A = 0) :
    pderivIter m (A * B) = A * pderivIter m B := by
  rw [mul_comm A B, Commons.Algebra.MvPolynomial.pderivIter_mul_of_pderiv_eq_zero m B A
    (fun x hx => by rw [hm x hx]; exact hA), mul_comm]

/-- `∂^{e_i} = ∂_i`. -/
lemma pderivIter_single_one (i : Fin (n + 1)) (P : MvPolynomial (Fin (n + 1)) K) :
    pderivIter (Finsupp.single i 1) P = MvPolynomial.pderiv i P := by
  have h0 := (Commons.Algebra.MvPolynomial.pderivIter_properties (R := K)
    (σ := Fin (n + 1))).1 P
  have h := (Commons.Algebra.MvPolynomial.pderivIter_properties (R := K)
    (σ := Fin (n + 1))).2.2.1 i (0 : Fin (n + 1) →₀ ℕ) P
  rw [zero_add, h0] at h
  exact h.symm

/-- `∂^{m} 0 = 0`. -/
lemma pderivIter_zero_poly (m : Fin (n + 1) →₀ ℕ) :
    pderivIter m (0 : MvPolynomial (Fin (n + 1)) K) = 0 := by
  rw [Commons.Algebra.MvPolynomial.pderivIter_eq_sum]
  simp

/-- `∂_0` kills `∂^{ν} Φ` when it kills `Φ` (and `ν` only involves the `Fin.succ` variables). -/
lemma pderiv_zero_pderivIter_mapDomain_succ {ν : Fin n →₀ ℕ} {Φ : MvPolynomial (Fin (n + 1)) K}
    (hΦ : MvPolynomial.pderiv (0 : Fin (n + 1)) Φ = 0) :
    MvPolynomial.pderiv (0 : Fin (n + 1)) (pderivIter (ν.mapDomain Fin.succ) Φ) = 0 := by
  have h1 : MvPolynomial.pderiv (0 : Fin (n + 1)) (pderivIter (ν.mapDomain Fin.succ) Φ)
      = pderivIter (ν.mapDomain Fin.succ + Finsupp.single (0 : Fin (n + 1)) 1) Φ :=
    (Commons.Algebra.MvPolynomial.pderivIter_properties (R := K) (σ := Fin (n + 1))).2.2.1
      (0 : Fin (n + 1)) (ν.mapDomain Fin.succ) Φ
  rw [h1]
  have hcomm : ν.mapDomain Fin.succ + Finsupp.single (0 : Fin (n + 1)) 1
      = Finsupp.single (0 : Fin (n + 1)) 1 + ν.mapDomain Fin.succ :=
    add_comm _ _
  rw [hcomm, Commons.Algebra.MvPolynomial.pderivIter_add, pderivIter_single_one, hΦ]
  exact pderivIter_zero_poly _

/-- **The Wronskian of a decomposition factors** (sum form).  If `P = ∑_r Φ_r Ψ_r` with `Φ_r`
killed by `∂_0` and `Ψ_r` killed by `∂_{x_i}` for `i ≥ 1`, then
`∂^{μᵢ + j e₀} P = ∑_r (∂^{μᵢ} Φ_r) (∂^{j e₀} Ψ_r)`. -/
theorem wronskian_factorization_mv_sum (P : MvPolynomial (Fin (n + 1)) K)
    (Φ Ψ : Fin k → MvPolynomial (Fin (n + 1)) K)
    (hdec : P = ∑ r, Φ r * Ψ r)
    (hΦ : ∀ r, MvPolynomial.pderiv (0 : Fin (n + 1)) (Φ r) = 0)
    (hΨ : ∀ r (t : Fin n), MvPolynomial.pderiv (Fin.succ t) (Ψ r) = 0)
    (μ : Fin k → Fin n →₀ ℕ) (i j : Fin k) :
    pderivIter ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P =
      ∑ r, pderivIter ((μ i).mapDomain Fin.succ) (Φ r) *
        pderivIter ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ r) := by
  subst hdec
  rw [Commons.Algebra.MvPolynomial.pderivIter_add]
  have hinner : pderivIter ((μ i).mapDomain Fin.succ) (∑ r, Φ r * Ψ r)
      = ∑ r, pderivIter ((μ i).mapDomain Fin.succ) (Φ r) * Ψ r := by
    rw [Commons.Algebra.MvPolynomial.pderivIter_sum_apply]
    exact Finset.sum_congr rfl fun r _ => pderivIter_mapDomain_succ_mul (Φ r) (Ψ r) (hΨ r)
  rw [hinner, Commons.Algebra.MvPolynomial.pderivIter_sum_apply]
  exact Finset.sum_congr rfl fun r _ =>
    pderivIter_mul_smul_single_zero
      (m := (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1)
      (fun x hx => eq_zero_of_mem_support_smul_single_zero hx) _ _
      (pderiv_zero_pderivIter_mapDomain_succ (hΦ r))

/-- **The Wronskian matrix of a decomposition factors.** -/
theorem wronskian_factorization_mv (P : MvPolynomial (Fin (n + 1)) K)
    (Φ Ψ : Fin k → MvPolynomial (Fin (n + 1)) K)
    (hdec : P = ∑ r, Φ r * Ψ r)
    (hΦ : ∀ r, MvPolynomial.pderiv (0 : Fin (n + 1)) (Φ r) = 0)
    (hΨ : ∀ r (t : Fin n), MvPolynomial.pderiv (Fin.succ t) (Ψ r) = 0)
    (μ : Fin k → Fin n →₀ ℕ) :
    (Matrix.of fun i j : Fin k =>
        pderivIter ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) =
      (Matrix.of fun i r : Fin k => pderivIter ((μ i).mapDomain Fin.succ) (Φ r)) *
        (Matrix.of fun r j : Fin k =>
          pderivIter ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ r)) := by
  classical
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  exact wronskian_factorization_mv_sum P Φ Ψ hdec hΦ hΨ μ i j

/-- **Determinant form of the Wronskian factorisation** in `MvPolynomial` language. -/
theorem det_wronskian_factorization_mv {K : Type*} [CommRing K] {n k : ℕ}
    (P : MvPolynomial (Fin (n + 1)) K)
    (Φ Ψ : Fin k → MvPolynomial (Fin (n + 1)) K)
    (hdec : P = ∑ r, Φ r * Ψ r)
    (hΦ : ∀ r, MvPolynomial.pderiv (0 : Fin (n + 1)) (Φ r) = 0)
    (hΨ : ∀ r (t : Fin n), MvPolynomial.pderiv (Fin.succ t) (Ψ r) = 0)
    (μ : Fin k → Fin n →₀ ℕ) :
    (Matrix.of fun i j : Fin k =>
        pderivIter ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det =
      (Matrix.of fun i r : Fin k => pderivIter ((μ i).mapDomain Fin.succ) (Φ r)).det *
        (Matrix.of fun r j : Fin k =>
          pderivIter ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ r)).det := by
  rw [wronskian_factorization_mv P Φ Ψ hdec hΦ hΨ μ, Matrix.det_mul]

set_option maxHeartbeats 800000 in
/-- **Index lower bound for the Wronskian of a decomposition.**  Combining
`det_wronskian_factorization_mv` with `index_det_wronskian_ge`: if `B` bounds
`∑ₜ (μᵢ)ₜ/r(succ t)` for all `i`, then the determinant of the Wronskian has index at least
`∑_j (Ind P - B - j/r 0)`. -/
theorem index_det_wronskian_mv {K : Type*} [Field K] [CharZero K] {n k : ℕ}
    (β : Fin (n + 1) → K) (r : Fin (n + 1) → ℕ) (P : MvPolynomial (Fin (n + 1)) K)
    (Φ Ψ : Fin k → MvPolynomial (Fin (n + 1)) K)
    (_hdec : P = ∑ r, Φ r * Ψ r)
    (_hΦ : ∀ r, MvPolynomial.pderiv (0 : Fin (n + 1)) (Φ r) = 0)
    (_hΨ : ∀ r (t : Fin n), MvPolynomial.pderiv (Fin.succ t) (Ψ r) = 0)
    (μ : Fin k → Fin n →₀ ℕ) (B : ℝ) (hB : ∀ i, indexWt r ((μ i).mapDomain Fin.succ) ≤ B)
    (hdet : (Matrix.of fun i j : Fin k =>
        pderivIter ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1)
          P).det ≠ 0) :
    ∑ j : Fin k, (index β r P - B - (j : ℝ) / (r 0 : ℝ)) ≤
      index β r (Matrix.of fun i j : Fin k =>
        pderivIter ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1)
          P).det := by
  have hdet' : (Matrix.of fun i j : Fin k =>
      MvPolynomial.C (1 : K) * pderivIter ((μ i).mapDomain Fin.succ
        + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det ≠ 0 := by
    simpa using hdet
  have key := index_det_wronskian_ge β r P 0 (fun i => (μ i).mapDomain Fin.succ) B hB
    (fun _ _ => (1 : K)) (fun _ _ => one_ne_zero) hdet'
  have hmat : (Matrix.of fun i j : Fin k => pderivIter ((μ i).mapDomain Fin.succ
        + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)
      = (Matrix.of fun i j : Fin k => MvPolynomial.C (1 : K) * pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) := by
    ext i j
    simp
  rw [hmat]
  exact key

end Submission.Subspace
