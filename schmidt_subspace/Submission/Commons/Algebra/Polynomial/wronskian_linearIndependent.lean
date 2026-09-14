import Mathlib
import Submission.Commons.Algebra.Matrix.det_zero_last_row_adjugate
import Submission.Commons.Algebra.Polynomial.wronskian_eq_zero_ratio

open scoped BigOperators Matrix

namespace Commons.Algebra.Polynomial

/-- The Wronskian matrix of a family of polynomials: the entry in row `i` and column `j` is the
`i`-th derivative of `f j`. -/
noncomputable def wmat {K : Type*} [Semiring K] {n : ℕ} (f : Fin n → Polynomial K) : Matrix (Fin n) (Fin n) (Polynomial K) :=
  Matrix.of (fun i j => (Polynomial.derivative^[(i : ℕ)]) (f j))

/-- The top-left `(n-1) × (n-1)` minor of the Wronskian matrix of `f : Fin n → K[X]` is the
Wronskian matrix of the restricted family `l ↦ f (Fin.castSucc l)`. -/
private lemma wmat_submatrix_castSucc {K : Type*} [Semiring K] {m : ℕ}
    (f : Fin (m + 1) → Polynomial K) :
    (wmat f).submatrix Fin.castSucc Fin.castSucc
      = wmat (fun l : Fin m => f (Fin.castSucc l)) := by
  ext i j
  simp [wmat, Matrix.submatrix_apply, Matrix.of_apply]

/-- Differentiating the Wronskian relation `D * Y^{(i)} = ∑_l F_l^{(i)} * C_l` for `i0` and
using the same relation at `i0 + 1` yields the relation for the derivatives. -/
private lemma diff_step {K : Type*} [CommRing K] {m : ℕ} (D Y : Polynomial K)
    (F Cv : Fin m → Polynomial K) (i0 : Fin m)
    (h1 : D * (Polynomial.derivative^[(i0:ℕ)]) Y
        = ∑ l, (Polynomial.derivative^[(i0:ℕ)]) (F l) * Cv l)
    (h2 : D * (Polynomial.derivative^[((i0:ℕ)+1)]) Y
        = ∑ l, (Polynomial.derivative^[((i0:ℕ)+1)]) (F l) * Cv l) :
    Polynomial.derivative D * (Polynomial.derivative^[(i0:ℕ)]) Y
      = ∑ l, (Polynomial.derivative^[(i0:ℕ)]) (F l) * Polynomial.derivative (Cv l) := by
  have hder : Polynomial.derivative ((Polynomial.derivative^[(i0:ℕ)]) Y)
      = (Polynomial.derivative^[((i0:ℕ)+1)]) Y :=
    (Function.iterate_succ_apply' Polynomial.derivative (i0:ℕ) Y).symm
  have hderF : ∀ l, Polynomial.derivative ((Polynomial.derivative^[(i0:ℕ)]) (F l))
      = (Polynomial.derivative^[((i0:ℕ)+1)]) (F l) := by
    intro l; exact (Function.iterate_succ_apply' Polynomial.derivative (i0:ℕ) (F l)).symm
  have h1' := congrArg Polynomial.derivative h1
  rw [Polynomial.derivative_mul, Polynomial.derivative_sum] at h1'
  simp only [Polynomial.derivative_mul] at h1'
  rw [hder] at h1'
  simp only [hderF] at h1'
  rw [Finset.sum_add_distrib] at h1'
  rw [← h2] at h1'
  linear_combination h1'

/-
**Univariate Wronskian criterion (characteristic 0).**

If `f : Fin n → K[X]` is linearly independent over `K` (a field of characteristic zero), then the
Wronskian determinant `det (fun i j => f_j^(i))` is a nonzero polynomial.

Proof: strong induction on `n`, contrapositive.  Given `f : Fin n → K[X]` with vanishing Wronskian
`W_n`, we produce a nontrivial linear relation.  Let `D` be the top-left `(n-1) × (n-1)` minor.
If `D = 0` we are done by the induction hypothesis (extending the relation by `0`).  Otherwise write
`A` for that minor, `b_i = f_{n-1}^{(i)}`, `C := adj(A) *ᵥ b`.  The adjugate identity
`A * adj(A) = D • 1` gives `D * f_{n-1}^{(i)} = ∑_l C_l * f_l^{(i)}` for `i < n-1`, and the identical
identity at `i = n-1` follows from `det_zero_last_row_adjugate` applied to the full matrix (whose
determinant is `0`).  Differentiating and recombining gives `D' * C_l = D * C_l'`, so each `C_l`
is a constant multiple of `D` (`wronskian_eq_zero_ratio`); substituting into the order-`0` relation
and cancelling `D ≠ 0` exhibits `f_{n-1}` as a linear combination of the previous `f_l`.
-/
theorem wronskian_linearIndependent {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (f : Fin n → Polynomial K) (h : LinearIndependent K f) :
    (Matrix.of (fun i j : Fin n => (Polynomial.derivative^[(i : ℕ)]) (f j))).det ≠ 0 := by
  change (wmat f).det ≠ 0
  suffices hmain : ∀ n, ∀ (f : Fin n → Polynomial K),
      (wmat f).det = 0 → ¬ LinearIndependent K f by
    intro hz; exact hmain n f hz h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro f hw hLI
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Matrix.det_fin_zero] at hw
      exact absurd hw one_ne_zero
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
      set W : Matrix (Fin (m+1)) (Fin (m+1)) (Polynomial K) := wmat f with hW
      set A : Matrix (Fin m) (Fin m) (Polynomial K) := W.submatrix Fin.castSucc Fin.castSucc with hA
      have hAwmat : A = wmat (fun l : Fin m => f (Fin.castSucc l)) := by
        rw [hA, hW, wmat_submatrix_castSucc]
      by_cases hAdet : A.det = 0
      · -- the leading minor is singular: apply the induction hypothesis
        have hgw : (wmat (fun l : Fin m => f (Fin.castSucc l))).det = 0 := by
          rw [← hAwmat]; exact hAdet
        have hng : ¬ LinearIndependent K (fun l : Fin m => f (Fin.castSucc l)) :=
          IH m (by omega) _ hgw
        rw [Fintype.linearIndependent_iff] at hng
        push Not at hng
        obtain ⟨c, hc0, l0, hl0⟩ := hng
        let c' : Fin (m+1) → K := Fin.lastCases 0 c
        have hc'sum : ∑ i, c' i • f i = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last, zero_smul, add_zero]
          simpa using hc0
        have hc'ne : c' (Fin.castSucc l0) ≠ 0 := by simpa [c'] using hl0
        exact hc'ne (Fintype.linearIndependent_iff.mp hLI c' hc'sum (Fin.castSucc l0))
      · -- the leading minor is invertible: Cramer + differentiation + ratio argument
        set b : Fin m → Polynomial K := fun i => W (Fin.castSucc i) (Fin.last m) with hb
        set Cv : Fin m → Polynomial K := A.adjugate *ᵥ b with hCv
        have hAC : A *ᵥ Cv = A.det • b := by
          rw [hCv, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
            Matrix.one_mulVec]
        have ha_i : ∀ i : Fin m, ∑ l, W (Fin.castSucc i) (Fin.castSucc l) * Cv l
            = A.det * W (Fin.castSucc i) (Fin.last m) := by
          intro i
          have := congrFun hAC i
          simp only [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at this
          simpa [hA, hb, Matrix.submatrix_apply] using this
        have hb_ext : ∑ l, W (Fin.last m) (Fin.castSucc l) * Cv l
            = A.det * W (Fin.last m) (Fin.last m) := by
          have h := Commons.Algebra.Matrix.det_zero_last_row_adjugate W hw
            (by simpa [hA] using hAdet)
          simpa [hA, hb, hCv] using h
        have hE : ∀ i : Fin (m+1), A.det * W i (Fin.last m)
            = ∑ l, W i (Fin.castSucc l) * Cv l := by
          intro i
          induction i using Fin.lastCases with
          | last => exact hb_ext.symm
          | cast i => exact (ha_i i).symm
        have hE' : ∀ i : Fin (m+1),
            A.det * (Polynomial.derivative^[(i:ℕ)]) (f (Fin.last m))
            = ∑ l, (Polynomial.derivative^[(i:ℕ)]) (f (Fin.castSucc l)) * Cv l := by
          intro i
          have := hE i
          simpa [hW, wmat, Matrix.of_apply] using this
        have hdiff : ∀ i0 : Fin m,
            Polynomial.derivative A.det * (Polynomial.derivative^[(i0:ℕ)]) (f (Fin.last m))
            = ∑ l, (Polynomial.derivative^[(i0:ℕ)]) (f (Fin.castSucc l))
                * Polynomial.derivative (Cv l) := by
          intro i0
          have h1 : A.det * (Polynomial.derivative^[(i0:ℕ)]) (f (Fin.last m))
              = ∑ l, (Polynomial.derivative^[(i0:ℕ)]) (f (Fin.castSucc l)) * Cv l := by
            have := hE' (Fin.castSucc i0); simpa using this
          have h2 : A.det * (Polynomial.derivative^[((i0:ℕ)+1)]) (f (Fin.last m))
              = ∑ l, (Polynomial.derivative^[((i0:ℕ)+1)]) (f (Fin.castSucc l)) * Cv l := by
            have := hE' (Fin.succ i0); simpa using this
          exact diff_step (A.det) (f (Fin.last m)) (fun l => f (Fin.castSucc l)) Cv i0 h1 h2
        let dCv : Fin m → Polynomial K := fun l => Polynomial.derivative (Cv l)
        have hAC' : A *ᵥ dCv = (Polynomial.derivative A.det) • b := by
          funext i
          have h := hdiff i
          simp only [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul]
          have hAij : ∀ j, A i j = (Polynomial.derivative^[(i:ℕ)]) (f (Fin.castSucc j)) := by
            intro j
            simp only [hA, hW, wmat, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_castSucc]
          have hbi : b i = (Polynomial.derivative^[(i:ℕ)]) (f (Fin.last m)) := by
            simp only [hb, hW, wmat, Matrix.of_apply, Fin.val_castSucc]
          simp only [hAij, hbi, dCv]
          exact h.symm
        have hAw : A *ᵥ (fun l => Polynomial.derivative A.det * Cv l - A.det * dCv l) = 0 := by
          rw [show (fun l => Polynomial.derivative A.det * Cv l - A.det * dCv l)
                = (Polynomial.derivative A.det) • Cv - A.det • dCv from by
                funext l; simp [Pi.sub_apply, Pi.smul_apply]]
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hAC, hAC']
          rw [smul_smul, smul_smul, mul_comm (Polynomial.derivative A.det) A.det, sub_self]
        have hw0 : ∀ l, Polynomial.derivative A.det * Cv l - A.det * dCv l = 0 := by
          have h2 : A.adjugate *ᵥ
              (A *ᵥ (fun l => Polynomial.derivative A.det * Cv l - A.det * dCv l)) = 0 := by
            rw [hAw, Matrix.mulVec_zero]
          rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
            at h2
          intro l
          have := congrFun h2 l
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
          exact (mul_eq_zero.mp this).resolve_left hAdet
        have hk : ∀ l, ∃ k : K, Cv l = Polynomial.C k * A.det := by
          intro l
          have hrel : Polynomial.derivative (Cv l) * A.det
              = Cv l * Polynomial.derivative A.det := by
            have h := sub_eq_zero.mp (hw0 l)
            rw [mul_comm (Polynomial.derivative A.det) (Cv l)] at h
            rw [mul_comm A.det (Polynomial.derivative (Cv l))] at h
            exact h.symm
          exact wronskian_eq_zero_ratio hAdet hrel
        choose k hk using hk
        have hY : f (Fin.last m) = ∑ l, (k l) • f (Fin.castSucc l) := by
          have h0 := hE' 0
          simp only [Fin.val_zero, Function.iterate_zero_apply] at h0
          simp only [hk] at h0
          have h0' : A.det * f (Fin.last m)
              = (∑ l, (k l) • f (Fin.castSucc l)) * A.det := by
            rw [h0, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro l _
            rw [Polynomial.smul_eq_C_mul]; ring
          rw [mul_comm (∑ l, (k l) • f (Fin.castSucc l)) A.det] at h0'
          exact mul_left_cancel₀ hAdet h0'
        let c' : Fin (m+1) → K := Fin.lastCases 1 (fun l => -(k l))
        have hc'sum : ∑ i, c' i • f i = 0 := by
          rw [Fin.sum_univ_castSucc]
          simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last, one_smul]
          have hneg : (∑ l, (-(k l)) • f (Fin.castSucc l))
              = -(∑ l, (k l) • f (Fin.castSucc l)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl; intro l _; rw [neg_smul]
          rw [hneg, ← hY]
          ring
        have hc'last : c' (Fin.last m) ≠ 0 := by
          simp only [c', Fin.lastCases_last]; exact one_ne_zero
        exact hc'last (Fintype.linearIndependent_iff.mp hLI c' hc'sum (Fin.last m))

end Commons.Algebra.Polynomial
