import Mathlib
import Submission.Work.WilE8.Clear

namespace Work.WilE8.Clear

theorem clearDenom_totalDegree_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (Work.WilE8.clearDenom P).totalDegree ≤ n * P.totalDegree := by
  classical
  rw [Work.WilE8.clearDenom]
  refine MvPolynomial.totalDegree_finsetSum_le (fun a ha => ?_)
  have ha_i : ∀ i, a i ≤ P.totalDegree := fun i =>
    (Finsupp.single_eval_le_sum a (g := fun (m : ℕ) => m) rfl (fun x => Nat.zero_le x) i).trans
      (MvPolynomial.le_totalDegree ha)
  have hA : (∏ i : Fin n, (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin n ⊕ Fin n) ℝ) ^ a i).totalDegree
      ≤ ∑ i : Fin n, a i := by
    have h := MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin n))
      (fun i => (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin n ⊕ Fin n) ℝ) ^ a i)
    simpa [MvPolynomial.totalDegree_X_pow] using h
  have hB : (∏ i : Fin n, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin n) ℝ) ^ (P.totalDegree - a i)).totalDegree
      ≤ ∑ i : Fin n, (P.totalDegree - a i) := by
    have h := MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin n))
      (fun i => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin n) ℝ) ^ (P.totalDegree - a i))
    simpa [MvPolynomial.totalDegree_X_pow] using h
  have hsum : (∑ i : Fin n, a i) + (∑ i : Fin n, (P.totalDegree - a i)) = n * P.totalDegree := by
    have h1 : (∑ i : Fin n, (a i + (P.totalDegree - a i))) = ∑ _i : Fin n, P.totalDegree :=
      Finset.sum_congr rfl (fun i _ => Nat.add_sub_cancel' (ha_i i))
    rw [Finset.sum_add_distrib] at h1
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp
  calc
    (MvPolynomial.C (P.coeff a) * (∏ i : Fin n, MvPolynomial.X (Sum.inl i) ^ a i)
        * ∏ i : Fin n, MvPolynomial.X (Sum.inr i) ^ (P.totalDegree - a i)).totalDegree
        ≤ (MvPolynomial.C (P.coeff a) * (∏ i : Fin n, MvPolynomial.X (Sum.inl i) ^ a i)).totalDegree
            + (∏ i : Fin n, MvPolynomial.X (Sum.inr i) ^ (P.totalDegree - a i)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ ((MvPolynomial.C (P.coeff a)).totalDegree
            + (∏ i : Fin n, MvPolynomial.X (Sum.inl i) ^ a i).totalDegree)
            + (∏ i : Fin n, MvPolynomial.X (Sum.inr i) ^ (P.totalDegree - a i)).totalDegree := by
          gcongr
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ (∑ i : Fin n, a i) + (∑ i : Fin n, (P.totalDegree - a i)) := by
          rw [MvPolynomial.totalDegree_C, zero_add]
          exact add_le_add hA hB
    _ = n * P.totalDegree := hsum

end Work.WilE8.Clear
