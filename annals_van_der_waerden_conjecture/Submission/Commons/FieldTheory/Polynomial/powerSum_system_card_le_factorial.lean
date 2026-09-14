import Mathlib
import Submission.Commons.RingTheory.Ideal.card_minimalPrimes_quotient_le_univ
import Submission.Commons.RingTheory.Ideal.card_minimalPrimes_quotient_eq
import Submission.Commons.Algebra.MvPolynomial.ncard_zeroLocus_le_card_minimalPrimes

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Commons.FieldTheory.Polynomial

open MvPolynomial

noncomputable section

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- The `j`-th equation as a polynomial over `F[Fin r]`. -/
def systemPoly (r : ℕ) (m c : Fin r → F) (j : Fin r) : MvPolynomial (Fin r) F :=
  (∑ i : Fin r, MvPolynomial.C (m i) * MvPolynomial.X i ^ ((j : ℕ) + 1)) - MvPolynomial.C (c j)

omit [IsAlgClosed F] in
theorem systemPoly_totalDegree_le (r : ℕ) (m c : Fin r → F) (j : Fin r) :
    (systemPoly r m c j).totalDegree ≤ (j : ℕ) + 1 := by
  rw [systemPoly]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    rw [Finset.sup_le_iff]
    intro i _
    have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (m i))
      ((MvPolynomial.X i : MvPolynomial (Fin r) F) ^ ((j:ℕ)+1))
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow] at h
    omega
  · rw [MvPolynomial.totalDegree_C]; omega

omit [IsAlgClosed F] in
/-- Evaluating the `j`-th system polynomial at a point. -/
theorem aeval_systemPoly (r : ℕ) (m c : Fin r → F) (x : Fin r → F) (j : Fin r) :
    MvPolynomial.aeval x (systemPoly r m c j)
      = (∑ i : Fin r, m i * (x i) ^ ((j : ℕ) + 1)) - c j := by
  rw [systemPoly, map_sub, map_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by
      rw [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Algebra.algebraMap_self_apply])
  · rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]

omit [IsAlgClosed F] in
/-- The solution set of the system is the zero locus of the system ideal. -/
theorem zeroLocus_systemPoly (r : ℕ) (m c : Fin r → F) :
    MvPolynomial.zeroLocus F (Ideal.span (Set.range (systemPoly r m c)))
      = {x : Fin r → F | ∀ j : Fin r, ∑ i : Fin r, m i * (x i) ^ ((j : ℕ) + 1) = c j} := by
  ext x
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h j
    have h' := h (systemPoly r m c j) (Ideal.subset_span ⟨j, rfl⟩)
    rw [aeval_systemPoly, sub_eq_zero] at h'
    exact h'
  · intro h p hp
    have hgen : ∀ j : Fin r, MvPolynomial.aeval x (systemPoly r m c j) = 0 := by
      intro j
      rw [aeval_systemPoly, h j, sub_self]
    have hle : Ideal.span (Set.range (systemPoly r m c)) ≤
        RingHom.ker (MvPolynomial.aeval x).toRingHom :=
      Ideal.span_le.mpr (by rintro q ⟨j, rfl⟩; exact RingHom.mem_ker.mpr (hgen j))
    exact RingHom.mem_ker.mp (hle hp)

omit [IsAlgClosed F] in
theorem fact_prod_fin (r : ℕ) : (∏ j : Fin r, ((j:ℕ)+1)) = r.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun k => k+1) r]
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    ring

theorem powerSum_system_card_le_factorial (F : Type*) [Field F] [IsAlgClosed F]
    (r : ℕ) (m c : Fin r → F)
    (hm : ∀ s : Finset (Fin r), s.Nonempty → ∑ i ∈ s, m i ≠ 0) :
    Nat.card {x : Fin r → F // ∀ j : Fin r, ∑ i : Fin r, m i * (x i) ^ ((j : ℕ) + 1) = c j}
      ≤ r.factorial := by
  classical
  have hbez : Nat.card {p : Ideal (MvPolynomial (Fin r) F) //
        p ∈ (Ideal.span (Set.range (systemPoly r m c))).minimalPrimes} ≤ r.factorial := by
    have hprod : (∏ j : Fin r, (systemPoly r m c j).totalDegree.max 1) ≤ r.factorial := by
      calc (∏ j : Fin r, (systemPoly r m c j).totalDegree.max 1)
          ≤ ∏ j : Fin r, ((j : ℕ) + 1) :=
            Finset.prod_le_prod (fun j _ => Nat.zero_le _)
              (fun j _ => max_le (systemPoly_totalDegree_le r m c j) (by omega))
        _ = r.factorial := fact_prod_fin r
    have heq := (Commons.RingTheory.Ideal.card_minimalPrimes_quotient_eq
      (Ideal.span (Set.range (systemPoly r m c)))).symm
    exact heq.le.trans ((Commons.RingTheory.Ideal.card_minimalPrimes_quotient_le_univ
      (systemPoly r m c)).trans hprod)
  have hcard : Nat.card {x : Fin r → F // ∀ j : Fin r, ∑ i : Fin r, m i * (x i) ^ ((j : ℕ) + 1) = c j}
      ≤ Nat.card {p : Ideal (MvPolynomial (Fin r) F) //
          p ∈ (Ideal.span (Set.range (systemPoly r m c))).minimalPrimes} := by
    have h1 : Nat.card {x : Fin r → F // ∀ j : Fin r, ∑ i : Fin r, m i * (x i) ^ ((j : ℕ) + 1) = c j}
        = (MvPolynomial.zeroLocus F (Ideal.span (Set.range (systemPoly r m c)))).ncard := by
      rw [zeroLocus_systemPoly, ← Nat.card_coe_set_eq]
      rfl
    rw [h1]
    exact Commons.Algebra.MvPolynomial.ncard_zeroLocus_le_card_minimalPrimes _
  exact le_trans hcard hbez

end

end Commons.FieldTheory.Polynomial
