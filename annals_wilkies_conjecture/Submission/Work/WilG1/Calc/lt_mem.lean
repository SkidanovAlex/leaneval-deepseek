import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Calc

/-- The strict coordinate inequality `x i < x j` is `Ω`-definable.

Key identity: for reals, `x i < x j ↔ ∃ t, (x j - x i) * t ^ 2 = 1`, i.e. the set is the
projection (dropping the last coordinate `t`) of the hypersurface cut out by the degree-`3`
polynomial `(X j - X i) * X_{last} ^ 2 - 1`.  The projection raises the format by one, so the
result lands in format `n + 2`, and we raise it to `n + 3` by monotonicity. -/
theorem lt_mem {S : WilkiesDesign.SOMin} {n : ℕ} (D : ℕ) (i j : Fin n) :
    {x : Fin n → ℝ | x i < x j} ∈ S.Ω (n + 3) ((Polynomial.C 3).eval D) n := by
  set P : MvPolynomial (Fin (n+1)) ℝ :=
    (MvPolynomial.X (Fin.castSucc j) - MvPolynomial.X (Fin.castSucc i)) *
      MvPolynomial.X (Fin.last n) ^ 2 - 1 with hPdef
  -- `P` has total degree at most `3`.
  have htd : P.totalDegree ≤ 3 := by
    rw [hPdef]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.X (Fin.castSucc j) - MvPolynomial.X (Fin.castSucc i) :
        MvPolynomial (Fin (n+1)) ℝ).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        rw [max_le_iff]
        exact ⟨by rw [MvPolynomial.totalDegree_X], by rw [MvPolynomial.totalDegree_X]⟩
      have h2 : (MvPolynomial.X (Fin.last n) ^ 2 :
        MvPolynomial (Fin (n+1)) ℝ).totalDegree ≤ 2 := by
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        rw [MvPolynomial.totalDegree_X]
      linarith
    · rw [MvPolynomial.totalDegree_one]; norm_num
  -- The zero set of `P` in `ℝ^{n+1}` is an `Ω`-set.
  have h0 : {z : Fin (n+1) → ℝ | MvPolynomial.eval z P = 0} ∈
      S.Ω (n+1) ((Polynomial.C P.totalDegree).eval D) (n+1) :=
    Work.WilG1.Omega.hyp_mem (S := S) D P
  have h1 : {z : Fin (n+1) → ℝ | MvPolynomial.eval z P = 0} ∈
      S.Ω (n+1) ((Polynomial.C 3).eval D) (n+1) :=
    Work.WilG1.Omega.mono h0 le_rfl (by simpa [Polynomial.eval_C] using htd)
  -- Project out the last coordinate.
  have h2 : WilkiesDesign.projLast {z : Fin (n+1) → ℝ | MvPolynomial.eval z P = 0} ∈
      S.Ω (n+2) ((Polynomial.C 3).eval D) n :=
    Work.WilG1.Omega.projLast_mem (S := S) (n := n) (b := Polynomial.C 3) (D := D) h1
  -- Raise the format to `n + 3`.
  have h3 : WilkiesDesign.projLast {z : Fin (n+1) → ℝ | MvPolynomial.eval z P = 0} ∈
      S.Ω (n+3) ((Polynomial.C 3).eval D) n :=
    Work.WilG1.Omega.mono h2 (by omega) le_rfl
  -- The projection is exactly `{x | x i < x j}`.
  have hset : WilkiesDesign.projLast {z : Fin (n+1) → ℝ | MvPolynomial.eval z P = 0}
      = {x : Fin n → ℝ | x i < x j} := by
    ext x
    simp only [hPdef, WilkiesDesign.projLast, Set.mem_ofPred_eq, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X, Fin.snoc_castSucc,
      Fin.snoc_last, map_one]
    constructor
    · rintro ⟨t, ht⟩
      have key : (x j - x i) * t ^ 2 = 1 := by linarith
      have ht2 : 0 < t ^ 2 := by
        rcases lt_or_eq_of_le (sq_nonneg t) with h | h
        · exact h
        · rw [← h] at key; norm_num at key
      have hc : 0 < x j - x i := by
        by_contra hcon
        have hcon' : x j - x i ≤ 0 := le_of_not_gt hcon
        have : (x j - x i) * t ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hcon' (sq_nonneg t)
        linarith
      linarith
    · intro hlt
      have hd : 0 < x j - x i := by linarith
      refine ⟨(Real.sqrt (x j - x i))⁻¹, ?_⟩
      have hs : (Real.sqrt (x j - x i)) ^ 2 = x j - x i := Real.sq_sqrt (le_of_lt hd)
      have hne : (x j - x i) ≠ 0 := ne_of_gt hd
      have key : (x j - x i) * ((Real.sqrt (x j - x i))⁻¹) ^ 2 = 1 := by
        rw [inv_pow, hs, mul_inv_cancel₀ hne]
      rw [key]; norm_num
  rw [hset] at h3
  exact h3

end Work.WilG1.Calc
