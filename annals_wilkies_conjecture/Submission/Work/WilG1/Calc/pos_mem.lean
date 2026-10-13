import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Calc

/-- The positivity set of a polynomial is `Ω`-definable.

Key identity: for reals, `0 < P x ↔ ∃ t, t ^ 2 * P x = 1`, i.e. the set is the projection
(dropping the last coordinate `t`) of the hypersurface cut out by the degree-`(deg P + 2)`
polynomial `X_{last} ^ 2 * (rename castSucc P) - 1`.  The projection raises the format by one,
so the result lands in format `m + 2` with degree `P.totalDegree + 2`, exactly the stated
bounds. -/
theorem pos_mem {S : WilkiesDesign.SOMin} {m : ℕ} (D : ℕ) (P : MvPolynomial (Fin m) ℝ) :
    {x : Fin m → ℝ | 0 < MvPolynomial.eval x P} ∈
      S.Ω (m + 2) ((Polynomial.C (P.totalDegree + 2)).eval D) m := by
  -- The extra variable `t` is the last coordinate; `P` acts on the first `m` coordinates.
  set Q : MvPolynomial (Fin (m+1)) ℝ :=
    MvPolynomial.X (Fin.last m) ^ 2 * MvPolynomial.rename Fin.castSucc P - 1 with hQdef
  -- `Q` has total degree at most `P.totalDegree + 2`.
  have htd : Q.totalDegree ≤ P.totalDegree + 2 := by
    rw [hQdef]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.rename Fin.castSucc P :
          MvPolynomial (Fin (m+1)) ℝ).totalDegree ≤ P.totalDegree :=
        MvPolynomial.totalDegree_rename_le _ _
      have h2 : (MvPolynomial.X (Fin.last m) ^ 2 :
          MvPolynomial (Fin (m+1)) ℝ).totalDegree ≤ 2 := by
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        rw [MvPolynomial.totalDegree_X]
      linarith
    · rw [MvPolynomial.totalDegree_one]; omega
  -- The zero set of `Q` is an `Ω`-set of format `m + 1`.
  have h0 : {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0} ∈
      S.Ω (m+1) ((Polynomial.C Q.totalDegree).eval D) (m+1) :=
    Work.WilG1.Omega.hyp_mem (S := S) D Q
  have h1 : {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0} ∈
      S.Ω (m+1) ((Polynomial.C (P.totalDegree + 2)).eval D) (m+1) :=
    Work.WilG1.Omega.mono h0 le_rfl (by simpa [Polynomial.eval_C] using htd)
  -- Project out the extra coordinate: format `m + 2`.
  have h2 : WilkiesDesign.projLast {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0} ∈
      S.Ω (m+2) ((Polynomial.C (P.totalDegree + 2)).eval D) m :=
    Work.WilG1.Omega.projLast_mem (S := S) (n := m)
      (b := Polynomial.C (P.totalDegree + 2)) (D := D) h1
  -- The projection is exactly `{x | 0 < P x}`.
  have hset : WilkiesDesign.projLast {z : Fin (m+1) → ℝ | MvPolynomial.eval z Q = 0}
      = {x : Fin m → ℝ | 0 < MvPolynomial.eval x P} := by
    ext x
    simp only [hQdef, WilkiesDesign.projLast, Set.mem_ofPred_eq, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_rename,
      Fin.snoc_last, map_one]
    have hev : ∀ t : ℝ,
        MvPolynomial.eval (Fin.snoc x t ∘ Fin.castSucc) P = MvPolynomial.eval x P := by
      intro t
      have hfun : (Fin.snoc x t ∘ Fin.castSucc) = x := by
        funext i
        simp [Function.comp_apply, Fin.snoc_castSucc]
      rw [hfun]
    simp only [hev]
    constructor
    · rintro ⟨t, ht⟩
      nlinarith [sq_nonneg t]
    · intro h
      refine ⟨(Real.sqrt (MvPolynomial.eval x P))⁻¹, ?_⟩
      have hs : (Real.sqrt (MvPolynomial.eval x P)) ^ 2 = MvPolynomial.eval x P :=
        Real.sq_sqrt (le_of_lt h)
      have hne : MvPolynomial.eval x P ≠ 0 := ne_of_gt h
      rw [inv_pow, hs, inv_mul_cancel₀ hne]
      norm_num
  rw [hset] at h2
  exact h2

end Work.WilG1.Calc
