import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Calc

/-- `{x | x i ≤ x j}` is an `Ω`-set.  The half-space is the projection of the hypersurface
`t ^ 2 = x j - x i` (a polynomial of total degree `2`) in one extra variable: every
nonnegative real is a square.  Format `n + 2` from the projection, degree `2`; both are
weakened to the stated bounds `n + 4` and `4`. -/
theorem le_mem {S : WilkiesDesign.SOMin} {n : ℕ} (D : ℕ) (i j : Fin n) :
    {x : Fin n → ℝ | x i ≤ x j} ∈ S.Ω (n + 4) ((Polynomial.C 4).eval D) n := by
  -- The defining polynomial of the hypersurface `t ^ 2 = x j - x i` in `Fin (n+1) → ℝ`,
  -- where the extra (last) coordinate is `t`.
  set Q : MvPolynomial (Fin (n + 1)) ℝ :=
    MvPolynomial.X (Fin.last n) ^ 2 -
      (MvPolynomial.X (Fin.castSucc j) - MvPolynomial.X (Fin.castSucc i))
  have hQ : Q = MvPolynomial.X (Fin.last n) ^ 2 -
      (MvPolynomial.X (Fin.castSucc j) - MvPolynomial.X (Fin.castSucc i) :
        MvPolynomial (Fin (n + 1)) ℝ) := rfl
  -- `Q` has total degree at most `2`.
  have h1 : (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 2 := by
    simp [MvPolynomial.totalDegree_X_pow]
  have h2 : (MvPolynomial.X (Fin.castSucc j) - MvPolynomial.X (Fin.castSucc i) :
      MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  have htd : Q.totalDegree ≤ 2 := by
    rw [hQ]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨h1, le_trans h2 (by norm_num)⟩
  -- The zero set of `Q` in coordinates.
  have hset : {w : Fin (n + 1) → ℝ | MvPolynomial.eval w Q = 0} =
      {w : Fin (n + 1) → ℝ |
        w (Fin.last n) ^ 2 = w (Fin.castSucc j) - w (Fin.castSucc i)} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    rw [hQ]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  have hC2 : (Polynomial.C 2 : Polynomial ℕ).eval D = 2 := by simp
  have hC4 : (Polynomial.C 4 : Polynomial ℕ).eval D = 4 := by simp
  -- The hypersurface is an `Ω`-set of format `n + 1` and degree `Q.totalDegree ≤ 2`.
  have hB : {w : Fin (n + 1) → ℝ |
      w (Fin.last n) ^ 2 = w (Fin.castSucc j) - w (Fin.castSucc i)} ∈
      S.Ω (n + 1) ((Polynomial.C 2 : Polynomial ℕ).eval D) (n + 1) := by
    have h := S.hyp (n + 1) Q
    rw [hset] at h
    rw [hC2]
    exact Work.WilG1.Omega.mono h le_rfl htd
  -- Projecting out the extra coordinate turns it into `{x | x i ≤ x j}`.
  have hprojset : WilkiesDesign.projLast {w : Fin (n + 1) → ℝ |
        w (Fin.last n) ^ 2 = w (Fin.castSucc j) - w (Fin.castSucc i)} =
      {x : Fin n → ℝ | x i ≤ x j} := by
    ext x
    simp only [WilkiesDesign.projLast, Set.mem_ofPred_eq, Fin.snoc_last, Fin.snoc_castSucc]
    constructor
    · rintro ⟨t, ht⟩
      linarith [sq_nonneg t]
    · intro h
      exact ⟨Real.sqrt (x j - x i), Real.sq_sqrt (by linarith)⟩
  -- Projection gives format `n + 2`, weakened to `n + 4` and degree `4`.
  have hmono : WilkiesDesign.projLast {w : Fin (n + 1) → ℝ |
        w (Fin.last n) ^ 2 = w (Fin.castSucc j) - w (Fin.castSucc i)} ∈
      S.Ω (n + 4) ((Polynomial.C 4 : Polynomial ℕ).eval D) n :=
    Work.WilG1.Omega.mono (S.proj hB) (by omega) (by rw [hC2, hC4]; norm_num)
  rw [hprojset] at hmono
  exact hmono

end Work.WilG1.Calc
