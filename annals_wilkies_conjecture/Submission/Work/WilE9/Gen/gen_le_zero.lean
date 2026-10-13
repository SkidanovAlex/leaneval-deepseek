import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Gen

open Classical

/-- The sublevel set `{P ≤ 0}` of a polynomial is in `Gen`, with format `N + 2` and degree
`P.totalDegree + 2`.

The witness is the projection of the zero set of `Q = P + y²` in `N + 1` variables: for fixed
`x`, the equation `P x + y² = 0` has a real solution `y` exactly when `P x ≤ 0` (take
`y = √(-P x)`).  The extra `+2` in the format is the single `proj` step, the `+2` in the degree
comes from `y²`. -/
theorem gen_le_zero {N : ℕ} (P : MvPolynomial (Fin N) ℝ) :
    WilkiesDesign.E.Gen (N + 2) (P.totalDegree + 2) N {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} := by
  -- Lift `P` to `N + 1` variables through `Fin.castSucc` and add the new squared variable.
  set Q : MvPolynomial (Fin (N + 1)) ℝ :=
    MvPolynomial.rename Fin.castSucc P + MvPolynomial.X (Fin.last N) ^ 2 with hQ
  -- Evaluation of `Q` on a point `Fin.snoc x t`.
  have hQeval : ∀ (x : Fin N → ℝ) (t : ℝ),
      MvPolynomial.eval (Fin.snoc x t) Q = MvPolynomial.eval x P + t ^ 2 := by
    intro x t
    have hcomp : Fin.snoc x t ∘ Fin.castSucc = x := by
      funext i; simp [Fin.snoc_castSucc]
    rw [hQ, MvPolynomial.eval_add, MvPolynomial.eval_rename, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, Fin.snoc_last, hcomp]
  -- Degree bound.
  have hdeg : Q.totalDegree ≤ P.totalDegree + 2 := by
    have h1 : (MvPolynomial.rename Fin.castSucc P).totalDegree ≤ P.totalDegree :=
      MvPolynomial.totalDegree_rename_le _ _
    have h2 : (MvPolynomial.X (Fin.last N) ^ 2 : MvPolynomial (Fin (N + 1)) ℝ).totalDegree = 2 :=
      MvPolynomial.totalDegree_X_pow _ _
    calc Q.totalDegree
        = (MvPolynomial.rename Fin.castSucc P
            + MvPolynomial.X (Fin.last N) ^ 2).totalDegree := by rw [hQ]
      _ ≤ max (MvPolynomial.rename Fin.castSucc P).totalDegree
            (MvPolynomial.X (Fin.last N) ^ 2).totalDegree := MvPolynomial.totalDegree_add _ _
      _ ≤ P.totalDegree + 2 := by rw [h2]; exact max_le (by omega) (by omega)
  -- The projection of the zero set of `Q` is exactly the sublevel set of `P`.
  have hset : WilkiesDesign.projLast {z : Fin (N + 1) → ℝ | MvPolynomial.eval z Q = 0}
      = {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} := by
    ext x
    simp only [WilkiesDesign.projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [hQeval] at ht
      nlinarith [sq_nonneg t]
    · intro h
      refine ⟨Real.sqrt (-(MvPolynomial.eval x P)), ?_⟩
      rw [hQeval]
      have h0 : 0 ≤ -(MvPolynomial.eval x P) := by linarith
      have hs : (Real.sqrt (-(MvPolynomial.eval x P))) ^ 2 = -(MvPolynomial.eval x P) :=
        Real.sq_sqrt h0
      linarith
  have hgen : WilkiesDesign.E.Gen (N + 2) Q.totalDegree N
      {x : Fin N → ℝ | MvPolynomial.eval x P ≤ 0} := by
    rw [← hset]
    exact WilkiesDesign.E.Gen.proj (WilkiesDesign.E.Gen.hyp (N + 1) Q)
  exact Work.WilE9.Gen.monoD hdeg hgen

end Work.WilE9.Gen
