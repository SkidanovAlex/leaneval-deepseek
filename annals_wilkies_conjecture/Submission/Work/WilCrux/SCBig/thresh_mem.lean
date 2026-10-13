/-
  WilCrux / SCBig / thresh_mem.

  The *uniform* threshold sets `threshSet k = {1/(k+1) < η ≤ 1}` (`η` the last coordinate of
  `ℝ^{a+1}`) all lie in a *single* format of `S.Ω`, with a degree bound `q.eval D` that is
  independent of `k`.

  The point is that the two defining conditions are the positivity loci

    `η - 1/(k+1) > 0`      and      `η - 1 > 0`,

  of polynomials of total degree `1`: the *coefficient* `1/(k+1)` varies with `k`, but the
  *degree* does not.  So `pos_mem` gives both in format `(a+1) + 2` and degree `3`; the second
  is complemented (format `+1`, degree unchanged), the first is raised to the same format, and
  the two are intersected (`inter₂`, format `+1`, degrees added: `3 + 3 = 6`).  The result is
  `Ω ((a+1)+4) 6 (a+1)`, i.e. `A = (a+1)+4` and `q = C 6`.

  `1 ≤ η` is obtained as the complement of `{η > 1}` rather than through the closed half-space,
  which keeps the whole construction at degree `1` before the intersect.
-/
import Mathlib
import Submission.Work.WilCrux.SliceCauchyBig
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux.SCBig

/-- A linear polynomial `X i - c` has total degree at most `1`. -/
theorem totalDegree_X_sub_C {n : ℕ} (i : Fin n) (c : ℝ) :
    (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨by rw [MvPolynomial.totalDegree_X],
    by rw [MvPolynomial.totalDegree_C]; omega⟩

theorem thresh_mem (S : WilkiesDesign.SOMin) (a : ℕ) :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (k : ℕ) (D : ℕ),
      threshSet (a := a) k ∈ S.Ω A (q.eval D) (a + 1) := by
  refine ⟨(a + 1) + 4, Polynomial.C 6, fun k D => ?_⟩
  -- The two degree-`1` polynomials whose positivity loci cut out the threshold set
  -- (`η` is `etaS`, the last coordinate of `ℝ^{a+1}`).
  set P1 : MvPolynomial (Fin (a + 1)) ℝ :=
    MvPolynomial.X (etaS (a := a)) - MvPolynomial.C (1 / ((k : ℝ) + 1)) with hP1
  set P2 : MvPolynomial (Fin (a + 1)) ℝ :=
    MvPolynomial.X (etaS (a := a)) - MvPolynomial.C 1 with hP2
  have htd : ∀ c : ℝ, (MvPolynomial.X (etaS (a := a)) -
      MvPolynomial.C c : MvPolynomial (Fin (a + 1)) ℝ).totalDegree ≤ 1 :=
    fun c => totalDegree_X_sub_C _ c
  -- Reading the two positivity loci as coordinate conditions.
  have hset1 : {x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P1} =
      {x : Fin (a + 1) → ℝ | 1 / ((k : ℝ) + 1) < x (etaS (a := a))} := by
    rw [hP1]
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_pos]
  have hset2 : {x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P2} =
      {x : Fin (a + 1) → ℝ | 1 < x (etaS (a := a))} := by
    rw [hP2]
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, sub_pos]
  have hthresh : threshSet (a := a) k =
      {x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P1} ∩
        ({x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P2})ᶜ := by
    rw [hset1, hset2]
    ext x
    simp only [threshSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
  -- `pos_mem` for the two degree-`1` polynomials: format `(a+1)+2`, degree `3`.
  have hp1 : {x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P1} ∈
      S.Ω ((a + 1) + 2) ((Polynomial.C 3).eval D) (a + 1) := by
    refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D P1) le_rfl ?_
    simp only [Polynomial.eval_C, hP1]
    have := htd (1 / ((k : ℝ) + 1))
    omega
  have hp2 : {x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P2} ∈
      S.Ω ((a + 1) + 2) ((Polynomial.C 3).eval D) (a + 1) := by
    refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D P2) le_rfl ?_
    simp only [Polynomial.eval_C, hP2]
    have := htd 1
    omega
  -- Complement the `{η > 1}` piece, raise the other to the same format, and intersect.
  have hp1' : {x : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval x P1} ∈
      S.Ω (((a + 1) + 2) + 1) ((Polynomial.C 3).eval D) (a + 1) :=
    Work.WilG1.Omega.mono hp1 (by omega) le_rfl
  have hinter := Work.WilG1.Omega.inter₂ hp1' (S.compl hp2)
  rw [hthresh]
  refine Work.WilG1.Omega.mono hinter (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  norm_num

end Work.WilCrux.SCBig
