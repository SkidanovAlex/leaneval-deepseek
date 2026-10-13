import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1.Calc

open WilkiesDesign

/-!
# The sup-ball `{z : |z i| < |z (last n)|}` is an `Ω`-set

We show that `B = {z : Fin (n+1) → ℝ | ∀ i : Fin n, z (castSucc i)^2 < z (last n)^2}` lies in
`S.Ω (n+4) (4*n) (n+1)` for every sharply o-minimal structure `S` and every degree bound `D`.

The set is the intersection of the `n` sets `B_i = {z | z_i^2 < z_{n}^2}`.  Each `B_i` is the
projection (drop the last, fresh, coordinate `t`) of the hypersurface
`t^2 (z_n^2 - z_i^2) - 1 = 0` in `ℝ^{n+2}`: over `ℝ` the equation `t^2 a = 1` is solvable in `t`
iff `a > 0`.  That hypersurface has total degree `4`, hence lives in `Ω (n+2) 4 (n+2)` by the
axiom `hyp`; projecting costs one format (giving `Ω (n+3) 4 (n+1)`), and intersecting the `n`
pieces costs one more format and adds the degrees (`4 + ⋯ + 4 = 4n`), giving
`Ω (n+4) (4n) (n+1)`.
-/

/-- Over `ℝ`, the equation `t ^ 2 * a = 1` has a solution `t` iff `a > 0`. -/
theorem sq_mul_eq_one_iff_pos {a : ℝ} : (∃ t : ℝ, t ^ 2 * a = 1) ↔ 0 < a := by
  constructor
  · rintro ⟨t, ht⟩
    nlinarith [sq_nonneg t, sq_nonneg a]
  · intro ha
    refine ⟨Real.sqrt a⁻¹, ?_⟩
    rw [Real.sq_sqrt (by positivity), inv_mul_cancel₀ (ne_of_gt ha)]

/-- The hypersurface `t^2 (z_n^2 - z_i^2) = 1` in `ℝ^{n+2}`, with coordinates `z` on
`Fin (n+1)` (embedded by `castSucc`) and `t` the last coordinate. -/
def supBallPoly {n : ℕ} (i : Fin n) : MvPolynomial (Fin (n + 1 + 1)) ℝ :=
  MvPolynomial.X (Fin.last (n + 1)) ^ 2 *
    ((MvPolynomial.X (Fin.castSucc (Fin.last n)) : MvPolynomial (Fin (n + 1 + 1)) ℝ) ^ 2 -
      (MvPolynomial.X (Fin.castSucc (Fin.castSucc i))) ^ 2) - 1

/-- `supBallPoly i` has total degree at most `4`. -/
theorem supBallPoly_totalDegree_le {n : ℕ} (i : Fin n) :
    (supBallPoly i).totalDegree ≤ 4 := by
  have hX2 : ∀ j : Fin (n + 1 + 1),
      (MvPolynomial.X j ^ 2 : MvPolynomial (Fin (n + 1 + 1)) ℝ).totalDegree ≤ 2 := by
    intro j
    calc (MvPolynomial.X j ^ 2 : MvPolynomial (Fin (n + 1 + 1)) ℝ).totalDegree
        ≤ 2 * (MvPolynomial.X j : MvPolynomial (Fin (n + 1 + 1)) ℝ).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
      _ = 2 := by simp [MvPolynomial.totalDegree_X]
  have h1 : ((MvPolynomial.X (Fin.last (n + 1)) : MvPolynomial (Fin (n + 1 + 1)) ℝ) ^ 2 *
      ((MvPolynomial.X (Fin.castSucc (Fin.last n)) : MvPolynomial (Fin (n + 1 + 1)) ℝ) ^ 2 -
        (MvPolynomial.X (Fin.castSucc (Fin.castSucc i))) ^ 2)).totalDegree ≤ 4 :=
    calc _ ≤ (MvPolynomial.X (Fin.last (n + 1)) ^ 2 :
                MvPolynomial (Fin (n + 1 + 1)) ℝ).totalDegree +
              ((MvPolynomial.X (Fin.castSucc (Fin.last n)) :
                  MvPolynomial (Fin (n + 1 + 1)) ℝ) ^ 2 -
                (MvPolynomial.X (Fin.castSucc (Fin.castSucc i))) ^ 2).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 + 2 := add_le_add (hX2 _) (by
          refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
          rw [max_le_iff]; exact ⟨hX2 _, hX2 _⟩)
      _ = 4 := by norm_num
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨h1, by rw [MvPolynomial.totalDegree_one]; norm_num⟩

/-- Projecting the hypersurface `supBallPoly i` onto the `z`-coordinates gives the "one
coordinate strictly smaller in absolute value" set `B_i`. -/
theorem projLast_supBallPoly {n : ℕ} (i : Fin n) :
    projLast {w : Fin (n + 1 + 1) → ℝ | MvPolynomial.eval w (supBallPoly i) = 0}
      = {z : Fin (n + 1) → ℝ | z (Fin.castSucc i) ^ 2 < z (Fin.last n) ^ 2} := by
  ext z
  simp only [projLast, Set.mem_ofPred_eq]
  have hev : ∀ t : ℝ, MvPolynomial.eval (Fin.snoc z t) (supBallPoly i)
      = t ^ 2 * (z (Fin.last n) ^ 2 - z (Fin.castSucc i) ^ 2) - 1 := by
    intro t
    simp [supBallPoly, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨t, ht⟩
    rw [hev t] at ht
    have h2 : t ^ 2 * (z (Fin.last n) ^ 2 - z (Fin.castSucc i) ^ 2) = 1 := by linarith
    have ha : 0 < z (Fin.last n) ^ 2 - z (Fin.castSucc i) ^ 2 :=
      sq_mul_eq_one_iff_pos.mp ⟨t, h2⟩
    linarith
  · intro hz
    have ha : 0 < z (Fin.last n) ^ 2 - z (Fin.castSucc i) ^ 2 := by linarith
    obtain ⟨t, ht⟩ := sq_mul_eq_one_iff_pos.mpr ha
    exact ⟨t, by rw [hev t, ht]; ring⟩

theorem supBall_mem {S : WilkiesDesign.SOMin} {n : ℕ} (D : ℕ) :
    {z : Fin (n + 1) → ℝ | ∀ i : Fin n, z (Fin.castSucc i) ^ 2 < z (Fin.last n) ^ 2} ∈
      S.Ω (n + 4) ((Polynomial.C (4 * n)).eval D) (n + 1) := by
  -- Each single-coordinate piece `B_i` lies in `Ω (n+3) 4 (n+1)`.
  have hA : ∀ i : Fin n,
      {z : Fin (n + 1) → ℝ | z (Fin.castSucc i) ^ 2 < z (Fin.last n) ^ 2} ∈
        S.Ω (n + 3) 4 (n + 1) := by
    intro i
    have hZ : projLast {w : Fin (n + 1 + 1) → ℝ | MvPolynomial.eval w (supBallPoly i) = 0} ∈
        S.Ω ((n + 1 + 1) + 1) 4 (n + 1) := by
      refine S.proj ?_
      exact Omega.mono (S.hyp (n + 1 + 1) (supBallPoly i)) le_rfl (supBallPoly_totalDegree_le i)
    rw [projLast_supBallPoly i] at hZ
    have hF : ((n + 1 + 1) + 1) = n + 3 := by omega
    rwa [hF] at hZ
  -- Intersecting the `n` pieces: one more format, degrees add up to `4 * n`.
  have hinter := S.inter (F := n + 3) (n := n + 1) (k := n)
      (D := fun _ : Fin n => 4)
      (A := fun i : Fin n =>
        {z : Fin (n + 1) → ℝ | z (Fin.castSucc i) ^ 2 < z (Fin.last n) ^ 2}) hA
  rw [Set.iInter_ofPred] at hinter
  have hF : ((n + 3) + 1) = n + 4 := by omega
  have hD : (∑ i : Fin n, (4 : ℕ)) = 4 * n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  rw [hF, hD] at hinter
  rw [Polynomial.eval_C]
  exact hinter

end Work.WilG1.Calc
