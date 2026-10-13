import Mathlib
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Topology
namespace Work.WilE9.Gen
open WilkiesDesign WilkiesDesign.E

/-!
  `gen_pos_mpoly` — a strict polynomial inequality is in the FD-filtration `Gen`.

  The strict inequality `0 < P x` is equivalent to `∃ t, t ^ 2 * P x = 1` (take
  `t = 1 / √(P x)` in one direction, and note that `t ^ 2 * P x = 1` forces `t ≠ 0`
  and hence `P x = 1 / t ^ 2 > 0` in the other).  So `{x | 0 < P x}` is the projection
  along the last coordinate of the hypersurface `t ^ 2 * P - 1 = 0` in `ℝ^{N + 1}`.

  The defining polynomial `X (last N) ^ 2 * rename Fin.castSucc P - C 1` has
  total degree `≤ P.totalDegree + 2`, and `Gen.hyp` gives its zero set at format
  `N + 1`; `Gen.proj` then produces the inequality at format `(N + 1) + 1 ≤ N + 3`.
-/

/-- A strict polynomial inequality `0 < P` is in `Gen`, at constant format and degree one
polynomial degree plus two. -/
theorem gen_pos_mpoly {N : ℕ} (P : MvPolynomial (Fin N) ℝ) :
    WilkiesDesign.E.Gen (N + 3) (P.totalDegree + 2) N {x : Fin N → ℝ | 0 < MvPolynomial.eval x P} := by
  let Q : MvPolynomial (Fin (N + 1)) ℝ :=
    MvPolynomial.X (Fin.last N) ^ 2 * MvPolynomial.rename Fin.castSucc P - MvPolynomial.C 1
  have hA : Gen (N + 1) Q.totalDegree (N + 1)
      {z : Fin (N + 1) → ℝ | MvPolynomial.eval z Q = 0} := Gen.hyp (N + 1) Q
  have hproj : Gen ((N + 1) + 1) Q.totalDegree N
      (projLast {z : Fin (N + 1) → ℝ | MvPolynomial.eval z Q = 0}) := Gen.proj hA
  have hval : ∀ (x : Fin N → ℝ) (t : ℝ),
      MvPolynomial.eval (Fin.snoc x t) Q = t ^ 2 * MvPolynomial.eval x P - 1 := by
    intro x t
    simp only [Q, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_rename, MvPolynomial.eval_X, MvPolynomial.eval_C, Fin.snoc_last,
      Fin.snoc_comp_castSucc]
  have hset : projLast {z : Fin (N + 1) → ℝ | MvPolynomial.eval z Q = 0} =
      {x : Fin N → ℝ | 0 < MvPolynomial.eval x P} := by
    ext x
    simp only [projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [hval] at ht
      have h1 : t ^ 2 * MvPolynomial.eval x P = 1 := by linarith
      have ht0 : t ≠ 0 := by
        intro h0
        rw [h0] at h1
        simp at h1
      have ht2 : 0 < t ^ 2 := pow_pos (abs_pos.mpr ht0) 2 |> fun h => by rwa [sq_abs] at h
      have he : MvPolynomial.eval x P = 1 / t ^ 2 := by
        rw [eq_div_iff (ne_of_gt ht2)]
        linarith
      rw [he]
      exact div_pos one_pos ht2
    · intro hx
      refine ⟨1 / Real.sqrt (MvPolynomial.eval x P), ?_⟩
      rw [hval]
      have hsq : Real.sqrt (MvPolynomial.eval x P) ^ 2 = MvPolynomial.eval x P :=
        Real.sq_sqrt hx.le
      rw [div_pow, one_pow, hsq, one_div, inv_mul_cancel₀ (ne_of_gt hx), sub_self]
  rw [hset] at hproj
  have hdeg : Q.totalDegree ≤ P.totalDegree + 2 := by
    have h1 := MvPolynomial.totalDegree_mul
      (MvPolynomial.X (Fin.last N) ^ 2 : MvPolynomial (Fin (N + 1)) ℝ)
      (MvPolynomial.rename Fin.castSucc P)
    have h2 : (MvPolynomial.X (Fin.last N) ^ 2 : MvPolynomial (Fin (N + 1)) ℝ).totalDegree = 2 :=
      MvPolynomial.totalDegree_X_pow _ _
    have h3 : (MvPolynomial.rename Fin.castSucc P).totalDegree ≤ P.totalDegree :=
      MvPolynomial.totalDegree_rename_le _ _
    have h4 := MvPolynomial.totalDegree_sub_C_le
      (MvPolynomial.X (Fin.last N) ^ 2 * MvPolynomial.rename Fin.castSucc P) (1 : ℝ)
    show (MvPolynomial.X (Fin.last N) ^ 2 * MvPolynomial.rename Fin.castSucc P
      - MvPolynomial.C 1 : MvPolynomial (Fin (N + 1)) ℝ).totalDegree ≤ P.totalDegree + 2
    omega
  exact Gen.monoF (by omega) (Gen.monoD hdeg hproj)

end Work.WilE9.Gen
