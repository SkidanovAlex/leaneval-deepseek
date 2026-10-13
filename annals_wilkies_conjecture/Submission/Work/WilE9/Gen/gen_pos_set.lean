/-
  WilE9 / `Gen` — a strict polynomial inequality is in the filtration, at format `n + 2`.

  The strict inequality `0 < P x` is equivalent to `∃ t, t ^ 2 * P x = 1` (take
  `t = 1 / √(P x)` in one direction; and `t ^ 2 * P x = 1` forces `t ≠ 0`, hence
  `P x = 1 / t ^ 2 > 0`, in the other).  So `{x | 0 < P x}` is the projection along the last
  coordinate of the hypersurface `t ^ 2 * P - 1 = 0` in `ℝ^{n + 1}`.  The defining polynomial
  `X (last n) ^ 2 * rename Fin.castSucc P - C 1` has total degree `≤ P.totalDegree + 2`, and
  `Gen.hyp` gives its zero set at format `n + 1`; `Gen.proj` then produces the inequality at
  format `(n + 1) + 1 = n + 2`.

  This is the format bookkeeping that the E9 interior/closure assembly needs: the
  `ε > 0`-atoms of `ballPoly` must be available at format `variables + 2`, so that
  intersecting the `n + 1` of them (`Gen.inter`, one format) stays inside a constant budget.
-/
import Mathlib
import Submission.Work.WilE9.Gen.gen_interior_defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Topology
namespace Work.WilE9.Gen
open WilkiesDesign WilkiesDesign.E

/-- A strict polynomial inequality is in `Gen`, at format `n + 2` and degree `P.totalDegree + 2`:
`{x | 0 < P x}` is the projection along the last coordinate of the quadric
`t ^ 2 * P - 1 = 0` in `ℝ^{n+1}`. -/
theorem gen_pos_mpoly_fmt {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    WilkiesDesign.E.Gen (n + 2) (P.totalDegree + 2) n
      {x : Fin n → ℝ | 0 < MvPolynomial.eval x P} := by
  let Q : MvPolynomial (Fin (n + 1)) ℝ :=
    MvPolynomial.X (Fin.last n) ^ 2 * MvPolynomial.rename Fin.castSucc P - MvPolynomial.C 1
  have hA : Gen (n + 1) Q.totalDegree (n + 1)
      {z : Fin (n + 1) → ℝ | MvPolynomial.eval z Q = 0} := Gen.hyp (n + 1) Q
  have hproj : Gen ((n + 1) + 1) Q.totalDegree n
      (projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z Q = 0}) := Gen.proj hA
  have hval : ∀ (x : Fin n → ℝ) (t : ℝ),
      MvPolynomial.eval (Fin.snoc x t) Q = t ^ 2 * MvPolynomial.eval x P - 1 := by
    intro x t
    simp only [Q, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_rename, MvPolynomial.eval_X, MvPolynomial.eval_C, Fin.snoc_last,
      Fin.snoc_comp_castSucc]
  have hset : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z Q = 0} =
      {x : Fin n → ℝ | 0 < MvPolynomial.eval x P} := by
    ext x
    show (∃ t : ℝ, MvPolynomial.eval (Fin.snoc x t) Q = 0) ↔ 0 < MvPolynomial.eval x P
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
      (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ)
      (MvPolynomial.rename Fin.castSucc P)
    have h2 : (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree = 2 :=
      MvPolynomial.totalDegree_X_pow _ _
    have h3 : (MvPolynomial.rename Fin.castSucc P).totalDegree ≤ P.totalDegree :=
      MvPolynomial.totalDegree_rename_le _ _
    have h4 := MvPolynomial.totalDegree_sub_C_le
      (MvPolynomial.X (Fin.last n) ^ 2 * MvPolynomial.rename Fin.castSucc P) (1 : ℝ)
    show (MvPolynomial.X (Fin.last n) ^ 2 * MvPolynomial.rename Fin.castSucc P
      - MvPolynomial.C 1 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ P.totalDegree + 2
    omega
  exact Gen.monoF (by omega) (Gen.monoD hdeg hproj)

/-- **A strict polynomial inequality is in `Gen`**, at format `m + 2`; the degree bound may be
taken to be `P.totalDegree + 2`. -/
theorem gen_pos_set {m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    ∃ b : ℕ, WilkiesDesign.E.Gen (m + 2) b m {z : Fin m → ℝ | 0 < MvPolynomial.eval z P} :=
  ⟨P.totalDegree + 2, gen_pos_mpoly_fmt P⟩

end Work.WilE9.Gen
