import Mathlib
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.PA.Glue
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quadratic reaction term versus the trace-free part

For an algebraic curvature tensor `R` with scalar curvature `S` and `d = n(n-1)`,
`qPair R - 4 S/d * ricSq R = ⟪R°, Q R⟫` with `R° = R - (S/d) Iso n` the trace-free part, and this
pairing is bounded by `c |R°|² |R|`.  This is the algebraic heart of the contract `PinchingAlgebra`.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The left-hand side of conjunct 2 is the pairing of the trace-free part with `Q R`. -/
theorem qPair_sub_eq_tpair (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) :
    qPair R - 4 * scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)) * ricSq R
      = tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Q R) := by
  have hanti : ∀ i j k l : Fin n, Q R j i k l = - Q R i j k l :=
    Work.Diff.Alg.Pinch.Q_antisym_first n R hR
  have hpair : tpair n (Iso n) (Q R) = 4 * ricSq R := by
    have h1 : tpair n (Q R) (Iso n) = ∑ i, ∑ j, ∑ k, ∑ l, Q R i j k l * Iso n i j k l := rfl
    rw [tpair_comm, h1, Work.Diff.GE.rm_iso_trace (Q R) hanti, scalAlg_Q' n R hR]
    ring
  have h2 : tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Q R)
      = tpair n R (Q R) - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) * (4 * ricSq R) := by
    rw [tpair_sub_left, tpair_smul_left, hpair]
  have h3 : qPair R = tpair n R (Q R) := rfl
  rw [h2, h3]
  ring

/-- The reaction part `Q (λ • Iso n)` does not contribute to the pairing with the trace-free part. -/
theorem tpair_iso_reaction_eq_zero (n : ℕ) (hn : 2 ≤ n) (R : Curv4 n) (hR : IsAlgCurv R) :
    tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
      (Q ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) = 0 := by
  rw [Q_smul, Work.Diff.PP.Q_Iso, tpair_smul_right, tpair_smul_right,
    tpair_sub_iso_eq_zero n hn R hR]
  ring

/-- **Conjunct 2 of `PinchingAlgebra`.**  The pairing of the trace-free part with Hamilton's
reaction term is bounded by `c |R°|² |R|`. -/
theorem qPair_bound (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c)
    (hQb : ∀ A : Curv4 n, Real.sqrt (frobSq (Q A)) ≤ c * frobSq A)
    (hQbb : ∀ A B : Curv4 n,
      Real.sqrt (frobSq (Qbil n A B)) ≤ c * Real.sqrt (frobSq A) * Real.sqrt (frobSq B))
    (htp : ∀ A B : Curv4 n, |tpair n A B| ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B))
    (R : Curv4 n) (hR : IsAlgCurv R) :
    qPair R - 4 * scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)) * ricSq R
      ≤ (c * (1 + 2 * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1))) + 1)
          * frobSqTF R * Real.sqrt (frobSq R) := by
  have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := denom_pos n hn
  set a : ℝ := Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) with ha
  set b : ℝ := Real.sqrt (frobSq R) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hs : 0 ≤ Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = frobSqTF R := by
    rw [ha, Real.sq_sqrt (frobSq_nonneg _), ← frobSqTF_eq n R hR]
  have hab : a ≤ b := sqrt_frobSq_sub_iso_le n hn R hR
  have hlam : |scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))| ≤ b := abs_iso_coeff_le n hn R hR
  rw [qPair_sub_eq_tpair n R hR]
  have hQexp : Q R = Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
      + Q ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
      + (2 : ℝ) • Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
          ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) := by
    have h := Q_add_Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
      ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
    rw [show (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)
        + (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n = R from by abel] at h
    exact h
  rw [hQexp, tpair_add_right, tpair_add_right, tpair_smul_right,
    tpair_iso_reaction_eq_zero n hn R hR, add_zero]
  -- bound on the `Q R°` term
  have hA : tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) ≤ c * a ^ 2 * b := by
    have h2 : tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
        ≤ Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) * Real.sqrt (frobSq (Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) :=
      le_trans (le_abs_self _) (htp _ _)
    have h3 : Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) = a := ha
    rw [h3] at h2
    have h4 : Real.sqrt (frobSq (Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) ≤ c * frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) := hQb _
    have h6 : frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) = a ^ 2 := by
      rw [← Real.sq_sqrt (frobSq_nonneg (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)), ← ha]
    calc tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
        ≤ a * Real.sqrt (frobSq (Q (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) := h2
      _ ≤ a * (c * frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) := mul_le_mul_of_nonneg_left h4 ha0
      _ = c * a ^ 3 := by rw [h6]; ring
      _ ≤ c * a ^ 2 * b := by
          have h5 : 0 ≤ c * a ^ 2 := mul_nonneg hc (sq_nonneg a)
          nlinarith [ha0, hab, hc, h5]
  -- bound on the `Qbil` term
  have hC : 2 * tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
      ≤ 2 * (c * a ^ 2 * (b * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)))) := by
    have h2 : tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
        ≤ a * (c * a * Real.sqrt (frobSq ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) := by
      have h2a : tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
          ≤ Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) * Real.sqrt (frobSq (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) :=
        le_trans (le_abs_self _) (htp _ _)
      have h3 : Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) = a := ha
      rw [h3] at h2a
      have h3b : Real.sqrt (frobSq (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)))
          ≤ c * Real.sqrt (frobSq (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) * Real.sqrt (frobSq ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)) := hQbb _ _
      rw [h3] at h3b
      calc tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
          ≤ a * Real.sqrt (frobSq (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) := h2a
        _ ≤ a * (c * a * Real.sqrt (frobSq ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) := mul_le_mul_of_nonneg_left h3b ha0
    have h5 : Real.sqrt (frobSq ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
        = |scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))| * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
      rw [sqrt_frobSq_smul, frobSq_Iso]
    calc 2 * tpair n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) (Qbil n (R - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n) ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))
        ≤ 2 * (a * (c * a * Real.sqrt (frobSq ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n)))) := by linarith
      _ = 2 * (c * a ^ 2 * Real.sqrt (frobSq ((scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) • Iso n))) := by ring
      _ = 2 * (c * a ^ 2 * (|scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))|
            * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)))) := by rw [h5]
      _ ≤ 2 * (c * a ^ 2 * (b * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)))) := by
          have h6 : |scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))|
              * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1))
              ≤ b * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hlam hs
          have h7 : 0 ≤ 2 * (c * a ^ 2) := by positivity
          nlinarith [h6, hc, ha0, sq_nonneg a, hs, h7]
  have hfin : (c * (1 + 2 * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1))) + 1) * frobSqTF R
      * Real.sqrt (frobSq R) = c * a ^ 2 * b
        + 2 * (c * a ^ 2 * (b * Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)))) + a ^ 2 * b := by
    rw [hb, ha2]; ring
  rw [hfin]
  have hnn : 0 ≤ a ^ 2 * b := by positivity
  linarith [hA, hC, hnn]

end Work.Diff.Alg.PA
