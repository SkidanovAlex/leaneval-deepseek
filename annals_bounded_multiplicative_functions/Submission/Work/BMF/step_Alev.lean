import Mathlib
import Submission.Work.BMF.adi_descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- `1 + Dgrow k C₀ ≥ 1`. -/
theorem one_le_one_add_Dgrow (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    1 ≤ 1 + Dgrow k C₀ := by
  have := Dgrow_nonneg k C₀ hC₀
  linarith

/-- Unfolding `Alev` at level `j - 1`, with the exponent rewritten as `k + 2 - j`. -/
theorem Alev_pred_eq (k : ℕ) (C₀ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Alev k C₀ (j - 1) =
      (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) * ((k : ℝ) + 3 - (j : ℝ)) := by
  unfold Alev
  have h1 : k + 1 - (j - 1) = k + 2 - j := by omega
  have h2 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj]; norm_num
  rw [h1, h2]
  ring

/-- The one-step recursion for the sup-norm bound: if `A ≤ Alev k C₀ j` with `1 ≤ j ≤ k`, then
`A (1 + Dgrow) + 1 ≤ Alev k C₀ (j - 1)`. -/
theorem Alev_step (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    {A : ℝ} (hA : A ≤ Alev k C₀ j) :
    A * (1 + Dgrow k C₀) + 1 ≤ Alev k C₀ (j - 1) := by
  have hG1 : 1 ≤ 1 + Dgrow k C₀ := one_le_one_add_Dgrow k C₀ hC₀
  have hG0 : (0 : ℝ) ≤ 1 + Dgrow k C₀ := by linarith
  have hjcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hbase : (0 : ℝ) ≤ C₀ + (k : ℝ) + 2 := by positivity
  have hk2j : (0 : ℝ) ≤ (k : ℝ) + 2 - (j : ℝ) := by linarith
  have hkey1 : (1 : ℝ) ≤ (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) := by
    have hb1 : (1 : ℝ) ≤ C₀ + (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hp1 : (1 : ℝ) ≤ (1 + Dgrow k C₀) ^ (k + 2 - j) := one_le_pow₀ hG1
    nlinarith [hb1, hp1]
  have hja : Alev k C₀ j
      = (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1 - j) * ((k : ℝ) + 2 - (j : ℝ)) := by
    unfold Alev
    ring
  have hpow : (1 + Dgrow k C₀) ^ (k + 1 - j) * (1 + Dgrow k C₀)
      = (1 + Dgrow k C₀) ^ (k + 2 - j) := by
    rw [← pow_succ]
    congr 1
    omega
  -- Step 1: multiply `hA` by the nonnegative factor `G`.
  have hstep1 : A * (1 + Dgrow k C₀) ≤ Alev k C₀ j * (1 + Dgrow k C₀) :=
    mul_le_mul_of_nonneg_right hA hG0
  -- Rewrite `Alev k C₀ j * G` as `(C₀+k+2) * G^(k+2-j) * (k+2-j)`.
  have hstep2 : Alev k C₀ j * (1 + Dgrow k C₀)
      = (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) * ((k : ℝ) + 2 - (j : ℝ)) := by
    rw [hja]
    calc (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1 - j) * ((k : ℝ) + 2 - (j : ℝ))
            * (1 + Dgrow k C₀)
        = (C₀ + (k : ℝ) + 2) * ((1 + Dgrow k C₀) ^ (k + 1 - j) * (1 + Dgrow k C₀))
            * ((k : ℝ) + 2 - (j : ℝ)) := by ring
      _ = (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) * ((k : ℝ) + 2 - (j : ℝ)) := by
          rw [hpow]
  have hAG : A * (1 + Dgrow k C₀)
      ≤ (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) * ((k : ℝ) + 2 - (j : ℝ)) :=
    le_trans hstep1 (le_of_eq hstep2)
  -- Final assembly.
  rw [Alev_pred_eq k C₀ hj]
  have hfin : (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) * ((k : ℝ) + 3 - (j : ℝ))
      = (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) * ((k : ℝ) + 2 - (j : ℝ))
        + (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 2 - j) := by
    ring
  rw [hfin]
  linarith [hAG, hkey1]

theorem step_Alev (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    (dstep p s).A ≤ Alev p.k p.C₀ (s.j - 1) := by
  rw [dstep_A]
  obtain ⟨hjk, -, -, -, -, -, -, hA, -, -, -, -⟩ := hs
  exact Alev_step p.k p.C₀ hp.1 hj hjk hA

end Work.BMF
