import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas.Density4.sum_exp_div_le

namespace Work.LinnikAreas2

theorem far_piece_le_gen {ε C₁ L U V X : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁) (hU : 0 < U)
    (hX : 0 < X) (hU1 : 1 ≤ U) (hUV : U < V) (hVX : V ≤ X) (hcase : U ≤ L^2 * X)
    (h2 : ∀ N : ℕ, V ≤ (N:ℝ) →
      Work.LinnikAreas2.psSum U V N
        ≤ (1+ε) * (N:ℝ) / Real.log (V/U) + C₁ * (N:ℝ) / (Real.log (V/U))^2)
    (N : ℕ) :
    ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        Work.LinnikAreas2.psSum U V n
          * (Work.LinnikAreas2.phiW L U X n - Work.LinnikAreas2.phiW L U X (n+1))
      ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (Real.log (X/V) + 3) := by
  have hV1 : 1 ≤ V := le_trans hU1 hUV.le
  have hΛpos : 0 < Real.log (V/U) := by
    apply Real.log_pos
    rw [one_lt_div hU]
    exact hUV
  have hCnn : 0 ≤ (1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2 := by
    have h1 : 0 ≤ (1+ε)/Real.log (V/U) := div_nonneg (by linarith) hΛpos.le
    have h2' : 0 ≤ C₁/(Real.log (V/U))^2 := by positivity
    linarith
  have hA1 : 1 ≤ Nat.floor V + 1 := by omega
  -- Termwise bound: on the range, `A(n) = psSum U V n ≤ C n` and `k(n) ≥ 0`.
  have hterm : ∀ n ∈ Finset.Ico (Nat.floor V + 1) N,
      Work.LinnikAreas2.psSum U V n
        * (Work.LinnikAreas2.phiW L U X n
            - Work.LinnikAreas2.phiW L U X (n+1))
        ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2)
            * ((n:ℝ) * (Work.LinnikAreas2.phiW L U X n
                - Work.LinnikAreas2.phiW L U X (n+1))) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : 1 ≤ n := le_trans hA1 hn.1
    have hVn : V ≤ (n:ℝ) := by
      have hlt : V < ((Nat.floor V + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one V
      have hle : ((Nat.floor V + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      linarith
    have hps : Work.LinnikAreas2.psSum U V n
        ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ) := by
      calc Work.LinnikAreas2.psSum U V n
          ≤ (1+ε) * (n:ℝ) / Real.log (V/U)
              + C₁ * (n:ℝ) / (Real.log (V/U))^2 := h2 n hVn
        _ = ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ) := by ring
    have hk : 0 ≤ Work.LinnikAreas2.phiW L U X n
        - Work.LinnikAreas2.phiW L U X (n+1) :=
      Work.LinnikAreas2.phiW_sub_nonneg hU hX hcase hn1
    calc Work.LinnikAreas2.psSum U V n
          * (Work.LinnikAreas2.phiW L U X n
              - Work.LinnikAreas2.phiW L U X (n+1))
        ≤ (((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (n:ℝ))
            * (Work.LinnikAreas2.phiW L U X n
                - Work.LinnikAreas2.phiW L U X (n+1)) :=
          mul_le_mul_of_nonneg_right hps hk
      _ = ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2)
            * ((n:ℝ) * (Work.LinnikAreas2.phiW L U X n
                - Work.LinnikAreas2.phiW L U X (n+1))) := by ring
  -- Abel identity: `n k n = (wt n - wt (n+1)) + wt (n+1)/(n+1)`.
  have hident : ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        (n:ℝ) * (Work.LinnikAreas2.phiW L U X n
          - Work.LinnikAreas2.phiW L U X (n+1))
      = (∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
            (Work.LinnikAreas2.wt L U X n - Work.LinnikAreas2.wt L U X (n+1)))
        + ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
            Work.LinnikAreas2.wt L U X (n+1) / ((n:ℝ)+1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact Work.LinnikAreas2.phiW_sub_ident (le_trans hA1 hn.1)
  -- The telescoping difference sum is at most `wt (⌊V⌋+1) ≤ 1`.
  have hsum1 : (∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        (Work.LinnikAreas2.wt L U X n - Work.LinnikAreas2.wt L U X (n+1))) ≤ 1 := by
    have hb := Work.LinnikAreas2.sum_Ico_diff_le
      (w := Work.LinnikAreas2.wt L U X)
      (fun n => Work.LinnikAreas2.wt_nonneg hU hX hcase n)
      (Nat.floor V + 1) N
    have hwA : Work.LinnikAreas2.wt L U X (Nat.floor V + 1) ≤ 1 :=
      Work.LinnikAreas2.wt_le_one hU hX _
    linarith
  -- The shifted exponential sum is bounded by `sum_exp_div_le`.
  have hsum2 : (∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        Work.LinnikAreas2.wt L U X (n+1) / ((n:ℝ)+1))
      ≤ Real.log (X/V) + 2 := by
    have hExpBound : ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        Real.exp (-(((n:ℝ)+1))/X) / ((n:ℝ)+1) ≤ Real.log (X/V) + 2 := by
      rw [show Finset.Ico (Nat.floor V + 1) N = Finset.Icc (Nat.floor V + 1) (N-1) from by
        ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
      exact Work.LinnikAreas.Density4.sum_exp_div_le hV1 hVX (N-1)
    refine le_trans (Finset.sum_le_sum ?_) hExpBound
    intro n _
    have h := Work.LinnikAreas2.wt_le_exp (L := L) (U := U) (X := X) (n+1)
    have hcast : (((n+1 : ℕ)) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    exact div_le_div_of_nonneg_right h (by positivity)
  -- Kernel sum bound.
  have hinner : ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        (n:ℝ) * (Work.LinnikAreas2.phiW L U X n
          - Work.LinnikAreas2.phiW L U X (n+1)) ≤ Real.log (X/V) + 3 := by
    rw [hident]
    linarith
  -- Assemble.
  have hS_le : ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        Work.LinnikAreas2.psSum U V n
          * (Work.LinnikAreas2.phiW L U X n
              - Work.LinnikAreas2.phiW L U X (n+1))
      ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2)
          * ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
              (n:ℝ) * (Work.LinnikAreas2.phiW L U X n
                - Work.LinnikAreas2.phiW L U X (n+1)) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.mul_sum]
  calc ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
        Work.LinnikAreas2.psSum U V n
          * (Work.LinnikAreas2.phiW L U X n
              - Work.LinnikAreas2.phiW L U X (n+1))
      ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2)
          * ∑ n ∈ Finset.Ico (Nat.floor V + 1) N,
              (n:ℝ) * (Work.LinnikAreas2.phiW L U X n
                - Work.LinnikAreas2.phiW L U X (n+1)) := hS_le
    _ ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (Real.log (X/V) + 3) :=
        mul_le_mul_of_nonneg_left hinner hCnn

end Work.LinnikAreas2
