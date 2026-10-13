/-
# `Transfer/CSQ_succ.lean` — Cauchy–Schwarz at level `n+1` from level `n`

The transfer of the level-4 coercivity of the clean operator `𝓛̂` to the paper's operator
`𝓛_Γ^T` runs the slot-by-slot argument of `Transfer/stepT.lean`.  The pair bounds it
consumes are the finite-order Cauchy–Schwarz statements `Transfer.CSQ`: at level `n`,

  `|IP X Y| ≤ CC |X|_{ℋⁿ} |Y|_{ℋⁿ}`  for `X, Y` in `C^n(Qd)` and in `ℋⁿ`,

and the levels are climbed by the paper's inner-product step
`HkIPStep c₁ c₂ IP = IP + c₁·IP(D_θ·,D_θ·) + c₂·IP(D_z·,D_z·)`.

This file proves the **induction step of that pair bound**: the three pairings occurring in
`HkIPStep c₁ c₂ IP X Y` are each bounded by `CC |X|_{ℋ^{n+1}} |Y|_{ℋ^{n+1}}`, since

  `|X|_{ℋⁿ}`, `|D_θX|_{ℋⁿ}`, `|D_zX|_{ℋⁿ} ≤ |X|_{ℋ^{n+1}}`

(the first by monotonicity of `ℋ^k` in `k`, the second and third because the `ℋⁿ`-integrand
of `D_θX` / `D_zX` is dominated by the `ℋ^{n+1}`-integrand of `X`).  Because the classes
here are the *finite-order* ones, the membership descent is
`Transfer/HkMem_descent_Q0Sm.lean` and the `D_z`-comparison is
`Transfer/HkSq_Dz_le_Q0Sm.lean`; the `D_θ`-comparison needs no smoothness at all
(`Work.FTS.CoercivityStep.Norm.HkSq_Dth_le`).

The constant is `3·max 1 (max c₁ c₂)`: the three terms contribute `1`, `c₁`, `c₂` times
`CC |X| |Y|`, and `1 + c₁ + c₂ ≤ 3 max 1 (max c₁ c₂)` for `c₁, c₂ ≥ 0`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

theorem CSQ_succ (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {CC c₁ c₂ : ℝ}
    (hCC : 0 ≤ CC) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : Work.FTS.CoercivityFix.Transfer.CSQ α n IP CC) :
    Work.FTS.CoercivityFix.Transfer.CSQ α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) (3 * max 1 (max c₁ c₂) * CC) := by
  intro X Y hXq hYq hXm hYm
  -- `ℋⁿ`-membership of the three functions at both arguments, from the descent
  obtain ⟨hXm0, hXmd, hXmz⟩ := HkMem_descent_Q0Sm α hα n hXq hXm
  obtain ⟨hYm0, hYmd, hYmz⟩ := HkMem_descent_Q0Sm α hα n hYq hYm
  -- `C^n`-smoothness of the three functions at both arguments
  have hXq0 : Q0Sm n X := hXq.mono (Nat.le_succ n)
  have hYq0 : Q0Sm n Y := hYq.mono (Nat.le_succ n)
  have hXqd : Q0Sm n (Work.Spaces.Dth X) := hXq.dth
  have hYqd : Q0Sm n (Work.Spaces.Dth Y) := hYq.dth
  have hXqz : Q0Sm n (Work.Spaces.Dz X) := hXq.dz
  have hYqz : Q0Sm n (Work.Spaces.Dz Y) := hYq.dz
  -- the three Cauchy–Schwarz bounds at level `n`
  have h1 := h X Y hXq0 hYq0 hXm0 hYm0
  have h2 := h (Work.Spaces.Dth X) (Work.Spaces.Dth Y) hXqd hYqd hXmd hYmd
  have h3 := h (Work.Spaces.Dz X) (Work.Spaces.Dz Y) hXqz hYqz hXmz hYmz
  -- the three norm comparisons with level `n+1`
  have hN0X : Work.Spaces.HkNorm α n X ≤ Work.Spaces.HkNorm α (n + 1) X := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hXm)
  have hN0Y : Work.Spaces.HkNorm α n Y ≤ Work.Spaces.HkNorm α (n + 1) Y := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hYm)
  have hN1X : Work.Spaces.HkNorm α n (Work.Spaces.Dth X)
      ≤ Work.Spaces.HkNorm α (n + 1) X := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hXm)
  have hN1Y : Work.Spaces.HkNorm α n (Work.Spaces.Dth Y)
      ≤ Work.Spaces.HkNorm α (n + 1) Y := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hYm)
  have hN2X : Work.Spaces.HkNorm α n (Work.Spaces.Dz X)
      ≤ Work.Spaces.HkNorm α (n + 1) X := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dz_le_Q0Sm α n hXq hXm)
  have hN2Y : Work.Spaces.HkNorm α n (Work.Spaces.Dz Y)
      ≤ Work.Spaces.HkNorm α (n + 1) Y := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dz_le_Q0Sm α n hYq hYm)
  -- the three products are dominated by `CC |X|_{n+1} |Y|_{n+1}`
  have hNX : 0 ≤ Work.Spaces.HkNorm α (n + 1) X := Work.Spaces.HkNorm_nonneg α (n + 1) X
  have hNY : 0 ≤ Work.Spaces.HkNorm α (n + 1) Y := Work.Spaces.HkNorm_nonneg α (n + 1) Y
  have hNXn : 0 ≤ Work.Spaces.HkNorm α n X := Work.Spaces.HkNorm_nonneg α n X
  have hNYn : 0 ≤ Work.Spaces.HkNorm α n Y := Work.Spaces.HkNorm_nonneg α n Y
  have e1 : CC * Work.Spaces.HkNorm α n X * Work.Spaces.HkNorm α n Y
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN0X hCC) hN0Y hNYn (mul_nonneg hCC hNX)
  have e2 : CC * Work.Spaces.HkNorm α n (Work.Spaces.Dth X)
        * Work.Spaces.HkNorm α n (Work.Spaces.Dth Y)
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN1X hCC) hN1Y
      (Work.Spaces.HkNorm_nonneg α n _) (mul_nonneg hCC hNX)
  have e3 : CC * Work.Spaces.HkNorm α n (Work.Spaces.Dz X)
        * Work.Spaces.HkNorm α n (Work.Spaces.Dz Y)
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN2X hCC) hN2Y
      (Work.Spaces.HkNorm_nonneg α n _) (mul_nonneg hCC hNX)
  -- the triangle inequality for the three terms of the step
  have habs : |Work.Coercivity.HkIPStep c₁ c₂ IP X Y|
      ≤ |IP X Y| + c₁ * |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
        + c₂ * |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)| := by
    have hA := abs_add_le (IP X Y + c₁ * IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y))
      (c₂ * IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y))
    have hB := abs_add_le (IP X Y) (c₁ * IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y))
    simp only [Work.Coercivity.HkIPStep]
    simp only [abs_mul, abs_of_nonneg hc₁, abs_of_nonneg hc₂] at hA hB ⊢
    linarith
  refine le_trans habs ?_
  have e4 : |IP X Y|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    le_trans h1 e1
  have e5 : |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    le_trans h2 e2
  have e6 : |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    le_trans h3 e3
  -- the arithmetic: `1 + c₁ + c₂ ≤ 3 max 1 (max c₁ c₂)`
  have hM1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hMc₁ : c₁ ≤ max 1 (max c₁ c₂) :=
    le_trans (le_max_left c₁ c₂) (le_max_right (1 : ℝ) (max c₁ c₂))
  have hMc₂ : c₂ ≤ max 1 (max c₁ c₂) :=
    le_trans (le_max_right c₁ c₂) (le_max_right (1 : ℝ) (max c₁ c₂))
  have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by linarith
  have hP : 0 ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_nonneg (mul_nonneg hCC hNX) hNY
  have hsum : |IP X Y| + c₁ * |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
        + c₂ * |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)|
      ≤ (1 + c₁ + c₂)
        * (CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y) := by
    nlinarith [e4, e5, e6, hP]
  calc |IP X Y| + c₁ * |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
        + c₂ * |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)|
      ≤ (1 + c₁ + c₂)
          * (CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y) := hsum
    _ ≤ (3 * max 1 (max c₁ c₂))
          * (CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y) :=
        mul_le_mul_of_nonneg_right hcoef hP
    _ = 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) X
          * Work.Spaces.HkNorm α (n + 1) Y := by ring

end Work.FTS.CoercivityFix.Transfer
