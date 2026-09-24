import Mathlib
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_tail_arith

namespace Work.GM.S3

/-- Final real arithmetic of GM Prop 7.1: `X` is the bound on the `v`-integral produced by
`Work.GM.S3.prop71_box_integral_bound` and `Ctail` the constant of `Work.GM.S3.prop71_tail_arith`
(`N³(2 M N)³ ((M N)^η)^{-j} ≤ Ctail · N^{-20}`, valid because `j η ≥ 133/6`).  With
`|W| ≤ 2 M N`, `Main ≥ 0`, `K, Cj, Ctail ≥ 0` and `C := max K ((9/4) Cj Ctail)`:

`N³ X ≤ C · (N³ Main) + C · N^{-20}`.

The only ingredients are `mul_le_mul_of_nonneg_left/right`, `|W|³ ≤ (2 M N)³`, `le_max_left/right`,
`Real.rpow_nonneg` for `((M N)^η)^{-j} ≥ 0` and `ring`. -/
theorem prop71_final_arith (η : ℝ) (hη : 0 < η) (j : ℕ) (hj : (133 : ℝ) / 6 ≤ (j : ℝ) * η)
    (K Cj Ctail : ℝ) (hK : 0 ≤ K) (hCj : 0 ≤ Cj) (hCtail : 0 ≤ Ctail)
    (hCtail_spec : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ^ 3 * (2 * Submission.LargeValues.M N) ^ 3 *
        (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) ≤ Ctail * (N : ℝ) ^ (-20 : ℤ))
    (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (hW : (W.card : ℝ) ≤ 2 * Submission.LargeValues.M N)
    (Main X : ℝ) (hMain : 0 ≤ Main)
    (hX : X ≤ K * Main + (9 / 4) * Cj * ((W.card : ℝ) ^ 3 *
        (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))))) :
    (N : ℝ) ^ 3 * X ≤ max K ((9 / 4) * Cj * Ctail) * ((N : ℝ) ^ 3 * Main) +
      max K ((9 / 4) * Cj * Ctail) * (N : ℝ) ^ (-20 : ℤ) := by
  set C : ℝ := max K ((9 / 4) * Cj * Ctail) with hC
  have hCdef : K ≤ C := by rw [hC]; exact le_max_left _ _
  have hCdef' : (9 / 4) * Cj * Ctail ≤ C := by rw [hC]; exact le_max_right _ _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hP3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := pow_nonneg hN0 3
  have hM0 : 0 ≤ Submission.LargeValues.M N := by
    rw [Submission.LargeValues.M]; exact Real.rpow_nonneg hN0 _
  have hT0 : 0 ≤ 2 * Submission.LargeValues.M N := by linarith
  have hrpow : 0 ≤ (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) :=
    Real.rpow_nonneg (Real.rpow_nonneg hM0 η) _
  have hcard : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hcube : (W.card : ℝ) ^ 3 ≤ (2 * Submission.LargeValues.M N) ^ 3 :=
    pow_le_pow_left₀ hcard hW 3
  have hQle : (W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) ≤
      (2 * Submission.LargeValues.M N) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) :=
    mul_le_mul_of_nonneg_right hcube hrpow
  -- multiply `hX` by `N³`
  have hA : (N : ℝ) ^ 3 * X ≤ K * ((N : ℝ) ^ 3 * Main) +
      (9 / 4) * Cj * ((N : ℝ) ^ 3 *
        ((W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))))) := by
    calc (N : ℝ) ^ 3 * X
        ≤ (N : ℝ) ^ 3 * (K * Main + (9 / 4) * Cj * ((W.card : ℝ) ^ 3 *
            (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))))) :=
          mul_le_mul_of_nonneg_left hX hP3
      _ = K * ((N : ℝ) ^ 3 * Main) + (9 / 4) * Cj * ((N : ℝ) ^ 3 *
            ((W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))))) := by ring
  -- the `|W|³` term is bounded by the tail constant
  have hKey : (N : ℝ) ^ 3 *
      ((W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ)))) ≤
      Ctail * (N : ℝ) ^ (-20 : ℤ) := by
    calc (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))))
        ≤ (N : ℝ) ^ 3 * ((2 * Submission.LargeValues.M N) ^ 3 *
            (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ)))) :=
          mul_le_mul_of_nonneg_left hQle hP3
      _ = (N : ℝ) ^ 3 * (2 * Submission.LargeValues.M N) ^ 3 *
            (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) := by ring
      _ ≤ Ctail * (N : ℝ) ^ (-20 : ℤ) := hCtail_spec N hN
  have hNin : (0 : ℝ) ≤ (N : ℝ) ^ (-20 : ℤ) := zpow_nonneg hN0 _
  have h9 : (0 : ℝ) ≤ (9 / 4) * Cj := by linarith
  have hB : (9 / 4) * Cj * ((N : ℝ) ^ 3 *
        ((W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))))) ≤
      C * (N : ℝ) ^ (-20 : ℤ) := by
    calc (9 / 4) * Cj * ((N : ℝ) ^ 3 *
          ((W.card : ℝ) ^ 3 * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ)))))
        ≤ (9 / 4) * Cj * (Ctail * (N : ℝ) ^ (-20 : ℤ)) := mul_le_mul_of_nonneg_left hKey h9
      _ = (9 / 4) * Cj * Ctail * (N : ℝ) ^ (-20 : ℤ) := by ring
      _ ≤ C * (N : ℝ) ^ (-20 : ℤ) := mul_le_mul_of_nonneg_right hCdef' hNin
  have hPmain : (0 : ℝ) ≤ (N : ℝ) ^ 3 * Main := mul_nonneg hP3 hMain
  have hA1 : K * ((N : ℝ) ^ 3 * Main) ≤ C * ((N : ℝ) ^ 3 * Main) :=
    mul_le_mul_of_nonneg_right hCdef hPmain
  linarith [hA, hB, hA1]

end Work.GM.S3
