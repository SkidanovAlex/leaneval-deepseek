import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.Taylor

/-- Pure real arithmetic of the Łojasiewicz step: if `C · η ^ q ≤ A ≤ I · d ^ (κ ^ 2)` with
`C > 0`, `I ≥ 0`, `0 < q`, `0 ≤ d ≤ 1` and `q + 1 ≤ κ`, then `η ≤ max 1 (I / C) · d ^ (κ + 1)`.
(Indeed `d ^ (κ ^ 2) ≤ d ^ (q * (κ + 1)) = (d ^ (κ + 1)) ^ q` because `q * (κ + 1) ≤ κ ^ 2`, and
`I / C ≤ max 1 (I / C) ≤ (max 1 (I / C)) ^ q`; compare `q`-th powers.)  With `η = dist (x, Z)` this
is the "`dist (x, Z) ≪ d ^ κ` because `κ ^ 2 / q > κ`" step of the `(⇐)` direction of
`E3_taylor_closure`, which is what lets the point `x` be moved to the nearest point of `Z`. -/
theorem E3_infDist_le_of_pow_le {k : ℕ} (Z : Set (Fin k → ℝ)) (x : Fin k → ℝ)
    (A C I d : ℝ) (q κ : ℕ) (hC : 0 < C) (hI : 0 ≤ I) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hq : 0 < q) (hqκ : q + 1 ≤ κ)
    (h1 : C * Metric.infDist x Z ^ q ≤ A) (h2 : A ≤ I * d ^ (κ ^ 2)) :
    Metric.infDist x Z ≤ max 1 (I / C) * d ^ (κ + 1) := by
  set η := Metric.infDist x Z with hη
  have hη0 : 0 ≤ η := Metric.infDist_nonneg
  have hCA : C * η ^ q ≤ I * d ^ (κ ^ 2) := le_trans h1 h2
  -- divide the hypothesis by `C > 0`
  have hA : η ^ q ≤ (I / C) * d ^ (κ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hC]
    linarith
  -- `I / C ≤ (max 1 (I / C)) ^ q`, using `max 1 (I / C) ≥ 1` and `q ≥ 1`
  have hM1 : 1 ≤ max 1 (I / C) := le_max_left _ _
  have hM : I / C ≤ (max 1 (I / C)) ^ q :=
    le_trans (le_max_right _ _) (le_self_pow₀ hM1 (by omega))
  -- `q * (κ + 1) ≤ κ ^ 2`, from `q + 1 ≤ κ`
  have hqk : q * (κ + 1) ≤ κ ^ 2 := by
    have h2' : (q : ℝ) * ((κ : ℝ) + 1) ≤ (κ : ℝ) ^ 2 := by
      have hqκ' : (q : ℝ) + 1 ≤ (κ : ℝ) := by exact_mod_cast hqκ
      nlinarith [sq_nonneg ((κ : ℝ) - 1)]
    exact_mod_cast h2'
  -- monotonicity of `d ^ ·` on `[0,1]`
  have hdp : d ^ (κ ^ 2) ≤ d ^ (q * (κ + 1)) := pow_le_pow_of_le_one hd0 hd1 hqk
  have hstep : (I / C) * d ^ (κ ^ 2) ≤ (max 1 (I / C)) ^ q * d ^ (q * (κ + 1)) :=
    mul_le_mul hM hdp (pow_nonneg hd0 _) (pow_nonneg (le_trans zero_le_one hM1) _)
  have hB : 0 ≤ max 1 (I / C) * d ^ (κ + 1) :=
    mul_nonneg (le_trans zero_le_one hM1) (pow_nonneg hd0 _)
  -- compare `q`-th powers
  refine (pow_le_pow_iff_left₀ hη0 hB (by omega : q ≠ 0)).mp ?_
  calc η ^ q ≤ (I / C) * d ^ (κ ^ 2) := hA
    _ ≤ (max 1 (I / C)) ^ q * d ^ (q * (κ + 1)) := hstep
    _ = (max 1 (I / C) * d ^ (κ + 1)) ^ q := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (κ + 1) q]

end Work.WilE3.Taylor
