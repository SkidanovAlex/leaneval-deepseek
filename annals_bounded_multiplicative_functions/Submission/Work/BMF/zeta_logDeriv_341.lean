import Mathlib
import Submission.Commons.NumberTheory.Zeta.mangoldt_series_re
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators

/-- The elementary trigonometric identity `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)²`. -/
private lemma cos_3_4_1 (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) =
    2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- `3 + 4 cos θ + cos 2θ ≥ 0`. -/
private lemma cos_341_nonneg (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [cos_3_4_1]
  positivity

/-- The von-Mangoldt cosine series defining `Re(-ζ'/ζ)` at `σ + i t`, `σ > 1`, is summable. -/
private lemma summable_mangoldt_cos (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ) := by
  have hbase : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) /
      ((n + 1 : ℕ) : ℝ) ^ σ) := by
    exact (summable_nat_add_iff 1).2
      (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow (σ := σ) hσ)
  refine Summable.of_norm ?_
  let f : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  change Summable (fun n => ‖f n‖)
  apply Summable.of_nonneg_of_le (g := fun n => ‖f n‖)
      (f := fun n => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ σ)
  · intro n
    exact norm_nonneg _
  · intro n
    have hpos : 0 < (((n + 1 : ℕ) : ℝ) ^ σ) :=
      Real.rpow_pos_of_pos (by positivity : 0 < ((n+1:ℕ):ℝ)) σ
    have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hcos : |Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))| ≤ 1 := Real.abs_cos_le_one _
    change |(ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) /
          (((n + 1 : ℕ) : ℝ) ^ σ)| ≤
        (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ)
    calc
      |(ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) /
          (((n + 1 : ℕ) : ℝ) ^ σ)|
          = (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
              |Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))| /
              (((n + 1 : ℕ) : ℝ) ^ σ) := by
              rw [abs_div, abs_mul, abs_of_nonneg hΛ0]
              rw [abs_of_nonneg (le_of_lt hpos)]
      _ ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ) := by
            have hm : (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
                |Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))| ≤
                (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := by
              exact mul_le_of_le_one_right hΛ0 hcos
            exact div_le_div_of_nonneg_right hm (le_of_lt hpos)
  · simpa [f] using hbase

/-- Linearity of the sum for three absolutely convergent real series. -/
private lemma tsum_three_lin {f g h : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (hh : Summable h)
    (c1 c2 c3 : ℝ) :
    c1 * (∑' n, f n) + c2 * (∑' n, g n) + c3 * (∑' n, h n) =
      ∑' n, (c1 * f n + c2 * g n + c3 * h n) := by
  have hfg : Summable (fun n => c1 * f n + c2 * g n) :=
    (hf.mul_left c1).add (hg.mul_left c2)
  calc
    c1 * (∑' n, f n) + c2 * (∑' n, g n) + c3 * (∑' n, h n)
        = (∑' n, c1 * f n) + (∑' n, c2 * g n) + (∑' n, c3 * h n) := by
            rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    _ = (∑' n, (c1 * f n + c2 * g n)) + (∑' n, c3 * h n) := by
            rw [← hf.mul_left c1 |>.tsum_add (hg.mul_left c2)]
    _ = ∑' n, (c1 * f n + c2 * g n + c3 * h n) := by
            rw [← hfg.tsum_add (hh.mul_left c3)]

/-- The classical `3 + 4 cos θ + cos 2θ ≥ 0` trigonometric inequality for the logarithmic
derivative of `ζ`: for real `σ > 1` and real `t`,
`0 ≤ 3 Re(-ζ'/ζ(σ)) + 4 Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it))`.

Expand each logarithmic derivative as the von Mangoldt series `-ζ'/ζ(s) = Σ_n Λ(n) n^{-s}`
(absolutely convergent for `Re s > 1`), combine the finitely many absolutely convergent series and
use `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`. -/
theorem zeta_logDeriv_341 (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
              riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
              riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  -- von Mangoldt series expansions for the three arguments
  have h0 : (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        Real.cos ((0 : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ)) := by
    have h := Commons.NumberTheory.Zeta.mangoldt_series_re σ hσ 0
    simpa using h
  have ht : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ)) :=
    Commons.NumberTheory.Zeta.mangoldt_series_re σ hσ t
  have h2 : (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        Real.cos ((2 * t) * Real.log (((n + 1 : ℕ) : ℝ)))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ)) :=
    Commons.NumberTheory.Zeta.mangoldt_series_re σ hσ (2 * t)
  let f0 : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos ((0 : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  let ft : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  let f2 : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos ((2 * t) * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  have hs0 : Summable f0 := by simpa [f0] using (summable_mangoldt_cos σ hσ 0)
  have hst : Summable ft := by simpa [ft] using (summable_mangoldt_cos σ hσ t)
  have hs2 : Summable f2 := by simpa [f2] using (summable_mangoldt_cos σ hσ (2 * t))
  rw [h0, ht, h2]
  change 0 ≤ 3 * (∑' n, f0 n) + 4 * (∑' n, ft n) + (∑' n, f2 n)
  rw [← one_mul (∑' n, f2 n)]
  rw [tsum_three_lin hs0 hst hs2 (3 : ℝ) 4 1]
  apply tsum_nonneg
  intro n
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hpow : 0 < (((n + 1 : ℕ) : ℝ) ^ σ) :=
    Real.rpow_pos_of_pos (by positivity : 0 < ((n+1:ℕ):ℝ)) σ
  have hco0 : Real.cos ((0 : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) = 1 := by simp
  have hc2a : Real.cos ((2 * t) * Real.log ((n + 1 : ℕ) : ℝ)) =
      Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ))) := by
    congr 1
    ring
  have hfacθ : 0 ≤ 3 + 4 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) +
      Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ))) := cos_341_nonneg _
  dsimp [f0, ft, f2]
  rw [hco0, hc2a]
  have hmain : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      (3 + 4 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) +
        Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ)))) /
      (((n + 1 : ℕ) : ℝ) ^ σ) := by
    exact div_nonneg (mul_nonneg hΛ0 hfacθ) (le_of_lt hpow)
  have heq : 3 * ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * 1 / (((n + 1 : ℕ) : ℝ) ^ σ)) +
        4 * ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ) ^ σ)) +
        1 * ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ))) / (((n + 1 : ℕ) : ℝ) ^ σ)) =
      (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        (3 + 4 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) +
          Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ)))) /
        (((n + 1 : ℕ) : ℝ) ^ σ) := by
    ring_nf
  rwa [heq]

end Work.BMF
