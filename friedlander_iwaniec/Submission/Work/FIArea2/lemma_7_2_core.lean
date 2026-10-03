/-
# (7.10) — the leading Fourier integral, with the correct normalisation

`lemma_7_6_identity` gives the *exact* value of the leading Fourier integral of *FI* §7,
`F₀ = 4∫∫_{t₁,t₂>0} f(t₁⁴−2γt₁²t₂²+t₂⁴) = (1/2)·E(γ)·f̂(0)` with
`f̂(0) = ∫₀^∞ f(u)u^{−1/2}du` (the frozen `|w|²`-normalisation of `Fhat`) and
`E(γ) = ∫₀^∞(t²−2γt+1)^{−1/2}t^{−1/2}dt`; and `ellInt_asymptotic` gives
`E(γ) = log(64/(1−γ²)) + O((1−γ²)log(64/(1−γ²)))` as `γ → 1⁻`.  Combining the two (below) gives
(7.10) in the *correct* form:

  `F₀ = (1/2)·f̂(0)·log(64/δ²) + O(f̂(0)·δ²log δ^{−2}) = f̂(0)·log(8|z₁z₂|/Δ) + O(…)`,
  `δ² = 1 − γ² = Δ²/|z₁z₂|²`,

which is *exactly half* the paper's (7.10) `F₀ = f̂(0)·2log(2|z₁z₂|/Δ)` **in the frozen
normalisation** (the paper's own `f̂(0) = ∫f(u)du` is half the frozen `Fhat`, so no contradiction:
only one of the two conventions can carry the factor `2`).  `NormWitness.lean` shows the
consequence: `C0mod ≠ C0true` at an explicit pair where the two kernels agree.
-/
import Mathlib
import Submission.Work.FIArea2.lemma_7_6_identity
import Submission.Work.FIArea2.ellInt_asymptotic

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

/-- **(7.10), corrected**: the leading Fourier integral equals
`(1/2)·f̂(0)·log(64/δ²)` up to the error `(1/2)|f̂(0)|·64·δ²·log(64/δ²)`, where
`f̂(0) = ∫₀^∞f(u)u^{−1/2}du` and `δ² = 1−γ²` (so `log(64/δ²) = 2log(8|z₁z₂|/Δ)`). -/
theorem lemma_7_2_core (f : ℝ → ℝ) (γ : ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hfsupp : ∀ x, x ≤ 0 → f x = 0) (hcc : HasCompactSupport f) (hγ0 : 1 / 2 ≤ γ)
    (hγ1 : γ < 1) :
    |4 * (∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
          f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4))
        - (1 / 2) * (∫ u in Set.Ioi 0, f u / Real.sqrt u) * Real.log (64 / (1 - γ ^ 2))|
      ≤ (1 / 2) * |∫ u in Set.Ioi 0, f u / Real.sqrt u|
          * (64 * (1 - γ ^ 2) * Real.log (64 / (1 - γ ^ 2))) := by
  have hγ2 : γ ^ 2 < 1 := by nlinarith
  rw [lemma_7_6_identity f γ hf0 hfc hfsupp hcc hγ2]
  have hE := ellInt_asymptotic γ hγ0 hγ1
  have hfac : |(1 / 2)
        * (∫ t in Set.Ioi 0,
            (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
        * (∫ u in Set.Ioi 0, f u / Real.sqrt u)
      - (1 / 2) * (∫ u in Set.Ioi 0, f u / Real.sqrt u) * Real.log (64 / (1 - γ ^ 2))|
      = (1 / 2) * |∫ u in Set.Ioi 0, f u / Real.sqrt u|
        * |(∫ t in Set.Ioi 0,
              (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
            - Real.log (64 / (1 - γ ^ 2))| := by
    rw [show (1 / 2)
          * (∫ t in Set.Ioi 0,
              (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
          * (∫ u in Set.Ioi 0, f u / Real.sqrt u)
        - (1 / 2) * (∫ u in Set.Ioi 0, f u / Real.sqrt u) * Real.log (64 / (1 - γ ^ 2))
        = (1 / 2) * (∫ u in Set.Ioi 0, f u / Real.sqrt u)
          * ((∫ t in Set.Ioi 0,
                (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
              - Real.log (64 / (1 - γ ^ 2))) by ring,
      abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hfac]
  have hnn : 0 ≤ (1 / 2) * |∫ u in Set.Ioi 0, f u / Real.sqrt u| := by positivity
  calc (1 / 2) * |∫ u in Set.Ioi 0, f u / Real.sqrt u|
        * |(∫ t in Set.Ioi 0,
              (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
            - Real.log (64 / (1 - γ ^ 2))|
      ≤ (1 / 2) * |∫ u in Set.Ioi 0, f u / Real.sqrt u|
        * (64 * (1 - γ ^ 2) * Real.log (64 / (1 - γ ^ 2))) := by
        gcongr

end

end Work.FIArea2
