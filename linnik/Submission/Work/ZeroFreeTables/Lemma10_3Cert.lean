/-
# ZeroFreeTables — Lemma10_3Cert.lean

The rational core of HB Lemma 10.3: at `a = 3λ = 18/7` the inequality (10.14)
specialises to `0 ≤ p1014 δ ε`, where `p1014 δ ε = P₃((3+δ)/3) - P₃(1) -
2P₃((3+δ)/4) + (3+δ)(9/14+ε)` and `δ = λ₁/λ ∈ [0,1]`.  Here we prove that this is
*strictly negative* for `ε = 1/1000` on the whole interval, so that (10.14) forces
`λ₃ > 6/7`.

With HB's polynomial `P₃(X) = X + X² + (2/3)X³` and `x = 3 + δ`,
`p1014 δ ε = (5/1296)x³ - (1/72)x² + (10/21 + ε)x - 8/3`, and its maximum on
`[3,4]` is at `x = 4`, where it equals `-103933/141750 + 4ε` — negative for
`ε ≤ 1/100`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine

namespace Work.ZeroFreeTables

theorem Lemma10_3Cert : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → Work.ZeroFreeTables.p1014 δ (1/1000) < 0 := by
  intro δ h0 h1
  set x : ℝ := 3 + δ with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; linarith
  have hx4 : x ≤ 4 := by rw [hx]; linarith
  have hval : p1014 δ (1/1000)
      = (5/1296 : ℝ) * x^3 - (1/72) * x^2 + (10/21 + 1/1000) * x - 8/3 := by
    rw [hx]
    unfold p1014 P3R
    field_simp
    ring
  have hfac : (5/1296 : ℝ) * x^3 - (1/72) * x^2 + (10/21 + 1/1000) * x - 8/3
      = (-103933/141750 : ℝ)
        + (x - 4) * ((5/1296 : ℝ) * x^2 + (1/648) * x + (274067/567000)) := by
    ring
  have hQ : 0 ≤ (5/1296 : ℝ) * x^2 + (1/648) * x + (274067/567000) := by
    have hsq : (5/1296 : ℝ) * x^2 + (1/648) * x + (274067/567000)
        = (5/1296) * (x - 3)^2 + (2/81) * (x - 3) + (592759/1134000) := by
      ring
    rw [hsq]
    nlinarith [sq_nonneg (x - 3), hx3]
  rw [hval, hfac]
  nlinarith [hQ, hx4]

/-- **HB Lemma 10.3 with no margin.**  The same certificate at `ε = 0`, i.e. the
engine's contradiction is already reached with `ε = 0`: HB (10.14) forces
`λ₃ ≥ 6/7` (not merely `6/7 - 1/1000`). -/
theorem Lemma10_3CertZero : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → Work.ZeroFreeTables.p1014 δ 0 < 0 := by
  intro δ h0 h1
  have h := Lemma10_3Cert δ h0 h1
  have hd : p1014 δ (1/1000) = p1014 δ 0 + (3 + δ) * (1/1000) := by
    unfold p1014
    ring
  have hpos : 0 < (3 + δ) * (1/1000) := by
    have : (0:ℝ) < 3 + δ := by linarith
    positivity
  linarith

end Work.ZeroFreeTables
