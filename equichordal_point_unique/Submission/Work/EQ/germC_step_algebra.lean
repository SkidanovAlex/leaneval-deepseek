import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- Pure complex-number algebra behind `germC_facts`.  Write `A = h u`, `B = h (λ u)`,
`C = h (λ² u)`, `S = (1 + B²)^{1/2}`, `E = a C/(C - B)`, `R = -E S`, and let
`P = (a B/(B - A) - a/2, a A B/(B - A))` be the germ point at `u` and `Q = (E - a/2, B E)` the
one at `λ u`.  Then the cleared germ equation `(B - A)(C - B) + a B (C - A) S = 0` implies
`EqRelC a P Q`, and if moreover `Re R > 0` (so that the principal square root of
`(Q.1 + a/2)² + Q.2²` is `R`) the principal backward branch inverts the step:
`invBranch a true Q = P`. -/
theorem germC_step_algebra {a : ℝ} {A B C E S R : ℂ}
    (hBA : B - A ≠ 0) (hCB : C - B ≠ 0)
    (hFE : (B - A) * (C - B) + (a : ℂ) * B * (C - A) * S = 0)
    (hS : S ^ 2 = 1 + B ^ 2)
    (hE : E = (a : ℂ) * C / (C - B))
    (hR : R = -E * S) (hRe : 0 < R.re) :
    EqRelC a ((a : ℂ) * B / (B - A) - ((a / 2 : ℝ) : ℂ), A * ((a : ℂ) * B / (B - A)))
        (E - ((a / 2 : ℝ) : ℂ), B * E) ∧
      invBranch a true (E - ((a / 2 : ℝ) : ℂ), B * E) =
        ((a : ℂ) * B / (B - A) - ((a / 2 : ℝ) : ℂ), A * ((a : ℂ) * B / (B - A))) := by
  -- `R ≠ 0` from `Re R > 0`, hence `E ≠ 0` and `S ≠ 0` (as `R = -E S`).
  have hRne : R ≠ 0 := by
    intro h0
    rw [h0] at hRe
    simp at hRe
  have hEne : E ≠ 0 := by
    intro h0
    exact hRne (by rw [hR, h0]; ring)
  have hSne : S ≠ 0 := by
    intro h0
    exact hRne (by rw [hR, h0]; ring)
  -- `c + c = a` on the real halves.
  have h2c : ((a / 2 : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ) = (a : ℂ) := by push_cast; ring
  -- The two cleared identities coming from the germ equation `hFE`.
  -- (They say `P + Q = (-1/S, -B/S)`.)
  have hk1 : E + (a : ℂ) * B / (B - A) - (a : ℂ) + S⁻¹ = 0 := by
    rw [hE]; field_simp; linear_combination hFE
  have hsum1 : E + (a : ℂ) * B / (B - A) - (a : ℂ) = -S⁻¹ := by
    linear_combination hk1
  have hk2 : B * E + A * ((a : ℂ) * B / (B - A)) + B * S⁻¹ = 0 := by
    rw [hE]; field_simp; linear_combination B * hFE
  have hsum2 : B * E + A * ((a : ℂ) * B / (B - A)) = -B * S⁻¹ := by
    linear_combination hk2
  -- Coordinates of `P + Q`.
  have hQ1 : (E - ((a / 2 : ℝ) : ℂ)) + ((a : ℂ) * B / (B - A) - ((a / 2 : ℝ) : ℂ)) = -S⁻¹ := by
    linear_combination hsum1 - h2c
  have hPc : ((a : ℂ) * B / (B - A) - ((a / 2 : ℝ) : ℂ)) - ((a / 2 : ℝ) : ℂ)
      = (a : ℂ) * B / (B - A) - (a : ℂ) := by
    linear_combination -h2c
  -- `A t = B (t - a)` with `t = aB/(B-A)`: the parallelism of `P + Q` with `P - O₂`.
  have hAB : A * ((a : ℂ) * B / (B - A)) = B * ((a : ℂ) * B / (B - A) - (a : ℂ)) := by
    field_simp
    ring
  -- `bsq (P + Q) = 1`.
  have hsqfin : (-S⁻¹) ^ 2 + (-B * S⁻¹) ^ 2 = 1 := by
    have h1 : (-S⁻¹) ^ 2 + (-B * S⁻¹) ^ 2 = (1 + B ^ 2) / S ^ 2 := by field_simp
    rw [h1, ← hS, div_self (pow_ne_zero 2 hSne)]
  -- `((Q.1 + a/2)² + Q.2²)^{1/2} = R`.
  have hEz : E - ((a / 2 : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ) = E := by ring
  have hbsq : E ^ 2 + (B * E) ^ 2 = R ^ 2 := by
    have h1 : E ^ 2 + (B * E) ^ 2 = E ^ 2 * (1 + B ^ 2) := by ring
    rw [h1, ← hS, hR]; ring
  have hρ : (E ^ 2 + (B * E) ^ 2) ^ (1 / 2 : ℂ) = R := by
    rw [hbsq]
    have h12 : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
    rw [h12]
    exact Complex.sq_cpow_two_inv hRe
  -- The divisions by `R`.
  have hER : E / R = -S⁻¹ := by rw [hR]; field_simp
  have hBER : B * E / R = -B * S⁻¹ := by rw [hR]; field_simp
  constructor
  · constructor
    · rw [hQ1, hsum2]
      exact hsqfin
    · rw [hQ1, hsum2, hPc, hAB]
      ring
  · rw [invBranch]
    simp only [ite_true, one_mul, Prod.mk.injEq]
    constructor
    · rw [hEz, hρ, hER]
      linear_combination -hsum1 + h2c
    · rw [hEz, hρ, hBER]
      linear_combination -hsum2

end Work.EQ
