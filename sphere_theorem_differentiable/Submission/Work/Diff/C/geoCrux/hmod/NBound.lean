import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The extraction of the operator-norm bound from the two-centre inequality

`Work.Diff.C.geoCrux.NBoundProp` (in `Submission/Work/Diff/C/geoCrux/variation_modulus.lean`) is the
one-dimensional extraction of the operator norm of the family `ξ ↦ Z_ξ(σ)` of radial variation
fields out of the two-centre Wronskian inequality: with

`κ = cot σ + cot(τ-σ)`, `λ = cot σ - cot τ`, `η = ε₁(1/sin σ + 1/sin τ)`,
`δ = ε₁(1/sin σ + 1/sin(τ-σ))` and `N` the operator norm, the Wronskian argument gives
`(κλ - κη - λδ - δη)N² ≤ 1` together with `η ≤ 3ε₁λ`, `δ ≤ 3ε₁κ` (valid when `τ = 2σ ≤ ρ₀` and
`cos σ ≥ 1/2`, where `κλ = 1/sin²σ` exactly); the extraction is then
`N ≤ sin σ (1 + 7ε₁)`.

That is the pure real-analysis content of the anchor; the proof below is self-contained.
-/

namespace Work.Diff.C.geoCrux.hmod

/-- **The operator-norm bound extracted from the two-centre inequality.**  For `σ` with
`sin σ > 0`, `0 ≤ e ≤ 1/24`, `κ, λ > 0`, `η, δ ≥ 0`, `N ≥ 0`, `κλ = 1/sin²σ`, `η ≤ 3eλ`,
`δ ≤ 3eκ` and `(κλ - κη - λδ - δη)N² ≤ 1`, one has `N ≤ sin σ (1 + 7e)`.

(Algebra: `κη ≤ 3eκλ`, `λδ ≤ 3eκλ`, `δη ≤ 9e²κλ`, so the coefficient in the hypothesis is at least
`κλ(1 - 6e - 9e²) ≥ 0`; hence `(1 - 6e - 9e²)N² ≤ sin²σ`; and
`(1 - 6e - 9e²)(1+7e)² = 1 + 8e - 44e² - 420e³ - 441e⁴ ≥ 1` for `0 ≤ e ≤ 1/24` since
`44e² + 420e³ + 441e⁴ ≤ (44 + 420/24 + 441/576)e² < 8e`.) -/
theorem NBound {σ κ lam eta delta N e : ℝ} (hsin : 0 < Real.sin σ) (he0 : 0 ≤ e)
    (he24 : e ≤ 1 / 24) (hk : 0 < κ) (hlam : 0 < lam) (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hN : 0 ≤ N) (hkl : κ * lam = 1 / (Real.sin σ) ^ 2) (heta3 : eta ≤ 3 * e * lam)
    (hdel3 : delta ≤ 3 * e * κ)
    (hmain : (κ * lam - κ * eta - lam * delta - delta * eta) * N ^ 2 ≤ 1) :
    N ≤ Real.sin σ * (1 + 7 * e) := by
  have hs0 : 0 < Real.sin σ := hsin
  have hs2 : 0 < Real.sin σ ^ 2 := pow_pos hs0 2
  -- the polynomial inequality `1 ≤ (1 - 6e - 9e²)(1+7e)²`
  have he3 : e ^ 3 ≤ e ^ 2 * (1 / 24) := by nlinarith [mul_nonneg he0 he0]
  have he4 : e ^ 4 ≤ e ^ 2 * (1 / 576) := by nlinarith [mul_nonneg he0 he0]
  have hp : 1 ≤ (1 - 6 * e - 9 * e ^ 2) * (1 + 7 * e) ^ 2 := by nlinarith
  -- the three bounds on the cross terms
  have hκlam : 0 < κ * lam := mul_pos hk hlam
  have h1 : κ * eta ≤ 3 * e * (κ * lam) := by
    have h := mul_le_mul_of_nonneg_left heta3 hk.le
    calc κ * eta ≤ κ * (3 * e * lam) := h
      _ = 3 * e * (κ * lam) := by ring
  have h2 : lam * delta ≤ 3 * e * (κ * lam) := by
    have h := mul_le_mul_of_nonneg_left hdel3 hlam.le
    calc lam * delta ≤ lam * (3 * e * κ) := h
      _ = 3 * e * (κ * lam) := by ring
  have h3 : delta * eta ≤ 9 * e ^ 2 * (κ * lam) := by
    have h := mul_le_mul hdel3 heta3 heta (by positivity)
    calc delta * eta ≤ (3 * e * κ) * (3 * e * lam) := h
      _ = 9 * e ^ 2 * (κ * lam) := by ring
  have hfac : 0 ≤ 1 - 6 * e - 9 * e ^ 2 := by nlinarith
  -- the coefficient is at least `κλ(1 - 6e - 9e²)`
  have hC : κ * lam * (1 - 6 * e - 9 * e ^ 2)
      ≤ κ * lam - κ * eta - lam * delta - delta * eta := by nlinarith [h1, h2, h3]
  have hN2 : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
  -- multiply the hypothesis by the nonnegativity of the coefficient
  have h5 : κ * lam * (1 - 6 * e - 9 * e ^ 2) * N ^ 2 ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hC hN2) hmain
  -- substitute `κλ = 1/sin²σ`
  have h6 : (1 - 6 * e - 9 * e ^ 2) * N ^ 2 ≤ Real.sin σ ^ 2 := by
    rw [hkl] at h5
    rw [one_div] at h5
    rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hs2] at h5
    simpa using h5
  -- conclude
  have h7 : N ^ 2 ≤ (Real.sin σ * (1 + 7 * e)) ^ 2 := by nlinarith [h6, hp, hN2, hfac]
  have h8 : 0 ≤ Real.sin σ * (1 + 7 * e) := by positivity
  nlinarith [h7, h8, hN]

end Work.Diff.C.geoCrux.hmod
