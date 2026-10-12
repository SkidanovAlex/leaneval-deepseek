import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.All.farTauAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.All.tauSmFloor` — the floor of the smoothed kinetic symbol

`Work.BoseBoxFock.tauSm eT s d ℓ` is the smoothed kinetic symbol `τ̃` of FS `def:tau`:
the two kinks of the box kinetic term (`at |k| = (2sℓ)⁻¹` with weight `1-eT` and
`at |k| = (2dsℓ)⁻¹` with weight `eT`) mollified by the profile `tauProf` of
`Work.BoseBoxFock.TauProf`.  The companion lemma `All.tauSm_ge_shifted` bounds it from below by
the *shifted kinks* `(max 0 (‖k‖ - 2c))²`, `c = (2sℓ)⁻¹, (2dsℓ)⁻¹`, which is the only
quantitative input available pointwise.

This file turns that bound into the **floor**

  `‖q‖² / (1 + 100√ε)  ≤  (1-ε)·τ̃(q) + ρ ε^{-1/2} a`,

under the two arithmetic side conditions `hC5`, `hC4` of the source (the per-kink scale and the
weighted-average scale versus the payable constant `ρ ε^{-1/2} a`).

## The mathematics

Write `x = ‖q‖`, `δ = 100√ε ∈ (0,1]` (so `ε = δ²/10⁴`), `c₁ = (2sℓ)⁻¹ ≤ c₂ = (2dsℓ)⁻¹`,
`c = (1-eT)c₁ + eT c₂`, `K = ρ ε^{-1/2} a`.  The two facts used are

* `τ̃(q) ≥ A₀ := (1-eT)(x-2c₁)₊² + eT(x-2c₂)₊²` (`tauSm_ge_shifted`), and
* `A₀ ≥ (x-2c)₊²` — the weighted Jensen inequality for the convex `t ↦ t₊²`
  (the weights `1-eT, eT` sum to `1`).

The claim `x²/(1+δ) ≤ (1-ε)(x-2c)₊² + K` then splits at `x = 2c₂`:

* `x ≤ 2c₂`: the right side is `≥ K`, and `x² ≤ 4c₂² ≤ K` by `hC5`;
* `x ≥ 2c₂` (hence `x ≥ 2c₁`, so the positive parts drop): multiply by `1+δ` and complete the
  square.  With `σ := (1-ε)(1+δ) - 1 = δ - ε(1+δ) ≥ δ/2 > 0`,

  `σ·[(1-ε)(1+δ)(x-2c)² + (1+δ)K - x²] = (σx - 2(1-ε)(1+δ)c)² + (1+δ)(σK - 4(1-ε)c²) ≥ 0`,

  because `4(1-ε)c² ≤ 4c² ≤ δK/2 ≤ σK` (from `hC4` and `ε(1+δ) ≤ δ/2`, which is `δ ≤ 1`).

Everything is `nlinarith` over the single algebraic relation `(√ε)² = ε`.
-/

noncomputable section

namespace Work.BoseFixR.All

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The completed-square core.**  With `σ := (1-ε)(1+δ) - 1 > 0` (from `ε(1+δ) ≤ δ/2`) and
`σK ≥ 4(1-ε)c²` (from `8c² ≤ δK`), the quadratic `(1-ε)(x-2c)² + K - x²/(1+δ)` is nonnegative
for every `x`. -/
private lemma quad_core {ε δ c K x : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ)
    (hεδ : ε * (1 + δ) ≤ δ / 2) (hK : 0 ≤ K) (hC4 : 8 * c ^ 2 ≤ δ * K) :
    x ^ 2 / (1 + δ) ≤ (1 - ε) * (x - 2 * c) ^ 2 + K := by
  have hσpos : 0 < (1 - ε) * (1 + δ) - 1 := by nlinarith
  have hσge : δ / 2 ≤ (1 - ε) * (1 + δ) - 1 := by nlinarith
  have hineq : 4 * (1 - ε) * c ^ 2 ≤ ((1 - ε) * (1 + δ) - 1) * K := by
    have h1 : 4 * (1 - ε) * c ^ 2 ≤ 4 * c ^ 2 := by nlinarith
    have h2 : (4:ℝ) * c ^ 2 ≤ δ * K / 2 := by nlinarith
    have h3 : δ * K / 2 ≤ ((1 - ε) * (1 + δ) - 1) * K := by
      have := mul_le_mul_of_nonneg_right hσge hK
      linarith
    linarith
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + δ)]
  nlinarith [sq_nonneg (((1 - ε) * (1 + δ) - 1) * x - 2 * ((1 - ε) * (1 + δ)) * c),
    hσpos, hineq, hδ0, hε, hK]

/-- **The pure-real core of `tauSmFloor`**: the shifted-kink lower bound of the smoothed symbol
dominates `x²/(1+100√ε)` up to the payable constant `K`. -/
private lemma tauSmFloorCore {ε c₁ c₂ eT K x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ1 : 100 * Real.sqrt ε ≤ 1) (ht0 : 0 ≤ eT) (ht1 : eT ≤ 1)
    (hc1 : 0 ≤ c₁) (hc12 : c₁ ≤ c₂) (hK : 0 ≤ K)
    (hC5 : 4 * c₂ ^ 2 ≤ K)
    (hC4 : 8 * ((1 - eT) * c₁ + eT * c₂) ^ 2 ≤ 100 * Real.sqrt ε * K)
    (hx : 0 ≤ x) :
    x ^ 2 / (1 + 100 * Real.sqrt ε)
      ≤ (1 - ε) * ((1 - eT) * (max 0 (x - 2 * c₁)) ^ 2 + eT * (max 0 (x - 2 * c₂)) ^ 2) + K := by
  set δ := 100 * Real.sqrt ε with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 := by rw [hδdef]; exact hδ1
  have hsqq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hδsq : δ ^ 2 = 10000 * ε := by rw [hδdef]; nlinarith [hsqq]
  have hεδ : ε * (1 + δ) ≤ δ / 2 := by nlinarith [hδsq, hδ0, hδle]
  have hC4' : 8 * ((1 - eT) * c₁ + eT * c₂) ^ 2 ≤ δ * K := by rw [hδdef]; exact hC4
  have hc2 : 0 ≤ c₂ := le_trans hc1 hc12
  have hA0 : 0 ≤ (1 - eT) * (max 0 (x - 2 * c₁)) ^ 2 + eT * (max 0 (x - 2 * c₂)) ^ 2 := by
    have h1 : 0 ≤ (max 0 (x - 2 * c₁)) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (max 0 (x - 2 * c₂)) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - eT) h1, mul_nonneg ht0 h2]
  rcases le_or_gt x (2 * c₂) with hcase | hcase
  · -- `x ≤ 2c₂`: the right side is `≥ K` and `x² ≤ 4c₂² ≤ K`
    have hx2 : x ^ 2 ≤ 4 * c₂ ^ 2 := by nlinarith
    have hK' : x ^ 2 / (1 + δ) ≤ K := by
      have hden : (0:ℝ) < 1 + δ := by linarith
      rw [div_le_iff₀ hden]
      nlinarith
    nlinarith
  · -- `x ≥ 2c₂ ≥ 2c₁`: the positive parts drop; weighted Jensen and the completed square
    have hmax1 : max 0 (x - 2 * c₁) = x - 2 * c₁ := max_eq_right (by linarith)
    have hmax2 : max 0 (x - 2 * c₂) = x - 2 * c₂ := max_eq_right (by linarith)
    rw [hmax1, hmax2]
    set c := (1 - eT) * c₁ + eT * c₂ with hcdef
    have hA : (x - 2 * c) ^ 2 ≤ (1 - eT) * (x - 2 * c₁) ^ 2 + eT * (x - 2 * c₂) ^ 2 := by
      rw [hcdef]
      nlinarith [mul_nonneg (mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 1 - eT))
        (sq_nonneg (2 * c₁ - 2 * c₂))]
    have hC4'' : 8 * c ^ 2 ≤ δ * K := by rw [hcdef]; exact hC4'
    have hq := quad_core hε hδ0 hεδ hK hC4'' (x := x)
    nlinarith [hA, hq]

theorem tauSmFloor {eT s d ℓ a ρ ε : ℝ} (hs : 0 < s) (hd : 0 < d) (hd1 : d ≤ 1) (hℓ : 0 < ℓ)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ1 : 100 * Real.sqrt ε ≤ 1)
    (hC5 : 4 * ((2 * d * s * ℓ)⁻¹) ^ 2 ≤ ρ * a * ε ^ (-(1 / 2 : ℝ)))
    (hC4 : 8 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹) ^ 2
            ≤ 100 * Real.sqrt ε * (ρ * a * ε ^ (-(1 / 2 : ℝ))))
    (q : EuclideanSpace ℝ (Fin 3)) :
    ‖q‖ ^ 2 / (1 + 100 * Real.sqrt ε) ≤ (1 - ε) * Work.BoseBoxFock.tauSm eT s d ℓ q
      + ρ * ε ^ (-(1 / 2 : ℝ)) * a := by
  set K := ρ * ε ^ (-(1/2:ℝ)) * a with hKdef
  have hcomm : ρ * a * ε ^ (-(1/2:ℝ)) = ρ * ε ^ (-(1/2:ℝ)) * a := by ring
  have hC5' : 4 * ((2 * d * s * ℓ)⁻¹) ^ 2 ≤ K := by rw [hcomm] at hC5; exact hC5
  have hC4' : 8 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹) ^ 2
      ≤ 100 * Real.sqrt ε * K := by rw [hcomm] at hC4; exact hC4
  have hK0 : 0 ≤ K := by
    have h5 := hC5'
    nlinarith [sq_nonneg ((2 * d * s * ℓ)⁻¹ : ℝ)]
  have hc1 : 0 ≤ (2 * s * ℓ)⁻¹ := by positivity
  have hc12 : (2 * s * ℓ)⁻¹ ≤ (2 * d * s * ℓ)⁻¹ := by
    have h0 : (0:ℝ) ≤ 2 * s * ℓ := by positivity
    have hd2 : 2 * d * s * ℓ ≤ 2 * s * ℓ := by
      nlinarith [mul_le_mul_of_nonneg_right hd1 h0]
    exact inv_anti₀ (by positivity : (0:ℝ) < 2 * d * s * ℓ) hd2
  have hcore := tauSmFloorCore (ε := ε) (c₁ := (2 * s * ℓ)⁻¹) (c₂ := (2 * d * s * ℓ)⁻¹)
    (eT := eT) (K := K) (x := ‖q‖) hε hε1 hδ1 heT0 heT1 hc1 hc12 hK0 hC5' hC4' (norm_nonneg q)
  have hshift := Work.BoseFixR.All.tauSm_ge_shifted hs hd hℓ heT0 heT1 q
  have hmono : (1 - ε) * ((1 - eT) * (max 0 (‖q‖ - 2 * (2 * s * ℓ)⁻¹)) ^ 2
      + eT * (max 0 (‖q‖ - 2 * (2 * d * s * ℓ)⁻¹)) ^ 2)
      ≤ (1 - ε) * Work.BoseBoxFock.tauSm eT s d ℓ q :=
    mul_le_mul_of_nonneg_left hshift (by linarith)
  linarith [hcore, hmono]

end Work.BoseFixR.All
