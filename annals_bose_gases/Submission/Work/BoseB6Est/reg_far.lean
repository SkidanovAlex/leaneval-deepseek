import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseB6Est.beta_close_bounds
import Submission.Work.BoseB6Est.fsInt
import Submission.Work.BoseB6Est.fsTau_ge_half
import Submission.Work.BoseB6Est.gFun_tau_diff
import Submission.Work.BoseB6Est.radialMidBetaBound
import Submission.Work.BoseB6Est.radialMidBetaNonpos
import Submission.Work.BoseB6Est.radialMidTauBound
import Submission.Work.BoseB6Est.radialTauDiffBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the far region `(min 4 T, T]` of the `I₁` estimate

`reg_far`: the part of the regularised radial Bogoliubov integral

  `∫₀^∞ r² (G(r) − G₀(r)) dr`,  `G = fsGR K ε_T c₁ c₂`,  `G₀ = fsG0R = lhyRad (8π)`,

over the far region `(min 4 K.T, K.T]` is bounded by `2750·ε(μ,ρ_z)`
(`ε = Work.BoseB6.lhyEps a R ε_T K_ℓ s d μ`); when `K.T ≤ 4` the region is empty.

On `4 < r ≤ K.T` the two deviations that make up the integrand are
`u(r) = r² − τ̃(r)` and `δ(r) = β(r) − 8π`, and the *exact* decomposition
(inserting the bracket at the model kinetic symbol `r²` with the physical `β`)

  `G(r) − G₀(r) = [F(τ̃,β) − F(r²,β)] + [G₀(r²,β) − G₀(r²,8π)]`,
  `F(σ,b) = (σ+b) − √(σ²+2σb) = b²/(σ+b+√(σ²+2σb))`

splits the estimate into the `τ`-increment and the `β`-increment:

* **`τ`-increment.**  The rationalised increment is *exactly*
  `F(τ,β) − F(r²,β) = (r²−τ)·β²(1/W(τ,β) + 1/W(r²,β))/(A+C)` with
  `W(σ,b) = σ+b+√(σ²+2σb)` and `A+C = √(τ²+2τβ)+√(r⁴+2r²β)`.  Since
  `u ≤ 2r(c₁+ε_Tc₂)` (`radialTauDiffBound`) and `W(σ,b) ≥ 2σ+β`, this gives

    `r²·[τ-increment] ≤ 2500·(c₁+ε_Tc₂)/r` for `4 ≤ r`, `9r²/32 ≤ τ ≤ r²`,
    `0 ≤ β ≤ 26.2` (`reg_far_tauDiff`; the constant `2500` is what the sharp
    `2r⁴·β²(1/W(τ,β)+1/W(r²,β)) ≤ 2500·(A+C)` yields: `32β²/9 ≤ 2500`).

* **`β`-increment.**  `G₀(r²,β) − G₀(r²,8π) ≤ (3/2)(8π)²|β−8π|/r⁴`, so with
  `|β(r)−8π| ≤ ηr` (`FsKernel.close`, `r ≤ K.T`) it is
  `≤ (3/2)(8π)²η/r` (`reg_far_betaPart`).

Integrating `2500(c₁+ε_Tc₂)/r + (3/2)(8π)²η/r` over `(4,T]` and using
`(c₁+ε_Tc₂)log T ≤ ε` (`FsI1Regime.hEpsLogT`) together with
`η log T ≤ (ηT)(log T/T) ≤ ε/(8π)²` (from `hηT` and `hEpsTlog`) gives
`2500ε + (3/2)ε ≤ 2750ε`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

/-! ## 1. `τ̃ ≥ 9r²/32` on the far region -/

/-- On the far region `4 ≤ r` (and `c₁ ≤ r/4`) FS's truncated kinetic symbol
satisfies `τ̃(r) ≥ 9r²/32`: the first truncation is active and
`(1−ε_T)(r−c₁)² ≥ (1/2)(3r/4)² = 9r²/32`. -/
lemma reg_far_tau_lower {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1 / 2)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (hr : 4 ≤ r) (hc1r : c1 ≤ r / 4) :
    9 * r ^ 2 / 32 ≤ Work.BoseB6.fsTau εT c1 c2 r := by
  have hr0 : 0 ≤ r := by linarith
  have htabs : |r| = r := abs_of_nonneg hr0
  have hX : max (r - c1) 0 = r - c1 := max_eq_left (by linarith)
  have h1m : (1 : ℝ) / 2 ≤ 1 - εT := by linarith
  have hkey : (3 * r / 4) ^ 2 ≤ (r - c1) ^ 2 := by
    have h3 : 3 * r / 4 ≤ r - c1 := by linarith
    nlinarith [h3, hr0, hc1r]
  have hA : (1 / 2) * (3 * r / 4) ^ 2 ≤ (1 - εT) * (r - c1) ^ 2 :=
    mul_le_mul h1m hkey (by positivity) (by linarith)
  have hB : 0 ≤ εT * (max (r - c2) 0) ^ 2 := mul_nonneg hε0 (sq_nonneg _)
  rw [Work.BoseB6.fsTau, htabs, hX]
  nlinarith [hA, hB]

/-! ## 2. The sharp `τ`-difference bound -/

/-- **The `τ`-increment on the far region.**  For `4 ≤ r`, `9r²/32 ≤ τ ≤ r²`,
`0 ≤ β ≤ 26.2` and `r² − τ ≤ 2rs` with `s ≥ 0`,

  `r²·[(τ+β)−√(τ²+2τβ) − ((r²+β)−√((r²)²+2r²β))] ≤ 2500·s/r`.

The proof uses the exact rationalised increment
`F(τ,β) − F(r²,β) = u·β²(1/W(τ,β)+1/W(r²,β))/(A+C)`: with `u ≤ 2rs` and
`1/W(σ,β) ≤ 1/(2σ)` this is at most `32β²/9 ≤ 2500` per unit of `s/r`. -/
lemma reg_far_tauDiff {τ β s r : ℝ} (hr : 4 ≤ r) (hτ0 : 0 ≤ τ)
    (hτ9 : 9 * r ^ 2 / 32 ≤ τ) (hτy : τ ≤ r ^ 2) (hβ0 : 0 ≤ β) (hβ26 : β ≤ 26.2)
    (hs : 0 ≤ s) (hu : r ^ 2 - τ ≤ 2 * r * s) :
    r ^ 2 * (((τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β))
        - ((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β)))
      ≤ 2500 * s / r := by
  have hr0 : 0 < r := by linarith
  have hτpos : 0 < τ := by nlinarith [hτ9, hr]
  set y := r ^ 2 with hydef
  set A := Real.sqrt (τ ^ 2 + 2 * τ * β) with hAdef
  set C := Real.sqrt (y ^ 2 + 2 * y * β) with hCdef
  set u := y - τ with hudef
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hApos : 0 < A := by
    rw [hAdef]; exact Real.sqrt_pos.mpr (by nlinarith)
  have hCpos : 0 < C := by
    rw [hCdef]; exact Real.sqrt_pos.mpr (by nlinarith)
  have hA2 : A ^ 2 = τ ^ 2 + 2 * τ * β := by
    rw [hAdef]; exact Real.sq_sqrt (by nlinarith)
  have hC2 : C ^ 2 = y ^ 2 + 2 * y * β := by
    rw [hCdef]; exact Real.sq_sqrt (by nlinarith)
  have hu0 : 0 ≤ u := by rw [hudef]; linarith [hτy]
  have hu2 : u ≤ 2 * r * s := by rw [hudef]; exact hu
  have hW1 : 0 < τ + β + A := by linarith
  have hW2 : 0 < y + β + C := by linarith
  have hAC : 0 < A + C := by linarith
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  set G := β ^ 2 * (1 / (τ + β + A) + 1 / (y + β + C)) with hGdef
  have hGnn : 0 ≤ G := by rw [hGdef]; positivity
  -- rationalisations
  have hrat1 : (τ + β) - A = β ^ 2 / (τ + β + A) := by
    rw [hAdef]; exact rat τ β hτpos hβ0
  have hrat2 : (y + β) - C = β ^ 2 / (y + β + C) := by
    rw [hCdef]; exact rat y β hy0 hβ0
  -- `C − A = u(y+τ+2β)/(A+C)`
  have hCA : C - A = u * (y + τ + 2 * β) / (A + C) := by
    rw [eq_div_iff (ne_of_gt hAC)]
    have h1 : (C - A) * (A + C) = C ^ 2 - A ^ 2 := by ring
    rw [h1, hC2, hA2, hudef]
    ring
  -- the exact increment identity
  have hident : ((τ + β) - A) - ((y + β) - C) = u * G / (A + C) := by
    rw [hrat1, hrat2, hGdef]
    have hkey : (y + β + C) - (τ + β + A)
        = u * ((τ + β + A) + (y + β + C)) / (A + C) := by
      have hW : (y + β + C) - (τ + β + A) = u + (C - A) := by ring
      rw [hW, hCA]
      field_simp; ring
    have e1 : β ^ 2 / (τ + β + A) - β ^ 2 / (y + β + C)
        = β ^ 2 * ((y + β + C) - (τ + β + A)) / ((τ + β + A) * (y + β + C)) := by
      field_simp
    rw [e1, hkey]
    field_simp; ring
  -- lower bounds for `A`, `C`
  have hAge : τ ≤ A := by
    rw [hAdef]
    calc τ = Real.sqrt (τ ^ 2) := (Real.sqrt_sq hτpos.le).symm
      _ ≤ Real.sqrt (τ ^ 2 + 2 * τ * β) := Real.sqrt_le_sqrt (by nlinarith)
  have hCge : y ≤ C := by
    rw [hCdef]
    calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy0.le).symm
      _ ≤ Real.sqrt (y ^ 2 + 2 * y * β) := Real.sqrt_le_sqrt (by nlinarith)
  have hτge : 9 * y / 32 ≤ τ := hτ9
  -- `2y²G ≤ 2500(A+C)`
  have hboundG : 2 * y ^ 2 * G ≤ 2500 * (A + C) := by
    rw [hGdef]
    have hsum : 1 / (τ + β + A) + 1 / (y + β + C) ≤ 1 / (2 * τ) + 1 / (2 * y) := by
      have h1 : 1 / (τ + β + A) ≤ 1 / (2 * τ) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 1 / (y + β + C) ≤ 1 / (2 * y) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have hstep1 : 2 * y ^ 2 * (β ^ 2 * (1 / (τ + β + A) + 1 / (y + β + C)))
        ≤ 2 * y ^ 2 * (β ^ 2 * (1 / (2 * τ) + 1 / (2 * y))) := by
      have hb2 : (0 : ℝ) ≤ β ^ 2 := sq_nonneg β
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hb2) (by positivity)
    have hstep2 : 2 * y ^ 2 * (β ^ 2 * (1 / (2 * τ) + 1 / (2 * y)))
        = β ^ 2 * y * (y + τ) / τ := by
      field_simp
    have hyτ : y + τ ≤ (41 / 9) * τ := by nlinarith [hτge]
    have hstep3 : β ^ 2 * y * (y + τ) / τ ≤ β ^ 2 * y * (41 / 9) := by
      rw [div_le_iff₀ hτpos]
      have hm : (0 : ℝ) ≤ β ^ 2 * y := mul_nonneg (sq_nonneg β) hy0.le
      have h := mul_le_mul_of_nonneg_left hyτ hm
      nlinarith [h]
    have hACge : 41 * y / 32 ≤ A + C := by nlinarith [hAge, hCge, hτge]
    have hβ2 : β ^ 2 ≤ (26.2 : ℝ) ^ 2 := by nlinarith [hβ26, hβ0]
    have hnum : 32 * β ^ 2 / 9 ≤ 2500 := by nlinarith [hβ2]
    have hstep4 : β ^ 2 * y * (41 / 9) ≤ 2500 * (A + C) := by
      have hmm : (41 * y / 32) * (32 * β ^ 2 / 9) ≤ (A + C) * 2500 :=
        mul_le_mul hACge hnum (by positivity) (by linarith)
      nlinarith [hmm]
    linarith [hstep1, hstep2, hstep3, hstep4]
  -- conclude
  have hmain : y * (u * G / (A + C)) ≤ 2500 * s / r := by
    rw [show y * (u * G / (A + C)) = y * u * G / (A + C) by ring]
    rw [div_le_div_iff₀ hAC hr0]
    have h1 : y * u * G * r ≤ y * (2 * r * s) * G * r := by
      have h0 : u ≤ 2 * r * s := hu2
      have h3 : u * G ≤ (2 * r * s) * G := mul_le_mul_of_nonneg_right h0 hGnn
      nlinarith [h3, le_of_lt hy0, le_of_lt hr0]
    have h2 : y * (2 * r * s) * G * r = s * (2 * y ^ 2 * G) := by
      rw [hydef]; ring
    have h3 : s * (2 * y ^ 2 * G) ≤ s * (2500 * (A + C)) :=
      mul_le_mul_of_nonneg_left hboundG hs
    linarith [h1, h2, h3]
  have hgoal : ((τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β))
      - ((y + β) - Real.sqrt (y ^ 2 + 2 * y * β)) = u * G / (A + C) := by
    rw [← hAdef, ← hCdef]
    exact hident
  rw [hgoal]
  exact hmain

/-! ## 3. The `β`-increment -/

/-- **The `β`-increment at the model kinetic symbol.**  For `r > 0`,
`0 ≤ β`, `η ≥ 0` and `|β − 8π| ≤ ηr`,

  `r²·[(r²+β)−√((r²)²+2r²β) − β²/(2r²)
      − ((r²+8π)−√((r²)²+2r²8π) − (8π)²/(2r²))] ≤ (3/2)(8π)²η/r`. -/
lemma reg_far_betaPart {β η r : ℝ} (hr : 0 < r) (hβ0 : 0 ≤ β) (hη0 : 0 ≤ η)
    (hclose : |β - 8 * Real.pi| ≤ η * r) :
    r ^ 2 * (((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - β ^ 2 / (2 * r ^ 2))
        - ((r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi))
            - (8 * Real.pi) ^ 2 / (2 * r ^ 2)))
      ≤ (3 / 2) * (8 * Real.pi) ^ 2 * η / r := by
  have hc : 0 < 8 * Real.pi := by positivity
  have hy : 0 < r ^ 2 := by positivity
  have hA0 : 0 < (3 / 2) * (8 * Real.pi) ^ 2 := by positivity
  have hkey : (3 / 2) * (8 * Real.pi) ^ 2 * |β - 8 * Real.pi| / r ^ 2
      ≤ (3 / 2) * (8 * Real.pi) ^ 2 * η / r := by
    have h2 : (3 / 2) * (8 * Real.pi) ^ 2 * η / r * r ^ 2
        = (3 / 2) * (8 * Real.pi) ^ 2 * η * r := by
      field_simp
    rw [div_le_iff₀ hy, h2]
    have := mul_le_mul_of_nonneg_left hclose hA0.le
    nlinarith [this]
  rcases le_total β (8 * Real.pi) with hbc | hcb
  · have h := radialMidBetaBound (y := r ^ 2) (β := β) (c := 8 * Real.pi) hy hβ0 hbc
    have h4 : (0 : ℝ) ≤ r ^ 2 := by positivity
    have h5 : r ^ 2 * ((3 / 2) * (8 * Real.pi) ^ 2 * |β - 8 * Real.pi| / (r ^ 2) ^ 2)
        = (3 / 2) * (8 * Real.pi) ^ 2 * |β - 8 * Real.pi| / r ^ 2 := by
      field_simp
    calc r ^ 2 * (((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - β ^ 2 / (2 * r ^ 2))
          - ((r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi))
              - (8 * Real.pi) ^ 2 / (2 * r ^ 2)))
        ≤ r ^ 2 * ((3 / 2) * (8 * Real.pi) ^ 2 * |β - 8 * Real.pi| / (r ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h h4
      _ = (3 / 2) * (8 * Real.pi) ^ 2 * |β - 8 * Real.pi| / r ^ 2 := h5
      _ ≤ (3 / 2) * (8 * Real.pi) ^ 2 * η / r := hkey
  · have h := radialMidBetaNonpos (y := r ^ 2) (β := β) (c := 8 * Real.pi) hy hβ0 hc.le hcb
    have h4 : (0 : ℝ) ≤ r ^ 2 := by positivity
    have h5 : r ^ 2 * (((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - β ^ 2 / (2 * r ^ 2))
          - ((r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi))
              - (8 * Real.pi) ^ 2 / (2 * r ^ 2))) ≤ 0 := by
      have h6 := mul_le_mul_of_nonneg_left h h4
      linarith [h6]
    have h7 : 0 ≤ (3 / 2) * (8 * Real.pi) ^ 2 * η / r := by positivity
    linarith [h5, h7]

/-! ## 4. The pointwise bound on the far region -/

/-- **Pointwise bound on the far region.**  For `4 ≤ r ≤ K.T`,

  `r²(G(r) − G₀(r)) ≤ 2500(c₁+ε_Tc₂)/r + (3/2)(8π)²η/r`. -/
lemma reg_far_pointwise (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ} (hr4 : 4 ≤ r) (hrT : r ≤ K.T) :
    r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)
      ≤ 2500 * (c1 + εT * c2) / r + (3 / 2) * (8 * Real.pi) ^ 2 * K.η / r := by
  have hr0 : 0 < r := by linarith
  have hε1' : εT ≤ 1 := by linarith [h.hε1]
  set τ := Work.BoseB6.fsTau εT c1 c2 r with hτdef
  set β := K.β r with hβdef
  have hτ0 : 0 ≤ τ := fsTau_nonneg h.hε0 hε1' hr0.le
  have hτy : τ ≤ r ^ 2 := fsTau_le_sq h.hε0 h.hε1 h.hc1 h.hc12 hr0.le
  have hτ9 : 9 * r ^ 2 / 32 ≤ τ :=
    reg_far_tau_lower h.hε0 h.hε1 h.hc1 h.hc12 hr4 (by linarith [h.c1_le_one])
  have hβ0 : 0 ≤ β := K.nonneg r
  have hβ26 : β ≤ 26.2 := K.beta_le_B0 h.hηT hr0
  have hS0 : 0 ≤ c1 + εT * c2 := by
    have hc2 : 0 ≤ c2 := le_trans h.hc1 h.hc12
    nlinarith [mul_nonneg h.hε0 hc2, h.hc1]
  have hu : r ^ 2 - τ ≤ 2 * r * (c1 + εT * c2) :=
    radialTauDiffBound h.hε0 hε1' h.hc1 h.hc12 hr0.le
  have h1 : r ^ 2 * (((τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β))
      - ((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β)))
      ≤ 2500 * (c1 + εT * c2) / r :=
    reg_far_tauDiff hr4 hτ0 hτ9 hτy hβ0 hβ26 hS0 hu
  have h2 : r ^ 2 * (((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - β ^ 2 / (2 * r ^ 2))
      - ((r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi))
          - (8 * Real.pi) ^ 2 / (2 * r ^ 2)))
      ≤ (3 / 2) * (8 * Real.pi) ^ 2 * K.η / r :=
    reg_far_betaPart hr0 hβ0 K.ηnn (K.close r hr0.le hrT)
  have hGR : fsGR K εT c1 c2 r
      = (τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β) - β ^ 2 / (2 * r ^ 2) := by
    simp only [fsGR, ← hτdef, ← hβdef]; ring_nf
  have hG0 : fsG0R r = (r ^ 2 + 8 * Real.pi)
      - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi)) - (8 * Real.pi) ^ 2 / (2 * r ^ 2) := by
    simp only [fsG0R]; ring_nf
  rw [hGR, hG0]
  have hsplit : ((τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β) - β ^ 2 / (2 * r ^ 2))
      - ((r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi))
          - (8 * Real.pi) ^ 2 / (2 * r ^ 2))
      = (((τ + β) - Real.sqrt (τ ^ 2 + 2 * τ * β))
          - ((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β)))
        + (((r ^ 2 + β) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * β) - β ^ 2 / (2 * r ^ 2))
          - ((r ^ 2 + 8 * Real.pi) - Real.sqrt ((r ^ 2) ^ 2 + 2 * r ^ 2 * (8 * Real.pi))
              - (8 * Real.pi) ^ 2 / (2 * r ^ 2))) := by ring
  rw [hsplit, mul_add]
  linarith [h1, h2]

/-! ## 5. The far-region integral -/

theorem reg_far (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    (∫ r in Set.Ioc (min 4 K.T) K.T, r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      ≤ 2750 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  set eps := Work.BoseB6.lhyEps a R εT Kl s d μ with hepsdef
  have hεnn : 0 ≤ eps := FsI1Regime.lhyEps_nonneg h
  by_cases hT4 : K.T ≤ 4
  · have hmin : min 4 K.T = K.T := min_eq_right hT4
    rw [hmin, Set.Ioc_eq_empty (lt_irrefl K.T), MeasureTheory.setIntegral_empty]
    exact mul_nonneg (by norm_num) hεnn
  · have h4T : 4 ≤ K.T := le_of_lt (not_le.mp hT4)
    rw [min_eq_left h4T]
    have hTpos : 0 < K.T := by linarith
    have hε1' : εT ≤ 1 := by linarith [h.hε1]
    have hc2 : 0 ≤ c2 := le_trans h.hc1 h.hc12
    have hS0 : 0 ≤ c1 + εT * c2 := by nlinarith [mul_nonneg h.hε0 hc2, h.hc1]
    have hg1 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioi 0) :=
      integrableOn_r2_fsGR K h.hε0 hε1' h.hηT
    have hg0 : IntegrableOn (fun r : ℝ => r ^ 2 * fsG0R r) (Set.Ioi 0) := integrableOn_r2_fsG0R
    have hg : IntegrableOn (fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)) (Set.Ioi 0) :=
      (MeasureTheory.integrableOn_congr_fun
        (f := fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r)
        (g := fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
        (fun r _ => by ring) measurableSet_Ioi).mp (hg1.sub hg0)
    have hgi : IntegrableOn (fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
        (Set.Ioc (4:ℝ) K.T) :=
      hg.mono_set (fun r hr => lt_trans (by norm_num) hr.1)
    set Cc : ℝ := 2500 * (c1 + εT * c2) + (3 / 2) * (8 * Real.pi) ^ 2 * K.η with hCc
    have hC0 : 0 ≤ Cc := by
      rw [hCc]; nlinarith [K.ηnn, hS0]
    have hmaj : IntegrableOn (fun r : ℝ => Cc / r) (Set.Ioc (4:ℝ) K.T) := by
      refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioc (4:ℝ) K.T)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_ (Cc / 4) ?_
      · exact (measurable_const.div measurable_id).aestronglyMeasurable.restrict
      · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun r hr => ?_)
        have hr4 : (4:ℝ) ≤ r := hr.1.le
        have hr0 : 0 < r := by linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hC0 hr0.le)]
        exact div_le_div_of_nonneg_left hC0 (by norm_num) hr4
    have hpt : ∀ r ∈ Set.Ioc (4:ℝ) K.T, r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r) ≤ Cc / r := by
      intro r hr
      have hr4 : 4 ≤ r := hr.1.le
      have hrT : r ≤ K.T := hr.2
      have h1 := reg_far_pointwise K h hr4 hrT
      have h2 : 2500 * (c1 + εT * c2) / r + (3 / 2) * (8 * Real.pi) ^ 2 * K.η / r
          = (2500 * (c1 + εT * c2) + (3 / 2) * (8 * Real.pi) ^ 2 * K.η) / r := by ring
      rw [hCc]
      linarith [h1, h2.le]
    have hmono := MeasureTheory.setIntegral_mono_on hgi hmaj measurableSet_Ioc hpt
    have hInt_inv : ∫ r in Set.Ioc (4:ℝ) K.T, (1 / r : ℝ) ≤ Real.log K.T :=
      integral_Ioc_inv_le_log (by norm_num) h.hT1
    have hIntmaj : ∫ r in Set.Ioc (4:ℝ) K.T, Cc / r
        = Cc * ∫ r in Set.Ioc (4:ℝ) K.T, (1 / r : ℝ) := by
      rw [show (fun r : ℝ => Cc / r) = fun r => Cc * (1 / r) from funext (fun r => by ring)]
      exact MeasureTheory.integral_const_mul _ _
    have hlog0 : 0 ≤ Real.log K.T := Real.log_nonneg h.hT1
    -- `η log T ≤ ε/(8π)²`
    have hηlog : K.η * Real.log K.T ≤ eps / (8 * Real.pi) ^ 2 := by
      have h0' : Real.log K.T / K.T ≤ eps / (K.B + 8 * Real.pi) ^ 2 := by
        rw [div_le_div_iff₀ hTpos (by nlinarith [K.Bnn, Real.pi_pos])]
        have h1 := h.hEpsTlog
        rw [← hepsdef, div_le_iff₀ hTpos] at h1
        linarith [h1]
      have h2 : K.η * Real.log K.T = (K.η * K.T) * (Real.log K.T / K.T) := by
        field_simp
      rw [h2]
      have h3 : K.η * K.T * (Real.log K.T / K.T) ≤ 1 * (eps / (K.B + 8 * Real.pi) ^ 2) :=
        mul_le_mul h.hηT h0' (div_nonneg hlog0 hTpos.le) (by norm_num)
      have h4 : eps / (K.B + 8 * Real.pi) ^ 2 ≤ eps / (8 * Real.pi) ^ 2 := by
        refine div_le_div_of_nonneg_left hεnn (by positivity) ?_
        nlinarith [K.Bnn, Real.pi_pos]
      linarith [h3, h4]
    have hE : (c1 + εT * c2) * Real.log K.T ≤ eps := by
      rw [hepsdef]; exact h.hEpsLogT
    have hCc_bound : Cc * Real.log K.T ≤ 2750 * eps := by
      have h1 : 2500 * ((c1 + εT * c2) * Real.log K.T) ≤ 2500 * eps :=
        mul_le_mul_of_nonneg_left hE (by norm_num)
      have h2 : (3 / 2) * (8 * Real.pi) ^ 2 * (K.η * Real.log K.T) ≤ (3 / 2) * eps := by
        have hh := mul_le_mul_of_nonneg_left hηlog
          (by positivity : (0:ℝ) ≤ (3 / 2) * (8 * Real.pi) ^ 2)
        have h6 : (3 / 2) * (8 * Real.pi) ^ 2 * (eps / (8 * Real.pi) ^ 2) = (3 / 2) * eps := by
          field_simp
        linarith [hh, h6.le]
      rw [hCc]
      linarith [h1, h2, hεnn]
    have hbound : ∫ r in Set.Ioc (4:ℝ) K.T, Cc / r ≤ 2750 * eps := by
      rw [hIntmaj]
      have h1 : Cc * ∫ r in Set.Ioc (4:ℝ) K.T, (1 / r : ℝ) ≤ Cc * Real.log K.T :=
        mul_le_mul_of_nonneg_left hInt_inv hC0
      linarith [h1, hCc_bound]
    linarith [hmono, hbound]

end Work.BoseB6Est
