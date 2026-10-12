import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB6.lhyValue_eight_pi
import Submission.Work.BoseBox.bog_model_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — FS §10 `lem:BogIntegral`: the zero-point integral

`lem:BogIntegral` bounds the (improperly convergent) Bogoliubov zero-point
integral

    −½(2π)⁻³ℓ³ ∫ (𝒜(k) − √(𝒜(k)²−ℬ(k)²)) dk

below by `−(ĝω(0)/2)ρ_z²ℓ³ + 4π·(128/(15√π))·ρ_z²a√(ρ_z a³)ℓ³` minus errors.
The proof has three layers.

1. **The value.**  With `𝒜(k) = τ(k) + ρ_zŴ₁(k)`, `ℬ(k) = ρ_zŴ₁(k)` and the
   scaling `k = √(ρ_z a)t` one gets `𝒜 = ρ_z a(τ̃+β)`, `ℬ = ρ_z aβ` with
   `β(t) = a⁻¹Ŵ₁(√(ρ_z a)t)`, so the integral splits (FS `LHYIntegral1`) as

     ∫(𝒜−√(𝒜²−ℬ²))dk = (ρ_z a)^{5/2} I₁ + ρ_z²∫Ŵ₁(k)²/(2k²)dk,

   with `I₁ = ∫_{ℝ³}[α − √(α²−β²) − β²/(2t²)]dt`, `α = τ̃+β`.  The *model*
   value `β = 8π`, `τ̃ = t²` of `I₁` is the corpus's Bogoliubov integral
   `Work.BoseB6.integral_lhyFun` / `Submission.LhyIntegral.lhy_model_integral_fs`:
   `∫ lhyFun c = −lhyValue c`, so `I₁ ≈ −lhyValue (8π)` and

     −½(2π)⁻³(ρ_z a)^{5/2}·(−lhyValue (8π)) = 4π·lhySharp.

   The second term is FS `eq:I2-integral`, the *mass* term, giving
   `−(ĝω(0)/2)ρ_z²ℓ³` after the `(2π)⁻³ℓ³` prefactor.
2. **The error.**  FS write `I₁ = I₁' + I₁''` (`eq:SplitIntegrals`): `I₁'` is the
   part converted to the model integral by dominated convergence
   (`eq:LebesgueError`, error `(μa)^{1/4}√R + ε_T + (K_ℓs)⁻¹`), and `I₁''` is the
   logarithmically estimated remainder (`eq:Logarithm`, error
   `ε_T(K_ℓds)⁻¹ + (K_ℓs)⁻¹(1+log(d⁻¹)+log(K_ℓds/(μa³)^{1/2}))`).  Their sum is
   `lhyEps` (`eq:LebesgueError-Total`).
3. **The lattice.**  At the mode lattice the integral is a Riemann sum; the
   explicit error is node B6's `Work.BoseB6.latticeMeshErr`.

`lem_bogIntegral` below is layer 1+2 in the form "given the error estimate
`I₁ ≤ −lhyValue(8π) + ε`, the FS display follows"; `lhyEps` is the FS value of
`ε`.  The lattice version of the *model* integral (with the explicit
`latticeMeshErr`) is node B6's `Work.BoseB6.Lattice` chapter.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The model integral and its value -/

/-- The model Bogoliubov integral is minus `lhyValue`: `∫_{ℝ³}lhyFun c = −lhyValue c`
(the corpus's delivered value, `Work.BoseBox.bog_model_integral`,
`Submission.LhyIntegral`). -/
theorem integral_lhyFun {c : ℝ} (hc : 0 < c) :
    (∫ k : ℝ³, lhyFun c k) = -lhyValue c := by
  have h : (∫ k : ℝ³, lhyFun c k) = -(c ^ (5 / 2 : ℝ)) * (64 * Real.pi / (15 * Real.sqrt 2)) := by
    simpa only [lhyFun] using Work.BoseBox.bog_model_integral (c := c) hc
  rw [h]
  simp only [lhyValue]
  ring

/-- **FS `eq:SplitIntegrals`**: the algebraic identity at the heart of
`lem:BogIntegral`'s proof,
`I₁ = I₁' + I₁''` with `α = τ+β`:

  `α − √(α²−β²) − β²/(2t²) = [α − β²/(2α) − √(α²−β²) − β³/(2t²α)] + (β²/2)(t²−τ)/(t²α)`. -/
theorem lhyRad_split {τ β t : ℝ} (hα : τ + β ≠ 0) (ht : t ≠ 0) :
    (τ + β) - Real.sqrt ((τ + β) ^ 2 - β ^ 2) - β ^ 2 / (2 * t ^ 2)
      = ((τ + β) - β ^ 2 / (2 * (τ + β)) - Real.sqrt ((τ + β) ^ 2 - β ^ 2) -
            β ^ 3 / (2 * t ^ 2 * (τ + β)))
        + (β ^ 2 / 2) * (t ^ 2 - τ) / (t ^ 2 * (τ + β)) := by
  field_simp
  ring

/-! ## 2. FS `lem:BogIntegral`, the `I₁` display -/

/-- **FS `lem:BogIntegral`** (the `I₁` part, `eq:BogIntegral` with the mass term
`)` carried separately): if the Bogoliubov zero-point integral in the scaled
variables satisfies FS `eq:LebesgueError-Total`, i.e.

  `I₁ ≤ −lhyValue(8π) + ε`,   `ε = lhyEps a R ε_T K_ℓ s d μ`,

then the physical zero-point term is bounded below by the sharp LHY term minus
the corresponding error:

  `−½(2π)⁻³ℓ³ρ_z²a√(ρ_z a³)·I₁ ≥ 4π·(128/(15√π))·ρ_z²a√(ρ_z a³)ℓ³
      − ½(2π)⁻³ℓ³ρ_z²a√(ρ_z a³)·ε`.

`hconst` is the numerical identity `½(2π)⁻³lhyValue(8π) = 4π·lhySharp`. -/
theorem lem_bogIntegral {ρz a ℓ I1 ε : ℝ} (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * lhyValue (8 * Real.pi) =
      4 * Real.pi * lhySharp)
    (hI1 : I1 ≤ -lhyValue (8 * Real.pi) + ε) :
    4 * Real.pi * lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3
      - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ε
      ≤ -(1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * I1 := by
  set X := ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    have h : 0 ≤ ρz * a ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg (sq_nonneg ρz) ha.le) (Real.sqrt_nonneg _)
  have hCnn : 0 ≤ (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * X := by
    have h1 : (0 : ℝ) ≤ (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) := by positivity
    have h2 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) hXnn
  have h' : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * lhyValue (8 * Real.pi) * X * ℓ ^ 3 =
      4 * Real.pi * lhySharp * X * ℓ ^ 3 := by rw [hconst]
  have hc : 4 * Real.pi * lhySharp * X * ℓ ^ 3 =
      (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * X * lhyValue (8 * Real.pi) := by
    rw [← h']
    ring
  have h1 : -(1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * X * I1
      ≥ (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * X * lhyValue (8 * Real.pi)
        - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * X * ε := by
    have h := mul_le_mul_of_nonneg_left hI1 hCnn
    nlinarith [h]
  rw [hX] at hc h1 ⊢
  nlinarith [hc, h1]


/-- The corpus's delivered sharp-constant evaluation, in chapter vocabulary:
`∫_{ℝ³}lhyFun (8π) = −64π⁴·(128/(15√π))` (FS's `I₁'` value, i.e.
`Submission.LhyIntegral.lhy_model_integral_fs`). -/
theorem integral_lhyFun_eight_pi :
    (∫ k : ℝ³, lhyFun (8 * Real.pi) k) = -64 * Real.pi ^ 4 * lhySharp := by
  rw [integral_lhyFun (by positivity), lhyValue_eight_pi]
  ring

/-- **FS `lem:BogIntegral` with the error instantiated at `lhyEps`**
(`eq:LebesgueError-Total`): the `I₁` input is `I₁ ≤ −lhyValue(8π) + C·lhyEps …`,
and the conclusion carries `C·lhyEps` as the error. -/
theorem lem_bogIntegral_lhyEps {ρz a ℓ R Kl s d εT μ C I1 : ℝ} (hρz : 0 < ρz) (ha : 0 < a)
    (hℓ : 0 < ℓ)
    (hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * lhyValue (8 * Real.pi) =
      4 * Real.pi * lhySharp)
    (hI1 : I1 ≤ -lhyValue (8 * Real.pi) + C * lhyEps a R εT Kl s d μ) :
    4 * Real.pi * lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3
      - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) *
          (C * lhyEps a R εT Kl s d μ)
      ≤ -(1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * I1 :=
  lem_bogIntegral hρz ha hℓ hconst hI1

end Work.BoseB6
