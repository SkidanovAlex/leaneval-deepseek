import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Bog2Mode
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — definitions and conventions

FS §10 `thm:BogHamDiag`, App. `thm:bogolubov-complete`, `lem:BogIntegral`:
the Bogoliubov diagonalisation and the lattice sum converging to `128/(15√π)`
with explicit errors.

This module fixes the vocabulary of the chapter.  Everything above imports it.

## 1. The pair-mode (two-mode) Bogoliubov data

For one mode pair with diagonal coefficient `𝒜` and pairing coefficient `ℬ`
(FS hypotheses: `0 < 𝒜` and either `|ℬ| < 𝒜` or `ℬ = 𝒜`; here always
`0 < 𝒜 + ℬ`):

* `bogDD 𝒜 ℬ      = (𝒜 + √(𝒜²−ℬ²))/2`   (FS's `𝒟`);
* `bogAlphaP 𝒜 ℬ  = ℬ/(𝒜 + √(𝒜²−ℬ²))`   (FS's `α`);
* `bogZeroPoint`  = `𝒜 − √(𝒜²−ℬ²)`       (FS's zero-point constant, `= 2𝒟α²`);
* `bogKappaErr`   = `2κ²/(𝒜+ℬ)`          (FS's κ-term error).

## 2. The Bogoliubov model bracket

`lhyFun c` is the (radial) Bogoliubov model integrand of `lem:BogIntegral`

    k ↦ (‖k‖²+c) − √((‖k‖²+c)² − c²) − c²/(2‖k‖²)   on ℝ³,

`lhyR3 c` its transport to `Fin 3 → ℝ` along the Euclidean norm `eucNorm3`,
and `lhyRad c` its radial form `r ↦ (r²+c) − √((r²+c)²−c²) − c²/(2r²)`.

Its integral is the object of `lem:BogIntegral` (`Submission.LhyIntegral`,
`Work.BoseBox.bog_model_integral`) and carries the sharp constant
`lhySharp = 128/(15√π)`; with the FS prefactor `−(1/2)(2π)⁻³` the coefficient
is `lhyCoeff = 4π·128/(15√π)` (FS eq:BogIntegral's `4π(128/(15√π))ρ_z²a√(ρ_z a³)ℓ³`).

## 3. The mode lattice

The modes of the small box lie on the lattice `δ·(k − N/2)`, `k : Fin 3 → Fin N`
of mesh `δ`; `δ = meshD n = 2π/(n+1)` is FS's dimensionless mesh
`2π/(ℓ√(ρ_z a))` and `gridD n = (n+1)²` the number of points per coordinate.
`latticeSum c δ n` is the *dimensionless* mode sum `Σ_k lhyRad-like bracket`,
the object of FS's `(2π)⁻³ℓ³∫(𝒜−√(𝒜²−ℬ²))dk` in the variables `k = √(ρ_z a)t`
(so that `(2π)⁻³ℓ³(ρ_z a)^{3/2}δ³ = 1`).  `latticeMeshErr c n` is the explicit
Riemann/truncation error of `Work.BoseBox.latticeErr`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Pair-mode Bogoliubov data -/

/-- FS's `𝒟 = (𝒜 + √(𝒜²−ℬ²))/2`. -/
def bogDD (A B : ℝ) : ℝ := (A + Real.sqrt (A ^ 2 - B ^ 2)) / 2

/-- FS's `α = ℬ/(𝒜 + √(𝒜²−ℬ²))` (`= ℬ⁻¹(𝒜−√(𝒜²−ℬ²))` when `ℬ ≠ 0`). -/
def bogAlphaP (A B : ℝ) : ℝ := B / (A + Real.sqrt (A ^ 2 - B ^ 2))

/-- The zero-point constant `𝒜 − √(𝒜²−ℬ²)` of one mode pair. -/
def bogZeroPoint (A B : ℝ) : ℝ := A - Real.sqrt (A ^ 2 - B ^ 2)

/-- The κ-term error `2κ²/(𝒜+ℬ)` of one mode pair (FS `eq:BogIdentity`). -/
def bogKappaErr (A B kappa : ℝ) : ℝ := 2 * kappa ^ 2 / (A + B)

/-- FS's c-number shift `c₀ = 2κ/(𝒜+ℬ+√(𝒜²−ℬ²))` completing the square. -/
def bogShift (A B kappa : ℝ) : ℝ := 2 * kappa / (A + B + Real.sqrt (A ^ 2 - B ^ 2))

/-! ## 2. The model bracket and the sharp constants -/

/-- The sharp Lee–Huang–Yang constant `128/(15√π)`. -/
def lhySharp : ℝ := 128 / (15 * Real.sqrt Real.pi)

/-- The FS-normalised LHY coefficient `4π·128/(15√π)` of `eq:BogIntegral`. -/
def lhyCoeff : ℝ := 4 * Real.pi * lhySharp

/-- The Bogoliubov model integrand on `ℝ³`. -/
def lhyFun (c : ℝ) (k : ℝ³) : ℝ :=
  (‖k‖ ^ 2 + c) - Real.sqrt ((‖k‖ ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * ‖k‖ ^ 2)

/-- The radial Bogoliubov model bracket (FS `lem:BogIntegral`'s integrand). -/
def lhyRad (c r : ℝ) : ℝ :=
  (r ^ 2 + c) - Real.sqrt ((r ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * r ^ 2)

/-- `lhyFun` transported to `Fin 3 → ℝ` along the Euclidean norm `eucNorm3`
(the form in which the mode-lattice sums are taken). -/
def lhyR3 (c : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (Submission.BoseGases.eucNorm3 x ^ 2 + c)
    - Real.sqrt ((Submission.BoseGases.eucNorm3 x ^ 2 + c) ^ 2 - c ^ 2)
    - c ^ 2 / (2 * Submission.BoseGases.eucNorm3 x ^ 2)

/-! ## 3. The mode lattice -/

/-- FS's dimensionless mode-lattice mesh `2π/(n+1)`. -/
def meshD (n : ℕ) : ℝ := 2 * Real.pi / ((n : ℝ) + 1)

/-- The number of lattice points per coordinate. -/
def gridD (n : ℕ) : ℕ := (n + 1) * (n + 1)

/-- The dimensionless mode sum `Σ_k bracket` of the Bogoliubov zero point:
`Σ_{k : Fin 3 → Fin (gridD n)} lhyR3 c (meshD n · (k − gridD n / 2))`. -/
def latticeSum (c : ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin 3 → Fin (gridD n),
    lhyR3 c (Work.BoseBox.latticeCenter (meshD n) (gridD n) k)

/-- The explicit Riemann/truncation error of the lattice approximation. -/
def latticeMeshErr (c : ℝ) (n : ℕ) : ℝ :=
  512 * Real.pi * Real.sqrt 3 * c * (meshD n) ^ 3
    + 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (meshD n)
    + 128 * Real.pi * Real.sqrt 3 * c ^ 2 * (meshD n) * Real.log (gridD n)
    + 4 * c ^ 3 / ((n : ℝ) + 1)

/-- The value of the dimensionless model integral (FS `lem:BogIntegral`,
`I_1'`'s limit), i.e. `−∫_{ℝ³}` bracket `= c^{5/2}·64π/(15√2)`. -/
def lhyValue (c : ℝ) : ℝ := c ^ (5 / 2 : ℝ) * (64 * Real.pi / (15 * Real.sqrt 2))

/-! ## 4. FS's error `ε(μ,ρ_z)` of `eq:LebesgueError-Total`

`ε(μ,ρ_z) = (μa)^{1/4}√R + ε_T + (K_ℓs)⁻¹(1 + log d⁻¹ + log(K_ℓds/(μa³)^{1/2}))
            + ε_T(K_ℓds)⁻¹(1 + log(K_ℓds/(μa³)^{1/2}))`. -/

/-- FS's `eq:LebesgueError-Total` error of `lem:BogIntegral`. -/
def lhyEps (a R eT Kl s d mu : ℝ) : ℝ :=
  (mu * a) ^ (1 / 4 : ℝ) * Real.sqrt R + eT
    + (Kl * s)⁻¹ * (1 + Real.log d⁻¹ + Real.log (Kl * d * s / (mu * a ^ 3) ^ (1 / 2 : ℝ)))
    + eT * (Kl * d * s)⁻¹
        * (1 + Real.log (Kl * d * s / (mu * a ^ 3) ^ (1 / 2 : ℝ)))

/-! ## 5. The definitions agree with the corpus's `Bog2Mode` data -/

lemma bogDD_eq_bogD (A B : ℝ) : bogDD A B = Submission.BoseGases.bogD A B := rfl

lemma bogAlphaP_eq_bogAlpha (A B : ℝ) :
    bogAlphaP A B = Submission.BoseGases.bogAlpha A B := rfl

lemma bogZeroPoint_eq (A B : ℝ) :
    bogZeroPoint A B = A - Submission.BoseGases.bogS A B := rfl

lemma bogKappaErr_eq (A B L : ℝ) : bogKappaErr A B L = 2 * L ^ 2 / (A + B) := rfl

lemma bogShift_eq (A B κ : ℝ) :
    bogShift A B κ = 2 * κ / (A + B + Submission.BoseGases.bogS A B) := rfl

/-! ## 6. Elementary API -/

lemma lhySharp_pos : 0 < lhySharp := by
  have h : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  unfold lhySharp
  positivity

lemma lhySharp_nonneg : 0 ≤ lhySharp := lhySharp_pos.le

lemma lhyCoeff_eq : lhyCoeff = 4 * Real.pi * (128 / (15 * Real.sqrt Real.pi)) := rfl

lemma lhyCoeff_pos : 0 < lhyCoeff := by
  unfold lhyCoeff
  exact mul_pos (by positivity) lhySharp_pos

/-- `B² ≤ A²` from `|B| ≤ A`. -/
lemma sq_le_sq_of_abs_le {A B : ℝ} (hB : |B| ≤ A) : B ^ 2 ≤ A ^ 2 := by
  have h1 : B ^ 2 = |B| ^ 2 := (sq_abs B).symm
  rw [h1]
  exact pow_le_pow_left₀ (abs_nonneg B) hB 2

/-- The zero point is nonnegative: `0 ≤ 𝒜 − √(𝒜²−ℬ²)` for `|ℬ| ≤ 𝒜`. -/
lemma bogZeroPoint_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : |B| ≤ A) :
    0 ≤ bogZeroPoint A B := by
  have h1 : B ^ 2 ≤ A ^ 2 := sq_le_sq_of_abs_le hB
  have h2 : Real.sqrt (A ^ 2 - B ^ 2) ≤ A := by
    calc Real.sqrt (A ^ 2 - B ^ 2) ≤ Real.sqrt (A ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg B])
      _ = A := Real.sqrt_sq hA
  unfold bogZeroPoint
  linarith

/-- The zero point is at most `ℬ²/𝒜`: `𝒜 − √(𝒜²−ℬ²) = ℬ²/(𝒜+√(𝒜²−ℬ²)) ≤ ℬ²/𝒜`. -/
lemma bogZeroPoint_le {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    bogZeroPoint A B ≤ B ^ 2 / A := by
  set s := Real.sqrt (A ^ 2 - B ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = A ^ 2 - B ^ 2 := by
    rw [hsdef, Real.sq_sqrt]
    linarith [sq_le_sq_of_abs_le hB]
  have hid : bogZeroPoint A B * (A + s) = B ^ 2 := by
    unfold bogZeroPoint
    rw [← hsdef, sub_mul]
    nlinarith [hs2]
  have hz0 : 0 ≤ bogZeroPoint A B := bogZeroPoint_nonneg hA.le hB
  rw [le_div_iff₀ hA]
  calc bogZeroPoint A B * A ≤ bogZeroPoint A B * (A + s) := by nlinarith [hs0, hz0]
    _ = B ^ 2 := hid

/-- `𝒟 > 0` whenever `0 < 𝒜`. -/
lemma bogDD_pos {A B : ℝ} (hA : 0 < A) : 0 < bogDD A B := by
  have : 0 ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_nonneg _
  unfold bogDD
  linarith

end Work.BoseB6
