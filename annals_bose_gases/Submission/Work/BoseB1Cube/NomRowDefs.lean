import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NominalPerBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.NomRowDefs` — the nominal per-box demand row as a *function*,
# the state-free box data, and the pure-real arithmetic of FS's `n = m n' + n''` descent

No analysis in this module: vocabulary plus scalar arithmetic.

* `nomGamma` — FS's error bracket `Γ = (R/(ℓd))² + K_B³(μ a³)^{1/2}`;
* `nomV`, `nomW`, `nomChi`, `nomE` — the state-free box data `|B(u)|`, `∬w_{1,B}`, `∫χ_B²` and the
  error row `C(μ²aΓχ + μa)`;
* `nomRow` — the left-hand side of `PerBoxFNom` as a function of an *arbitrary* `ContDiff`
  function `Ψ : X n → ℝ` (denormalised: every term carries `∫_{abox}Ψ²`), so that a per-size bound
  can be consumed by FS's descent `Work.BoseB1Cube.sbWordCube_descent_atSizes`, whose hypotheses
  are quantified over `ContDiff` states (the slices of a big state are *not* symmetric, hence not
  `BoxState`s);
* `nomDescentArith`, `nomLinArith` — the two scalar steps of FS `final_v2.tex` l.4000–4045.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- FS's error bracket `Γ = (R/(ℓ d))² + K_B³(μ (a v)³)^{1/2}` at the parameters of `μ`. -/
noncomputable def nomGamma (v : E3 → ℝ) (R μ : ℝ) : ℝ :=
  (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
    + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)

/-- The sliding box volume `V = |B(u)|`. -/
noncomputable def nomV (v : E3 → ℝ) (μ : ℝ) (u : E3) : ℝ :=
  boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u

/-- The localised `w₁`-box mass `W = ∬w_{1,B}(u)`. -/
noncomputable def nomW (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) : ℝ :=
  w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u

/-- The window mass `χ = ∫χ_B²`. -/
noncomputable def nomChi (v : E3 → ℝ) (μ : ℝ) (u : E3) : ℝ :=
  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u

/-- The error row `E = C(μ²aΓχ + μa)` of the demand at the *box* parameter `μ`. -/
noncomputable def nomE (v : E3 → ℝ) (R C μ : ℝ) (u : E3) : ℝ :=
  C * (μ ^ 2 * (a v) * nomGamma v R μ * nomChi v μ u + μ * (a v))

/-- The error row of the demand with a *separate* chemical-potential slot: `C(μp²aΓ(μ)χ(μ) + μp a)`.
The **box** data (`Γ`, `χ`, the box, the window) stay at the parameter block `μ`; only the
chemical-potential slot `μp` moves — FS's `m(u)μ` substitution (`PerBoxFNom`'s error row carries
`μp²` and `μp`, but `R/λ₁`, `K_B` and `∫χ_B²` at the block `μ`).  At `μp = μ` it is `nomE`. -/
noncomputable def nomESlot (v : E3 → ℝ) (R C : ℝ) (μ μp : ℝ) (u : E3) : ℝ :=
  C * (μp ^ 2 * (a v) * nomGamma v R μ * nomChi v μ u + μp * (a v))

/-- **The per-box demand row of FS `thm:smallbox` at the sliding box, in the nominal
(indicator-count) spelling, as a function of the state.**  Denormalised (every term carries the
factor `∫_{abox}Ψ²`), hence homogeneous of degree two and meaningful for an arbitrary `ContDiff`
function `Ψ : X n → ℝ`. -/
noncomputable def nomRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C μp μ : ℝ) (n : ℕ)
    (u : E3) (Ψ : X n → ℝ) : ℝ :=
  c₁ * (nomW v h μ u * psiWeight 1 μp ((n : ℝ) / nomV v μ u))
      * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2)
    - (1 / 2) * μp ^ 2 * nomW v h μ u
      * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2)
    - nomESlot v R C μ μp u * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2)

/-- `nomRow` in factored form: the bracket times the `L²`-mass. -/
theorem nomRow_eq (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C μp μ : ℝ) (n : ℕ) (u : E3)
    (Ψ : X n → ℝ) :
    nomRow v h R c₁ C μp μ n u Ψ
      = (c₁ * (nomW v h μ u * psiWeight 1 μp ((n : ℝ) / nomV v μ u))
          - (1 / 2) * μp ^ 2 * nomW v h μ u - nomESlot v R C μ μp u)
        * (∫ x in abox n (sideAt μ (a v)), (Ψ x) ^ 2) := by
  rw [nomRow]
  ring

/-- `ψ(1,μ,t) = μ(t−μ)²/(μ+t)`. -/
theorem psiWeight_one_eq {μ t : ℝ} (hμ : 0 < μ) :
    psiWeight 1 μ t = μ * (t - μ) ^ 2 / (μ + t) := by
  have h1 : 1 + t * μ⁻¹ = (μ + t) / μ := by
    field_simp
  rw [psiWeight, one_mul, h1, div_div_eq_mul_div]
  ring

/-! ## The pure-real arithmetic of the descent

FS `final_v2.tex` l.4000–4045.  With `n = m n' + n''`, `n'' < n' < (C_n+1)μ|B|`, `C_n ≥ 3`, the
two per-size bounds

    (1/18)·μ·(n'/|B|)·W·‖Ψ‖² ≤ sbWord Ψ            (the `m` blocks),
    (¼((n''/|B|) − μ)² − ½μ²)·W·‖Ψ‖² − E·‖Ψ‖² ≤ sbWord Ψ   (the last block),

give the theorem's row at `t = n/|B|`:

    c₁·W·ψ(1,μ,t)·‖Ψ‖² − ½μ²W‖Ψ‖² − E‖Ψ‖² ≤ sbWord Ψ ,

as soon as `c₁ ≤ 1/36`. -/

/-- **The scalar core of FS's descent** (`final_v2.tex` l.4000–4045).  With `s₁ = n'/|B| ≥ C_n μ`
(the size of a block), `s₂ = n''/|B| ∈ [0, (C_n+1)μ]` and `t = m s₁ + s₂` (the full density),

    c₁·ψ(1,μ,t) ≤ (1/18)·μ·(m s₁) + ¼(s₂ − μ)²        for `3 ≤ C_n`, `c₁ ≤ 1/36` . -/
theorem nomDescentArith {μ s₁ s₂ t c₁ : ℝ} (hμ : 0 < μ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 36)
    {m : ℕ} (hm : 1 ≤ m) {Cn : ℝ} (hCn : 3 ≤ Cn)
    (hs1 : Cn * μ ≤ s₁) (hs2 : 0 ≤ s₂) (hs2' : s₂ ≤ (Cn + 1) * μ)
    (ht : t = (m : ℝ) * s₁ + s₂) :
    c₁ * psiWeight 1 μ t ≤ (1 / 18) * μ * ((m : ℝ) * s₁) + (1 / 4) * (s₂ - μ) ^ 2 := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1nn : 0 ≤ s₁ := le_trans (by nlinarith [hμ, hCn]) hs1
  have hTge : Cn * μ ≤ (m : ℝ) * s₁ := by
    have h : s₁ ≤ (m : ℝ) * s₁ := by nlinarith [hs1nn, hmr]
    linarith
  have hT3 : 3 * μ ≤ (m : ℝ) * s₁ := by nlinarith [hTge, hCn, hμ]
  have hTnn : 0 ≤ (m : ℝ) * s₁ := le_trans (by nlinarith [hμ]) hT3
  have htge : 0 ≤ t := by
    rw [ht]; exact add_nonneg hTnn hs2
  have hpos : 0 < 1 + t * μ⁻¹ := by
    have h : 0 ≤ t * μ⁻¹ := mul_nonneg htge (inv_nonneg.mpr hμ.le)
    linarith
  have hpsi : psiWeight 1 μ t ≤ 2 * μ * ((m : ℝ) * s₁) := by
    rw [psiWeight]
    rw [div_le_iff₀ hpos]
    have hden : 2 * μ * ((m : ℝ) * s₁) * (1 + t * μ⁻¹)
        = 2 * ((m : ℝ) * s₁) * (μ + t) := by
      field_simp
    rw [hden]
    nlinarith [ht, hTge, hCn, hs2, hs2', hμ, sq_nonneg (s₂ - μ), sq_nonneg ((m:ℝ)*s₁ - Cn*μ)]
  calc c₁ * psiWeight 1 μ t
      ≤ c₁ * (2 * μ * ((m : ℝ) * s₁)) := mul_le_mul_of_nonneg_left hpsi hc₁.le
    _ ≤ (1 / 18) * μ * ((m : ℝ) * s₁) + (1 / 4) * (s₂ - μ) ^ 2 := by
        have h1 : c₁ * (2 * μ * ((m : ℝ) * s₁)) ≤ (1 / 36) * (2 * μ * ((m : ℝ) * s₁)) :=
          mul_le_mul_of_nonneg_right hc₁' (by positivity)
        nlinarith [h1, sq_nonneg (s₂ - μ)]

/-- **The scalar step `Sq`-form ⟹ linear form** (FS l.4019–4026).  `(1/18)μs ≤ (1/8)(s−μ)²` for
`3μ ≤ s`, so the linear supply `(1/18)μsW` follows from the `Sq`-row at the same size once
`E + ½μ²W ≤ (1/8)(s−μ)²W`. -/
theorem nomLinArith {μ s W E : ℝ} (hμ : 0 < μ) (hW : 0 ≤ W)
    (hs3 : 3 * μ ≤ s) (hE : E + (1 / 2) * μ ^ 2 * W ≤ (1 / 8) * (s - μ) ^ 2 * W) :
    (1 / 18) * μ * s * W + (1 / 2) * μ ^ 2 * W + E ≤ (1 / 4) * (s - μ) ^ 2 * W := by
  have hkey : (1 / 18) * μ * s ≤ (1 / 8) * (s - μ) ^ 2 := by nlinarith [hs3, hμ]
  have := mul_le_mul_of_nonneg_right hkey hW
  linarith

end Work.BoseB1Cube
