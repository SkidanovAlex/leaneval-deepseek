import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.psiSc_bulk_le
import Submission.Work.BoseBogFS.tauScRad_ge_eighth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.psiScTailPointwise` — the pointwise tail bound at a bare `β`-bound

The target is the "tail" row of FS `lem:BogIntegral` in its **kernel-free** form: for the
scaled clean bracket

`psiSc v h ρ μ t = 𝒵(τ_s + β, β) − β²/(2‖t‖²)`,   `τ_s = tauScRad v ρ μ ‖t‖`, `β = betaSc v h ρ μ t`,

the only inputs about the pairing coefficient are the two *bare* bounds
`|β| ≤ B` and `16 B ≤ ‖t‖²` — no FS kernel `B_β + η‖t‖`, no Lipschitz constant `η`, appears.
The conclusion is the three-term bound

`psiSc ≤ 48κβ²/r³ + 16Bβ²/r⁴ + 128B²β²/r⁶`,   `r = ‖t‖`, `κ = bogKappa v ρ μ`.

## The mathematics

Write `r = ‖t‖`, `b = β`, `τ = τ_{s,r}`, `A = τ + b`, `s = √(A²−b²)`, `L = A + s`.  The two
identities `A − s = b²/L` and `2r² − L = 2(r²−A) + b²/L` give

`psiSc = A − s − b²/(2r²) = b²(2r² − L)/(2Lr²)`,

so the whole claim is equivalent (for `b ≠ 0`) to

`2r² ≤ L·Θ`,   `Θ = 1 + 96κ/r + 32B/r² + 256B²/r⁴ = 96κ/r + (1 + 16B/r²)²`.

Three inputs now close it:

* **the kinetic symbol is not small.**  `h3 : 4c₁ ≤ r` with `ε_T ≤ 1/2` and the profile bound
  `τ̃(u) ≥ (max 0 (u−2))²` (from `exists_tauProf`, via `sq_mul_tauProf_ge`) give
  `τ_s ≥ (1−ε_T)c₁²τ̃(r/c₁) ≥ (1−ε_T)(r/2)² ≥ r²/8`, i.e. `σ := τ/r² ∈ [1/8,1]`
  (`tauScRad_le_sq` is the upper end).  This is the *only* place the parameter block is used, and
  it does not need `μ > 0`, `c₂ > 0`, or the relation `ε_T = d^{23/24}`.
* **the deficit pays the `κ`-term.**  `hdef : r² − τ ≤ 3κr` gives `96κ/r ≥ 32(r²−τ)/r²`, so
  `Θ ≥ Ξ := 1 + 32(r²−τ)/r² + 32B/r² + 256B²/r⁴`.
* **the pairing term is dominated by the other two slots.**  `b ≥ −B` together with `s ≥ τ − 2B`
  (from `A² − b² = τ(τ+2b) ≥ τ(τ−2B) ≥ (τ−2B)²`) gives `L ≥ 2τ − 3B`, and `16B ≤ r²` gives
  `B/r² ≤ 1/16`.  In the dimensionless variables `x = τ/r² ∈ [1/8,1]`, `y = B/r² ∈ [0,1/16]` the
  remaining inequality is the two-variable polynomial

  `(2x − 3y)(33 − 32x + 32y + 256y²) ≥ 2`   (`poly_core`, proved by `nlinarith`),

  whose equality corners are exactly `(x,y) = (1,0)` and `(x,y) = (1/8,1/16)` — the latter being
  the configuration `τ = r²/8`, `β = −B = −r²/16`, `r² − τ = 3κr` in which **all** the constants
  of the target are simultaneously sharp.  So no step of the argument may discard slack: the
  chain `L ≥ 2τ − 3B`, `Θ ≥ Ξ` is tight precisely at that corner.

Finally `b²/L − b²/(2r²) = b²(2r²−L)/(2Lr²) ≤ b²(Θ−1)/(2r²)`, and expanding
`b²(Θ−1)/(2r²) = 48κb²/r³ + 16Bb²/r⁴ + 128B²b²/r⁶` is the right-hand side.

The degenerate case `r = 0` is separate: `16B ≤ 0` forces `β = 0`, hence `psiSc = τ − |τ| = 0`
and the right-hand side vanishes too.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The kinetic symbol is at least `r²/8`

The lower bound `r²/8 ≤ tauScRad v ρ μ r` (for `4c₁ ≤ r`, `ε_T ≤ 1/2`) is proved in the sibling
module `Submission/Work/BoseBogFS/tauScRad_ge_eighth.lean` as `Work.BoseBogFS.tauScRad_ge_eighth`:
from `tauScRad_eq` the symbol is `(1−ε_T)c₁²τ̃(r/c₁) + ε_Tc₂²τ̃(r/c₂)`, the profile bound
`τ̃(u) ≥ (max 0 (u−2))²` and `r ≥ 4c₁` give `c₁²τ̃(r/c₁) ≥ (r/2)²`, the second summand is
nonnegative (`ε_T ≥ 0`), and `1 − ε_T ≥ 1/2`. -/

/-! ## 2. The two-variable polynomial core -/

/-- **The sharp two-variable inequality**: for `x ∈ [1/8,1]`, `y ∈ [0,1/16]`,
`(2x − 3y)(33 − 32x + 32y + 256y²) ≥ 2`.  Equality holds exactly at `(x,y) = (1,0)` and at
`(x,y) = (1/8,1/16)` (the tail's sharp corner). -/
lemma poly_core {x y : ℝ} (h1 : 1 / 8 ≤ x) (h2 : x ≤ 1) (h3 : 0 ≤ y) (h4 : y ≤ 1 / 16) :
    2 ≤ (2 * x - 3 * y) * (33 - 32 * x + 32 * y + 256 * y ^ 2) := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 32), sq_nonneg (4 * x - 1),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), mul_nonneg h3 (sub_nonneg.mpr h4)]

/-! ## 3. The real core of the tail row -/

/-- **The kernel-free tail core.**  Under `τ ∈ [r²/8, r²]`, `|b| ≤ B`, `16B ≤ r²` and
`r² − τ ≤ 3κr` (`r > 0`), the clean bracket is dominated by the three-term display.  See the
module docstring for the reduction `2r² ≤ LΘ` and the sharp corner. -/
lemma psiSc_core {τ b B r κ : ℝ} (hr : 0 < r) (hτlo : r ^ 2 / 8 ≤ τ) (hτhi : τ ≤ r ^ 2)
    (hκ : 0 ≤ κ) (hdef : r ^ 2 - τ ≤ 3 * κ * r) (hB : |b| ≤ B) (hBr : 16 * B ≤ r ^ 2) :
    (τ + b) - Real.sqrt ((τ + b) ^ 2 - b ^ 2) - b ^ 2 / (2 * r ^ 2)
      ≤ 48 * κ * b ^ 2 / r ^ 3 + 16 * B * b ^ 2 / r ^ 4 + 128 * B ^ 2 * b ^ 2 / r ^ 6 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hB0 : 0 ≤ B := le_trans (abs_nonneg b) hB
  have hBle : B ≤ r ^ 2 / 16 := by linarith
  have hτ2B : 2 * B ≤ τ := by linarith
  have hτ0 : 0 ≤ τ := by nlinarith [hτlo, sq_nonneg r]
  have hτpos : 0 < τ := by nlinarith [hτlo, hr2]
  have hb_low : -B ≤ b := (abs_le.mp hB).1
  have hb_up : b ≤ B := (abs_le.mp hB).2
  have harg : 0 ≤ (τ + b) ^ 2 - b ^ 2 := by
    have h : (τ + b) ^ 2 - b ^ 2 = τ * (τ + 2 * b) := by ring
    rw [h]; exact mul_nonneg hτ0 (by linarith)
  set s : ℝ := Real.sqrt ((τ + b) ^ 2 - b ^ 2) with hsdef
  have hs_sq : s ^ 2 = (τ + b) ^ 2 - b ^ 2 := by rw [hsdef]; exact Real.sq_sqrt harg
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  set A : ℝ := τ + b with hAdef
  have hApos : 0 < A := by rw [hAdef]; linarith
  set L : ℝ := A + s with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have h5 : s ^ 2 = A ^ 2 - b ^ 2 := by rw [hAdef]; linarith [hs_sq]
  -- the identity `A - s = b²/L`
  have hAL : (A - s) * L = b ^ 2 := by rw [hLdef]; nlinarith [h5]
  have hAs : A - s = b ^ 2 / L := by
    rw [eq_div_iff (ne_of_gt hLpos)]; linarith [hAL]
  -- `s ≥ τ - 2B` and hence `L ≥ 2τ - 3B`
  have hs_ge : τ - 2 * B ≤ s := by
    rw [hsdef]
    refine (Real.le_sqrt (by linarith) harg).mpr ?_
    nlinarith [hb_low, hτ2B, hτ0]
  have hLge : 2 * τ - 3 * B ≤ L := by rw [hLdef, hAdef]; linarith
  -- the scaled polynomial, in the variables `τ/r²`, `B/r²`
  have hpoly : 2 * r ^ 2 ≤ (2 * τ - 3 * B) *
      (1 + 32 * (r ^ 2 - τ) / r ^ 2 + 32 * B / r ^ 2 + 256 * B ^ 2 / r ^ 4) := by
    have hx1 : (1 : ℝ) / 8 ≤ τ / r ^ 2 := by rw [le_div_iff₀ hr2]; linarith
    have hx2 : τ / r ^ 2 ≤ 1 := by rw [div_le_one hr2]; exact hτhi
    have hy1 : 0 ≤ B / r ^ 2 := div_nonneg hB0 hr2.le
    have hy2 : B / r ^ 2 ≤ 1 / 16 := by rw [div_le_iff₀ hr2]; linarith
    have hp := poly_core hx1 hx2 hy1 hy2
    have hid : (2 * τ - 3 * B)
          * (1 + 32 * (r ^ 2 - τ) / r ^ 2 + 32 * B / r ^ 2 + 256 * B ^ 2 / r ^ 4)
        = r ^ 2 * ((2 * (τ / r ^ 2) - 3 * (B / r ^ 2)) *
            (33 - 32 * (τ / r ^ 2) + 32 * (B / r ^ 2) + 256 * (B / r ^ 2) ^ 2)) := by
      field_simp; try ring
    rw [hid]
    nlinarith [hp, hr2]
  -- the two slots of `Θ`, and `Θ ≥ Ξ ≥ 0`
  set Θ : ℝ := 1 + 96 * κ / r + 32 * B / r ^ 2 + 256 * B ^ 2 / r ^ 4 with hΘdef
  have hΞΘ : 1 + 32 * (r ^ 2 - τ) / r ^ 2 + 32 * B / r ^ 2 + 256 * B ^ 2 / r ^ 4 ≤ Θ := by
    rw [hΘdef]
    have h1 : 32 * (r ^ 2 - τ) / r ^ 2 ≤ 96 * κ / r := by
      have h2 : 32 * (r ^ 2 - τ) / r ^ 2 ≤ 96 * κ * r / r ^ 2 :=
        div_le_div_of_nonneg_right (by linarith [hdef]) hr2.le
      have h3 : 96 * κ * r / r ^ 2 = 96 * κ / r := by field_simp
      linarith [h2, h3]
    linarith
  have hΞ0 : 0 ≤ 1 + 32 * (r ^ 2 - τ) / r ^ 2 + 32 * B / r ^ 2 + 256 * B ^ 2 / r ^ 4 := by
    have a1 : 0 ≤ 32 * (r ^ 2 - τ) / r ^ 2 := div_nonneg (by linarith [hτhi]) hr2.le
    have a2 : 0 ≤ 32 * B / r ^ 2 := div_nonneg (by linarith) hr2.le
    have a3 : 0 ≤ 256 * B ^ 2 / r ^ 4 := div_nonneg (by positivity) (by positivity)
    linarith
  have hLΘ : 2 * r ^ 2 ≤ L * Θ := by
    calc 2 * r ^ 2 ≤ (2 * τ - 3 * B)
          * (1 + 32 * (r ^ 2 - τ) / r ^ 2 + 32 * B / r ^ 2 + 256 * B ^ 2 / r ^ 4) := hpoly
      _ ≤ L * Θ := mul_le_mul hLge hΞΘ hΞ0 hLpos.le
  have hkey : 2 * r ^ 2 - L ≤ L * (Θ - 1) := by nlinarith [hLΘ]
  rw [hAs]
  have hLHS : b ^ 2 / L - b ^ 2 / (2 * r ^ 2) = b ^ 2 * (2 * r ^ 2 - L) / (2 * L * r ^ 2) := by
    field_simp; try ring
  rw [hLHS]
  have hRHS : 48 * κ * b ^ 2 / r ^ 3 + 16 * B * b ^ 2 / r ^ 4 + 128 * B ^ 2 * b ^ 2 / r ^ 6
      = b ^ 2 * (Θ - 1) / (2 * r ^ 2) := by
    rw [hΘdef]; field_simp; try ring
  rw [hRHS]
  have hstep : b ^ 2 * (2 * r ^ 2 - L) / (2 * L * r ^ 2)
      ≤ b ^ 2 * (L * (Θ - 1)) / (2 * L * r ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hkey (sq_nonneg b)
  calc b ^ 2 * (2 * r ^ 2 - L) / (2 * L * r ^ 2)
      ≤ b ^ 2 * (L * (Θ - 1)) / (2 * L * r ^ 2) := hstep
    _ = b ^ 2 * (Θ - 1) / (2 * r ^ 2) := by field_simp; try ring

/-! ## 4. The target -/

theorem psiScTailPointwise {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ρ μ B : ℝ} {t : EuclideanSpace ℝ (Fin 3)}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (hκ : 0 ≤ Work.BoseBogFS.bogKappa v ρ μ)
    (h3 : 4 * Work.BoseBogFS.bogC1 v ρ μ ≤ ‖t‖)
    (hdef : ‖t‖ ^ 2 - Work.BoseBogFS.tauScRad v ρ μ ‖t‖ ≤ 3 * Work.BoseBogFS.bogKappa v ρ μ * ‖t‖)
    (hB : |Work.BoseBogFS.betaSc v h ρ μ t| ≤ B) (hBr : 16 * B ≤ ‖t‖ ^ 2) :
    Work.BoseBogFS.psiSc v h ρ μ t
      ≤ 48 * Work.BoseBogFS.bogKappa v ρ μ * (Work.BoseBogFS.betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 3
        + 16 * B * (Work.BoseBogFS.betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 4
        + 128 * B ^ 2 * (Work.BoseBogFS.betaSc v h ρ μ t) ^ 2 / ‖t‖ ^ 6 := by
  by_cases hr : ‖t‖ = 0
  · -- the degenerate case `t = 0`
    have hB0 : B ≤ 0 := by have h := hBr; rw [hr] at h; linarith
    have hb0 : betaSc v h ρ μ t = 0 := by
      have h1 : |betaSc v h ρ μ t| = 0 := le_antisymm (le_trans hB hB0) (abs_nonneg _)
      exact abs_eq_zero.mp h1
    have hτ0 : 0 ≤ tauScRad v ρ μ ‖t‖ :=
      tauScRad_nonneg v hP heT0 (by linarith only [heT1]) _
    have hpsi0 : psiSc v h ρ μ t = 0 := by
      rw [psiSc, hb0, tauSc_eq_tauScRad]
      simp only [Work.BoseB6.bogZeroPoint, mul_zero, add_zero, sub_zero, pow_two]
      rw [Real.sqrt_mul_self hτ0]
      ring
    rw [hpsi0, hb0]
    simp
  · -- the honest case `r > 0`
    have hrpos : 0 < ‖t‖ := lt_of_le_of_ne (norm_nonneg t) (Ne.symm hr)
    have hτhi : tauScRad v ρ μ ‖t‖ ≤ ‖t‖ ^ 2 :=
      tauScRad_le_sq v hP hc1 hc2 heT0 (by linarith only [heT1]) (norm_nonneg t)
    have hτlo : ‖t‖ ^ 2 / 8 ≤ tauScRad v ρ μ ‖t‖ := tauScRad_ge_eighth hP hc1 heT0 heT1 h3
    have hpsi : psiSc v h ρ μ t = (tauScRad v ρ μ ‖t‖ + betaSc v h ρ μ t)
        - Real.sqrt ((tauScRad v ρ μ ‖t‖ + betaSc v h ρ μ t) ^ 2 - (betaSc v h ρ μ t) ^ 2)
        - (betaSc v h ρ μ t) ^ 2 / (2 * ‖t‖ ^ 2) := by
      rw [psiSc, Work.BoseB6.bogZeroPoint, tauSc_eq_tauScRad]
    rw [hpsi]
    exact psiSc_core hrpos hτlo hτhi hκ hdef hB hBr

end Work.BoseBogFS
