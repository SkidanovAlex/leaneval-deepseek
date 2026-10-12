import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.DLWire.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLWire.PerBox` — the `n″`-arm as a reusable interface

FS's two-arm split needs the *tight block bound* at **every** window count
(`P/s³ ≤ 9μ`), not only at the bundle's own count `N`: the `n″`-arm of the
assembly and the corpus's sliding chain both apply it at counts that are not
the bundle's.  The DL bundle's regime field `hblkMax`
(`Work.DLRepoint.D4Regime` at the single maximal count `⌊9μs³⌋ - 1`) is
transported to every window count by the PROVED
`Work.DLRepoint.d4Regime_family_of_max`, and the DELIVERED faithful block bound
`Work.DLRepoint.d4_block_bound_at` (from `Work.BlockBound4.diagW_block_bound`,
no rung, no input) then gives the bound in the DL's error shape `Γ`.

Two statements are given:

* `block_bound_family_of` — the `n″`-arm at **a given** error constant `Cb`,
  from the raw block bound at the counts `n + 1` (`hraw`).  This is the form the
  re-wired DL bundle uses, where the universal `Cb` is BOTH the `n″`-arm's
  constant and the theorem's `C` (so it must be read off
  `Work.BlockBound4.diagW_block_bound` once, outside the bundle quantifier);
* `block_bound_family` — the same with `Cb` produced existentially from
  `Work.DLRepoint.d4_block_bound_at` (for a *fixed* box, as a consumer of FS's
  `thm:smallbox` at that box sees it).

Both are the `hblk` slot of `d4_dl_bound_of_simpleA2Two`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLWire

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The `n″`-arm at every window count, at a GIVEN constant `Cb`.**  From the
raw tight block bound at the counts `n + 1` (in the block bundle's own error
shape `Work.BlockBound4.d4Gamma R0`), the maximal-count regime datum, and the
range ordering `R0 ≤ R`, one gets the same bound at **every** `P ≥ 1` with
`P/s³ ≤ 9μ`, in the DL's error shape `Γ = (R/s)² + K_B³(μ(av)³)^{1/2}`. -/
theorem block_bound_family_of {s μ R0 R K_B Ct c₀ cgap Cb : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v}
    (hCb0 : 0 ≤ Cb)
    (hraw : ∀ (n : ℕ) (hwin : ((((n + 1 : ℕ) : ℝ))) / s ^ 3 ≤ 9 * μ)
      (reg : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v n),
      ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
            * (8 * π * (a v) * s ^ 3)
        - Cb * μ ^ 2 * (a v) * s ^ 3 * Work.BlockBound4.d4Gamma R0 s K_B μ v
        - Cb * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt (n + 1) s μ v h c₀ cgap)
    (hs : 0 < s) (hav : 0 < a v) (hR0 : 0 < R0) (hR0R : R0 ≤ R)
    (hc0 : 0 < c₀) (hdil : 2 * c₀ * (a v) ≤ 1)
    (hblkMax : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v
      (Nat.floor (9 * μ * s ^ 3) - 1))
    (hfloor : 1 ≤ Nat.floor (9 * μ * s ^ 3)) :
    ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / s ^ 3 - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - Cb * μ ^ 2 * (a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
        - Cb * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap := by
  intro P hP1 hwin
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : P ≠ 0) with ⟨n, rfl⟩
  have hfam := Work.DLRepoint.d4Regime_family_of_max (s := s) (μ := μ) (R0 := R0)
    (K_B := K_B) (Ct := Ct) (c₀ := c₀) (cgap := cgap) (v := v) hs (le_of_lt hav) hc0 hdil
    hfloor hblkMax
  have hb := hraw n hwin (hfam n hwin)
  have hGle : Work.BlockBound4.d4Gamma R0 s K_B μ v
      ≤ Work.DLRepoint.d4GammaWith R s K_B μ v :=
    Work.DLRepoint.d4Gamma_le_d4GammaWith (le_of_lt hR0) hR0R hs
  have hs3 : (0 : ℝ) < s ^ 3 := pow_pos hs 3
  have hav' : 0 ≤ a v := le_of_lt hav
  have hcoef : (0 : ℝ) ≤ Cb * μ ^ 2 * (a v) * s ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg hCb0 (sq_nonneg μ)) hav') (le_of_lt hs3)
  have := mul_le_mul_of_nonneg_left hGle hcoef
  linarith [hb, this]

/-- **The `n″`-arm at every window count** (the tight block bound in the DL's
error shape), with the constant produced existentially by the delivered block
bound.  For a *fixed* box this is the per-box lower bound FS `thm:smallbox`
consumes. -/
theorem block_bound_family {s μ R0 R K_B Ct c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hμ : 0 < μ) (hav : 0 < a v) (hR0 : 0 < R0) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0s : R0 ≤ s * chiR0)
    (hμs : 1 ≤ μ * s ^ 3) (hKB : 0 < K_B) (hCt : 0 ≤ Ct) (hc0 : 0 < c₀)
    (hdil : 2 * c₀ * (a v) ≤ 1)
    (hWfin : MeasureTheory.Integrable (fun q : ℝ³ × ℝ³ =>
      wScaled s (g0 v h) q.1 * wScaled s (g0 v h) q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹))
    (hNewton : ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
        ((FourierTransform.fourier (fun x : ℝ³ => (wScaled s (g0 v h) x : ℂ))
            (((2 * Real.pi)⁻¹) • q)).re) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + 6 * Ct * (R0 / s) ^ 2) * g0w0Mass (v := v) h)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v))
    (hR0R : R0 ≤ R)
    (hblkMax : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v
      (Nat.floor (9 * μ * s ^ 3) - 1))
    (hfloor : 1 ≤ Nat.floor (9 * μ * s ^ 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / s ^ 3 - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - C * μ ^ 2 * (a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
        - C * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap := by
  obtain ⟨C, hC0, hblk⟩ := Work.DLRepoint.d4_block_bound_at s μ R0 K_B Ct c₀ cgap v h
    hs hμ hv_nonneg hvrad hv_memL1 hR0 hv_supp hR0s hμs hKB hCt hc0 hav hdil hWfin hNewton hD
  exact ⟨C, hC0, block_bound_family_of (Cb := C) hC0
    (fun n hwin reg => hblk n hwin reg) hs hav hR0 hR0R hc0 hdil hblkMax hfloor⟩

end Work.DLWire
