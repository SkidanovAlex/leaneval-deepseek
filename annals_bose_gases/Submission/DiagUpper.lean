import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.DiagDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — upper side of the diagonal limit.

The single quantitative estimate behind the upper side of the diagonal
limit: a box of side `L ∈ [G_m, G_{m+1}]` (`G_m := mℓ + (m−1)R`), holding
`⌊ρL³⌋` particles, is covered by the `m³` cells of the grid of side `ℓ`
with spacing `ℓ + R`.  Every cell takes the same number

    Nbar := ⌊ρ·G_{m+1}³/m³⌋ + 2 ≥ ⌈N/m³⌉

of particles (allowed, since adding particles can only raise the energy,
and the grid comparison needs `N ≤ m³·Nbar`).  Hence

    diag v ρ L ≤ (m³/G_m³) · E(Nbar, ℓ).

Letting `m → ∞` with `ℓ` fixed this becomes the *upper-side inequality*
`diagLimsup v ρ ≤ diagLiminf v ρ'` for every `ρ' > ρ`, proved in the
follow-up module once the two-scale limit and continuity of the liminf
function are in place.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The side of the `m`-per-axis grid of cells of side `ℓ` with spacing `ℓ+R`:
`G_m := mℓ + (m−1)R`. -/
noncomputable def gridSide (m : ℕ) (ℓ R : ℝ) : ℝ :=
  (m : ℝ) * ℓ + ((m : ℝ) - 1) * R

/-- Elementary floor bound behind the grid cover: for `0 ≤ ρ`, `0 ≤ G` and
`1 ≤ m` one has `⌊ρ·G³⌋ ≤ m³·(⌊ρ·G³/m³⌋ + 2)`, i.e. the `m³` cells, each
holding `⌊ρ·G³/m³⌋ + 2` particles, can accommodate all `⌊ρ·G³⌋` particles
of a density-`ρ` box of side up to `G`. -/
lemma floor_pow3_le {ρ G : ℝ} {m : ℕ} (hρ : 0 ≤ ρ) (hG : 0 ≤ G)
    (hm : 1 ≤ m) :
    Nat.floor (ρ * G ^ 3) ≤ m ^ 3 * (Nat.floor (ρ * G ^ 3 / (m : ℝ) ^ 3) + 2) := by
  have hA0 : 0 ≤ ρ * G ^ 3 := mul_nonneg hρ (pow_nonneg hG 3)
  have hmr0 : 0 < (m : ℝ) ^ 3 := by positivity
  have hlt :
      (Nat.floor (ρ * G ^ 3) : ℝ) <
        (m : ℝ) ^ 3 * ((Nat.floor (ρ * G ^ 3 / (m : ℝ) ^ 3) : ℝ) + 2) := by
    calc
      (Nat.floor (ρ * G ^ 3) : ℝ) ≤ ρ * G ^ 3 := Nat.floor_le hA0
      _ = (ρ * G ^ 3 / (m : ℝ) ^ 3) * (m : ℝ) ^ 3 := by
        rw [div_mul_cancel₀ (ρ * G ^ 3) (ne_of_gt hmr0)]
      _ < ((Nat.floor (ρ * G ^ 3 / (m : ℝ) ^ 3) : ℝ) + 1) * (m : ℝ) ^ 3 := by
        exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (ρ * G ^ 3 / (m : ℝ) ^ 3)) hmr0
      _ ≤ ((Nat.floor (ρ * G ^ 3 / (m : ℝ) ^ 3) : ℝ) + 2) * (m : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hmr0)
      _ = (m : ℝ) ^ 3 * ((Nat.floor (ρ * G ^ 3 / (m : ℝ) ^ 3) : ℝ) + 2) := by
        ring
  have hreal : (Nat.floor (ρ * G ^ 3) : ℝ) ≤
        (m : ℝ) ^ 3 * ((Nat.floor (ρ * G ^ 3 / (m : ℝ) ^ 3) : ℝ) + 2) := le_of_lt hlt
  exact_mod_cast hreal

/-- Grid cover estimate: for a box side `L` between `G_m` and `G_{m+1}` at
density `ρ`, the diagonal energy density is bounded by the cell energy
`E(Nbar, ℓ)` with `Nbar := ⌊ρG_{m+1}³/m³⌋ + 2`, rescaled by `(m/G_m)³`. -/
lemma diag_le_grid_cover {ρ : ℝ} {L ℓ R : ℝ} {m : ℕ} (hρ : 0 ≤ ρ) (hm : 1 ≤ m)
    (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : 0 < L)
    (hGpos : 0 < gridSide m ℓ R)
    (hLlo : gridSide m ℓ R ≤ L)
    (hLhi : L ≤ gridSide (m + 1) ℓ R)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    diag v ρ L ≤ ((m : ℝ) ^ 3 / gridSide m ℓ R ^ 3) *
      boxEnergy (Nat.floor (ρ * gridSide (m + 1) ℓ R ^ 3 / (m : ℝ) ^ 3) + 2) ℓ v := by
  let Gm := gridSide m ℓ R
  let Gm1 := gridSide (m + 1) ℓ R
  let N : ℕ := Nat.floor (ρ * L ^ 3)
  let nbar : ℕ := Nat.floor (ρ * Gm1 ^ 3 / (m : ℝ) ^ 3) + 2
  have hGm1nonneg : 0 ≤ Gm1 := le_trans hL.le hLhi
  have hL3le : L ^ 3 ≤ Gm1 ^ 3 := pow_le_pow_left₀ hL.le hLhi 3
  have hρL3le : ρ * L ^ 3 ≤ ρ * Gm1 ^ 3 := mul_le_mul_of_nonneg_left hL3le hρ
  have hF : Nat.floor (ρ * Gm1 ^ 3) ≤ m ^ 3 * nbar := by
    dsimp [nbar]
    exact floor_pow3_le hρ hGm1nonneg hm
  have hN : N ≤ m ^ 3 * nbar := by
    dsimp [N]
    exact le_trans (Nat.floor_mono hρL3le) hF
  have hbal : boxEnergy N L v ≤ (m : ℝ) ^ 3 * boxEnergy nbar ℓ v := by
    exact boxEnergy_grid_balanced (m := m) (nbar := nbar) (N := N) hm hℓ hR hL
      (by simpa [gridSide] using hLlo) hv hv1 hsupp hN
  have hGm3ne : Gm ^ 3 ≠ 0 := by
    exact pow_ne_zero 3 (ne_of_gt hGpos)
  calc
    diag v ρ L = boxEnergy N L v / L ^ 3 := by
      simp [diag, N]
    _ ≤ ((m : ℝ) ^ 3 * boxEnergy nbar ℓ v) / L ^ 3 := by
      exact div_le_div_of_nonneg_right hbal (pow_nonneg hL.le 3)
    _ ≤ ((m : ℝ) ^ 3 * boxEnergy nbar ℓ v) / Gm ^ 3 := by
      have hnum0 : 0 ≤ (m : ℝ) ^ 3 * boxEnergy nbar ℓ v :=
        mul_nonneg (by positivity) (boxEnergy_nonneg hℓ hv)
      have hpow : Gm ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hGpos.le (by simpa [Gm] using hLlo) 3
      exact div_le_div_of_nonneg_left hnum0 (pow_pos hGpos 3) hpow
    _ = ((m : ℝ) ^ 3 / Gm ^ 3) * boxEnergy nbar ℓ v := by
      field_simp [hGm3ne]

end BoseGases

end Submission
