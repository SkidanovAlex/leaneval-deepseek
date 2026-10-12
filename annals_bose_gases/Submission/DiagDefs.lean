import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.GridInst
import Submission.ProductBound
import Submission.ThermoLimit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the diagonal of the box energy density and its extremal limits.

For a density `ρ ≥ 0` and a box side `L > 0` let

    f(ρ,L) := E(⌊ρ·L³⌋, L)/L³

be the canonical energy density of `⌊ρ·L³⌋` particles in a cube of side `L`.
The thermodynamic limit along the diagonal `N ≈ ρ·L³` is the limit of `f(ρ,L)`
as `L → ∞`.  We define `diag`, the liminf/limsup over `atTop` of the diagonal,
and record the elementary facts (nonnegativity, boundedness via the product
trial state, monotonicity in the density) that the diagonal-limit argument uses.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real
open Filter

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The diagonal of the box-energy density at density `ρ` and side `L`:
`E(⌊ρL³⌋,L)/L³`.  (For `L ≤ 0` this still returns a real, but all statements
restrict to `1 ≤ L`.) -/
noncomputable def diag (v : ℝ³ → ℝ) (ρ : ℝ) (L : ℝ) : ℝ :=
  boxEnergy (Nat.floor (ρ * L ^ 3)) L v / L ^ 3

/-- The liminf of the diagonal as `L → ∞`. -/
noncomputable def diagLiminf (v : ℝ³ → ℝ) (ρ : ℝ) : ℝ :=
  Filter.liminf (fun L : ℝ => diag v ρ L) atTop

/-- The limsup of the diagonal as `L → ∞`. -/
noncomputable def diagLimsup (v : ℝ³ → ℝ) (ρ : ℝ) : ℝ :=
  Filter.limsup (fun L : ℝ => diag v ρ L) atTop

/-- For `0 ≤ v` the diagonal is nonnegative at every admissible side. -/
lemma diag_nonneg {v : ℝ³ → ℝ} {ρ : ℝ} {L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    0 ≤ diag v ρ L := by
  unfold diag
  exact div_nonneg (boxEnergy_nonneg hL hv) (pow_nonneg hL.le 3)

/-- The number of particles `⌊ρL³⌋` has density at most `ρ` (for `0 ≤ ρ`, `0 < L`). -/
lemma floor_particles_density_le {ρ : ℝ} {L : ℝ} (hρ : 0 ≤ ρ) (hL : 0 < L) :
    ((Nat.floor (ρ * L ^ 3) : ℝ) / L ^ 3) ≤ ρ := by
  have hle : (Nat.floor (ρ * L ^ 3) : ℝ) ≤ ρ * L ^ 3 := by
    exact_mod_cast Nat.floor_le (mul_nonneg hρ (pow_nonneg hL.le 3))
  rwa [div_le_iff₀ (pow_pos hL 3)]

/-- Boundedness of the diagonal: at side `L ≥ 1` and density `ρ ≥ 0`, the diagonal
is at most `C(ρ²·‖v‖₁ + ρ)` (product trial state). -/
lemma diag_le_density_bound {v : ℝ³ → ℝ} (hv1 : MemLp v 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : ℝ} {L : ℝ}, 1 ≤ L → 0 ≤ ρ →
      diag v ρ L ≤ C * (ρ ^ 2 * vL1 v + ρ) := by
  rcases boxDensity_upper_bound hv1 with ⟨C, hCpos, hbd⟩
  refine ⟨C, hCpos, ?_⟩
  intro ρ L hL1 hρ0
  unfold diag
  let N : ℕ := Nat.floor (ρ * L ^ 3)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hdens : (N : ℝ) / L ^ 3 ≤ ρ := by
    simpa [N] using (floor_particles_density_le (ρ := ρ) (L := L) hρ0 hLpos)
  exact hbd ρ N hL1 hρ0 hdens

/-- The diagonal is nondecreasing in the density (same side). -/
lemma diag_mono_ρ {v : ℝ³ → ℝ} {ρ₁ ρ₂ : ℝ} {L : ℝ} (hL : 0 < L)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hρ : ρ₁ ≤ ρ₂) :
    diag v ρ₁ L ≤ diag v ρ₂ L := by
  unfold diag
  let N1 : ℕ := Nat.floor (ρ₁ * L ^ 3)
  let N2 : ℕ := Nat.floor (ρ₂ * L ^ 3)
  have hle : ρ₁ * L ^ 3 ≤ ρ₂ * L ^ 3 := mul_le_mul_of_nonneg_right hρ (pow_nonneg hL.le 3)
  have hNN : N1 ≤ N2 := by
    dsimp [N1, N2]
    exact Nat.floor_mono hle
  have hE := boxEnergy_mono_N (N := N1) (M := N2) hL hv hv1 hNN
  exact div_le_div_of_nonneg_right hE (pow_nonneg hL.le 3)

end BoseGases

end Submission
