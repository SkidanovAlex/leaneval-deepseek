/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Weights.lean` — the two weights of the `ε`-scheme

The log-coordinate mollifier `Jeps` of `Submission/Work/FTS/StrongEps/Basic.lean` is, in the
coordinates `s = log z`, `ζ = log tan θ`, the convolution with the kernel `Jker ρ ε`; the shifts
`z ↦ z e^{-p₁}`, `θ ↦ arctan (tan θ e^{-p₂})` therefore change the weights of the paper by a
factor `e^{C|p|}` at most, and *this* is the mechanism that makes `J_ε` bounded on the weighted
spaces `ℋ^k` (up to `e^{Cε}`) and makes the commutator of `E1` of the design of size `O(ε)`.

The two weights occurring in `Work.Spaces.HkIntegrand` are

* `w z ^ 2 * sin (2θ) ^ (-η)` — the weight of the pure `D_z`-slots
  (`(D_z^i f · w / sin(2θ)^{η/2})²`);
* `w z ^ 2 * sin (2θ) ^ (-γ)` — the weight of the mixed slots (`(D_z^j D_θ^i f · W)²`).

This module only *defines* them (and records the two obvious comparisons); the shift bounds are
statements of the `E1` chapter and are proved in `Submission/Work/FTS/StrongEps/E1/`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- The angular factor `sin(2θ)^{-η}` of the `D_z`-slots. -/
def sEtaW (θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-(Work.Spaces.eta))

/-- The angular factor `sin(2θ)^{-γ}` of the mixed slots. -/
def sGamW (α θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))

/-- The weight of the pure `D_z`-slots: `(w / sin(2θ)^{η/2})² = w² sin(2θ)^{-η}`. -/
def wtE (z θ : ℝ) : ℝ := Work.Spaces.w z ^ 2 * sEtaW θ

/-- The weight of the mixed slots: `(w sin(2θ)^{-γ/2})² = w² sin(2θ)^{-γ}`. -/
def wtG (α : ℝ) (z θ : ℝ) : ℝ := Work.Spaces.w z ^ 2 * sGamW α θ

/-- The `z`-part of both weights. -/
def wtZ (z : ℝ) : ℝ := Work.Spaces.w z ^ 2

theorem wtE_eq (z θ : ℝ) : wtE z θ = wtZ z * sEtaW θ := rfl

theorem wtG_eq (α : ℝ) (z θ : ℝ) : wtG α z θ = wtZ z * sGamW α θ := rfl

theorem wtZ_nonneg (z : ℝ) : 0 ≤ wtZ z := by
  rw [wtZ]; positivity

/-- `sin (2θ) > 0` on the open quadrant. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≥ 0` on the closed quadrant. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem wtZ_pos {z : ℝ} (hz : 0 < z) : 0 < wtZ z := by
  rw [wtZ, Work.Spaces.w]
  exact pow_pos (div_pos (by positivity) (pow_pos hz 2)) 2

theorem sEtaW_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) : 0 ≤ sEtaW θ := by
  rw [sEtaW]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem sGamW_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) : 0 ≤ sGamW α θ := by
  rw [sGamW]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

theorem sEtaW_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < sEtaW θ := by
  rw [sEtaW]
  exact Real.rpow_pos_of_pos (sin_two_pos hθ) _

theorem sGamW_pos {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < sGamW α θ := by
  rw [sGamW]
  exact Real.rpow_pos_of_pos (sin_two_pos hθ) _

theorem wtE_nonneg {z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) : 0 ≤ wtE z θ := by
  rw [wtE_eq]; exact mul_nonneg (wtZ_nonneg z) (sEtaW_nonneg hθ)

theorem wtG_nonneg {α : ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) : 0 ≤ wtG α z θ := by
  rw [wtG_eq]; exact mul_nonneg (wtZ_nonneg z) (sGamW_nonneg hθ)

theorem wtE_pos {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < wtE z θ := by
  rw [wtE_eq]; exact mul_pos (wtZ_pos hz) (sEtaW_pos hθ)

theorem wtG_pos {α : ℝ} {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < wtG α z θ := by
  rw [wtG_eq]; exact mul_pos (wtZ_pos hz) (sGamW_pos hθ)

end Work.FTS.StrongEps
