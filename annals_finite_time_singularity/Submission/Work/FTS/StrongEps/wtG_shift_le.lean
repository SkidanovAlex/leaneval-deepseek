/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/wtG_shift_le.lean` — the shift bound for the mixed weight `wtG`

The log-coordinate mollifier `Jeps` of `Submission/Work/FTS/StrongEps/Basic.lean` is, in the
coordinates `s = log z`, `ζ = log tan θ`, the convolution with the kernel `Jker ρ ε`; the shifts
`z ↦ z e^{-p₁}` (`zShift`) and `θ ↦ arctan (tan θ e^{-p₂})` (`thShift`) are therefore the
translations of the log-coordinates, and the weights of the paper change by at most a factor
`e^{C |p|}` under them.  This is the mechanism that makes `J_ε` bounded on the weighted spaces
`ℋ^k` up to `e^{Cε}`.

The present file proves the bound for the **mixed weight**

`wtG α z θ = w z ^ 2 * sin (2θ) ^ (-γ α)`,  `w z = (1 + z) ^ 2 / z ^ 2`,  `γ α = 1 + α / 10`,

i.e. the weight of the slots `(D_z^j D_θ^i f · W)²` with `W = w · sin(2θ)^{-γ/2}`.

The two factors are handled separately, and the only non-elementary inputs are

* `Work.FTS.StrongEps.wtZ_shift_le` (the radial factor `wtZ z = w z ^ 2`), and
* `Work.FTS.StrongEps.sinTwo_thShift_bounds` (the factor by which `sin (2 ·)` changes under
  `thShift`),

both proved in sibling modules.  Everything else — the `rpow` conversion of a two-sided bound on
`sin (2 ·)` into a bound on the negative power `sin (2 ·) ^ (-γ)` with `γ = γ α ≤ 2`, and the
multiplication of the two factors together with the exponent bookkeeping — is done here.

**Note.**  The statement below contains the notation `π`, so this file must `open scoped Real`
(as it does) for the statement to elaborate; with `autoImplicit` off a bare `π` is otherwise an
unknown identifier.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongEps.sinTwo_thShift_bounds

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

/-! ## The `rpow` step

A one-sided multiplicative bound on a positive number turns into a bound on any negative power
of it, with the reciprocal constant in the exponent: this is the generic form of the passage
`sin(2·thShift θ p) ≥ e^{-|p|} sin 2θ ⟹ sin(2·thShift θ p)^{-γ} ≤ e^{γ|p|} sin(2θ)^{-γ}`. -/

/-- **Powers with negative exponent invert multiplicative bounds.**  If `0 < s` and
`Real.exp (-c) * s ≤ s'` with `γ ≥ 0`, then `s' ^ (-γ) ≤ Real.exp (γ * c) * s ^ (-γ)`.
(The bound is sharp: for `s' = Real.exp (-c) * s` it is an equality.) -/
theorem rpow_shift_le {s s' c γ : ℝ} (hs : 0 < s) (hγ : 0 ≤ γ)
    (hlo : Real.exp (-c) * s ≤ s') :
    s' ^ (-γ) ≤ Real.exp (γ * c) * s ^ (-γ) := by
  have hpos : 0 < Real.exp (-c) * s := mul_pos (Real.exp_pos _) hs
  have h1 : s' ^ (-γ) ≤ (Real.exp (-c) * s) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hpos hlo (by linarith)
  rw [Real.mul_rpow (Real.exp_pos (-c)).le hs.le] at h1
  have h2 : (Real.exp (-c)) ^ (-γ) = Real.exp (γ * c) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos (-c)), Real.log_exp]
    congr 1
    ring
  rwa [h2] at h1

/-! ## The angular factor of `wtG` -/

/-- **The angular weight `sin (2θ) ^ (-γ)` is shifted by at most `e^{2 |p|}`.**  For
`α ∈ (0,1]`, `θ ∈ (0, π/2)` and every `p : ℝ`,
`sGamW α (thShift θ p) ≤ e^{2 |p|} sGamW α θ`.  The exact factor is `e^{γ α · |p|}` with
`γ α = 1 + α/10 ≤ 11/10 ≤ 2`. -/
theorem sGamW_shift_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sGamW α (thShift θ p) ≤ Real.exp (2 * |p|) * sGamW α θ := by
  have hlo : Real.exp (-|p|) * Real.sin (2 * θ) ≤ Real.sin (2 * thShift θ p) :=
    (sinTwo_thShift_bounds hθ).1
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hγ : 0 ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  have hgam : Work.Spaces.gam α ≤ 2 := by
    rw [Work.Spaces.gam]; linarith [hα.2]
  have h1 := rpow_shift_le hs hγ hlo
  have h3 : 0 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
    (Real.rpow_pos_of_pos hs _).le
  have h2 : Real.exp (Work.Spaces.gam α * |p|) ≤ Real.exp (2 * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p, hgam])
  have hsGam : sGamW α θ = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := rfl
  have hsGam' : sGamW α (thShift θ p)
      = Real.sin (2 * thShift θ p) ^ (-(Work.Spaces.gam α)) := rfl
  rw [hsGam, hsGam']
  exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)

/-! ## The shift bound for the full mixed weight -/

theorem wtG_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ z θ p₁ p₂ : ℝ,
      0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        wtG α (zShift z p₁) (thShift θ p₂)
          ≤ Real.exp (C * (|p₁| + |p₂|)) * wtG α z θ := by
  obtain ⟨Cz, hCzpos, hz⟩ := wtZ_shift_le
  refine ⟨Cz + 2, by linarith, ?_⟩
  intro α hα z θ p₁ p₂ hzpos hθ
  have hθIcc : θ ∈ Set.Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2.le⟩
  have hθ'Ioo : thShift θ p₂ ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
  have hθ'Icc : thShift θ p₂ ∈ Set.Icc 0 (π / 2) := ⟨hθ'Ioo.1.le, hθ'Ioo.2.le⟩
  have h1 : wtZ (zShift z p₁) ≤ Real.exp (Cz * |p₁|) * wtZ z := hz z p₁ hzpos
  have h2 : sGamW α (thShift θ p₂) ≤ Real.exp (2 * |p₂|) * sGamW α θ := sGamW_shift_le hα hθ
  have hb : 0 ≤ Real.exp (Cz * |p₁|) * wtZ z :=
    mul_nonneg (Real.exp_pos _).le (wtZ_nonneg z)
  have hprod : wtZ (zShift z p₁) * sGamW α (thShift θ p₂)
      ≤ (Real.exp (Cz * |p₁|) * wtZ z) * (Real.exp (2 * |p₂|) * sGamW α θ) :=
    mul_le_mul h1 h2 (sGamW_nonneg hθ'Icc) hb
  have hexp : Real.exp (Cz * |p₁| + 2 * |p₂|)
      ≤ Real.exp ((Cz + 2) * (|p₁| + |p₂|)) := by
    refine Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p₁, abs_nonneg p₂, hCzpos])
  have hZ : wtG α z θ = wtZ z * sGamW α θ := wtG_eq α z θ
  calc wtG α (zShift z p₁) (thShift θ p₂)
      = wtZ (zShift z p₁) * sGamW α (thShift θ p₂) := wtG_eq α _ _
    _ ≤ (Real.exp (Cz * |p₁|) * wtZ z) * (Real.exp (2 * |p₂|) * sGamW α θ) := hprod
    _ = Real.exp (Cz * |p₁| + 2 * |p₂|) * (wtZ z * sGamW α θ) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp ((Cz + 2) * (|p₁| + |p₂|)) * (wtZ z * sGamW α θ) :=
        mul_le_mul_of_nonneg_right hexp (mul_nonneg (wtZ_nonneg z) (sGamW_nonneg hθIcc))
    _ = Real.exp ((Cz + 2) * (|p₁| + |p₂|)) * wtG α z θ := by rw [← hZ]

end Work.FTS.StrongEps
