/-
# `Work.FTS.PhiStar.Model` — the model part and the assembly of `IsBslSol`

This file assembles the elementary facts about the two-term model
`Model α Gz ψ = Gz(z)·sin 2θ + α·φ(z)·ψ(θ)` and about the solution built from a decomposition
`Φ_* = Model α Gz ψ + R`:

* the Dirichlet data of `Model` at `θ = 0, π/2` (`Model_zero`, `Model_pi_half`);
* its decay at `z → ∞` (`Model_tendsto`), hence the decay of the whole decomposition;
* the identification of the singular residual `Φ̃_* = Φ_* − Θ` with the flat expansion
  `PhiTilExpansion α ψ R = Aprof·sin 2θ + αφψ + R` (`PhiTil_expansion_eq`);
* the assembly `IsBslSol α (Construction.Fstar α) Φ_*` from the model's `bslOp`-image
  (`phiStar_remainder_source`), the remainder's equation (`bslOp R = RemSource`), the
  differentiability of both pieces and their boundary/decay data (`isBslSol_of_split`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Boundary data and decay of the model part -/

/-- The model part vanishes at `θ = 0`. -/
theorem Model_zero {α : ℝ} {Gz ψ : ℝ → ℝ} {z : ℝ} (h : ψ 0 = 0) :
    Model α Gz ψ z 0 = 0 := by
  rw [Model]
  simp [h]

/-- The model part vanishes at `θ = π/2`. -/
theorem Model_pi_half {α : ℝ} {Gz ψ : ℝ → ℝ} {z : ℝ} (h : ψ (π / 2) = 0) :
    Model α Gz ψ z (π / 2) = 0 := by
  have h2 : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  rw [Model]
  simp [h, h2]

/-- The model part decays at `z → ∞` as soon as `Gz → 0` and `ψ` is bounded. -/
theorem Model_tendsto {α : ℝ} {Gz ψ : ℝ → ℝ} {C : ℝ}
    (hGz : Tendsto Gz atTop (𝓝 0)) (hψ : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) (θ : ℝ) :
    Tendsto (fun z => Model α Gz ψ z θ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => Gz z * Real.sin (2 * θ)) atTop (𝓝 (0 * Real.sin (2 * θ))) :=
    hGz.mul_const _
  have h2 : Tendsto (fun z : ℝ => α * Work.FTS.VocabO.phiR z * ψ θ)
      atTop (𝓝 (α * 0 * ψ θ)) :=
    (tendsto_phiR_atTop.const_mul α).mul_const (ψ θ)
  have h3 := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at h3
  refine h3.congr' (Eventually.of_forall fun z => ?_)
  simp only [Model]

/-! ## The flat expansion of `Φ̃_*` -/

/-- `Φ̃_* = Φ_* − Θ` in the flat coordinates: with `Φ_* = Model α GzProfile ψ + R`,
one has `Φ̃_*(z,θ) = Aprof α z · sin 2θ + α φ(z) ψ(θ) + R(z,θ)` for `z ≥ 0`. -/
theorem PhiTil_expansion_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ψ : ℝ → ℝ) (R : Fn)
    (z θ : ℝ) (hz : 0 ≤ z) :
    Work.Construction.PhiTil α (Work.Construction.Fstar α)
        (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) z θ
      = PhiTilExpansion α ψ R z θ := by
  rw [Work.Construction.PhiTil, PhiTilExpansion, Model, Aprof,
    Theta_eq_thetaProfile hα hα1 hz θ]
  ring

/-! ## Assembly of `IsBslSol` -/

/-- **The equation of the decomposition.**  If the model part has `bslOp`-image
`F_* − α²(𝒜φ)ψ` (the telescoping identity `phiStar_remainder_source`) and the remainder solves
`bslOp R = α²(𝒜φ)ψ`, then `Φ_* = Model + R` solves `bslOp α Φ_* = F_*` on the open quadrant.

The differentiability hypotheses are those needed by `Work.Elliptic.bslOp_add`. -/
theorem bslOp_split_eq {α : ℝ} {Gz ψ : ℝ → ℝ} {R : Fn}
    (hmodel : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α (Model α Gz ψ) z θ
        = Work.Construction.Fstar α z θ - RemSource α ψ z θ)
    (hrem : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hC2M : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry (Model α Gz ψ)) (z, θ))
    (hC2R : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry R) (z, θ))
    (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (fun z θ => Model α Gz ψ z θ + R z θ) z θ
      = Work.Construction.Fstar α z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ, Real.pi_pos], hθ2⟩)
  rw [Work.Elliptic.bslOp_add α _ R z θ hcos (hC2M z θ hz hθ hθ2) (hC2R z θ hz hθ hθ2),
    hmodel z hz θ hθ hθ2, hrem z hz θ hθ hθ2]
  ring

/-- **`IsBslSol` of the decomposition.**  Given the model equation, the remainder's equation,
the Dirichlet data of `Model` and `R` at `θ = 0, π/2`, and the decay of `Gz`, of `φ` and of `R`,
the sum `Model α Gz ψ + R` is a solution of `bslOp α Φ = F_*` in the class `IsBslSol`. -/
theorem isBslSol_of_split {α : ℝ} {Gz ψ : ℝ → ℝ} {R : Fn} {C : ℝ}
    (hmodel : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α (Model α Gz ψ) z θ
        = Work.Construction.Fstar α z θ - RemSource α ψ z θ)
    (hrem : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hC2M : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry (Model α Gz ψ)) (z, θ))
    (hC2R : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry R) (z, θ))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ (π / 2) = 0)
    (hR0 : ∀ z, R z 0 = 0) (hR1 : ∀ z, R z (π / 2) = 0)
    (hGzdec : Tendsto Gz atTop (𝓝 0)) (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C)
    (hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
      (fun z θ => Model α Gz ψ z θ + R z θ) := by
  refine ⟨fun z hz θ hθ hθ2 => bslOp_split_eq hmodel hrem hC2M hC2R z θ hz hθ hθ2, ?_, ?_, ?_⟩
  · intro z
    show Model α Gz ψ z 0 + R z 0 = 0
    rw [Model_zero hψ0, hR0 z, add_zero]
  · intro z
    show Model α Gz ψ z (π / 2) + R z (π / 2) = 0
    rw [Model_pi_half hψ1, hR1 z, add_zero]
  · intro θ hθ
    have h := (Model_tendsto (α := α) (Gz := Gz) (ψ := ψ) hGzdec hψbd θ).add (hRdec θ hθ)
    rw [add_zero] at h
    simpa using h

end Work.FTS.PhiStar
