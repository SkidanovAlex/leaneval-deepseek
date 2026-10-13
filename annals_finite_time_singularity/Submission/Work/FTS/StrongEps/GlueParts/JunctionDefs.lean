/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlueParts/JunctionDefs.lean` — the pieces of the fake-time axis
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.GlueParts.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 concat uncurry3)

/-! ## The pieces of the fake-time axis -/

/-- The target piece `[0, t+δ]` over the open quadrant. -/
def AT (t δ : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)

/-- The piece `[0,t]` over the open quadrant. -/
def AG (t : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t

/-- The piece `[0,δ]` over the open quadrant. -/
def AH (δ : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ

/-- The piece `[t,t+δ]` over the open quadrant. -/
def BT (t δ : ℝ) : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)

theorem mem_AT {t δ z θ τ : ℝ} :
    (z, θ, τ) ∈ AT t δ ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ 0 ≤ τ ∧ τ ≤ t + δ := by
  simp only [AT, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

theorem mem_AG {t z θ τ : ℝ} :
    (z, θ, τ) ∈ AG t ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ 0 ≤ τ ∧ τ ≤ t := by
  simp only [AG, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

theorem mem_AH {δ z θ τ : ℝ} :
    (z, θ, τ) ∈ AH δ ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ 0 ≤ τ ∧ τ ≤ δ := by
  simp only [AH, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

theorem mem_BT {t δ z θ τ : ℝ} :
    (z, θ, τ) ∈ BT t δ ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ t ≤ τ ∧ τ ≤ t + δ := by
  simp only [BT, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto


end Work.FTS.StrongEps.GlueParts
