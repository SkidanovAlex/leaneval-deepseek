/-
Copyright: work module for the Elgindi finite-time singularity project.

Auxiliary definitions and elementary lemmas for `SmoothCompact_HkInf`, the fact that a
smooth compactly supported function on the closed quadrant `[0,∞) × [0,π/2]` which
vanishes on the angular boundary and to second order in `z` at `z = 0` lies in
`ℋ^k ∩ 𝒲^{l,∞}` with finite norms.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## The open neighbourhood of the quadrant -/

/-- The open neighbourhood `(-1,∞) × (-1,π/2+1)` of the closed quadrant
`[0,∞) × [0,π/2]` on which `SmoothNbhd` demands smoothness. -/
def U : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)

theorem isOpen_U : IsOpen U := isOpen_Ioi.prod isOpen_Ioo

theorem smoothNbhd_iff (f : ℝ → ℝ → ℝ) :
    SmoothNbhd f ↔ ContDiffOn ℝ ⊤ (Function.uncurry f) U := Iff.rfl

theorem mem_U {z θ : ℝ} (hz : -1 < z) (hθ₀ : -1 < θ) (hθ₁ : θ < π/2 + 1) : (z, θ) ∈ U :=
  ⟨hz, hθ₀, hθ₁⟩

theorem mem_U_of_dom {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) : (z, θ) ∈ U := by
  refine mem_U ?_ ?_ ?_
  · have : (0 : ℝ) ≤ z := hz
    linarith
  · have : (0 : ℝ) ≤ θ := hθ.1
    linarith
  · have h₁ : θ ≤ π / 2 := hθ.2
    have := Real.pi_pos
    linarith

theorem mem_U_of_box {R z θ : ℝ} (hz : z ∈ Set.Icc 0 R) (hθ : θ ∈ Iθ) : (z, θ) ∈ U :=
  mem_U_of_dom hz.1 hθ

/-! ## The box `[0,R] × [0,π/2]` -/

theorem isCompact_box (R : ℝ) : IsCompact (Set.Icc 0 R ×ˢ Iθ) := by
  rw [Iθ]
  exact isCompact_Icc.prod isCompact_Icc

theorem box_nonempty {R : ℝ} (hR : 0 ≤ R) : (Set.Icc 0 R ×ˢ Iθ).Nonempty :=
  ⟨(0, 0), ⟨⟨le_refl 0, hR⟩, zero_mem_Iθ⟩⟩

/-- The set of values `|H z θ|` for `(z,θ)` in the box `[0,R] × [0,π/2]`. -/
def boxSet (R : ℝ) (H : ℝ → ℝ → ℝ) : Set ℝ := {y : ℝ | ∃ z ∈ Set.Icc 0 R, ∃ θ ∈ Iθ, y = |H z θ|}

/-- The supremum of `|H|` over the box `[0,R] × [0,π/2]`. -/
def boxSup (R : ℝ) (H : ℝ → ℝ → ℝ) : ℝ := sSup (boxSet R H)

theorem bddAbove_boxSup_of_continuousOn {R : ℝ} {H : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry H) (Set.Icc 0 R ×ˢ Iθ)) : BddAbove (boxSet R H) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => |Function.uncurry H q|) (Set.Icc 0 R ×ˢ Iθ) := h.abs
  refine (isCompact_box R).bddAbove_image hc |>.mono ?_
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  exact ⟨(z, θ), ⟨hz, hθ⟩, rfl⟩

theorem continuousOn_box_of_contDiffOn {R : ℝ} {H : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry H) U) :
    ContinuousOn (Function.uncurry H) (Set.Icc 0 R ×ˢ Iθ) :=
  h.continuousOn.mono fun p hp => mem_U_of_box hp.1 hp.2

theorem le_boxSup {R : ℝ} {H : ℝ → ℝ → ℝ} (hb : BddAbove (boxSet R H))
    {z θ : ℝ} (hz : z ∈ Set.Icc 0 R) (hθ : θ ∈ Iθ) : |H z θ| ≤ boxSup R H :=
  le_csSup hb ⟨z, hz, θ, hθ, rfl⟩

theorem boxSup_nonneg {R : ℝ} {H : ℝ → ℝ → ℝ} (hR : 0 ≤ R) (hb : BddAbove (boxSet R H)) :
    0 ≤ boxSup R H := by
  rcases box_nonempty hR with ⟨p, hp⟩
  exact le_trans (abs_nonneg _) (le_boxSup hb hp.1 hp.2)

/-- A function which vanishes above `R` and is bounded on the box is bounded on the whole
domain `[0,∞) × [0,π/2]`. -/
theorem abs_le_boxSup_of_dom {R : ℝ} {H : ℝ → ℝ → ℝ} (hR : 0 ≤ R)
    (hb : BddAbove (boxSet R H)) (hzero : ∀ z θ : ℝ, R < z → H z θ = 0) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ, |H z θ| ≤ boxSup R H := by
  intro z hz θ hθ
  by_cases h : z ≤ R
  · exact le_boxSup hb ⟨hz, h⟩ hθ
  · rw [hzero z θ (not_le.mp h), abs_zero]
    exact boxSup_nonneg hR hb

theorem supFinite_of_box {R : ℝ} {H : ℝ → ℝ → ℝ} (hR : 0 ≤ R) (hb : BddAbove (boxSet R H))
    (hzero : ∀ z θ : ℝ, R < z → H z θ = 0) : SupFinite H :=
  ⟨boxSup R H, by
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    exact abs_le_boxSup_of_dom hR hb hzero z hz θ hθ⟩

theorem supFinite_of_pointwise {H : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |H z θ| ≤ C) : SupFinite H :=
  ⟨C, fun y hy => by rcases hy with ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ⟩

end Work.Spaces
