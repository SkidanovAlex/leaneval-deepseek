/-
# The GALERKIN area: the elementary API of the dynamic modulated equation

This module collects the easy lemmas about the vocabulary of
`Submission/Work/FTS/Galerkin/Defs.lean`: the algebra of `slice`, the fact that the right hand
side of the dynamic equation depends on a family only through its slices, congruence of the
solution predicates, and the degenerate (`α = 0`) computations used by the inhabitation module.

Nothing here depends on the Galerkin scheme or on the a-priori bundle.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## `slice` -/

theorem slice_zero_fam (τ : ℝ) : slice (fun _ _ _ => (0 : ℝ)) τ = fun _ _ => (0 : ℝ) := rfl

theorem slice_add (g g' : Fam) (τ : ℝ) :
    slice (fun z θ s => g z θ s + g' z θ s) τ = fun z θ => slice g τ z θ + slice g' τ z θ := rfl

theorem slice_const (c : ℝ) (g : Fam) (τ : ℝ) :
    slice (fun z θ s => c * g z θ s) τ = fun z θ => c * slice g τ z θ := rfl

/-- Two families with the same pointwise values have the same slices. -/
theorem slice_eq {g g' : Fam} (h : ∀ τ z θ, g z θ τ = g' z θ τ) (τ : ℝ) : slice g τ = slice g' τ :=
  funext fun z => funext fun θ => h τ z θ

/-- Pointwise values from a slice equality. -/
theorem val_of_slice_eq {g g' : Fam} (h : ∀ τ, slice g τ = slice g' τ) (τ z θ : ℝ) :
    g z θ τ = g' z θ τ := by
  have h1 := congrFun (congrFun (h τ) z) θ
  simpa [slice] using h1

/-- The family of the `τ`-slices of `F_* + g`, at `α`. -/
theorem Ftau_congr {α : ℝ} {g g' : Fam} (h : ∀ τ, slice g τ = slice g' τ) (τ : ℝ) :
    Construction.Ftau α g τ = Construction.Ftau α g' τ := by
  funext z θ
  have hv := val_of_slice_eq h τ z θ
  simp only [Construction.Ftau]
  rw [hv]

/-! ## The right hand side depends only on the slices -/

theorem muDyn_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) (τ : ℝ) : muDyn α Φ g τ = muDyn α Φ' g' τ := by
  have h3 : Construction.Ftau α g τ = Construction.Ftau α g' τ := Ftau_congr hg τ
  simp only [muDyn, h3, hg τ, hΦ τ]

theorem lamDyn_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) (τ : ℝ) : lamDyn α Φ g τ = lamDyn α Φ' g' τ := by
  have h1 : muDyn α Φ g τ = muDyn α Φ' g' τ := muDyn_congr hg hΦ τ
  simp only [lamDyn, h1]

theorem dynLin_congr {α : ℝ} {g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ) (τ : ℝ) :
    dynLin α g τ = dynLin α g' τ := by
  funext z θ
  simp only [dynLin, hg τ]

theorem dynRHS_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) (τ : ℝ) : dynRHS α Φ g τ = dynRHS α Φ' g' τ := by
  have h1 : muDyn α Φ g τ = muDyn α Φ' g' τ := muDyn_congr hg hΦ τ
  have h2 : lamDyn α Φ g τ = lamDyn α Φ' g' τ := lamDyn_congr hg hΦ τ
  have h3 : Construction.Ftau α g τ = Construction.Ftau α g' τ := Ftau_congr hg τ
  simp only [dynRHS, h1, h2, h3, hg τ, hΦ τ]

/-- The dynamic equation depends only on the slices of `g` and `Φ`. -/
theorem isDynEqOn_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) : IsDynEqOn α Φ g ↔ IsDynEqOn α Φ' g' := by
  have key : ∀ (τ z θ : ℝ), dynLin α g τ z θ + dynRHS α Φ g τ z θ
      = dynLin α g' τ z θ + dynRHS α Φ' g' τ z θ := fun τ z θ => by
    rw [dynLin_congr hg τ, dynRHS_congr hg hΦ τ]
  have hd : ∀ (τ z θ : ℝ), (fun s => g z θ s) = fun s => g' z θ s :=
    fun τ z θ => funext fun s => val_of_slice_eq hg s z θ
  constructor
  · intro h z θ τ hτ hz
    have h' := h z θ τ hτ hz
    rw [hd τ z θ, key τ z θ] at h'
    exact h'
  · intro h z θ τ hτ hz
    have h' := h z θ τ hτ hz
    rw [← hd τ z θ, ← key τ z θ] at h'
    exact h'

theorem isDynEq_congr {α : ℝ} {Φ Φ' g g' : Fam} (hg : ∀ τ, slice g τ = slice g' τ)
    (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) : IsDynEq α Φ g ↔ IsDynEq α Φ' g' := by
  have key : ∀ (τ z θ : ℝ), dynLin α g τ z θ + dynRHS α Φ g τ z θ
      = dynLin α g' τ z θ + dynRHS α Φ' g' τ z θ := fun τ z θ => by
    rw [dynLin_congr hg τ, dynRHS_congr hg hΦ τ]
  have hd : ∀ (τ z θ : ℝ), (fun s => g z θ s) = fun s => g' z θ s :=
    fun τ z θ => funext fun s => val_of_slice_eq hg s z θ
  constructor
  · intro h z θ τ hτ hz
    have h' := h z θ τ hτ hz
    rw [hd τ z θ, key τ z θ] at h'
    exact h'
  · intro h z θ τ hτ hz
    have h' := h z θ τ hτ hz
    rw [← hd τ z θ, ← key τ z θ] at h'
    exact h'

/-- A solution is determined by its slices: two families with the same slices satisfy the same
packaged solution predicate. -/
theorem isDynGSolWith_congr {Law : Fn → Fn → Prop} {α : ℝ} {Φ Φ' g g' : Fam}
    (hg : ∀ τ, slice g τ = slice g' τ) (hΦ : ∀ τ, slice Φ τ = slice Φ' τ) :
    IsDynGSolWith Law α Φ g ↔ IsDynGSolWith Law α Φ' g' := by
  have hL : ∀ τ, Law (Construction.Ftau α g τ) (slice Φ τ)
      = Law (Construction.Ftau α g' τ) (slice Φ' τ) := by
    intro τ
    rw [Ftau_congr hg τ, hΦ τ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun τ hτ => (hL τ) ▸ h1 τ hτ, (isDynEqOn_congr hg hΦ).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun τ hτ => (hL τ) ▸ h1 τ hτ, (isDynEqOn_congr hg hΦ).mpr h2⟩

/-- Transport of the packaged solution predicate across equivalent elliptic laws. -/
theorem isDynGSolWith_congr_law {Law Law' : Fn → Fn → Prop} {α : ℝ} {Φ g : Fam}
    (h : ∀ F Φ, Law F Φ ↔ Law' F Φ) : IsDynGSolWith Law α Φ g ↔ IsDynGSolWith Law' α Φ g := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun τ hτ => (h _ _).mp (h1 τ hτ), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun τ hτ => (h _ _).mpr (h1 τ hτ), h2⟩

theorem IsDynGSolWith.elLaw {Law : Fn → Fn → Prop} {α : ℝ} {Φ g : Fam}
    (h : IsDynGSolWith Law α Φ g) : ∀ τ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ) := h.1

theorem IsDynGSolWith.eqn {Law : Fn → Fn → Prop} {α : ℝ} {Φ g : Fam}
    (h : IsDynGSolWith Law α Φ g) : IsDynEqOn α Φ g := h.2

/-! ## The elliptic law -/

theorem ellLaw_iff (α : ℝ) (F Φ : Fn) :
    EllLaw α F Φ ↔ ∀ z θ, (z, θ) ∈ Construction.Qd → Elliptic.bslOp α Φ z θ = F z θ := Iff.rfl

/-! ## Degenerate computations -/

/-- `F_*(z,θ) = α (Γ/c) 2z/(1+z)²` vanishes at `α = 0`. -/
theorem Fstar_zero_alpha : Construction.Fstar 0 = fun _ _ => (0 : ℝ) := by
  funext z θ
  simp [Construction.Fstar]

/-- The zero family has zero fake-time derivative. -/
theorem gdot_zero (τ : ℝ) : gdot (fun _ _ _ => (0 : ℝ)) τ = fun _ _ => (0 : ℝ) := by
  funext z θ
  simp [gdot]

end Work.FTS.Galerkin
