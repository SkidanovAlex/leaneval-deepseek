/-
# `aesm_pth_abs` — a.e. strong measurability of the angular derivative of a slice

The firing of the regularity package `RegPkgGal.RegPkg'` into the pressure clause
`PressureOn.PressureReconstructionOn` consumes the angular derivative `∂_θω` of the physical
vorticity through its slice form: the slice of `ω` is `A(τ)⁻¹ ·(F_*(z,θ) + g(z,θ,τ))` composed
with the self-similar variables, and the only *unknown* part of that profile is the perturbation
`g` of the package.  This file supplies the measurability of the angular derivative of that
perturbation slice,

  `q ↦ ∂_θ (gSlice g τ) q.1 (|q.2|)`,

as a function on the half-strip `(0,∞) × (-π/2, π/2)` of the physical `(r,z)`-plane (the second
coordinate is the absolute value of the axial variable, and the strip is the image of the meridian
domain away from the plane `z = 0`).

## Proof

The package gives `Jet α S Ng g`, i.e. the joint `α`-Hölder bound

  `|g z θ τ - g z' θ' τ| ≤ Ng · (|z - z'| + |θ - θ'|)^α`

on the closed quadrant `Q = [0,∞) × [0,π/2]`, together with the vanishing of `g` on the boundary
of `Q` (`hvt` at `θ = 0, π/2` and `hquad0` at `z = 0`).  Hence the zero-extension

  `φ⁺ p = if p ∈ Q then g p.1 p.2 τ else 0`

is *continuous* on `ℝ²`: this is `ZExt.continuous_zeroExt_of_holder` (Hölder data plus boundary
vanishing), and it is the hypothesis under which Mathlib's parametrised derivative
`measurable_deriv_with_param` applies — measurability of `deriv` with a parameter genuinely needs
continuity of the uncurried family.

Composing the resulting measurable function `p ↦ deriv (φ⁺ p.1) p.2` with the measurable map
`q ↦ (q.1, |q.2|)` gives a measurable function which, by `ZExt.ae_deriv_zeroExt_eq`, agrees a.e.
with the target: away from the null set `{q.2 = 0}`, the point `|q.2|` is an *interior* point of
`Icc 0 (π/2)` at a positive `z`, so the zero-extension and the slice agree on a whole neighbourhood
of it and the two derivatives coincide (`Filter.EventuallyEq.deriv_eq`).

## Layout

* `Submission/Work/FTS/FireFix/Clauses/PsiWt/ZExt/continuous_zeroExt_of_holder.lean` — Hölder data
  plus boundary vanishing on the closed quadrant make the zero-extension continuous;
* `Submission/Work/FTS/FireFix/Clauses/PsiWt/ZExt/ae_deriv_zeroExt_eq.lean` — the two derivatives
  agree a.e. on the half-strip.
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Clauses.PsiWt.ZExt.continuous_zeroExt_of_holder
import Submission.Work.FTS.FireFix.Clauses.PsiWt.ZExt.ae_deriv_zeroExt_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.FireFix.Clauses.PsiWt

theorem aesm_pth_abs {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (|q.2|))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
  obtain ⟨Ng, hNg⟩ := h.hg
  have hα : 0 < α := h.hα
  -- the joint Hölder bound of the package, at the fixed strip time `τ`
  have hHold : ∀ x ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      ∀ y ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      |g x.1 x.2 τ - g y.1 y.2 τ| ≤ Ng * (|x.1 - y.1| + |x.2 - y.2|) ^ α := by
    intro x hx y hy
    have := hNg.2.2 x.1 y.1 x.2 y.2 τ τ hx.1 hy.1 hx.2 hy.2 hτ hτ
    simpa using this
  -- the vanishing of the slice on the boundary of the closed quadrant
  have h0 : ∀ p ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) → g p.1 p.2 τ = 0 := by
    intro p hp hb
    rcases hb with h1 | h2 | h3
    · rw [h1]
      exact h.hquad0 τ hτ p.2 ⟨hp.2.1, hp.2.2⟩
    · rw [h2]
      exact (h.hvt τ hτ).1 p.1
    · rw [h3]
      exact (h.hvt τ hτ).2 p.1
  -- continuity of the zero-extension of the slice
  have hcont : Continuous (fun p : ℝ × ℝ =>
      if p ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) then g p.1 p.2 τ else 0) :=
    Work.FTS.FireFix.Clauses.PsiWt.ZExt.continuous_zeroExt_of_holder
      hNg.1 hα (φ := fun p : ℝ × ℝ => g p.1 p.2 τ) hHold h0
  -- the a.e. identification of the derivatives
  have hae := Work.FTS.FireFix.Clauses.PsiWt.ZExt.ae_deriv_zeroExt_eq
    (Φ := fun z θ' => g z θ' τ)
  -- measurability of the parametrised derivative of the extension
  have hmeasF : Measurable (fun p : ℝ × ℝ =>
      deriv (fun θ' => (if p.1 ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
        then g p.1 θ' τ else 0)) p.2) := by
    refine measurable_deriv_with_param (𝕜 := ℝ) (F := ℝ) (α := ℝ)
      (f := fun z θ' => (if z ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
        then g z θ' τ else 0)) ?_
    exact hcont
  have hφ : Measurable (fun q : ℝ × ℝ => (q.1, |q.2|)) :=
    measurable_fst.prodMk ((measurable_abs (α := ℝ)).comp measurable_snd)
  have hmeas2 : Measurable (fun q : ℝ × ℝ =>
      deriv (fun θ' => (if q.1 ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
        then g q.1 θ' τ else 0)) (|q.2|)) := hmeasF.comp hφ
  exact ((hmeas2.aestronglyMeasurable.restrict).congr hae)

end Work.FTS.FireFix.Clauses.PsiWt
