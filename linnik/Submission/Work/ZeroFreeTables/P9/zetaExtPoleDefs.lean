/-
# `Work.ZeroFreeTables.P9.zetaExtPoleDefs`

The removable-singularity extension `z ↦ (z-1)ζ(z)` of `ζ` at its pole `z = 1`, together with
the closed rectangle `{1 ≤ Re z ≤ 2, |Im z| ≤ 5}` on which the corrector
`zetaCorrector z = -ζ'/ζ(z) - 1/(z-1)` is to be bounded.

## Why

`-ζ'/ζ` has a simple pole with residue `1` at `z = 1`, so `zetaCorrector = -ζ'/ζ - 1/(z-1)` is
holomorphic across `1`.  The way to see this is to write `ζ(z) = φ(z)/(z-1)` with

`φ(z) = (z-1)Λ(z)/Γℝ(z)`,  `Λ = completedRiemannZeta`,

and to observe that `ψ(z) := (z-1)Λ₀(z) - (z-1)/z + 1` is — on `{0}ᶜ` — the same as
`(z-1)Λ(z)`, hence that `ζ(z) = ψ(z)/((z-1)Γℝ(z))` and `φ = ψ/Γℝ` is analytic on `{0}ᶜ` with
`φ(1) = 1`.  Then `-ζ'/ζ(z) - 1/(z-1) = -φ'/φ(z)`, so `zetaCorrector` agrees with the
logarithmic derivative of the nonzero analytic function `φ` near every point of the closed
rectangle (where `ζ` has no zeros), and is therefore bounded there together with its derivatives.

## Contents

* `zetaRect5`, `psiExtPole`, `zetaExtPole`;
* `isCompact_zetaRect5` — the rectangle is compact;
* `differentiableOn_psiExtPole`, `analyticOn_zetaExtPole` — the extension is analytic on `{0}ᶜ`;
* `zetaExtPole_eq` — away from `0` and `1` it literally is `(s-1)ζ(s)`.
-/
import Mathlib

open Complex Set Filter
open scoped Topology

noncomputable section

namespace Work.ZeroFreeTables.P9

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ 5}`. -/
def zetaRect5 : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 5}

/-- The holomorphic extension of `(s-1)Λ(s)`, `Λ = completedRiemannZeta`, across `s = 1`
(for `s ≠ 0, 1` it equals `(s-1)Λ(s)`). -/
def psiExtPole (s : ℂ) : ℂ := (s - 1) * completedRiemannZeta₀ s - (s - 1) / s + 1

/-- The holomorphic extension of `(s-1)ζ(s)` across the pole `s = 1`: `φ = ψ/Γℝ`.  Its
logarithmic derivative is minus the `ζ`-corrector `-ζ'/ζ - 1/(s-1)`. -/
def zetaExtPole (s : ℂ) : ℂ := psiExtPole s / Gammaℝ s

/-- The rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ 5}` is compact. -/
lemma isCompact_zetaRect5 : IsCompact zetaRect5 := by
  have h : zetaRect5 = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
      '' (Icc 1 2 ×ˢ Icc (-5:ℝ) 5) := by
    ext s
    constructor
    · intro ⟨h1, h2, h3⟩
      refine ⟨(s.re, s.im), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [abs_le] at h3; exact ⟨h3.1, h3.2⟩
      · simp
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · simpa using hp1
      · simpa using hp2
      · simp only [ofReal_re, ofReal_im, add_im, mul_I_im, zero_add]
        exact abs_le.mpr ⟨hp3, hp4⟩
  rw [h]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- `psiExtPole` is differentiable away from `0`. -/
lemma differentiableOn_psiExtPole : DifferentiableOn ℂ psiExtPole {0}ᶜ := by
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * completedRiemannZeta₀ z) s :=
    (differentiableAt_id.sub_const 1).mul hΛ.differentiableAt
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) / z) s :=
    (differentiableAt_id.sub_const 1).div differentiableAt_id hs
  exact ((h1.sub h2).add_const 1).differentiableWithinAt

/-- `zetaExtPole` is analytic on `{0}ᶜ` (in particular on a neighbourhood of the rectangle). -/
lemma analyticOn_zetaExtPole : AnalyticOnNhd ℂ zetaExtPole {0}ᶜ := by
  have hG : DifferentiableOn ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) {0}ᶜ :=
    differentiable_Gammaℝ_inv.differentiableOn
  have h : zetaExtPole = psiExtPole * fun s : ℂ => (Gammaℝ s)⁻¹ := rfl
  rw [h]
  exact (differentiableOn_psiExtPole.mul hG).analyticOnNhd isOpen_compl_singleton

/-- Away from `0` and `1` the extension is literally `(s-1)ζ(s)`. -/
lemma zetaExtPole_eq (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    zetaExtPole s = (s - 1) * riemannZeta s := by
  have hΛ : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have hζ : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero h0
  rw [hζ, hΛ]
  unfold zetaExtPole psiExtPole
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

end Work.ZeroFreeTables.P9
