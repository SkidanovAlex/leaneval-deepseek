/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# A *holomorphic* strip lift through the coverings `F^[n]`

(Q4, differentiable form) of the design in `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §2.1.

`Work.FatouParabolic.Core.exists_strip_lift` produces, for the inverse Fatou coordinate `Φ` of the
immediate basin on a tail strip, a *continuous* lift `X` of `τ ↦ Φ (τ + n)` through the covering
`F^[n] : Ω₀ → Ω₀`, on the deeper strip `tailStrip (C - n) B`, agreeing with `Φ` on `tailStrip C B`.

The Liouville argument of the design needs more than continuity: the glued function
`Ψ τ := (lift of height |Im τ| + 1 at τ) τ` has to be holomorphic.  This file provides the missing
analytic input: the lift can be chosen *complex differentiable* on the deeper strip.

The mechanism is that `F` has no critical point on `Ω₀`, so `F^[n]` is a *local biholomorphism*
there, and a continuous section of a local biholomorphism over a holomorphic map is holomorphic:
near a point `τ` of the strip the lift is `ρ ∘ (Φ (· + n))`, where `ρ` is the (analytic) local
inverse of `F^[n]` at `X τ` — see `differentiableWithinAt_of_comp_eq_of_continuousOn` below.
The non-vanishing of `deriv (F^[n])` on `Ω₀` is `deriv_iterate_ne_zero_of_mapsTo`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.exists_strip_lift
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.exists_petalInverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.FatouParabolic.Core.ImmBasin

/-- **The derivative of an iterate does not vanish on an invariant set free of critical points.**

If `F` is entire, `Ω` is `F`-invariant and `deriv F ≠ 0` on `Ω`, then `deriv (F^[n]) ≠ 0` on `Ω`
(the chain rule writes `deriv (F^[n]) w = deriv (F^[n-1]) (F w) * deriv F w`). -/
theorem deriv_iterate_ne_zero_of_mapsTo {F : ℂ → ℂ} {Ω : Set ℂ} (hF : Differentiable ℂ F)
    (hmap : Set.MapsTo F Ω Ω) (hnocrit : ∀ w ∈ Ω, deriv F w ≠ 0) :
    ∀ (n : ℕ) (w : ℂ), w ∈ Ω → deriv (F^[n]) w ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro w _
    rw [Function.iterate_zero, deriv_id]
    exact one_ne_zero
  | succ n ih =>
    intro w hw
    rw [Function.iterate_succ]
    rw [deriv_comp w (hF.iterate n).differentiableAt hF.differentiableAt]
    exact mul_ne_zero (ih (F w) (hmap hw)) (hnocrit w hw)

/-- **A continuous section of a local biholomorphism over a holomorphic map is holomorphic.**

Let `g` be complex differentiable with `deriv g (X τ) ≠ 0`, let `X` be continuous on `s` and
satisfy `g (X σ) = f σ` for `σ ∈ s`, and let `f` be complex differentiable at `τ ∈ s`.  Then `X`
is complex differentiable at `τ` within `s`.

Indeed `g` is analytic at `X τ`, hence strictly differentiable there with invertible differential;
its local inverse `ρ` is analytic at `g (X τ) = f τ`, and `ρ (g w) = w` for `w` near `X τ`.  By
continuity of `X` at `τ` within `s` this gives `X σ = ρ (f σ)` for `σ ∈ s` close to `τ`, and
`ρ ∘ f` is complex differentiable at `τ`. -/
theorem differentiableWithinAt_of_comp_eq_of_continuousOn {g X f : ℂ → ℂ} {s : Set ℂ} {τ : ℂ}
    (hτ : τ ∈ s) (hg : Differentiable ℂ g) (hX : ContinuousOn X s)
    (heq : ∀ σ ∈ s, g (X σ) = f σ) (hderiv : deriv g (X τ) ≠ 0)
    (hf : DifferentiableAt ℂ f τ) : DifferentiableWithinAt ℂ X s τ := by
  have hzan : AnalyticAt ℂ g (X τ) := hg.analyticAt (X τ)
  have hsd : HasStrictDerivAt g (deriv g (X τ)) (X τ) := hzan.hasStrictDerivAt
  set ρ : ℂ → ℂ := HasStrictDerivAt.localInverse g (deriv g (X τ)) (X τ) hsd hderiv with hρ
  have hρan : AnalyticAt ℂ ρ (g (X τ)) := hzan.analyticAt_localInverse hderiv
  have hρid : ∀ᶠ w in 𝓝 (X τ), ρ (g w) = w := hsd.eventually_left_inverse hderiv
  have hρdiff : DifferentiableAt ℂ ρ (f τ) := by
    rw [← heq τ hτ]; exact hρan.differentiableAt
  have hcomp : DifferentiableAt ℂ (ρ ∘ f) τ := hρdiff.comp τ hf
  have hmem : X =ᶠ[𝓝[s] τ] (ρ ∘ f) := by
    have h1 : ∀ᶠ σ in 𝓝[s] τ, ρ (g (X σ)) = X σ :=
      (hX.continuousWithinAt hτ).eventually hρid
    refine Filter.mem_of_superset (Filter.inter_mem h1 self_mem_nhdsWithin) ?_
    intro σ hσ
    obtain ⟨hσ1, hσs⟩ := hσ
    have hσ1' : ρ (g (X σ)) = X σ := hσ1
    show X σ = ρ (f σ)
    rw [← hσ1', heq σ hσs]
  exact DifferentiableWithinAt.congr_of_eventuallyEq hcomp.differentiableWithinAt hmem
    (hmem.self_of_nhdsWithin hτ)

theorem exists_differentiable_strip_lift {F : ℂ → ℂ} {z₀ p₀ : ℂ}
    (hFdiff : Differentiable ℂ F)
    (hnocrit : ∀ w ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀, deriv F w ≠ 0)
    (hmap : Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hcover : ∀ n : ℕ, IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n))
    {B C : ℝ} (hB : 0 < B) {Φ : ℂ → ℂ}
    (hΦ : ∀ τ : ℂ, C < τ.re → |τ.im| < B →
      Φ τ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧
      F (Φ τ) = Φ (τ + 1) ∧ DifferentiableAt ℂ Φ τ)
    (n : ℕ) :
    ∃ X : ℂ → ℂ, DifferentiableOn ℂ X (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) ∧
      (∀ τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B,
        X τ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧ (F^[n]) (X τ) = Φ (τ + n)) ∧
      (∀ τ ∈ Work.FatouParabolic.Core.tailStrip C B, X τ = Φ τ) := by
  classical
  -- the continuous lift of `τ ↦ Φ (τ + n)` through the covering `F^[n]`
  obtain ⟨X, hXcont, hXprop, hXagree⟩ :=
    Work.FatouParabolic.Core.exists_strip_lift (F := F) (z₀ := z₀) (p₀ := p₀) (B := B) (C := C)
      hB hmap hcover Φ hΦ n
  refine ⟨X, ?_, hXprop, hXagree⟩
  intro τ hτ
  -- `τ + n` lies in the shallower strip, where `Φ` is known to be holomorphic
  have hτC : C < (τ + (n : ℂ)).re := by
    have h : (τ + (n : ℂ)).re = τ.re + (n : ℝ) := by simp
    rw [h]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hτ.1]
  have hτB : |(τ + (n : ℂ)).im| < B := by
    have h : (τ + (n : ℂ)).im = τ.im := by simp
    rw [h]; exact hτ.2
  refine differentiableWithinAt_of_comp_eq_of_continuousOn
    (f := fun σ : ℂ => Φ (σ + (n : ℂ))) hτ (hFdiff.iterate n) hXcont
    (fun σ hσ => (hXprop σ hσ).2) ?_ ?_
  · -- the derivative of `F^[n]` does not vanish on the immediate basin
    exact deriv_iterate_ne_zero_of_mapsTo hFdiff hmap hnocrit n (X τ) (hXprop τ hτ).1
  · -- `σ ↦ Φ (σ + n)` is complex differentiable at `τ`
    have h2 := (hΦ (τ + (n : ℂ)) hτC hτB).2.2
    exact h2.comp τ (by fun_prop)

end Work.FatouParabolic.Core.ImmBasin
