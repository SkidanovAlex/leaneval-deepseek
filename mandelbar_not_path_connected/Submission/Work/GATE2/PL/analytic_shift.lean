/-
# Propagation of analyticity along a shift

If `ψ : ℂ → ℂ` is continuous and satisfies `F (ψ w) = ψ (w + 1)` for an entire `F` whose
derivative does not vanish on `ψ '' ℂ`, then analyticity of `ψ` on a right half-plane
`{Re > X}` propagates to all of `ℂ`: at a point `w₀` one has
`ψ z = ρ (ψ (z + 1))` for `z` near `w₀`, where `ρ` is the local analytic inverse of `F` at
`ψ w₀` (Mathlib's `AnalyticAt.analyticAt_localInverse`), and `ψ (· + 1)` is analytic near `w₀`
by hypothesis.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open scoped Topology
open Classical

variable {F ψ : ℂ → ℂ}

/-- **Propagation of analyticity one step to the left along a shift.**
If `ψ` is continuous at `w₀`, is analytic at `w₀ + 1`, and `F (ψ z) = ψ (z + 1)` for `z` near
`w₀`, with `F` analytic at `ψ w₀` and `deriv F (ψ w₀) ≠ 0`, then `ψ` is analytic at `w₀`. -/
theorem analyticAt_of_shift {w₀ : ℂ} (hF : AnalyticAt ℂ F (ψ w₀))
    (hderiv : deriv F (ψ w₀) ≠ 0) (hshift : F (ψ w₀) = ψ (w₀ + 1))
    (hψ1 : AnalyticAt ℂ ψ (w₀ + 1)) (hcont : ContinuousAt ψ w₀)
    (heq : ∀ᶠ z in 𝓝 w₀, F (ψ z) = ψ (z + 1)) :
    AnalyticAt ℂ ψ w₀ := by
  have hρa : AnalyticAt ℂ (hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv)
      (F (ψ w₀)) := hF.analyticAt_localInverse hderiv
  have hρa' : AnalyticAt ℂ (hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv)
      (ψ (w₀ + 1)) := by rw [← hshift]; exact hρa
  have hρF : ∀ᶠ z in 𝓝 (ψ w₀),
      hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv (F z) = z :=
    HasStrictDerivAt.eventually_left_inverse hF.hasStrictDerivAt hderiv
  have h2 : ψ =ᶠ[𝓝 w₀]
      fun z => hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv (ψ (z + 1)) := by
    filter_upwards [heq, hcont.eventually hρF] with z hz hzρ
    rw [← hzρ, hz]
  have h4 : AnalyticAt ℂ (fun z : ℂ => z + 1) w₀ := analyticAt_id.add analyticAt_const
  have h5 : AnalyticAt ℂ ψ ((fun z : ℂ => z + 1) w₀) := hψ1
  have h6 : AnalyticAt ℂ (fun z : ℂ => ψ (z + 1)) w₀ :=
    AnalyticAt.comp (f := fun z : ℂ => z + 1) (x := w₀) h5 h4
  have h7 : AnalyticAt ℂ
      (fun z => hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv (ψ (z + 1)))
      w₀ := AnalyticAt.comp (f := fun z : ℂ => ψ (z + 1)) (x := w₀) hρa' h6
  exact h7.congr h2.symm

/-- **Global propagation.**  If `ψ : ℂ → ℂ` is continuous, satisfies `F (ψ w) = ψ (w + 1)` for
all `w`, and `deriv F` does not vanish on the image of `ψ`, with `F` entire, then analyticity of
`ψ` on the right half-plane `{Re > X}` implies that `ψ` is analytic everywhere. -/
theorem analyticAt_of_shift_global (hcont : Continuous ψ) (hF : ∀ z, AnalyticAt ℂ F z)
    (hderiv : ∀ w : ℂ, deriv F (ψ w) ≠ 0) (hshift : ∀ w : ℂ, F (ψ w) = ψ (w + 1))
    {X : ℝ} (hbase : ∀ w : ℂ, X < w.re → AnalyticAt ℂ ψ w) :
    ∀ w : ℂ, AnalyticAt ℂ ψ w := by
  have hmain : ∀ n : ℕ, ∀ w : ℂ, X < w.re + (n : ℝ) → AnalyticAt ℂ ψ w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      exact hbase w (by simpa using hw)
    | succ n ih =>
      intro w hw
      have hw1 : X < (w + 1).re + (n : ℝ) := by
        have h2 : w.re + ((n + 1 : ℕ) : ℝ) = w.re + 1 + (n : ℝ) := by push_cast; ring
        rw [h2] at hw
        simpa using hw
      have h1 : AnalyticAt ℂ ψ (w + 1) := ih (w + 1) hw1
      refine analyticAt_of_shift (hF (ψ w)) (hderiv w) (hshift w) h1 hcont.continuousAt ?_
      exact Eventually.of_forall fun z => hshift z
  intro w
  obtain ⟨n, hn⟩ := exists_nat_gt (X - w.re)
  exact hmain n w (by linarith)

end Work.GATE2.PL
