import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.FatouParabolic.Core.ImmBasin

noncomputable section

/-- If `F` is differentiable on `ℂ`, maps `Ω` into itself and has no critical point on `Ω`, then
every iterate `F^[n]` has non-vanishing derivative on `Ω` (chain rule, by induction on `n`). -/
theorem deriv_iterate_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {Ω : Set ℂ}
    (hFmap : Set.MapsTo F Ω Ω) (hnocrit : ∀ w ∈ Ω, deriv F w ≠ 0) (n : ℕ) :
    ∀ w ∈ Ω, deriv (F^[n]) w ≠ 0 := by
  induction n with
  | zero =>
      intro w _
      rw [Function.iterate_zero, deriv_id]
      exact one_ne_zero
  | succ n ih =>
      intro w hw
      have hmapn : (F^[n]) w ∈ Ω := hFmap.iterate n hw
      have h1 : DifferentiableAt ℂ F ((F^[n]) w) := hF.differentiableAt
      have h2 : DifferentiableAt ℂ (F^[n]) w := (hF.iterate n).differentiableAt
      have hderiv : deriv (F^[n.succ]) w
          = deriv F ((F^[n]) w) * deriv (F^[n]) w := by
        rw [Function.iterate_succ']
        exact deriv_comp w h1 h2
      rw [hderiv]
      exact mul_ne_zero (hnocrit _ hmapn) (ih w hw)

/-- A continuous right inverse of `F^[n] ∘ · = g`, with values in a set `Ω` on which `F` has no
critical point, is holomorphic wherever `g` is. -/
theorem differentiableOn_of_comp_iterate_eq {F : ℂ → ℂ} (hF : Differentiable ℂ F) {Ω : Set ℂ}
    (hFmap : Set.MapsTo F Ω Ω) (hnocrit : ∀ w ∈ Ω, deriv F w ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) {X g : ℂ → ℂ} (n : ℕ)
    (hXc : ContinuousOn X U) (hXmem : ∀ τ ∈ U, X τ ∈ Ω) (hg : DifferentiableOn ℂ g U)
    (hcomp : ∀ τ ∈ U, (F^[n]) (X τ) = g τ) :
    DifferentiableOn ℂ X U := by
  intro τ₀ hτ₀
  let f : ℂ → ℂ := F^[n]
  let a : ℂ := X τ₀
  have hfdiff : Differentiable ℂ f := hF.iterate n
  have hfa : HasStrictDerivAt f (deriv f a) a := (hfdiff.analyticAt a).hasStrictDerivAt
  have hne : deriv f a ≠ 0 := deriv_iterate_ne_zero hF hFmap hnocrit n a (hXmem τ₀ hτ₀)
  let f' : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f a) hne)
  have hfd : HasStrictFDerivAt f (f' : ℂ →L[ℂ] ℂ) a := hfa.hasStrictFDerivAt_equiv hne
  let ψ : ℂ → ℂ := hfd.localInverse f f' a
  have hψ : HasStrictFDerivAt ψ (f'.symm : ℂ →L[ℂ] ℂ) (f a) := hfd.to_localInverse
  have hfa_eq : f a = g τ₀ := hcomp τ₀ hτ₀
  have hψd : DifferentiableAt ℂ ψ (g τ₀) := by
    rw [← hfa_eq]; exact hψ.differentiableAt
  have hgd : DifferentiableAt ℂ g τ₀ := hg.differentiableAt (hU.mem_nhds hτ₀)
  have hcompd : DifferentiableAt ℂ (ψ ∘ g) τ₀ := hψd.comp τ₀ hgd
  have hXca : ContinuousAt X τ₀ := hXc.continuousAt (hU.mem_nhds hτ₀)
  have hXtend : Tendsto X (𝓝 τ₀) (𝓝 a) := hXca
  have hleft : ∀ᶠ x in 𝓝 a, ψ (f x) = x := hfd.eventually_left_inverse
  have hev1 : ∀ᶠ τ in 𝓝 τ₀, ψ (f (X τ)) = X τ := hXtend.eventually hleft
  have hUn : ∀ᶠ τ in 𝓝 τ₀, τ ∈ U := hU.mem_nhds hτ₀
  have hev : X =ᶠ[𝓝 τ₀] (ψ ∘ g) := by
    filter_upwards [hev1, hUn] with τ h1 h2
    have h2' : f (X τ) = g τ := hcomp τ h2
    simp only [Function.comp_apply]
    rw [← h1, h2']
  exact (hcompd.congr_of_eventuallyEq hev).differentiableWithinAt

end

end Work.FatouParabolic.Core.ImmBasin
