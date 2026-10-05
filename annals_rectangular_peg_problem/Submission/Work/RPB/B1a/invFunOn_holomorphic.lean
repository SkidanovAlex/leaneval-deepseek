import Mathlib

open Filter

namespace Work.RPB.B1a

-- **The inverse of a locally biholomorphic map is holomorphic.**  If `Gamma` is complex
-- differentiable on the open set `A`, injective there, with `deriv Gamma ≠ 0` on `A`, then
-- `Function.invFunOn Gamma A` is holomorphic on `Gamma '' A` and is a left/right inverse of `Gamma`.
--
-- Route: For `w0 = Gamma z0` with `z0 ∈ A`: the inverse function theorem
-- (`HasStrictDerivAt.localInverse`, `HasStrictDerivAt.to_localInverse`,
-- `HasStrictDerivAt.eventually_left_inverse`, from `hd.differentiableAt` + `hd' z0`) gives a local
-- inverse `r`, holomorphic near `w0`, with `r (Gamma z) = z` eventually near `z0`; injectivity of
-- `Gamma` on `A` (note `A ∈ 𝓝 z0`) then gives `r =ᶠ[𝓝 w0] Function.invFunOn Gamma A`, so
-- `Function.invFunOn Gamma A` is differentiable at `w0`.  The two inverse identities follow from
-- `Function.invFunOn_eq` / `Function.invFunOn_mem` and injectivity.  (`Gamma '' A` need not be proved
-- open for `DifferentiableOn` on it; if useful it follows from the local open mapping theorem.)
theorem invFunOn_holomorphic {Γ : ℂ → ℂ} {A : Set ℂ} (hA : IsOpen A)
    (hd : DifferentiableOn ℂ Γ A) (hi : Set.InjOn Γ A) (hd' : ∀ w ∈ A, deriv Γ w ≠ 0) :
    DifferentiableOn ℂ (Function.invFunOn Γ A) (Γ '' A) ∧
      (∀ w ∈ A, Function.invFunOn Γ A (Γ w) = w) ∧
      (∀ y ∈ Γ '' A, Γ (Function.invFunOn Γ A y) = y) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `Function.invFunOn Γ A` is differentiable at each point `Γ x` of `Γ '' A`.
    rintro _ ⟨x, hxU, rfl⟩
    -- `Γ` is analytic at `x`, hence strictly differentiable there.
    have han : AnalyticAt ℂ Γ x := hd.analyticOnNhd hA x hxU
    have hsd : HasStrictDerivAt Γ (deriv Γ x) x := han.hasStrictDerivAt
    have hxne : deriv Γ x ≠ 0 := hd' x hxU
    -- The local inverse produced by the inverse function theorem.
    set r : ℂ → ℂ := hsd.localInverse Γ (deriv Γ x) x hxne with hr
    have hr' : HasStrictDerivAt r (deriv Γ x)⁻¹ (Γ x) := hsd.to_localInverse hxne
    have hrdiff : DifferentiableAt ℂ r (Γ x) := hr'.hasStrictFDerivAt.differentiableAt
    have hright : ∀ᶠ y in nhds (Γ x), Γ (r y) = y := hsd.eventually_right_inverse hxne
    have hleft : r (Γ x) = x := by
      have h := hsd.eventually_left_inverse hxne
      rw [← hr] at h
      exact h.self_of_nhds
    -- `r` is continuous at `Γ x`, so it takes values in the open set `A` near `Γ x`.
    have hUev : ∀ᶠ y in nhds (Γ x), r y ∈ A := by
      have hcont : ContinuousAt r (Γ x) := hr'.hasStrictFDerivAt.continuousAt
      have : A ∈ nhds (r (Γ x)) := by rw [hleft]; exact hA.mem_nhds hxU
      exact hcont.preimage_mem_nhds this
    -- Uniqueness of a preimage in `A` identifies `r` with `Function.invFunOn Γ A`.
    have heq : Function.invFunOn Γ A =ᶠ[nhds (Γ x)] r := by
      filter_upwards [hright, hUev] with y hry hryU
      have hex : ∃ z, z ∈ A ∧ Γ z = y := ⟨r y, hryU, hry⟩
      exact hi (Function.invFunOn_mem hex) hryU (by rw [Function.invFunOn_eq hex, hry])
    exact (hrdiff.congr_of_eventuallyEq heq).differentiableWithinAt
  · -- Left inverse identity.
    intro w hw
    have hex : ∃ z, z ∈ A ∧ Γ z = Γ w := ⟨w, hw, rfl⟩
    exact hi (Function.invFunOn_mem hex) hw (Function.invFunOn_eq hex)
  · -- Right inverse identity.
    rintro y ⟨x, hxA, rfl⟩
    exact Function.invFunOn_eq ⟨x, hxA, rfl⟩

end Work.RPB.B1a
