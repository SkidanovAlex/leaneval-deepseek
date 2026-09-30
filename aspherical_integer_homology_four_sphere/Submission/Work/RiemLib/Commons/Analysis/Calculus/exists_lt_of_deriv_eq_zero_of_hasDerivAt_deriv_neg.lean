import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.Calculus

open Set Filter Topology

/-- **Second derivative test, strict local maximum form (one-sided version), `deriv`-form.**

If `f` is continuous at `0`, `deriv f 0 = 0`, and `deriv f` has derivative `c < 0` at `0`,
then `f s < f 0` for every small `s > 0`.

The key point is that `deriv f` is differentiable at `0` with derivative `c`, so on a right
neighbourhood of `0` the derivative `deriv f` is strictly negative: indeed `deriv f` is
approximated by `x ↦ c x` which is negative for `x > 0`. At such a point `deriv f x ≠ 0`,
whence `f` is actually differentiable there, and the strict decrease follows from the
sign of the derivative. Note that `f` need not be differentiable at `0` itself; only its
continuity at `0` is required for the mean value / monotonicity argument. -/
theorem exists_lt_of_deriv_eq_zero_of_hasDerivAt_deriv_neg {f : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousAt f 0) (h1 : deriv f 0 = 0) (h2 : HasDerivAt (deriv f) c 0)
    (hc : c < 0) :
    ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f s < f 0 := by
  have hd0 : deriv f 0 = 0 := h1
  have hdd : deriv (deriv f) 0 < 0 := by rw [h2.deriv]; exact hc
  -- `deriv f` is negative on a right neighbourhood of `0`.
  have hsign : ∀ᶠ x in 𝓝 (0 : ℝ), SignType.sign (deriv f x) = SignType.sign (0 - x) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg (f := deriv f) hdd hd0
  have hright : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv f x < 0 :=
    deriv_neg_right_of_sign_deriv (Eventually.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)) hsign)
  obtain ⟨δ, hδpos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hright
  -- `hδ : ∀ x ∈ Ioo 0 δ, deriv f x < 0`.
  refine ⟨δ / 2, by linarith, ?_⟩
  -- On `Icc 0 (δ/2)` the function `f` is strictly antitone.
  have hcontOn : ContinuousOn f (Icc 0 (δ / 2)) := by
    have hdiff : DifferentiableOn ℝ f (Ioo 0 (δ / 2)) := fun x hx =>
      (differentiableAt_of_deriv_ne_zero
        (hδ ⟨hx.1, by linarith [hx.2]⟩).ne).differentiableWithinAt
    have hhalf : ContinuousAt f (δ / 2) :=
      (differentiableAt_of_deriv_ne_zero
        (hδ ⟨by linarith, by linarith⟩).ne).continuousAt
    rw [← Ioo_union_both (show (0 : ℝ) ≤ δ / 2 by linarith)]
    exact ContinuousOn.union_continuousAt isOpen_Ioo hdiff.continuousOn (by
      rintro x (rfl | rfl)
      · exact hcont
      · exact hhalf)
  have hanti : StrictAntiOn f (Icc 0 (δ / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 (δ / 2)) hcontOn ?_
    intro x hx
    rw [interior_Icc] at hx
    exact hδ ⟨hx.1, by linarith [hx.2]⟩
  intro s hs0 hsd
  exact hanti ⟨le_refl 0, by linarith⟩ ⟨le_of_lt hs0, by linarith⟩ hs0

end Commons.Analysis.Calculus
