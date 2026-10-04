import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.indexTransfer

/-- **Second derivative test, necessary condition.**

If `f` has a (non-strict) local maximum at `0`, if `f` is differentiable at `0` and if the
derivative `deriv f` is itself differentiable at `0` with derivative `c`, then `c ≤ 0`.

The proof is the classical one.  Fermat's theorem gives `deriv f 0 = 0`.  If moreover `0 < c`,
then the second-derivative test (`isLocalMin_of_deriv_deriv_pos`) turns `0` into a local *minimum*
of `f` as well, so `f` is eventually equal to the constant `f 0` near `0`; hence `deriv f` vanishes
on a whole neighbourhood of `0`, which forces `deriv (deriv f) 0 = 0`, i.e. `c = 0`, a
contradiction. -/
theorem second_deriv_nonpos_of_eventually_le {f : ℝ → ℝ} {c : ℝ}
    (h1 : DifferentiableAt ℝ f 0)
    (h2 : HasDerivAt (deriv f) c 0)
    (h3 : ∀ᶠ σ in nhds (0 : ℝ), DifferentiableAt ℝ f σ)
    (h4 : ∀ᶠ σ in nhds (0 : ℝ), f σ ≤ f 0) : c ≤ 0 := by
  by_contra hcon
  have hc : 0 < c := not_le.mp hcon
  -- Fermat's theorem: at a local maximum the first derivative vanishes.
  have hmax : IsLocalMax f 0 := by
    show ∀ᶠ σ in nhds (0 : ℝ), f σ ≤ f 0
    exact h4
  have hf0 : deriv f 0 = 0 := hmax.deriv_eq_zero
  -- `h2` says exactly that the second derivative of `f` at `0` is `c`.
  have hcc : deriv (deriv f) 0 = c := h2.deriv
  -- Second-derivative test: a strictly positive second derivative forces a local minimum.
  have hmin : IsLocalMin f 0 :=
    isLocalMin_of_deriv_deriv_pos (f := f) (x₀ := 0) (by rw [hcc]; exact hc) hf0 h1.continuousAt
  have hmin' : ∀ᶠ σ in nhds (0 : ℝ), f 0 ≤ f σ := hmin
  -- Being simultaneously a local minimum and a local maximum, `f` is eventually constant near `0`.
  have hconst : f =ᶠ[nhds (0 : ℝ)] fun _ => f 0 := by
    filter_upwards [h4, hmin'] with σ hσ₁ hσ₂
    exact le_antisymm hσ₁ hσ₂
  -- Hence `deriv f` vanishes on a neighbourhood of `0`, so its derivative at `0` is `0`.
  have hzero : deriv f =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
    have h := Filter.EventuallyEq.deriv hconst
    rwa [deriv_const'] at h
  have hc0 : c = 0 := by
    rw [← hcc, Filter.EventuallyEq.deriv_eq hzero, deriv_const]
  linarith

end Work.OddBound.indexTransfer
