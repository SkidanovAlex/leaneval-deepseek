import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

/-- **A one-sided comparison principle.**

If `h` is differentiable on the open interval `(a,b)` with nonnegative derivative there, and
`h` tends to `c ≤ 0` as `x → b⁻`, then `h ≤ 0` on all of `(a,b)`.

Proof: `h` is monotone nondecreasing on `(a,b)` by the mean value theorem
(`monotoneOn_of_deriv_nonneg`, using `deriv h x = h' x ≥ 0`).  For a fixed `x < b` we may
therefore compare `h` with the constant `h x` along the filter `𝓝[Ioo x b] b` (nontrivial
because `x < b`), and pass to the limit `c`. -/
theorem le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT {a b c : ℝ} (hab : a < b)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x)
    (hge : ∀ x ∈ Set.Ioo a b, 0 ≤ h' x)
    (hlim : Filter.Tendsto h (nhdsWithin b (Set.Iio b)) (nhds c)) (hc : c ≤ 0) :
    ∀ x ∈ Set.Ioo a b, h x ≤ 0 := by
  intro x hx
  have hxb : x < b := hx.2
  -- `h` is monotone nondecreasing on `(a,b)`.
  have hmono : MonotoneOn h (Set.Ioo a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo a b) ?_ ?_ ?_
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hd y hy).deriv]
      exact hge y hy
  -- the filter `𝓝[Ioo x b] b` is nontrivial, and `Ioo x b ⊆ Iio b`.
  have hne : Filter.NeBot (nhdsWithin b (Set.Ioo x b)) := right_nhdsWithin_Ioo_neBot hxb
  have htend : Filter.Tendsto h (nhdsWithin b (Set.Ioo x b)) (nhds c) :=
    hlim.mono_left (nhdsWithin_mono b Set.Ioo_subset_Iio_self)
  -- `h x ≤ h t` eventually as `t → b⁻`.
  have hle : ∀ᶠ t in nhdsWithin b (Set.Ioo x b), h x ≤ h t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmono hx ⟨lt_trans hx.1 ht.1, ht.2⟩ (le_of_lt ht.1)
  have hxc : h x ≤ c :=
    le_of_tendsto_of_tendsto (b := nhdsWithin b (Set.Ioo x b)) (hb := hne)
      tendsto_const_nhds htend hle
  exact le_trans hxc hc

end Work.FTS_EllLimOK.ProducerH.BoxAux
