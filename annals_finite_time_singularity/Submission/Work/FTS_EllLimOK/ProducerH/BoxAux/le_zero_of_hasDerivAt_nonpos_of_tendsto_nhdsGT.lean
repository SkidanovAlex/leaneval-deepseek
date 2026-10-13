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

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

/-- **One-sided maximum principle (left endpoint).**

If `h` is differentiable on the open interval `(a,b)` with derivative `h' ≤ 0` there, and if
`h` tends to some `c ≤ 0` at the left endpoint `a` (along `(a,b)`), then `h ≤ 0` on all of
`(a,b)`.  Indeed `h` is antitone on `(a,b)`, so `h x ≤ lim_{t→a⁺} h t = c` for every
`x ∈ (a,b)`.

The companion statement `le_zero_of_hasDerivAt_nonneg_of_tendsto_nhdsLT` is the mirrored
version at the right endpoint. -/
theorem le_zero_of_hasDerivAt_nonpos_of_tendsto_nhdsGT {a b c : ℝ} (hab : a < b)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x)
    (hle : ∀ x ∈ Set.Ioo a b, h' x ≤ 0)
    (hlim : Filter.Tendsto h (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≤ 0) :
    ∀ x ∈ Set.Ioo a b, h x ≤ 0 := by
  have _ : a < b := hab
  have hcont : ContinuousOn h (Set.Ioo a b) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  -- `h` is antitone on `(a,b)`: its derivative there is `h' ≤ 0`.
  have hAnti : AntitoneOn h (Set.Ioo a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo a b) hcont ?_ ?_
    · intro y hy
      rw [interior_Ioo] at hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hd y hy).deriv]
      exact hle y hy
  intro x hx
  -- `h x` is a lower bound of `h` on a right-neighbourhood of `a`, hence `h x ≤ c`.
  have hxc : h x ≤ c := by
    refine ge_of_tendsto hlim ?_
    have h1 : Set.Iio x ∈ nhdsWithin a (Set.Ioi a) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hx.1)
    filter_upwards [h1, self_mem_nhdsWithin] with t htx ht
    exact hAnti ⟨ht, lt_of_lt_of_le htx hx.2.le⟩ hx htx.le
  linarith

end Work.FTS_EllLimOK.ProducerH.BoxAux
