import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open Filter Set
open scoped Topology

theorem hasDerivWithinAt_of_tendsto_deriv (f g : ℝ → ℝ) {T L : ℝ} (hT : 0 < T)
    (hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (g t) t)
    (hcontf : ContinuousWithinAt f (Set.Ico 0 T) 0)
    (htend : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ico 0 T)) (nhds L)) :
    HasDerivWithinAt f L (Set.Ico 0 T) 0 := by
  -- `f` is differentiable on the open interval `(0, T)` with derivative `g`
  have hdf : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  -- continuity at `0` from the right is inherited from continuity within `[0, T)`
  have hcw : ContinuousWithinAt f (Set.Ioo 0 T) 0 :=
    hcontf.mono fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  -- `(0, T)`, and hence `[0, T)`, are neighbourhoods of `0` in the right filter
  have hIoo : Set.Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT
  have hIco : Set.Ico (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset hIoo fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  -- consequently `g → L` along the right filter at `0`
  have hgt : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (nhds L) :=
    htend.mono_left (nhdsWithin_le_iff.mpr hIco)
  -- on `(0, T)` the derivative `deriv f` agrees with `g`
  have heq : (fun x => deriv f x) =ᶠ[𝓝[>] (0 : ℝ)] g := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ioo 0 T, hIoo, fun x hx => (hderiv x hx).deriv⟩
  have hlim' : Filter.Tendsto (fun x => deriv f x) (𝓝[>] (0 : ℝ)) (nhds L) :=
    Filter.Tendsto.congr' heq.symm hgt
  -- the boundary-differentiability extension theorem gives the right derivative at `0`
  exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdf hcw hIoo hlim').mono fun _ hx => hx.1

end Work.Diff.GE
