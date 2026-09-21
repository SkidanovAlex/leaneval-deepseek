import Mathlib

namespace Work.OddVolterra.RowIdentity

open Filter Topology

/-- If `β` is smooth on all of `ℝ`, `y` is smooth on an open set `U`, and the
topological support of `β` is contained in `U`, then `t ↦ β t * y t` is smooth
on all of `ℝ`.

This is the standard "localisation" argument: away from `tsupport β` the product
vanishes identically on a neighbourhood, while on `U` both factors are smooth. -/
theorem contDiff_mul_of_contDiffOn_of_tsupport_subset {β y : ℝ → ℝ} {U : Set ℝ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hU : IsOpen U) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y U)
    (hsupp : tsupport β ⊆ U) : ContDiff ℝ (⊤ : ℕ∞) (fun t => β t * y t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · -- On `U` both factors are smooth at `x`.
    exact hβ.contDiffAt.mul (hy.contDiffAt (hU.mem_nhds hx))
  · -- Off `U`, and hence off `tsupport β`, the coefficient vanishes near `x`.
    have hx' : β =ᶠ[nhds x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsupp h))
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (by
      filter_upwards [hx'] with t ht
      simp [ht])

end Work.OddVolterra.RowIdentity
