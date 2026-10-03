import Mathlib
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular
import Submission.Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann

set_option autoImplicit false

namespace Work.Rep.Ore

open Work.ORVonNeumann

/-- A (two-sided) non-zero-divisor of the group von Neumann algebra `N(G)` acts as an
injective operator on `ℓ²(G)`.

The orthogonal projection `q` onto the kernel of `T` lies in `N(G)`
(`Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann`), since `T` commutes with the
right regular representation and hence the kernel is invariant under it.  Because the range
of `q` is exactly the kernel of `T`, we have `T * q = 0`; a non-zero-divisor of `N(G)` kills
only zero, so `q = 0`.  The kernel of `T` is therefore trivial. -/
theorem injective_of_mem_nonZeroDivisors {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (T : ↥(Work.ORVonNeumann.groupVonNeumann G)) (hT : T ∈ nonZeroDivisors (↥(Work.ORVonNeumann.groupVonNeumann G))) : Function.Injective (T : Work.ORVonNeumann.boundedEnd G) := by
  -- a non-zero-divisor of `N(G)` kills only zero on the left
  have hleft : ∀ z : ↥(groupVonNeumann G), T * z = 0 → z = 0 :=
    (mem_nonZeroDivisors_iff.mp hT).1
  -- the orthogonal projection onto the kernel of `T` lies in `N(G)`
  have hqmem : (T : boundedEnd G).ker.starProjection ∈ groupVonNeumann G :=
    Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann (T : boundedEnd G) T.2
  -- `T` annihilates that projection, its range being the kernel of `T`
  have hTq : (T : boundedEnd G) * (T : boundedEnd G).ker.starProjection = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    show (T : boundedEnd G) ((T : boundedEnd G).ker.starProjection v) = 0
    exact LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem (T : boundedEnd G).ker v)
  -- hence the projection is zero
  have hq0 : (T : boundedEnd G).ker.starProjection = 0 := by
    have hz : T * ⟨(T : boundedEnd G).ker.starProjection, hqmem⟩ = 0 := by
      apply Subtype.ext
      exact hTq
    have := congrArg Subtype.val (hleft _ hz)
    simpa using this
  -- and the kernel of `T` is trivial
  intro x y hxy
  have hker : x - y ∈ (T : boundedEnd G).ker := by
    rw [LinearMap.mem_ker]
    show (T : boundedEnd G) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hfix : (T : boundedEnd G).ker.starProjection (x - y) = x - y :=
    Submodule.starProjection_eq_self_iff.mpr hker
  rw [hq0, zero_apply] at hfix
  exact sub_eq_zero.mp hfix.symm

end Work.Rep.Ore
