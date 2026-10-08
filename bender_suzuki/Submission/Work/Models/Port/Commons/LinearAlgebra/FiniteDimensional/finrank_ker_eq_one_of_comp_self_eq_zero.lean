import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.LinearAlgebra.FiniteDimensional

/-- If `V` is a two-dimensional vector space over a field `K` and `T : V →ₗ[K] V`
is a nonzero linear map with `T ∘ T = 0`, then the kernel of `T` is one-dimensional.

Indeed `T.range ≤ T.ker` because `T.comp T = 0`; rank–nullity gives
`finrank T.range + finrank T.ker = 2`; `T ≠ 0` gives `finrank T.range ≥ 1`, and
monotonicity of `finrank` gives `finrank T.range ≤ finrank T.ker`. Hence both
are `1`. -/
theorem finrank_ker_eq_one_of_comp_self_eq_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hfin : Module.finrank K V = 2) (T : V →ₗ[K] V)
    (hT : T.comp T = 0) (hTne : T ≠ 0) : Module.finrank K T.ker = 1 := by
  -- `T ∘ T = 0` means the range of `T` is contained in its kernel
  have hle : T.range ≤ T.ker := by
    rw [LinearMap.range_le_ker_iff]
    exact hT
  -- rank–nullity, together with `finrank K V = 2`
  have hrank := LinearMap.finrank_range_add_finrank_ker T
  rw [hfin] at hrank
  -- `finrank T.range ≤ finrank T.ker`
  have hmono : Module.finrank K T.range ≤ Module.finrank K T.ker :=
    Submodule.finrank_mono hle
  -- `T ≠ 0` means the range is nonzero, hence `0 < finrank T.range`
  have hne : T.range ≠ ⊥ := fun h => hTne (LinearMap.range_eq_bot.mp h)
  have hpos : 0 < Module.finrank K T.range := by
    by_contra h
    exact hne (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos h))
  omega

end Commons.LinearAlgebra.FiniteDimensional