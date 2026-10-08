import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

theorem finrank_ker_dualMap_sub_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Module.Finite (ZMod 2) V] (f : V →ₗ[ZMod 2] V) :
    Module.finrank (ZMod 2) (LinearMap.ker (f.dualMap - 1)) =
      Module.finrank (ZMod 2) (LinearMap.ker (f - 1)) := by
  -- The dual of `f - 1` is `f.dualMap - 1`, and dualisation preserves the rank.
  have h1 : f.dualMap - 1 = (f - 1).dualMap := by
    ext φ x
    simp
  rw [h1]
  have hrg : Module.finrank (ZMod 2) (LinearMap.range (f - 1).dualMap)
      = Module.finrank (ZMod 2) (LinearMap.range (f - 1)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (f - 1)
  -- rank–nullity for `(f - 1).dualMap` and for `f - 1`, together with
  -- `finrank (Dual K V) = finrank K V`.
  have h2 := LinearMap.finrank_range_add_finrank_ker (f - 1).dualMap
  have h3 := LinearMap.finrank_range_add_finrank_ker (f - 1)
  rw [hrg, Subspace.dual_finrank_eq] at h2
  exact Nat.add_left_cancel (h2.trans h3.symm)

end Work.Hering.Wagner
