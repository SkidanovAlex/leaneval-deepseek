import Mathlib
import Submission.Work.LT.gb_rank_defs

namespace Work.LT

/-- (file `Submission/Work/LT/gb_finrank_map_add_finrank_inf_ker.lean`, inside `namespace Work.LT` / `namespace GB`, importing `Submission.Work.LT.gb_rank_defs`) Rank--nullity for the restriction of a linear map to a submodule: the dimension of `p.map f` plus the dimension of `p ⊓ ker f` equals the dimension of `p`. -/
lemma gb_finrank_map_add_finrank_inf_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : V →ₗ[K] W) (p : Submodule K V) :
    Module.finrank K (p.map f) + Module.finrank K ↥(p ⊓ (LinearMap.ker f : Submodule K V))
      = Module.finrank K ↥p := by
  -- Apply rank--nullity to the composite `f ∘ p.subtype : p → W`.
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.comp p.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype] at hrn
  -- Its kernel is `comap p.subtype (ker f) = comap p.subtype (p ⊓ ker f)`, which is
  -- linearly equivalent to `p ⊓ ker f`.
  have hker : LinearMap.ker (f.comp p.subtype)
      = Submodule.comap p.subtype (p ⊓ LinearMap.ker f) := by
    rw [LinearMap.ker_comp, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  rw [hker] at hrn
  have hfin := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : p ⊓ (LinearMap.ker f : Submodule K V) ≤ p)).finrank_eq
  rw [hfin] at hrn
  exact hrn

end Work.LT
