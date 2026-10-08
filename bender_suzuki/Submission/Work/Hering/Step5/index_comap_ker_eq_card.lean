import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step5

theorem index_comap_ker_eq_card {M A : Type*} [Group M] [Group A] (f : M →* A)
    (hf : Function.Surjective f) (Λ : Subgroup A) :
    (Subgroup.comap (Subgroup.comap f Λ).subtype f.ker).index = Nat.card Λ := by
  -- `comap (comap f Λ).subtype f.ker` is exactly `f.ker.subgroupOf (comap f Λ)`,
  -- i.e. `f.ker.relIndex (comap f Λ)`.
  show f.ker.relIndex (Subgroup.comap f Λ) = Nat.card Λ
  rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective hf Λ]

end Work.Hering.Step5
