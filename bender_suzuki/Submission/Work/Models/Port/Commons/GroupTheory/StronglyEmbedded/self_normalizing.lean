import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- A subgroup `M` of even order that meets every one of its conjugates (by an
element outside `M`) in an odd-order subgroup is self-normalizing.

Proof: `M` always lies in its normalizer, so it remains to show `N_G(M) ≤ M`.
Take `g ∈ N_G(M)`. If `g ∉ M`, then conjugation by `g` preserves `M`, so
`M ≤ M.map (MulAut.conj g)`; hence `M ⊓ M.map (MulAut.conj g) = M`, which has
even order — contradicting the hypothesis that this intersection has odd order
for every `g ∉ M`. -/
theorem self_normalizing {G : Type*} [Group G] (M : Subgroup G)
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)))) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  refine le_antisymm ?_ ?_
  · intro g hgN
    by_contra hgM
    have hodd : Odd (Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
      hOdd g hgM
    have hMleMap : M ≤ M.map (MulAut.conj g).toMonoidHom := by
      intro m hm
      refine ⟨g⁻¹ * m * g, ?_, ?_⟩
      · exact ((Subgroup.mem_set_normalizer_iff''.mp hgN) m).mp hm
      · change g * (g⁻¹ * m * g) * g⁻¹ = m
        group
    have hEq : (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) = M := by
      refine le_antisymm inf_le_left ?_
      intro m hm
      exact ⟨hm, hMleMap hm⟩
    have hEvenI :
        Even (Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)) := by
      rw [hEq]
      exact hEven
    exact (Nat.not_even_iff_odd.mpr hodd) hEvenI
  · exact Subgroup.le_normalizer

end Commons.GroupTheory.StronglyEmbedded