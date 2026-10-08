import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ZassenhausPSL2.Feit

theorem sylow_conj_le {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {Q P : Subgroup G} (hQ : IsPGroup p Q)
    (hidx : ¬ p ∣ Q.index) (hP : IsPGroup p P) :
    ∃ g : G, P ≤ Q.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `Q` is the underlying subgroup of a Sylow `p`-subgroup, since its index is
  -- prime to `p`.
  let Qs : Sylow p G := hQ.toSylow hidx
  have hQcoe : (Qs : Subgroup G) = Q := rfl
  -- `P` is contained in some Sylow `p`-subgroup `S`.
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  -- Sylow's second theorem: all Sylow `p`-subgroups are conjugate.
  obtain ⟨g, hg⟩ : ∃ g : G, g • S = Qs :=
    MulAction.IsPretransitive.exists_smul_eq (M := G) S Qs
  refine ⟨g⁻¹, ?_⟩
  have hS : (S : Subgroup G) = Qs.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 : S = g⁻¹ • Qs := by rw [← hg, inv_smul_smul]
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  calc P ≤ (S : Subgroup G) := hPS
    _ = Qs.map (MulAut.conj g⁻¹).toMonoidHom := hS
    _ = Q.map (MulAut.conj g⁻¹).toMonoidHom := by rw [hQcoe]

end Work.ZassenhausPSL2.Feit
