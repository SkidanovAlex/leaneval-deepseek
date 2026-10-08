import Mathlib
import Submission.Work.Reductions.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

/-- If `H` is strongly embedded then it is its own normalizer: any `g` normalizing `H` would
satisfy `H = H ⊓ H^g`, which has even order, contradicting the odd-order condition of strong
embeddedness. -/
theorem stronglyEmbedded_normalizer_eq {G : Type} [Group G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) : Subgroup.normalizer H = H := by
  obtain ⟨hne, heven, hodd⟩ := hH
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro g hg
  by_contra hgn
  have hmem : ∀ n : G, g * n * g⁻¹ ∈ H ↔ n ∈ H :=
    fun n => (Subgroup.mem_normalizer_iff.mp hg n).symm
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      rw [← hzy]
      exact (hmem z).mpr hz
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · exact (hmem (g⁻¹ * y * g)).mp
          (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y from by group])
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hthis := hodd g hgn
  rw [hmap, inf_idem] at hthis
  exact (Nat.not_even_iff_odd.mpr hthis) heven

end Work.Reductions
