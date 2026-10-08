import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.Step1.exists_mem_inv_mul_mem_of_isSylowIn

namespace Work.ZJB2

open Subgroup

/-- **The Frattini argument.**  If `L ≤ M`, `M` normalizes `L`, and `T` is a Sylow `p`-subgroup
of `L`, then every `g ∈ M` factors as `g = l * n` with `l ∈ L` and `n ∈ M ∩ N(T)`.

The proof uses Sylow conjugacy of `T` and its conjugate `g T g⁻¹` (both Sylow in `L`, the latter
because `g` normalizes `L`) to find `m ∈ L` with `m⁻¹ (g T g⁻¹) m ≤ T`; then `m⁻¹ g` normalizes
`T`, and `g = m * (m⁻¹ g)`. -/
theorem frattiniIn (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Work.ZJB.FrattiniInProp p G := by
  intro M L T hLM hMN hT g hg
  have hTL : T ≤ L := hT.1
  -- The conjugate `g T g⁻¹` lies in `L`, because `g ∈ M ≤ N(L)`.
  have hVL : T.map (MulAut.conj g).toMonoidHom ≤ L := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hgN : g ∈ Subgroup.normalizer (L : Set G) := hMN hg
    rw [Subgroup.mem_normalizer_iff] at hgN
    simpa [MulAut.conj_apply] using (hgN t).mp (hTL ht)
  have hVp : IsPGroup p (T.map (MulAut.conj g).toMonoidHom) := hT.2.1.map _
  -- Sylow conjugacy inside `L`: some `m ∈ L` conjugates `g T g⁻¹` into `T`.
  obtain ⟨m, hmL, hm⟩ :=
    Work.ZJB2.Step1.exists_mem_inv_mul_mem_of_isSylowIn hT hVL hVp
  refine ⟨m, hmL, m⁻¹ * g, ⟨?_, ?_⟩, by group⟩
  · exact M.mul_mem (M.inv_mem (hLM hmL)) hg
  · -- `m⁻¹ * g` normalizes `T`
    have hmap_le : T.map (MulAut.conj (m⁻¹ * g)).toMonoidHom ≤ T := by
      intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      show (MulAut.conj (m⁻¹ * g)) t ∈ T
      have hv : (MulAut.conj g) t ∈ T.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      have hmem := hm _ hv
      have key : (MulAut.conj (m⁻¹ * g)) t = m⁻¹ * (MulAut.conj g) t * m := by
        simp only [MulAut.conj_apply]
        group
      rw [key]
      exact hmem
    have hmap_eq : T.map (MulAut.conj (m⁻¹ * g)).toMonoidHom = T := by
      haveI : Finite ↥T := inferInstance
      refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj (m⁻¹ * g)).injective]
    change m⁻¹ * g ∈ Subgroup.normalizer (T : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    change t ∈ T ↔ (MulAut.conj (m⁻¹ * g)).toMonoidHom t ∈ T
    have hiff := (Subgroup.mem_map_iff_mem (f := (MulAut.conj (m⁻¹ * g)).toMonoidHom)
      (K := T) (x := t) (MulAut.conj (m⁻¹ * g)).injective).symm
    rw [hmap_eq] at hiff
    exact hiff

end Work.ZJB2
