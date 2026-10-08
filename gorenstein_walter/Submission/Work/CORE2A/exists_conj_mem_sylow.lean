import Mathlib

open scoped Pointwise

namespace Work.CORE2A

/-- **Conjugacy of `p`-elements into a Sylow subgroup inside a containing subgroup.**

Let `P` be a Sylow `p`-subgroup of `G` with `P ≤ H`, and let `x ∈ H` generate a `p`-subgroup
`⟨x⟩`. Then `x` is conjugate into `P` by an element of `H`: there is `h ∈ H` with
`h * x * h⁻¹ ∈ P`.

This is the Sylow conjugacy theorem applied inside `H`: `P` is also a Sylow `p`-subgroup of `H`
(`Sylow.subtype`), the subgroup `⟨x⟩ ≤ H` is a `p`-subgroup of `H`, hence lies in some Sylow of
`H`, and all Sylow `p`-subgroups of `H` are conjugate by an element of `H`
(`Sylow.isPretransitive_of_finite`). -/
theorem exists_conj_mem_sylow {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {H : Subgroup G} (P : Sylow p G) (hPH : (P : Subgroup G) ≤ H)
    {x : G} (hxH : x ∈ H) (hxp : IsPGroup p ↥(Subgroup.zpowers x)) :
    ∃ h ∈ H, h * x * h⁻¹ ∈ (P : Subgroup G) := by
  let xH : H := ⟨x, hxH⟩
  -- `⟨x⟩` as a subgroup of `H`, a `p`-group since `⟨x⟩` is one in `G`.
  let K : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  have hK : IsPGroup p K := by
    have h := hxp.comap_of_injective H.subtype H.subtype_injective
    rw [Subgroup.comap_subtype] at h
    exact h
  -- Some Sylow of `H` contains `K`.
  obtain ⟨R, hKR⟩ := hK.exists_le_sylow
  -- `P`, viewed inside `H`, is a Sylow of `H`.
  let Q : Sylow p H := P.subtype hPH
  -- Sylow conjugacy inside `H`.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R Q
  have hxK : xH ∈ K := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x)
  have hxR : xH ∈ (R : Subgroup H) := hKR hxK
  -- Conjugate `xH` into `Q` by `g`.
  have hconj : MulAut.conj g • xH ∈ MulAut.conj g • (R : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul xH (MulAut.conj g) (R : Subgroup H) hxR
  have hQR : MulAut.conj g • (R : Subgroup H) = (Q : Subgroup H) := by
    have h2 := congrArg (fun S : Sylow p H => (S : Subgroup H)) hg
    rwa [Sylow.coe_subgroup_smul] at h2
  have hmem : g * xH * g⁻¹ ∈ (Q : Subgroup H) := by
    rw [hQR] at hconj
    simpa [MulAut.conj_apply] using hconj
  refine ⟨(g : G), g.2, ?_⟩
  have hmem' : ((g * xH * g⁻¹ : H) : G) ∈ (P : Subgroup G) := by
    change g * xH * g⁻¹ ∈ ((P.subtype hPH : Sylow p H) : Subgroup H) at hmem
    rw [Sylow.coe_subtype] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  simpa using hmem'

end Work.CORE2A
