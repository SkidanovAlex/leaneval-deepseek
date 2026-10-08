import Mathlib

open scoped Pointwise

namespace Work.BSW.S3

/-- If `H ≤ G` has cardinality coprime to its index, then every element of order `p`
with `p` a prime dividing `|H|` is conjugate into `H`. -/
theorem hallConj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hcop : Nat.Coprime (Nat.card H) H.index) {p : ℕ} (hp : p.Prime)
    {z : G} (hz : orderOf z = p) (hpdvd : p ∣ Nat.card H) :
    ∃ g : G, g * z * g⁻¹ ∈ H := by
  have hprime : Fact p.Prime := ⟨hp⟩
  -- `p` does not divide the index of `H`, since it divides `|H|`, which is coprime to it.
  have hpndvd : ¬ p ∣ H.index := (hp.coprime_iff_not_dvd).mp (hcop.coprime_dvd_left hpdvd)
  -- A Sylow `p`-subgroup of `H`, viewed inside `G`.
  let P : Sylow p H := default
  have hPp : IsPGroup p (P.toSubgroup.map H.subtype) := P.isPGroup'.map H.subtype
  -- Its image in `G` still has index not divisible by `p`: the index multiplies.
  have hPndvd : ¬ p ∣ (P.toSubgroup.map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact Sylow.not_dvd_index P h1
    · exact hpndvd h2
  -- Hence it is a Sylow `p`-subgroup of `G`, and it is contained in `H`.
  let PS : Sylow p G := hPp.toSylow hPndvd
  have hPScoe : (PS : Subgroup G) = P.toSubgroup.map H.subtype :=
    IsPGroup.toSylow_coe hPp hPndvd
  -- `⟨z⟩` is a `p`-group, so it is contained in some Sylow `p`-subgroup `Q` of `G`.
  have hzpg : IsPGroup p (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  obtain ⟨Q, hQle⟩ := hzpg.exists_le_sylow
  -- All Sylow `p`-subgroups of `G` are conjugate: `Q = g PS g⁻¹`.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS Q
  have hzQ : z ∈ (Q : Subgroup G) := hQle (Subgroup.mem_zpowers z)
  have hzmem : g⁻¹ * z * g ∈ (P.toSubgroup.map H.subtype) := by
    have h1 : z ∈ ((g • PS : Sylow p G) : Set G) := by
      have h := hzQ
      rw [← hg] at h
      exact h
    rw [Sylow.coe_smul (g := g) (P := PS)] at h1
    have h2 : z ∈ (MulAut.conj g) • ((P.toSubgroup.map H.subtype) : Set G) := by
      rwa [show (PS : Set G) = ((P.toSubgroup.map H.subtype) : Set G) from
        congrArg (fun S : Subgroup G => (S : Set G)) hPScoe] at h1
    rw [Set.mem_smul_set_iff_inv_smul_mem] at h2
    change (MulAut.conj g)⁻¹ z ∈ (P.toSubgroup.map H.subtype) at h2
    rwa [MulAut.conj_inv_apply] at h2
  refine ⟨g⁻¹, ?_⟩
  simpa using Subgroup.map_subtype_le P.toSubgroup hzmem

end Work.BSW.S3
