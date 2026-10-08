import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A Sylow `p`-subgroup of a Bender subgroup is Sylow in the whole group

Let `H ≤ G` be a Bender subgroup for the prime `p` (Peterfalvi I §1 (1)):
`p ∣ |H|` and `p ∤ |H ∩ H^x|` for every `x ∉ H`.  Then a Sylow `p`-subgroup `P` of `H`
is a Sylow `p`-subgroup of `G`.

The proof is the classical one.  Let `P` act on `Ω = G ⧸ H`, the set of conjugates of `H`.
By the orbit-counting congruence for a `p`-group acting on a finite set,
`|Ω| ≡ |Fix(P)| (mod p)`.  The fixed points of `P` are the cosets `gH` with `P ≤ gHg⁻¹`;
since also `P ≤ H`, such a point gives `P ≤ H ∩ gHg⁻¹`, so `p ∣ |H ∩ gHg⁻¹|` (because
`p ∣ |P|`), and the Bender condition forces `g ∈ H`.  Hence `Fix(P) = {H}` and
`|Ω| ≡ 1 (mod p)`, i.e. `p ∤ [G : H]`.  Finally
`[G : P] = [H : P] · [G : H]`, and `p` divides neither factor.
-/

namespace Work.DoubleTransitivity.Sec1

open Submission.Blueprint

/-- **A Sylow `p`-subgroup of a Bender subgroup is Sylow in `G`.** -/
theorem sylow_of_sylowIn {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H P : Subgroup G} (hH : IsBenderFor p H) (hP : IsSylowSubgroupOf p P H) :
    IsSylowSub p P := by
  -- `p` divides the order of `P`, since `P` is a Sylow `p`-subgroup of the Bender subgroup `H`
  have hpdvd : p ∣ Nat.card (P.subgroupOf H) := by
    have hmul : Nat.card (P.subgroupOf H) * (P.subgroupOf H).index = Nat.card H :=
      Subgroup.card_mul_index _
    rcases hp.dvd_mul.mp (hmul ▸ hH.1) with h | h
    · exact h
    · exact absurd h hP.2.2
  have hdvdP : p ∣ Nat.card P :=
    hpdvd.trans (Subgroup.card_comap_dvd_of_injective P H.subtype
      (Subgroup.subtype_injective H))
  -- the canonical point `H` is fixed by `P`
  have hpt_mem : pt H ∈ MulAction.fixedPoints P (Omega H) := by
    rw [MulAction.mem_fixedPoints]
    intro m
    show (m : G) • pt H = pt H
    rw [smul_pt]
    exact mk_one_eq_iff.mpr (hP.1 m.2)
  -- and it is the only fixed point, by the Bender condition
  have hfix : MulAction.fixedPoints P (Omega H) = {pt H} := by
    ext ω
    constructor
    · intro hω
      rw [MulAction.mem_fixedPoints] at hω
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
      have hconj : P ≤ conj g H := by
        intro y hy
        have h1 : (y : G) • (QuotientGroup.mk g : Omega H) = QuotientGroup.mk g := hω ⟨y, hy⟩
        exact smul_mk_eq_mk_iff.mp h1
      have hle : P ≤ H ⊓ conj g H := le_inf hP.1 hconj
      have hd : p ∣ Nat.card ↥(H ⊓ conj g H) := hdvdP.trans (Subgroup.card_dvd_of_le hle)
      have hgH : g ∈ H := by
        by_contra hg
        exact hH.2 g hg hd
      exact Set.mem_singleton_iff.mpr (mk_one_eq_iff.mpr hgH)
    · intro hω
      rw [Set.mem_singleton_iff] at hω
      rw [hω]
      exact hpt_mem
  -- orbit counting: `|Ω| ≡ |Fix(P)| = 1 (mod p)`
  have hmod : Nat.card (Omega H) ≡ 1 [MOD p] := by
    haveI : Fact p.Prime := ⟨hp⟩
    have h := hP.2.1.card_modEq_card_fixedPoints (Omega H)
    rw [hfix] at h
    simpa using h
  -- hence `p ∤ [G : H]`
  have hHindex : ¬ p ∣ H.index := by
    have hmod' : H.index ≡ 1 [MOD p] := hmod
    intro hdd
    have h1 : (1 : ℕ) ≡ 0 [MOD p] := hmod'.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdd)
    exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h1)
  refine ⟨hP.2.1, ?_⟩
  -- and `[G : P] = [H : P] · [G : H]` is a product of two `p`-coprime factors
  have hidx : P.index = (P.subgroupOf H).index * H.index :=
    (Subgroup.relIndex_mul_index hP.1).symm
  intro hdd
  rcases hp.dvd_mul.mp (hidx ▸ hdd) with h | h
  · exact hP.2.2 h
  · exact hHindex h

end Work.DoubleTransitivity.Sec1
