import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.GLUE.PcoreApi

namespace Work.ZJB2

open Work.ZJB
open Subgroup

open scoped Pointwise

/-- If every element of a finite group `H` whose order is coprime to `p` lies in a normal
subgroup `L`, then the quotient `H ⧸ L` is a `p`-group.

(For an element `y` of `H` write `orderOf y = p ^ e * m` with `p ∤ m`; then `y ^ p ^ e` has
order `m`, hence lies in `L`, so the class of `y` has order dividing `p ^ e`.) -/
theorem isPGroup_quotient_of_coprime_order {H : Type*} [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (L : Subgroup H) [L.Normal]
    (hL : ∀ y : H, (orderOf y).Coprime p → y ∈ L) : IsPGroup p (H ⧸ L) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective L x
  obtain ⟨e, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p (Fact.out : p.Prime).ne_one
  have hord : orderOf (y ^ p ^ e) = m := by
    rw [orderOf_pow]
    rw [hn, Nat.gcd_eq_right ⟨m, rfl⟩]
    exact Nat.mul_div_cancel_left m (pow_pos (Fact.out : p.Prime).pos e)
  have hmcop : (orderOf (y ^ p ^ e)).Coprime p := by
    rw [hord]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hm |>.symm
  have hmem : y ^ p ^ e ∈ L := hL _ hmcop
  have h1 : (QuotientGroup.mk' L y) ^ (p ^ e) = 1 := by
    rw [← map_pow (QuotientGroup.mk' L) y (p ^ e), QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hmem
  have hdvd : orderOf (QuotientGroup.mk' L y) ∣ p ^ e := orderOf_dvd_iff_pow_eq_one.mpr h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact ⟨k, hk⟩

/-- If `T` is a maximal `p`-subgroup of the subgroup `M ≤ G` (`IsSylowIn p T M`), then
`T.subgroupOf M` is a `Sylow p ↥M`.  Local copy of a standard construction, so that this file
does not depend on a colleague's in-progress module. -/
private noncomputable def sylowOfIsSylowIn {G : Type*} [Group G] {p : ℕ} {T M : Subgroup G}
    (hT : IsSylowIn p T M) : Sylow p ↥M :=
  { toSubgroup := T.subgroupOf M
    isPGroup' := hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    is_maximal' := by
      intro Q hQ hTQ
      have hQmap : IsPGroup p ↥(Q.map M.subtype) := hQ.map M.subtype
      have hle : T ≤ Q.map M.subtype := by
        intro x hx
        exact ⟨⟨x, hT.1 hx⟩, hTQ (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
      have heq : Q.map M.subtype = T := hT.2.2 _ hle (Subgroup.map_subtype_le Q) hQmap
      exact Subgroup.map_injective (Subgroup.subtype_injective M)
        (heq.trans (Subgroup.map_subgroupOf_eq_of_le hT.1).symm) }

private theorem sylowOfIsSylowIn_coe {G : Type*} [Group G] {p : ℕ} {T M : Subgroup G}
    (hT : IsSylowIn p T M) :
    ((sylowOfIsSylowIn hT : Sylow p ↥M) : Subgroup ↥M) = T.subgroupOf M := rfl

/-- **T52.fac** If `L ⊴ H` contains every `p'`-element of `H` and `Q ∈ Syl_p(H)`, then
`H = L·Q`.

Since `L` contains all `p'`-elements, `H/L` is a `p`-group; hence the index of `L` in `H` is a
power of `p`. The index of `L ⊔ Q` divides both that of `L` and that of the Sylow subgroup `Q`
(whose index is coprime to `p`), so it is `1`, i.e. `L ⊔ Q = ⊤`. As `L` is normal,
`L ⊔ Q = L · Q` as sets, which is exactly the required factorisation. -/
theorem factorPPrime (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Work.ZJB.FactorPPrimeProp p G := by
  intro H L Q hLH hHL hLp' hQ y hy
  haveI hLnorm : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  -- `H ⧸ L` is a `p`-group
  have hquot : IsPGroup p (↥H ⧸ L.subgroupOf H) := by
    refine isPGroup_quotient_of_coprime_order p (L.subgroupOf H) ?_
    intro y' hy'
    rw [Subgroup.mem_subgroupOf]
    exact hLp' (y' : G) y'.2 (by simpa [Subgroup.orderOf_coe] using hy')
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hquot
  have hidx : (L.subgroupOf H).index = p ^ j := by
    rw [Subgroup.index_eq_card]
    exact hj
  -- `Q` is a Sylow `p`-subgroup of `↥H`, so `[↥H : Q]` is coprime to `p`
  let Qs : Sylow p ↥H := sylowOfIsSylowIn hQ
  have hQcoe : (Qs : Subgroup ↥H) = Q.subgroupOf H := sylowOfIsSylowIn_coe hQ
  have hnotdvd : ¬ p ∣ (Q.subgroupOf H).index := by
    have h := Sylow.not_dvd_index Qs
    rwa [hQcoe] at h
  have hcop : ((L.subgroupOf H).index).Coprime ((Q.subgroupOf H).index) := by
    rw [hidx]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hnotdvd).pow_left j
  have hd1 : (L.subgroupOf H ⊔ Q.subgroupOf H).index ∣ (L.subgroupOf H).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hd2 : (L.subgroupOf H ⊔ Q.subgroupOf H).index ∣ (Q.subgroupOf H).index :=
    Subgroup.index_dvd_of_le le_sup_right
  have hone : (L.subgroupOf H ⊔ Q.subgroupOf H).index = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have htop : L.subgroupOf H ⊔ Q.subgroupOf H = ⊤ := Subgroup.index_eq_one.mp hone
  have hmul : ((L.subgroupOf H ⊔ Q.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (L.subgroupOf H : Set ↥H) * (Q.subgroupOf H : Set ↥H) :=
    Subgroup.normal_mul _ _
  have hy_mem : (⟨y, hy⟩ : ↥H) ∈ (L.subgroupOf H : Set ↥H) * (Q.subgroupOf H : Set ↥H) := by
    rw [← hmul, htop]
    exact Subgroup.mem_top _
  obtain ⟨l', hl', q', hq', hlq⟩ := Set.mem_mul.mp hy_mem
  refine ⟨(l' : G), Subgroup.mem_subgroupOf.mp hl', (q' : G), Subgroup.mem_subgroupOf.mp hq', ?_⟩
  have h2 : ((l' : G) * (q' : G)) = y := by
    have hh := congrArg (Subtype.val) hlq
    simpa [Subgroup.coe_mul] using hh
  exact h2.symm

end Work.ZJB2
