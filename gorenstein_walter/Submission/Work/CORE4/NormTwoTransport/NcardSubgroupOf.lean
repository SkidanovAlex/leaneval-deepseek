import Mathlib
import Submission.Work.CORE4.A4bAux.mem_normalizer_subgroupOf
import Submission.Work.CORE4.Case2Count11

namespace Work.CORE4.NormTwoTransport

/-- For a subgroup `R` of `↥E`, mapping it forward along `E.subtype` and then viewing the
result inside `E` returns `R`. -/
lemma map_subtype_subgroupOf_eq {G : Type*} [Group G] (E : Subgroup G) (R : Subgroup ↥E) :
    (R.map E.subtype).subgroupOf E = R := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    rwa [← h]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The order of `Q.subgroupOf E` equals the order of `Q`, for `Q ≤ E`. -/
lemma ncard_subgroupOf {G : Type*} [Group G] (E : Subgroup G) (Q : Subgroup G) (hQE : Q ≤ E) :
    Nat.card ↥(Q.subgroupOf E) = Nat.card ↥Q :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv

/-- The order of `R.map E.subtype` equals the order of `R`, for `R` a subgroup of `↥E`. -/
lemma ncard_map_subtype {G : Type*} [Group G] (E : Subgroup G) (R : Subgroup ↥E) :
    Nat.card ↥(R.map E.subtype) = Nat.card ↥R :=
  (Nat.card_congr (R.equivMapOfInjective E.subtype (Subgroup.subtype_injective E)).toEquiv).symm

/-- `Y.subgroupOf E` normalizes a subgroup `R` of `↥E` iff `Y` normalizes the image of `R`
in `G`. -/
lemma subgroupOf_le_normalizer_iff {G : Type*} [Group G] (E : Subgroup G) (Y : Subgroup G)
    (hYE : Y ≤ E) (R : Subgroup ↥E) :
    Y.subgroupOf E ≤ Subgroup.normalizer (R : Set ↥E) ↔
      Y ≤ Subgroup.normalizer ((R.map E.subtype : Subgroup G) : Set G) := by
  have hVE : R.map E.subtype ≤ E := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  constructor
  · intro h y hy
    have hx : (⟨y, hYE hy⟩ : ↥E) ∈ Subgroup.normalizer (R : Set ↥E) :=
      h (by rw [Subgroup.mem_subgroupOf]; exact hy)
    have h1 : (⟨y, hYE hy⟩ : ↥E) ∈
        Subgroup.normalizer (((R.map E.subtype).subgroupOf E : Subgroup ↥E) : Set ↥E) := by
      rwa [map_subtype_subgroupOf_eq E R]
    exact (Work.CORE4.A4bAux.mem_normalizer_subgroupOf hVE ⟨y, hYE hy⟩).mp h1
  · intro h y hy
    have hyN : (↑(⟨y, hYE hy⟩ : ↥E) : G) ∈
        Subgroup.normalizer ((R.map E.subtype) : Set G) := h hy
    have h1 : (⟨y, hYE hy⟩ : ↥E) ∈
        Subgroup.normalizer (((R.map E.subtype).subgroupOf E : Subgroup ↥E) : Set ↥E) :=
      (Work.CORE4.A4bAux.mem_normalizer_subgroupOf hVE ⟨y, hYE hy⟩).mpr hyN
    rwa [map_subtype_subgroupOf_eq E R] at h1

theorem NcardSubgroupOf {G : Type} [Group G] (E : Subgroup G)
    (Y : Subgroup G) (hYE : Y ≤ E) (q : ℕ) :
    {Q : Subgroup G | Q ≤ E ∧ Nat.card ↥Q = q ∧
        Y ≤ Subgroup.normalizer (Q : Set G)}.ncard =
      {Q : Subgroup ↥E | Nat.card ↥Q = q ∧
        Y.subgroupOf E ≤ Subgroup.normalizer (Q : Set ↥E)}.ncard := by
  refine Set.ncard_congr' ?_
  refine Equiv.mk ?_ ?_ ?_ ?_
  · rintro ⟨Q, hQE, hcard, hN⟩
    exact ⟨Q.subgroupOf E, by rw [ncard_subgroupOf E Q hQE, hcard], by
      intro y hy
      rw [Work.CORE4.A4bAux.mem_normalizer_subgroupOf hQE y]
      exact hN hy⟩
  · rintro ⟨Q, hcard, hN⟩
    refine ⟨Q.map E.subtype, ?_, ?_, ?_⟩
    · rintro x ⟨z, -, rfl⟩
      exact z.2
    · rw [ncard_map_subtype E Q, hcard]
    · exact (subgroupOf_le_normalizer_iff E Y hYE Q).mp hN
  · intro Q
    exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le Q.2.1)
  · intro Q
    exact Subtype.ext (map_subtype_subgroupOf_eq E Q.1)

end Work.CORE4.NormTwoTransport
