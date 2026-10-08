import Mathlib

-- `htm : t ∈ Q` is part of the requested interface but is not needed for these quotient facts.
set_option linter.unusedVariables false

namespace Work.CORE4

theorem CoreQuotientSetup {E : Type} [Group E] [Finite E]
    (hZodd : Odd (Nat.card (Subgroup.center E)))
    (Q : Subgroup E) (t : E) (htm : t ∈ Q) (hto : orderOf t = 2)
    (Y : Subgroup E) (hYodd : Odd (Nat.card Y))
    (hYcent : Y ≤ Subgroup.centralizer ({t} : Set E)) :
    t ∉ Subgroup.center E ∧
    orderOf (QuotientGroup.mk' (Subgroup.center E) t) = 2 ∧
    Odd (Nat.card (Y.map (QuotientGroup.mk' (Subgroup.center E)))) ∧
    Y.map (QuotientGroup.mk' (Subgroup.center E)) ≤
      Subgroup.centralizer ({QuotientGroup.mk' (Subgroup.center E) t} :
        Set (E ⧸ Subgroup.center E)) ∧
    (Q ≤ Subgroup.normalizer (Y : Set E) →
      Q.map (QuotientGroup.mk' (Subgroup.center E)) ≤
        Subgroup.normalizer ((Y.map (QuotientGroup.mk' (Subgroup.center E))) :
          Set (E ⧸ Subgroup.center E))) := by
  classical
  -- A divisor of an odd number is odd.
  have hodd_of_dvd : ∀ {m n : ℕ}, m ∣ n → Odd n → Odd m := by
    intro m n hdvd hn
    rw [← Nat.not_even_iff_odd]
    intro hm
    exact (Nat.not_even_iff_odd.mpr hn)
      (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hm) hdvd))
  -- `t` is not central: otherwise `⟨t⟩ ≤ Z(E)` would force `2 ∣ |Z(E)|`, contradicting oddness.
  have ht_not_center : t ∉ Subgroup.center E := by
    intro ht
    have hle : Subgroup.zpowers t ≤ Subgroup.center E := Subgroup.zpowers_le.mpr ht
    have hdvd : Nat.card (Subgroup.zpowers t) ∣ Nat.card (Subgroup.center E) :=
      Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers]; exact hto
    have heven : Even (Nat.card (Subgroup.center E)) := by
      rw [even_iff_two_dvd]
      rw [h2] at hdvd
      exact hdvd
    exact (Nat.not_even_iff_odd.mpr hZodd) heven
  refine ⟨ht_not_center, ?_, ?_, ?_, ?_⟩
  · -- the image of `t` in the quotient still has order two
    have hdvd : orderOf (QuotientGroup.mk' (Subgroup.center E) t) ∣ 2 := by
      rw [← hto]; exact orderOf_map_dvd _ t
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exfalso
      have hthis : QuotientGroup.mk' (Subgroup.center E) t = 1 := orderOf_eq_one_iff.mp h1
      rw [QuotientGroup.mk'_apply] at hthis
      exact ht_not_center ((QuotientGroup.eq_one_iff t).mp hthis)
    · exact h2
  · -- the image of `Y` has odd order (it divides `|Y|`, by Lagrange)
    exact hodd_of_dvd (Subgroup.card_map_dvd Y _) hYodd
  · -- the image of `Y` centralises the image of `t`
    refine (Subgroup.map_mono hYcent).trans ?_
    refine (Subgroup.map_centralizer_le_centralizer_image ({t} : Set E) _).trans ?_
    rw [Set.image_singleton]
  · -- if `Q` normalises `Y`, its image normalises the image of `Y`
    intro hQ
    exact (Subgroup.map_mono hQ).trans (Subgroup.le_normalizer_map _)

end Work.CORE4
