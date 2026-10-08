import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- Every Sylow `p`-subgroup of a finite group of order `p ^ 3 * (p - 1)`, `p` prime,
has order `p ^ 3` (the `p`-part of the group order). -/
private lemma sylow_card {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (S : Sylow p X) (hX : Nat.card X = p ^ 3 * (p - 1)) :
    Nat.card ↥S.toSubgroup = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : p ^ 3 ∣ Nat.card ↥S.toSubgroup :=
    S.pow_dvd_card_of_pow_dvd_card (by rw [hX]; exact dvd_mul_right _ _)
  have h2 : Nat.card ↥S.toSubgroup ∣ p ^ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have hk' : Nat.card ↥S.toSubgroup = p ^ k := hk
    rw [hk']
    have hdvd : p ^ k ∣ Nat.card X :=
      ⟨S.toSubgroup.index, by rw [← Subgroup.card_mul_index S.toSubgroup, hk']⟩
    rw [hX] at hdvd
    have hnot : ¬ p ∣ p - 1 :=
      Nat.not_dvd_of_pos_of_lt (by have := hp.two_le; omega) (by have := hp.two_le; omega)
    exact ((hp.coprime_iff_not_dvd.mpr hnot).pow_left k).dvd_of_dvd_mul_right hdvd
  exact Nat.dvd_antisymm h2 h1

/-- The index of such a Sylow subgroup is `p - 1`. -/
private lemma sylow_index {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (S : Sylow p X) (hX : Nat.card X = p ^ 3 * (p - 1)) :
    S.toSubgroup.index = p - 1 := by
  have hcard := sylow_card hp S hX
  have h := Subgroup.card_mul_index S.toSubgroup
  rw [hcard, hX] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 3) h

/-- A finite group of order `p ^ 3 * (p - 1)`, `p` prime, has exactly one Sylow
`p`-subgroup: the number of Sylow `p`-subgroups divides `p - 1` and is `≡ 1` mod `p`. -/
private lemma card_sylow_eq_one {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hX : Nat.card X = p ^ 3 * (p - 1)) : Nat.card (Sylow p X) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := X)
  have hdvd : Nat.card (Sylow p X) ∣ p - 1 := (sylow_index hp S hX) ▸ S.card_dvd_index
  have hle : Nat.card (Sylow p X) ≤ p - 1 :=
    Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
  have hlt : Nat.card (Sylow p X) < p := by have := hp.two_le; omega
  have hmod : Nat.card (Sylow p X) % p = 1 % p := card_sylow_modEq_one p X
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp.one_lt] at hmod
  exact hmod

theorem normal_sylow_of_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (X R : Subgroup G) (hRX : R ≤ X)
    (hRn : X ≤ Work.ThmF.ChV3.NG R) (hRp : IsPGroup p R)
    (hX : Nat.card X = p ^ 3 * (p - 1)) :
    ∃ R1 : Subgroup G, R ≤ R1 ∧ R1 ≤ X ∧ Nat.card R1 = p ^ 3 ∧
      X ≤ Work.ThmF.ChV3.NG R1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- A Sylow `p`-subgroup of `X` containing `R`.
  have hR'p : IsPGroup p (R.subgroupOf X) :=
    hRp.comap_of_injective X.subtype X.subtype_injective
  obtain ⟨P, hR'P⟩ := IsPGroup.exists_le_sylow (p := p) (G := ↥X) hR'p
  have hcardP : Nat.card ↥P.toSubgroup = p ^ 3 := sylow_card hp P hX
  -- It is the *unique* Sylow `p`-subgroup of `X`, hence normal in `X`.
  haveI : Subsingleton (Sylow p ↥X) :=
    Finite.card_le_one_iff_subsingleton.mp (le_of_eq (card_sylow_eq_one hp hX))
  have hPn : P.toSubgroup.Normal := Sylow.normal_of_subsingleton P
  -- `R1` is that Sylow subgroup, viewed inside `G`.
  refine ⟨P.toSubgroup.map X.subtype, ?_, Subgroup.map_subtype_le P.toSubgroup, ?_, ?_⟩
  · intro r hr
    exact Subgroup.mem_map.mpr
      ⟨⟨r, hRX hr⟩, hR'P (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  · rw [Subgroup.card_subtype X P.toSubgroup]; exact hcardP
  · set R1 : Subgroup G := P.toSubgroup.map X.subtype with hR1def
    have hR1X : R1 ≤ X := Subgroup.map_subtype_le P.toSubgroup
    have hsub : R1.subgroupOf X = P.toSubgroup := by
      apply Subgroup.map_subtype_inj.mp
      rw [Subgroup.map_subgroupOf_eq_of_le hR1X]
    have hN : (R1.subgroupOf X).Normal := by rw [hsub]; exact hPn
    have hconj := (Subgroup.normal_subgroupOf_iff hR1X).mp hN
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨fun hn => hconj n g hn hg, fun hn => by
      have h := hconj (g * n * g⁻¹) g⁻¹ hn (X.inv_mem hg)
      rwa [show g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n by group] at h⟩

end Work.ThmF.ChV3.Prove
