import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

theorem normalizer_le_normalizer_centralizer {G : Type} [Group G] (s : Set G) :
    Subgroup.normalizer s ≤ Subgroup.normalizer ((Subgroup.centralizer s : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  rw [Subgroup.mem_centralizer_iff] at *
  constructor
  · intro ha x hx
    have hx' : g⁻¹ * x * g ∈ s := by
      apply (hg (g⁻¹ * x * g)).mpr
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [ha (g⁻¹ * x * g) hx']
      _ = g * a * g⁻¹ * x := by group
  · intro ha x hx
    have hx' : g * x * g⁻¹ ∈ s := (hg x).mp hx
    have h := ha (g * x * g⁻¹) hx'
    have h2 : g * (x * a) * g⁻¹ = g * (a * x) * g⁻¹ := by
      calc g * (x * a) * g⁻¹ = (g * x * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * (a * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem twoPoint_inf_normalizer_le_normalizer_inf_centralizer {G : Type} [Group G]
    {H Q X : Subgroup G} {t : G} (hQn : H ≤ Subgroup.normalizer (Q : Set G)) :
    twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (X : Set G)) : Set G) := by
  intro g hg
  obtain ⟨hgD, hgX⟩ := Subgroup.mem_inf.mp hg
  have hgH : g ∈ H := (Subgroup.mem_inf.mp hgD).1
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := hQn hgH
  have hgC : g ∈ Subgroup.normalizer ((Subgroup.centralizer (X : Set G)) : Set G) :=
    normalizer_le_normalizer_centralizer (X : Set G) hgX
  rw [Subgroup.mem_set_normalizer_iff] at hgQ hgC ⊢
  intro a
  constructor
  · intro ha
    exact ⟨(hgQ a).mp ha.1, (hgC a).mp ha.2⟩
  · intro ha
    exact ⟨(hgQ a).mpr ha.1, (hgC a).mpr ha.2⟩

theorem card_dvd_pow_two_of_sup_inf {G : Type} [Group G] [Finite G]
    {S T A U : Subgroup G} (hSU : S ⊔ T = U) (hST : S ⊓ T = ⊥)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hAT : A ⊓ T = ⊥)
    (hTA : T ≤ Subgroup.normalizer (A : Set G)) (hAU : A ≤ U)
    (hSp : IsPGroup 2 S) :
    ∃ n : ℕ, Nat.card ↥A ∣ 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTU : T ≤ U := by rw [← hSU]; exact le_sup_right
  have hcardU : Nat.card ↥U = Nat.card ↥S * Nat.card ↥T := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := S) (K := T) hTS
    rw [hSU, hST] at h
    simpa [Subgroup.card_bot] using h
  have hcardAT : Nat.card ↥(A ⊔ T) = Nat.card ↥A * Nat.card ↥T := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := A) (K := T) hTA
    rw [hAT] at h
    simpa [Subgroup.card_bot] using h
  have hle : A ⊔ T ≤ U := sup_le hAU hTU
  have hdvd : Nat.card ↥A * Nat.card ↥T ∣ Nat.card ↥S * Nat.card ↥T := by
    rw [← hcardAT, ← hcardU]
    exact Subgroup.card_dvd_of_le hle
  haveI : Nonempty ↥T := ⟨⟨1, T.one_mem⟩⟩
  have hTpos : 0 < Nat.card ↥T := Nat.card_pos
  have hdvdA : Nat.card ↥A ∣ Nat.card ↥S := (Nat.mul_dvd_mul_iff_right hTpos).mp hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hSp
  exact ⟨n, hn ▸ hdvdA⟩

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem oddPart_inf_centralizer_eq_bot {G : Type} [Group G] [Finite G] {H Q X : Subgroup G} {t : G} (hQH : Q ≤ H) (hQn : H ≤ Subgroup.normalizer (Q : Set G)) (hQD : Q ⊓ twoPoint H t = ⊥) (hnil : Group.IsNilpotent ↥Q) (hS : ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Subgroup.normalizer (X : Set G) ∧ S ≤ H ∧ S ⊓ twoPoint H t = ⊥ ∧ S ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = H ⊓ Subgroup.normalizer (X : Set G) ∧ H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G)) : oddPart Q ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  obtain ⟨S, hSp, hSX, hSH, hSD, hSU, hTnormS⟩ := hS
  have hD_le_H : twoPoint H t ≤ H := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hT_le_U : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
      H ⊓ Subgroup.normalizer (X : Set G) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hD_le_H hx1, hx2⟩
  have hTS : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (S : Set G) := le_trans hT_le_U hTnormS
  have hST : S ⊓ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = ⊥ := by
    rw [← inf_assoc, hSD, bot_inf_eq]
  have hAT : (Q ⊓ Subgroup.centralizer (X : Set G)) ⊓
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxA, hxT⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxQ, -⟩ := Subgroup.mem_inf.mp hxA
    obtain ⟨hxD, -⟩ := Subgroup.mem_inf.mp hxT
    exact (le_of_eq hQD) (Subgroup.mem_inf.mpr ⟨hxQ, hxD⟩)
  have hTA : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (X : Set G)) : Set G) :=
    twoPoint_inf_normalizer_le_normalizer_inf_centralizer hQn
  have hAU : Q ⊓ Subgroup.centralizer (X : Set G) ≤
      H ⊓ Subgroup.normalizer (X : Set G) := by
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hQH hxQ, Subgroup.centralizer_le_normalizer (X : Set G) hxC⟩
  obtain ⟨n, hn⟩ := card_dvd_pow_two_of_sup_inf (S := S)
      (T := twoPoint H t ⊓ Subgroup.normalizer (X : Set G))
      (A := Q ⊓ Subgroup.centralizer (X : Set G))
      (U := H ⊓ Subgroup.normalizer (X : Set G)) hSU hST hTS hAT hTA hAU hSp
  have hodd : Odd (Nat.card ↥(oddPart Q)) := by
    have heq : oddPart Q = Work.ThmG.oddPart Q := rfl
    rw [heq]
    exact (Work.ThmG.nilpotent_two_odd_split Q hnil).2.2.2.2.1
  have hle : oddPart Q ⊓ Subgroup.centralizer (X : Set G) ≤
      Q ⊓ Subgroup.centralizer (X : Set G) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨oddPart_le Q hx1, hx2⟩
  have hdiv1 : Nat.card ↥(oddPart Q ⊓ Subgroup.centralizer (X : Set G)) ∣ 2 ^ n :=
    (Subgroup.card_dvd_of_le hle).trans hn
  have hdiv2 : Nat.card ↥(oddPart Q ⊓ Subgroup.centralizer (X : Set G)) ∣
      Nat.card ↥(oddPart Q) := Subgroup.card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(oddPart Q ⊓ Subgroup.centralizer (X : Set G)))
      (Nat.card ↥(oddPart Q)) :=
    ((Nat.coprime_two_left.mpr hodd).pow_left n).coprime_dvd_left hdiv1
  have hm : Nat.card ↥(oddPart Q ⊓ Subgroup.centralizer (X : Set G)) = 1 := by
    have h1 : Nat.card ↥(oddPart Q ⊓ Subgroup.centralizer (X : Set G)) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd (dvd_refl _) hdiv2
    exact Nat.dvd_one.mp h1
  exact (Subgroup.eq_bot_iff_card _).mpr hm

end Work.ThmF.ChV12
