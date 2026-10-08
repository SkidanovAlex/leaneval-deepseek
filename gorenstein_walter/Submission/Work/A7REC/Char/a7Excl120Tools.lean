import Mathlib
import Submission.Work.A7REC.Char.a7Excl120Common
import Submission.Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup

theorem eq_of_mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hmem : a ∈ Subgroup.zpowers b) : a = b := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h2 : ((2 : ℕ) : ℤ) ∣ k := ⟨m, by rw [hm]; ring⟩
    have h1 : b ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one (x := b), hb]
      exact h2
    have h3 : a = 1 := by rw [← hk, h1]
    rw [h3, orderOf_one] at ha
    exact absurd ha (by norm_num)
  · have h2 : ((2 : ℕ) : ℤ) ∣ k - 1 := by
      refine ⟨m, ?_⟩
      rw [hm]; ring
    have h1 : b ^ (k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one (x := b), hb]
      exact h2
    have h4 : b ^ k = b := by
      have h5 : b ^ k = b ^ ((k - 1) + 1) := by ring_nf
      rw [h5, zpow_add_one, h1, one_mul]
    rw [← hk, h4]

theorem involution_unique_of_card_six {C : Type*} [Group C] [Finite C] (hc : Nat.card C = 6)
    (hcomm : ∀ x y : C, x * y = y * x) {a b : C} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    a = b := by
  by_contra hne
  set A : Subgroup C := Subgroup.zpowers a with hA
  set B : Subgroup C := Subgroup.zpowers b with hB
  have hAcard : Nat.card ↥A = 2 := by rw [hA, Nat.card_zpowers, ha]
  have hBcard : Nat.card ↥B = 2 := by rw [hB, Nat.card_zpowers, hb]
  have hdisj : Disjoint A B := by
    rw [disjoint_iff, Subgroup.eq_bot_iff_card]
    have hdvd : Nat.card ↥(A ⊓ B) ∣ 2 := by
      rw [← hAcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · exfalso
      have hEq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hAcard])
      have hle : A ≤ B := (le_of_eq hEq.symm).trans inf_le_right
      have hamem : a ∈ Subgroup.zpowers b := by
        have h' : a ∈ B := hle (Subgroup.mem_zpowers a)
        simpa [hB] using h'
      exact hne (eq_of_mem_zpowers_of_orderOf_eq_two ha hb hamem)
  have hnorm : B ≤ Subgroup.normalizer (A : Set C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : x * y * x⁻¹ = y := by rw [hcomm x y]; group
    rw [hxy]
  have hjoin : Nat.card ↥(A ⊔ B) = 4 := by
    have h := Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint (A := A) (B := B) hnorm hdisj
    rw [h, hAcard, hBcard]
  have hdvd : 4 ∣ Nat.card C := by
    rw [← Subgroup.card_top (G := C), ← hjoin]
    exact Subgroup.card_dvd_of_le le_top
  rw [hc] at hdvd
  norm_num at hdvd

theorem card_normalizer_le_card_centralizer_mul {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {p : ℕ} [Fact (Nat.Prime p)] (hA : Nat.card ↥A = p) :
    Nat.card ↥(Subgroup.normalizer (A : Set G)) ≤
      Nat.card ↥(Subgroup.centralizer (A : Set G)) * (p - 1) := by
  set N := Subgroup.normalizer (A : Set G) with hNdef
  have hle : A ≤ N := Subgroup.le_normalizer
  have hAsub : Nat.card ↥(A.subgroupOf N) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]; exact hA
  haveI : IsCyclic ↥(A.subgroupOf N) := isCyclic_of_prime_card hAsub
  have hmulAut : Nat.card (MulAut ↥(A.subgroupOf N)) = p - 1 := by
    rw [IsCyclic.card_mulAut, hAsub, Nat.totient_prime (Fact.out)]
  haveI : (A.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr le_rfl
  let φ : ↥N →* MulAut ↥(A.subgroupOf N) := MulAut.conjNormal
  have hker_le : φ.ker ≤ (Subgroup.centralizer (A : Set G)).subgroupOf N := by
    intro g hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : (MulAut.conjNormal g) (⟨⟨u, hle hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩ : ↥(A.subgroupOf N))
        = (⟨⟨u, hle hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩ : ↥(A.subgroupOf N)) := by
      rw [MonoidHom.mem_ker] at hg
      rw [hg]; rfl
    have h2 : ((g : G) * u * (g : G)⁻¹) = u := by
      have h3 := congr_arg (fun x : ↥(A.subgroupOf N) => ((x : ↥N) : G)) h1
      simpa [MulAut.conjNormal_apply] using h3
    calc u * (g : G) = ((g : G) * u * (g : G)⁻¹) * (g : G) := by rw [h2]
      _ = (g : G) * u := by group
  have hker_card : Nat.card ↥φ.ker ≤ Nat.card ↥(Subgroup.centralizer (A : Set G)) := by
    have h1 := Subgroup.card_le_of_le hker_le
    have h2 : Nat.card ↥((Subgroup.centralizer (A : Set G)).subgroupOf N)
        = Nat.card ↥(Subgroup.centralizer (A : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (A : Set G))).toEquiv
    rw [h2] at h1
    exact h1
  have hrange_card : Nat.card ↥φ.range ≤ p - 1 := by
    have h1 : Nat.card ↥φ.range ≤ Nat.card (MulAut ↥(A.subgroupOf N)) := by
      have h2 := Subgroup.card_le_of_le (le_top : φ.range ≤ ⊤)
      rwa [Subgroup.card_top] at h2
    rwa [hmulAut] at h1
  have hmul := Subgroup.card_ker_mul_card_range φ
  calc Nat.card ↥N = Nat.card ↥φ.ker * Nat.card ↥φ.range := hmul.symm
    _ ≤ Nat.card ↥(Subgroup.centralizer (A : Set G)) * (p - 1) :=
        Nat.mul_le_mul hker_card hrange_card

theorem factorization_three_120 : (120 : ℕ).factorization 3 = 1 := by
  rw [show (120 : ℕ) = 3 * 40 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 40)]


end Work.A7REC.Char
