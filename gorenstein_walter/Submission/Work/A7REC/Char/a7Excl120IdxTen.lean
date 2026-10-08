import Mathlib
import Submission.Work.A7REC.Char.a7Excl120Common
import Submission.Work.A7REC.Char.a7Excl120Tools

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup

theorem a7Excl120IdxTen {C : Type*} [Group C] [Finite C] {U S : Subgroup C} {τ : C}
    (h : Excl120Setup U S τ)
    (hi : (Subgroup.normalizer (U : Set C)).index = 10) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (U : Set C) with hNdef
  set K := Subgroup.centralizer (U : Set C) with hKdef
  have hNcard : Nat.card ↥N = 12 := by
    have hmul := Subgroup.card_mul_index N
    rw [hi, h.card_eq] at hmul
    omega
  have hKN : K ≤ N := Subgroup.centralizer_le_normalizer _
  have hKdvd : Nat.card ↥K ∣ 12 := by rw [← hNcard]; exact Subgroup.card_dvd_of_le hKN
  have hτN : τ ∈ N := by
    rw [hNdef]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.tau_normalizes
  have hτN' : τ ∈ Subgroup.normalizer (U : Set C) := by rw [← hNdef]; exact hτN
  have hτK : τ ∉ K := by
    intro hmem
    have hbot : τ ∈ (⊥ : Subgroup C) := by
      have hmem2 : τ ∈ S ⊓ Subgroup.centralizer (U : Set C) :=
        ⟨h.tau_mem, by rw [← hKdef]; exact hmem⟩
      rwa [h.disj] at hmem2
    rw [Subgroup.mem_bot] at hbot
    have h1 : orderOf τ = 1 := by rw [hbot]; exact orderOf_one
    rw [h.tau_order] at h1
    omega
  -- |K| = 6
  have hK6 : Nat.card ↥K = 6 := by
    have hbound := card_normalizer_le_card_centralizer_mul (A := U) h.card_U
    rw [← hNdef, ← hKdef] at hbound
    rw [hNcard] at hbound
    norm_num at hbound
    have hKge : 6 ≤ Nat.card ↥K := by omega
    have hmem : Nat.card ↥K ∈ (12 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hKdvd, by norm_num⟩
    have hlist : (12 : ℕ).divisors.filter (fun k => 6 ≤ k) = {6, 12} := by decide
    have hmem' : Nat.card ↥K ∈ (12 : ℕ).divisors.filter (fun k => 6 ≤ k) :=
      Finset.mem_filter.mpr ⟨hmem, hKge⟩
    rw [hlist] at hmem'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h6 | h12
    · exact h6
    · exfalso
      have hKeq : K = N := Subgroup.eq_of_le_of_card_ge hKN (by rw [h12, hNcard])
      exact hτK (by rw [hKeq]; exact hτN)
  -- `U` is abelian, so `U ≤ K`
  have hUK : U ≤ K := by
    intro u hu
    rw [hKdef, Subgroup.mem_centralizer_iff]
    intro v hv
    haveI : IsCyclic ↥U := isCyclic_of_prime_card h.card_U
    exact congrArg (fun t : ↥U => (t : C))
      ((IsMulCommutative.is_comm (M := ↥U)).comm (⟨v, hv⟩ : ↥U) (⟨u, hu⟩ : ↥U))
  -- `K` is commutative: `U ≤ Z(K)` and `K/U` has order `2`
  have hUZ : U.subgroupOf K ≤ Subgroup.center ↥K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxU : (x : C) ∈ U := Subgroup.mem_subgroupOf.mp hx
    have hcomm := Subgroup.mem_centralizer_iff.mp (by rw [← hKdef]; exact y.2) (x : C) hxU
    exact Subtype.ext hcomm.symm
  haveI hUnorm : (U.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).mpr hKN
  haveI hCyc : IsCyclic (↥K ⧸ U.subgroupOf K) := by
    apply isCyclic_of_prime_card (p := 2)
    rw [← Subgroup.index_eq_card]
    have hmul := Subgroup.card_mul_index (U.subgroupOf K)
    have hcard : Nat.card ↥(U.subgroupOf K) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]; exact h.card_U
    rw [hcard, hK6] at hmul
    omega
  have hKcomm : ∀ x y : ↥K, x * y = y * x := by
    haveI : IsMulCommutative ↥K := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (U.subgroupOf K)) (by rw [QuotientGroup.ker_mk']; exact hUZ)
    intro x y
    exact (IsMulCommutative.is_comm (M := ↥K)).comm x y
  -- an involution `w` in `K`
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (by rw [hK6]; norm_num)
  have hw1 : w ≠ 1 := by
    intro hcon
    have h1 : orderOf w = 1 := by rw [hcon, orderOf_one]
    omega
  -- `τ` normalizes `K`
  have hτKnorm : ∀ k : C, k ∈ K → τ * k * τ⁻¹ ∈ K := by
    intro k hk
    rw [hKdef, Subgroup.mem_centralizer_iff]
    intro u hu
    have hu2 : τ * u * τ⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hτN') u |>.mp hu
    have hkcomm : ∀ v ∈ U, v * k = k * v :=
      Subgroup.mem_centralizer_iff.mp (by rw [← hKdef]; exact hk)
    calc u * (τ * k * τ⁻¹) = τ * ((τ⁻¹ * u * τ) * k) * τ⁻¹ := by group
      _ = τ * (k * (τ⁻¹ * u * τ)) * τ⁻¹ := by
        have h1 : (τ⁻¹ * u * τ) * k = k * (τ⁻¹ * u * τ) := by
          have hinv : τ⁻¹ ∈ Subgroup.normalizer (U : Set C) := Subgroup.inv_mem _ hτN'
          have h2 : τ⁻¹ * u * τ ∈ U := by
            have h3 := (Subgroup.mem_normalizer_iff.mp hinv) u
            simpa using h3.mp hu
          exact hkcomm _ h2
        rw [h1]
      _ = (τ * k * τ⁻¹) * u := by group
  have hτKinv : ∀ k : C, k ∈ K → τ⁻¹ * k * τ ∈ K := by
    intro k hk
    rw [hKdef, Subgroup.mem_centralizer_iff]
    intro u hu
    have hinv : τ⁻¹ ∈ Subgroup.normalizer (U : Set C) := Subgroup.inv_mem _ hτN'
    have hu2 : τ⁻¹ * u * τ ∈ U := by
      have h3 := (Subgroup.mem_normalizer_iff.mp hinv) u
      simpa using h3.mp hu
    have hkcomm : ∀ v ∈ U, v * k = k * v :=
      Subgroup.mem_centralizer_iff.mp (by rw [← hKdef]; exact hk)
    calc u * (τ⁻¹ * k * τ) = τ⁻¹ * ((τ * u * τ⁻¹) * k) * τ := by group
      _ = τ⁻¹ * (k * (τ * u * τ⁻¹)) * τ := by
        have h1 : (τ * u * τ⁻¹) * k = k * (τ * u * τ⁻¹) := by
          have h2 : τ * u * τ⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hτN') u |>.mp hu
          exact hkcomm _ h2
        rw [h1]
      _ = (τ⁻¹ * k * τ) * u := by group
  let α : MulAut ↥K :=
    { toFun := fun k => ⟨τ * (k : C) * τ⁻¹, hτKnorm (k : C) k.2⟩
      invFun := fun k => ⟨τ⁻¹ * (k : C) * τ, hτKinv (k : C) k.2⟩
      left_inv := by intro k; ext; simp only; group
      right_inv := by intro k; ext; simp only; group
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    simpa [pow_two] using this
  have hαw2 : orderOf (α w) = 2 := by
    have h1 : (α w) * (α w) = 1 := by
      have h2 := map_mul α w w
      rw [hww, map_one] at h2
      exact h2.symm
    have h2 : α w ≠ 1 := by
      intro hcon
      apply hw1
      exact α.injective (by rw [hcon, map_one])
    exact orderOf_eq_prime (x := α w) (p := 2) (by rw [pow_two]; exact h1) h2
  have hfix : α w = w := involution_unique_of_card_six hK6 hKcomm hαw2 hw
  have hτw : τ * (w : C) * τ⁻¹ = (w : C) := by
    have := congrArg (fun k : ↥K => (k : C)) hfix
    simpa [α] using this
  have hτw' : τ * (w : C) = (w : C) * τ := by
    calc τ * (w : C) = (τ * (w : C) * τ⁻¹) * τ := by group
      _ = (w : C) * τ := by rw [hτw]
  have hwC : (w : C) ∈ Subgroup.centralizer ({τ} : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hτw'
  -- `8 ∣ |C_C(τ)| ∣ 24`
  have hSle : S ≤ Subgroup.centralizer ({τ} : Set C) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (h.tau_central x hx).symm
  have h8 : 8 ∣ Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) := by
    have h' := Subgroup.card_dvd_of_le hSle
    rwa [h.card_S] at h'
  have h24dvd : Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) ∣ 24 := h.cent_dvd τ h.tau_order
  have hcases : Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) = 8 ∨
      Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) = 24 := by
    have hmem : Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) ∈ (24 : ℕ).divisors :=
      Nat.mem_divisors.mpr ⟨h24dvd, by norm_num⟩
    have hle8 : 8 ≤ Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) :=
      Nat.le_of_dvd Nat.card_pos h8
    have hlist : (24 : ℕ).divisors.filter (fun k => 8 ≤ k ∧ 8 ∣ k) = {8, 24} := by decide
    have hmem' : Nat.card ↥(Subgroup.centralizer ({τ} : Set C)) ∈
        (24 : ℕ).divisors.filter (fun k => 8 ≤ k ∧ 8 ∣ k) :=
      Finset.mem_filter.mpr ⟨hmem, hle8, h8⟩
    rw [hlist] at hmem'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
    tauto
  rcases hcases with h8c | h24c
  · -- `C_C(τ) = S`, and `w ∈ S ⊓ K = ⊥`
    have hSeq : S = Subgroup.centralizer ({τ} : Set C) := by
      refine Subgroup.eq_of_le_of_card_ge hSle ?_
      rw [h8c, h.card_S]
    have hwS : (w : C) ∈ S := by rw [hSeq]; exact hwC
    have hwK : (w : C) ∈ Subgroup.centralizer (U : Set C) := by rw [← hKdef]; exact w.2
    have hbot : (w : C) ∈ (⊥ : Subgroup C) := by
      have hmem2 : (w : C) ∈ S ⊓ Subgroup.centralizer (U : Set C) := ⟨hwS, hwK⟩
      rwa [h.disj] at hmem2
    rw [Subgroup.mem_bot] at hbot
    exact hw1 (Subtype.ext hbot)
  · -- `|C_C(τ)| = 24`: the unique subgroup of order `3` of `C_C(τ)` is normal there, so `24 ∣ |N_C(A)| = 12`
    obtain ⟨x3, hx3⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer ({τ} : Set C))) 3 (by rw [h24c]; norm_num)
    set z : C := (x3 : C) with hzdef
    have hz3 : orderOf z = 3 := by rw [hzdef, Subgroup.orderOf_coe x3]; exact hx3
    have hzC : z ∈ Subgroup.centralizer ({τ} : Set C) := by rw [hzdef]; exact x3.2
    set A : Subgroup C := Subgroup.zpowers z with hAdef
    have hAcard : Nat.card ↥A = 3 := by rw [hAdef, Nat.card_zpowers]; exact hz3
    have hAcent : A ≤ Subgroup.centralizer ({τ} : Set C) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rw [hAdef] at hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, ← hn]
      have hcomm : Commute τ z := (Subgroup.mem_centralizer_iff.mp hzC) τ (Set.mem_singleton τ)
      exact hcomm.zpow_right n
    have hleN : Subgroup.centralizer ({τ} : Set C) ≤ Subgroup.normalizer (A : Set C) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hy3 : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = 3 := by
        rw [← hAcard]
        exact Subgroup.card_map_of_injective (K := A) (MulAut.conj g).injective
      have hAle : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({τ} : Set C) := by
        rintro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨a, ha, rfl⟩ := hy
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        rw [ht]
        have hτg : Commute τ g := (Subgroup.mem_centralizer_iff.mp hg) τ (Set.mem_singleton τ)
        have hτa : Commute τ a := (Subgroup.mem_centralizer_iff.mp (hAcent ha)) τ (Set.mem_singleton τ)
        show τ * (g * a * g⁻¹) = g * a * g⁻¹ * τ
        exact (hτg.mul_right hτa).mul_right hτg.inv_right
      exact (h.uniq_C3 τ h.tau_order) _ _ hAle hAcent hy3 hAcard
    have h24dvdN : 24 ∣ Nat.card ↥(Subgroup.normalizer (A : Set C)) := by
      have h' := Subgroup.card_dvd_of_le hleN
      rwa [h24c] at h'
    have hNA : Nat.card ↥(Subgroup.normalizer (A : Set C)) = 12 := by
      have hfac : (Nat.card C).factorization 3 = 1 := by rw [h.card_eq]; exact factorization_three_120
      let PA : Sylow 3 C := Sylow.ofCard A (by rw [hfac, pow_one]; exact hAcard)
      let PU : Sylow 3 C := Sylow.ofCard U (by rw [hfac, pow_one]; exact h.card_U)
      have hidxA : (Subgroup.normalizer (A : Set C)).index = Nat.card (Sylow 3 C) := by
        rw [← Sylow.coe_ofCard A (by rw [hfac, pow_one]; exact hAcard)]
        exact (Sylow.card_eq_index_normalizer PA).symm
      have hidxU : (Subgroup.normalizer (U : Set C)).index = Nat.card (Sylow 3 C) := by
        rw [← Sylow.coe_ofCard U (by rw [hfac, pow_one]; exact h.card_U)]
        exact (Sylow.card_eq_index_normalizer PU).symm
      have hindex : (Subgroup.normalizer (A : Set C)).index = 10 := by
        rw [hidxA, ← hidxU]; exact hi
      have hmul := Subgroup.card_mul_index (Subgroup.normalizer (A : Set C))
      rw [hindex, h.card_eq] at hmul
      omega
    rw [hNA] at h24dvdN
    norm_num at h24dvdN

end Work.A7REC.Char


