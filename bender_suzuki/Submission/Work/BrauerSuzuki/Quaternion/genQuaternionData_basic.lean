import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.coset_cover
import Submission.Work.BrauerSuzuki.Quaternion.pow_eq_pow_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Quaternion.rho_mul_pow_order

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

open Work.BrauerSuzuki

/-- The central involution `tau ^ (2 ^ (n-1))` of a generalized quaternion group has order `2`. -/
private theorem tau_pow_half_order {P : Type*} [Group P] (d : GenQuaternionData P) :
    orderOf (d.tau ^ (2 ^ (d.n - 1))) = 2 := by
  have hn : 2 ≤ d.n := d.hn
  have h2n : 2 ^ (d.n - 1) * 2 = 2 ^ d.n := by
    rw [← pow_succ]; congr 1; omega
  have hsq : (d.tau ^ (2 ^ (d.n - 1))) ^ 2 = 1 := by
    rw [← pow_mul, h2n, ← d.tau_order]; exact pow_orderOf_eq_one d.tau
  have hne : d.tau ^ (2 ^ (d.n - 1)) ≠ 1 := by
    intro h
    have hdvd : 2 ^ d.n ∣ 2 ^ (d.n - 1) := by
      rw [← d.tau_order]; exact orderOf_dvd_iff_pow_eq_one.mpr h
    have hlt : 2 ^ (d.n - 1) < 2 ^ d.n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hle : 2 ^ d.n ≤ 2 ^ (d.n - 1) := Nat.le_of_dvd (by positivity) hdvd
    exact absurd hle (not_le.mpr hlt)
  exact orderOf_eq_prime hsq hne

/-- `rho` is not a power of `tau`: otherwise `tau` and `rho` would commute and `rho_conj` would
force `tau = tau⁻¹`, contradicting `orderOf tau = 2 ^ n ≥ 4`. -/
private theorem rho_not_mem_zpowers {P : Type*} [Group P] (d : GenQuaternionData P) :
    d.rho ∉ Subgroup.zpowers d.tau := by
  have hn : 2 ≤ d.n := d.hn
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hconj : d.rho * d.tau * d.rho⁻¹ = d.tau := by rw [← hk]; group
  have hthis : d.tau⁻¹ = d.tau := by rw [← d.rho_conj, hconj]
  have h2 : d.tau ^ 2 = 1 := by rw [sq, mul_eq_one_iff_inv_eq]; exact hthis
  have hdvd : 2 ^ d.n ∣ 2 := by rw [← d.tau_order]; exact orderOf_dvd_iff_pow_eq_one.mpr h2
  have h4 : 4 ≤ 2 ^ d.n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) hn
  have hle : 2 ^ d.n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- In a finite group, membership in a cyclic subgroup is witnessed by a *natural* exponent. -/
private lemma mem_zpowers_iff_exists_nat {G : Type*} [Group G] [Finite G] {g h : G} :
    h ∈ Subgroup.zpowers g ↔ ∃ k : ℕ, g ^ k = h := by
  have hx : IsOfFinOrder g := isOfFinOrder_of_finite g
  constructor
  · intro hh
    exact (Submonoid.mem_powers_iff h g).mp (hx.mem_powers_iff_mem_zpowers.mpr hh)
  · rintro ⟨k, hk⟩
    exact hx.mem_powers_iff_mem_zpowers.mp ((Submonoid.mem_powers_iff h g).mpr ⟨k, hk⟩)

/-- Cardinality count: covering `P` by the two cosets `⟨tau⟩` and `rho · ⟨tau⟩` makes the map
`Bool × ⟨tau⟩ → P` a bijection, whence `|P| = 2 · 2 ^ n`. -/
private theorem card_of_cover {P : Type*} [Group P] [Finite P] (d : GenQuaternionData P)
    (hcover : ∀ g : P, g ∈ Subgroup.zpowers d.tau ∨
      ∃ h ∈ Subgroup.zpowers d.tau, g = d.rho * h)
    (hrho : d.rho ∉ Subgroup.zpowers d.tau) :
    Nat.card P = 2 ^ (d.n + 1) := by
  let H : Subgroup P := Subgroup.zpowers d.tau
  let f : Bool × H → P := fun p => if p.1 then d.rho * (p.2 : P) else (p.2 : P)
  have hf_false : ∀ h : H, f (false, h) = (h : P) := by intro h; simp [f]
  have hf_true : ∀ h : H, f (true, h) = d.rho * (h : P) := by intro h; simp [f]
  have hinj : Function.Injective f := by
    rintro ⟨b1, h1⟩ ⟨b2, h2⟩ heq
    cases b1 <;> cases b2
    · rw [hf_false, hf_false] at heq
      exact congrArg (Prod.mk false) (Subtype.ext heq)
    · rw [hf_false, hf_true] at heq
      exfalso
      have hrho_eq : d.rho = (h1 : P) * (h2 : P)⁻¹ := by rw [heq]; group
      exact hrho (by rw [hrho_eq]; exact H.mul_mem h1.2 (H.inv_mem h2.2))
    · rw [hf_true, hf_false] at heq
      exfalso
      have hrho_eq : d.rho = (h2 : P) * (h1 : P)⁻¹ := by rw [← heq]; group
      exact hrho (by rw [hrho_eq]; exact H.mul_mem h2.2 (H.inv_mem h1.2))
    · rw [hf_true, hf_true] at heq
      have h12 : h1 = h2 := by
        apply Subtype.ext
        exact mul_left_cancel heq
      rw [h12]
  have hsurj : Function.Surjective f := by
    intro g
    rcases hcover g with hg | ⟨h, hh, hgh⟩
    · exact ⟨(false, ⟨g, hg⟩), by rw [hf_false]⟩
    · exact ⟨(true, ⟨h, hh⟩), by rw [hf_true]; exact hgh.symm⟩
  have hle1 : Nat.card (Bool × H) ≤ Nat.card P := Nat.card_le_card_of_injective f hinj
  have hle2 : Nat.card P ≤ Nat.card (Bool × H) := Nat.card_le_card_of_surjective f hsurj
  have hcard : Nat.card P = Nat.card (Bool × H) := le_antisymm hle2 hle1
  have hBool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hH : Nat.card H = 2 ^ d.n := by
    change Nat.card (Subgroup.zpowers d.tau) = 2 ^ d.n
    rw [Nat.card_zpowers, d.tau_order]
  rw [hcard, Nat.card_prod, hBool, hH, pow_succ]
  ring

theorem genQuaternionData_basic {P : Type*} [Group P] [Finite P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) :
    Nat.card P = 2 ^ (d.n + 1) ∧ IsPGroup 2 P ∧
    orderOf (d.tau ^ (2 ^ (d.n - 1))) = 2 ∧
    (∀ z : P, orderOf z = 2 → z = d.tau ^ (2 ^ (d.n - 1))) ∧
    (∀ x : P, x ∉ Subgroup.zpowers d.tau → orderOf x = 4 ∧ x * d.tau * x⁻¹ = d.tau⁻¹) := by
  refine ⟨card_of_cover d (coset_cover d) (rho_not_mem_zpowers d), ?_,
    tau_pow_half_order d, ?_, ?_⟩
  · rw [IsPGroup.iff_card]
    exact ⟨d.n + 1, card_of_cover d (coset_cover d) (rho_not_mem_zpowers d)⟩
  · intro z hz
    rcases coset_cover d z with hzH | ⟨h, hh, hzh⟩
    · obtain ⟨k, hk⟩ := (mem_zpowers_iff_exists_nat (G := P)).mp hzH
      have hzk : orderOf (d.tau ^ k) = 2 := by rw [hk]; exact hz
      rw [← hk]
      exact pow_eq_pow_of_orderOf_eq_two (by have := d.hn; omega) d.tau_order hzk
    · obtain ⟨k, hk⟩ := (mem_zpowers_iff_exists_nat (G := P)).mp hh
      exfalso
      have h4 : orderOf (d.rho * d.tau ^ k) = 4 := (rho_mul_pow_order d k).1
      rw [← hk] at hzh
      rw [hzh] at hz
      omega
  · intro x hx
    rcases coset_cover d x with hxH | ⟨h, hh, hxh⟩
    · exact absurd hxH hx
    · obtain ⟨k, hk⟩ := (mem_zpowers_iff_exists_nat (G := P)).mp hh
      rw [← hk] at hxh
      rw [hxh]
      exact rho_mul_pow_order d k

end Work.BrauerSuzuki.Quaternion
