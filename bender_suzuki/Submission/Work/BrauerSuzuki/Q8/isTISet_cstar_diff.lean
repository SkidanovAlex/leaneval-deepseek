import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

open scoped Pointwise

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] [Finite G]

/-- A `zpow` of `x` reduces to a `pow` with exponent below `orderOf x`. -/
theorem aux_zpow_mod {x : G} {k : ℕ} (hk : 0 < k) (hx : orderOf x = k) (n : ℤ) :
    ∃ i : ℕ, i < k ∧ x ^ n = x ^ i := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hmod0 : 0 ≤ n % (k : ℤ) := Int.emod_nonneg n hkZ
  have hmodlt : n % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos n (by exact_mod_cast hk)
  refine ⟨(n % (k:ℤ)).toNat, by omega, ?_⟩
  have hx1 : x ^ (k : ℤ) = 1 := by rw [zpow_natCast, ← hx, pow_orderOf_eq_one]
  calc x ^ n = x ^ ((k:ℤ) * (n / (k:ℤ)) + n % (k:ℤ)) := by rw [Int.mul_ediv_add_emod]
    _ = (x ^ (k:ℤ)) ^ (n / (k:ℤ)) * x ^ (n % (k:ℤ)) := by rw [zpow_add, zpow_mul]
    _ = x ^ (n % (k:ℤ)) := by rw [hx1, one_zpow, one_mul]
    _ = x ^ (n % (k:ℤ)).toNat := by
        rw [← zpow_natCast x ((n % (k:ℤ)).toNat), Int.toNat_of_nonneg hmod0]

/-- The order of an element of a finite subgroup divides the order of the subgroup. -/
theorem orderOf_dvd_natCard_of_mem {H : Subgroup G} {h : G} (hh : h ∈ H) :
    orderOf h ∣ Nat.card ↥H := by
  have h2 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hh : Subgroup.zpowers h ≤ H)
  rwa [Nat.card_zpowers] at h2

/-- An element of a subgroup of odd order has odd order. -/
theorem odd_orderOf_of_mem {H : Subgroup G} (hH : Odd (Nat.card ↥H)) {h : G} (hh : h ∈ H) :
    Odd (orderOf h) :=
  hH.of_dvd_nat (orderOf_dvd_natCard_of_mem hh)

theorem coe_sup_zpowers_mul {x : G} {Hstar : Subgroup G}
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a) :
    ((Subgroup.zpowers x ⊔ Hstar : Subgroup G) : Set G)
      = (Subgroup.zpowers x : Set G) * (Hstar : Set G) := by
  have hle : Hstar ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    exact fun a ha => hcomm a ha b hb
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_trans hle (Subgroup.centralizer_le_normalizer _))

theorem exists_pow_mul_of_mem_centralizer {x : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a) {c : G}
    (hc : c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)) :
    ∃ i : ℕ, i < 4 ∧ ∃ h ∈ Hstar, c = x ^ i * h := by
  have hc' : c ∈ ((Subgroup.zpowers x ⊔ Hstar : Subgroup G) : Set G) := by
    rw [hsup]; exact hc
  rw [coe_sup_zpowers_mul hcomm, Set.mem_mul] at hc'
  obtain ⟨a, ha, b, hb, hab⟩ := hc'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨i, hi, hik⟩ := aux_zpow_mod (by norm_num) hx4 k
  exact ⟨i, hi, b, hb, by rw [← hab, ← hk, hik]⟩

theorem pow_mul_mem_mul_of_even {x : G} {Hstar : Subgroup G} {i : ℕ} (hieven : Even i) {h : G}
    (hh : h ∈ Hstar) :
    x ^ i * h ∈ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G) := by
  obtain ⟨j, rfl⟩ := hieven
  have hpow : x ^ (j + j) = (x ^ 2) ^ j := by rw [← two_mul, pow_mul]
  exact ⟨(x ^ 2) ^ j, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j, h, hh, by rw [hpow]⟩

theorem mem_mul_zpowers_sq_iff {x : G} {Hstar : Subgroup G}
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a) {c : G} :
    c ∈ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G) ↔
      c ∈ ((Subgroup.zpowers (x ^ 2) ⊔ Hstar : Subgroup G) : Set G) := by
  have hle2 : Subgroup.zpowers (x ^ 2) ≤ Subgroup.zpowers x :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)
  have hle : Hstar ≤ Subgroup.centralizer (Subgroup.zpowers (x ^ 2) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    exact fun a ha => hcomm a (hle2 ha) b hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers (x ^ 2)) Hstar
    (le_trans hle (Subgroup.centralizer_le_normalizer _))]

theorem mem_zpowers_sq_of_sq_eq_one {x : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hinf : Subgroup.zpowers x ⊓ Hstar = ⊥)
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar)) {c : G}
    (hc : c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)) (hsq : c ^ 2 = 1) :
    c ∈ Subgroup.zpowers (x ^ 2) := by
  obtain ⟨i, _hi, h, hh, rfl⟩ := exists_pow_mul_of_mem_centralizer hx4 hsup hcomm hc
  have hcm : Commute (x ^ i) h :=
    hcomm (x ^ i) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i) h hh
  have h2 : x ^ (2 * i) * h ^ 2 = 1 := by
    have h1 := hsq
    rw [hcm.mul_pow] at h1
    rwa [show (x ^ i) ^ 2 = x ^ (2 * i) by rw [← mul_comm i 2, ← pow_mul]] at h1
  have hx2i_inf : x ^ (2 * i) ∈ Subgroup.zpowers x ⊓ Hstar := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hh 2)
  have hx2i : x ^ (2 * i) = 1 := by
    have h1 := hx2i_inf
    rw [hinf] at h1
    simpa using h1
  have hh2 : h ^ 2 = 1 := by
    have h1 := h2
    rw [hx2i, one_mul] at h1
    exact h1
  have hh1 : h = 1 := by
    have hd : orderOf h ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hh2
    have hcop : Nat.Coprime (orderOf h) 2 := (odd_orderOf_of_mem hodd hh).coprime_two_right
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hd)
  have hie : Even i := by
    have h1 : orderOf x ∣ 2 * i := orderOf_dvd_iff_pow_eq_one.mpr hx2i
    rw [hx4] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, by omega⟩
  obtain ⟨j, rfl⟩ := hie
  rw [hh1, mul_one, ← two_mul, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j

theorem mem_centralizer_zpowers_self (x : G) :
    x ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_add_one, add_comm, zpow_one_add]

theorem mul_conj_mem_centralizer {x h c : G}
    (hh : h ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hc : c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)) :
    h * c * h⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro z hz
  have hz' : h⁻¹ * z * h ∈ Subgroup.zpowers x := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) z).mp hz
  have h1 : (h⁻¹ * z * h) * c = c * (h⁻¹ * z * h) := hc _ hz'
  calc z * (h * c * h⁻¹) = h * ((h⁻¹ * z * h) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * z * h)) * h⁻¹ := by rw [h1]
    _ = (h * c * h⁻¹) * z := by group

theorem conj_sq_mem_zpowers_sq {x h : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hinf : Subgroup.zpowers x ⊓ Hstar = ⊥)
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar))
    (hh : h ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    h * x ^ 2 * h⁻¹ ∈ Subgroup.zpowers (x ^ 2) := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4, pow_orderOf_eq_one]
  have hx22 : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; norm_num; exact hx4'
  refine mem_zpowers_sq_of_sq_eq_one hx4 hsup hinf hcomm hodd ?_ ?_
  · exact mul_conj_mem_centralizer hh (Subgroup.pow_mem _ (mem_centralizer_zpowers_self x) 2)
  · rw [← MulAut.conj_apply h (x ^ 2), ← map_pow (MulAut.conj h) (x ^ 2) 2, hx22, map_one]

theorem mul_conj_mem_mul {x : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hinf : Subgroup.zpowers x ⊓ Hstar = ⊥)
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar))
    (hnorm : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G),
      ∀ h ∈ Hstar, n * h * n⁻¹ ∈ Hstar)
    {n c : G} (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hc : c ∈ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G)) :
    n * c * n⁻¹ ∈ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G) := by
  rw [Set.mem_mul] at hc
  obtain ⟨t, ht, h, hh, rfl⟩ := hc
  have hT : n * x ^ 2 * n⁻¹ ∈ Subgroup.zpowers (x ^ 2) :=
    conj_sq_mem_zpowers_sq hx4 hsup hinf hcomm hodd hn
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hnt : n * t * n⁻¹ ∈ Subgroup.zpowers (x ^ 2) := by
    have h1 : n * t * n⁻¹ = (n * x ^ 2 * n⁻¹) ^ j := by
      rw [← hj, show n * (x ^ 2) ^ j * n⁻¹ = (MulAut.conj n) ((x ^ 2) ^ j) by
        rw [MulAut.conj_apply], map_zpow, MulAut.conj_apply]
    rw [h1]
    exact Subgroup.zpow_mem _ hT j
  have hnh : n * h * n⁻¹ ∈ Hstar := hnorm n hn h hh
  rw [Set.mem_mul]
  exact ⟨n * t * n⁻¹, hnt, n * h * n⁻¹, hnh, by group⟩

theorem zpowers_le_zpowers_of_notMem_mul {x : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar)) {a : G}
    (haC : a ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (haA : a ∉ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G)) :
    Subgroup.zpowers x ≤ Subgroup.zpowers a := by
  obtain ⟨i, _hi, h, hh, rfl⟩ := exists_pow_mul_of_mem_centralizer hx4 hsup hcomm haC
  have hiOdd : Odd i := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    exact haA (pow_mul_mem_mul_of_even hcon hh)
  have hcm : Commute (x ^ i) h :=
    hcomm (x ^ i) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i) h hh
  have hhpow : h ^ Nat.card ↥Hstar = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact orderOf_dvd_natCard_of_mem hh
  have ha_m : (x ^ i * h) ^ Nat.card ↥Hstar = x ^ (i * Nat.card ↥Hstar) := by
    rw [hcm.mul_pow, hhpow, mul_one, ← pow_mul]
  have hord : orderOf (x ^ (i * Nat.card ↥Hstar)) = 4 := by
    have hcop : Nat.gcd 4 (i * Nat.card ↥Hstar) = 1 := by
      have hOdd : Odd (i * Nat.card ↥Hstar) := hiOdd.mul hodd
      have h2 : Nat.Coprime (i * Nat.card ↥Hstar) 2 := hOdd.coprime_two_right
      have h3 : Nat.Coprime (i * Nat.card ↥Hstar) (2 ^ 2) := Nat.Coprime.pow_right 2 h2
      have h3' : Nat.gcd (i * Nat.card ↥Hstar) 4 = 1 := by simpa using h3
      rwa [Nat.gcd_comm] at h3'
    rw [orderOf_pow, hx4, hcop, Nat.div_one]
  have hle : Subgroup.zpowers (x ^ (i * Nat.card ↥Hstar)) ≤ Subgroup.zpowers x :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
  have hcard : Nat.card ↥(Subgroup.zpowers x)
      ≤ Nat.card ↥(Subgroup.zpowers (x ^ (i * Nat.card ↥Hstar))) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hx4, hord]
  have heq : Subgroup.zpowers (x ^ (i * Nat.card ↥Hstar)) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← ha_m] at heq
  rw [← heq]
  exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)

theorem mem_zpowers_of_pow_four_eq_one {x : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar)) {c : G}
    (hc : c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)) (hc4 : c ^ 4 = 1) :
    c ∈ Subgroup.zpowers x := by
  obtain ⟨i, _hi, h, hh, rfl⟩ := exists_pow_mul_of_mem_centralizer hx4 hsup hcomm hc
  have hx4' : x ^ 4 = 1 := by rw [← hx4, pow_orderOf_eq_one]
  have hcm : Commute (x ^ i) h :=
    hcomm (x ^ i) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i) h hh
  have hh4 : h ^ 4 = 1 := by
    have h1 := hc4
    rw [hcm.mul_pow] at h1
    have h2 : (x ^ i) ^ 4 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx4', one_pow]
    rwa [h2, one_mul] at h1
  have hh1 : h = 1 := by
    have hd : orderOf h ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hh4
    have hcop : Nat.Coprime (orderOf h) 4 := by
      have h2 : Nat.Coprime (orderOf h) (2 ^ 2) :=
        Nat.Coprime.pow_right 2 (odd_orderOf_of_mem hodd hh).coprime_two_right
      simpa using h2
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hd)
  rw [hh1, mul_one]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i

theorem mem_normalizer_of_mul_conj {x : G} {Hstar : Subgroup G} (hx4 : orderOf x = 4)
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar)) {g a b : G}
    (haC : a ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (haA : a ∉ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G))
    (hbC : b ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hconj : g * a * g⁻¹ = b) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hle := zpowers_le_zpowers_of_notMem_mul hx4 hsup hcomm hodd haC haA
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers x))
  have hbk : b ^ k = g * x * g⁻¹ := by
    rw [← hconj, ← MulAut.conj_apply g a, ← map_zpow (MulAut.conj g) a k, hk, MulAut.conj_apply]
  have hmemC : g * x * g⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [← hbk]
    exact Subgroup.zpow_mem _ hbC k
  have hpow4 : (g * x * g⁻¹) ^ 4 = 1 := by
    rw [← MulAut.conj_apply g x, ← map_pow (MulAut.conj g) x 4, ← hx4, pow_orderOf_eq_one, map_one]
  have hmemX : g * x * g⁻¹ ∈ Subgroup.zpowers x :=
    mem_zpowers_of_pow_four_eq_one hx4 hsup hcomm hodd hmemC hpow4
  have hmap : Subgroup.map (↑(MulAut.conj g)) (Subgroup.zpowers x)
      = Subgroup.zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (MulAut.conj_apply g x)
  have hcard : Nat.card ↥(Subgroup.zpowers x) = Nat.card ↥(Subgroup.zpowers (g * x * g⁻¹)) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [show Subgroup.map (↑(MulAut.conj g)) (Subgroup.zpowers x)
      = Subgroup.zpowers (g * x * g⁻¹) from hmap]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmemX) (le_of_eq hcard)

open scoped Pointwise in
theorem isTISet_cstar_diff {G : Type*} [Group G] [Finite G] {x : G} (hx4 : orderOf x = 4)
    {Hstar : Subgroup G}
    (hsup : Subgroup.zpowers x ⊔ Hstar = Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hinf : Subgroup.zpowers x ⊓ Hstar = ⊥)
    (hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Hstar, a * b = b * a)
    (hodd : Odd (Nat.card ↥Hstar))
    (hnorm : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G),
      ∀ h ∈ Hstar, n * h * n⁻¹ ∈ Hstar) :
    Work.BrauerSuzuki.IsTISet
      ((Subgroup.centralizer (Subgroup.zpowers x : Set G) : Set G) \
        ((Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G)))
      (Subgroup.normalizer (Subgroup.zpowers x : Set G)) := by
  have hxnot : x ∉ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G) := by
    intro hmem
    rw [Set.mem_mul] at hmem
    obtain ⟨t, ht, h', hh', hth⟩ := hmem
    have hh'1 : h' = 1 := by
      have h1 : h' ∈ Subgroup.zpowers x ⊓ Hstar := by
        refine Subgroup.mem_inf.mpr ⟨?_, hh'⟩
        have h2 : h' = t⁻¹ * x := by rw [← hth]; group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpowers_le.mpr
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2) ht)) (Subgroup.mem_zpowers x)
      rw [hinf] at h1
      simpa using h1
    have ht' : x ∈ Subgroup.zpowers (x ^ 2) := by
      have h2 : t = x := by rw [← hth, hh'1, mul_one]
      rw [h2] at ht
      exact ht
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers (x ^ 2) := Subgroup.zpowers_le.mpr ht'
    have hcard : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥(Subgroup.zpowers (x ^ 2)) :=
      Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow, hx4] at hcard
    norm_num at hcard
  have hxA : x ∈ (Subgroup.centralizer (Subgroup.zpowers x : Set G) : Set G) \
      ((Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G)) :=
    ⟨mem_centralizer_zpowers_self x, hxnot⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h1
    exact h1.2 ⟨1, Subgroup.one_mem _, 1, Hstar.one_mem, by simp⟩
  · rintro c hc
    exact Subgroup.centralizer_le_normalizer _ hc.1
  · rintro c hc
    refine ⟨Subgroup.inv_mem _ hc.1, fun hcinv => hc.2 ?_⟩
    have h1 : c⁻¹ ∈ ((Subgroup.zpowers (x ^ 2) ⊔ Hstar : Subgroup G) : Set G) :=
      (mem_mul_zpowers_sq_iff hcomm).mp hcinv
    have h2 : (c⁻¹)⁻¹ ∈ ((Subgroup.zpowers (x ^ 2) ⊔ Hstar : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ h1
    have h3 : c⁻¹⁻¹ ∈ (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G) :=
      (mem_mul_zpowers_sq_iff hcomm).mpr h2
    simpa using h3
  · rintro h hh c hc
    refine ⟨mul_conj_mem_centralizer hh hc.1, fun hmem => hc.2 ?_⟩
    have h1 : h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ ∈
        (Subgroup.zpowers (x ^ 2) : Set G) * (Hstar : Set G) :=
      mul_conj_mem_mul hx4 hsup hinf hcomm hodd hnorm (Subgroup.inv_mem _ hh) hmem
    have h2 : h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c := by group
    rwa [h2] at h1
  · rintro g hg
    exact mem_normalizer_of_mul_conj hx4 hsup hcomm hodd hxA.1 hxA.2 (hg hxA).1 rfl
  · rintro g hg a b ha hb hab
    exact hg (mem_normalizer_of_mul_conj hx4 hsup hcomm hodd ha.1 ha.2 hb.1 hab)

end Work.BrauerSuzuki.Q8
