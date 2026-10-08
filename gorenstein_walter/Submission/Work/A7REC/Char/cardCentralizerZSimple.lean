import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.IndexSeven
import Submission.Work.FUS.centralizer_has_normal_two_complement
import Submission.Work.FUS.Fusion
import Submission.Work.A7REC.Char.eq_of_card_five_of_card_fifteen
import Submission.Work.ASM.oddCore_odd
import Submission.Work.A7REC.Char.MinIndex
import Submission.Work.A7REC.Basic.card_centralizer_z
import Submission.Work.AUTA7.A7.CentralizerInvolution

set_option linter.unusedSectionVars false

namespace Work.A7REC.Char

open Subgroup

/-- A Sylow `2`-subgroup isomorphic to `DihedralGroup 4` has `8` elements. -/
theorem card_of_sylow_two_dihedral {G : Type*} [Group G] (S : Sylow 2 G)
    (h : Nonempty ((S : Subgroup G) ≃* DihedralGroup 4)) :
    Nat.card (S : Subgroup G) = 8 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- Transporting involution centralizers along a group isomorphism. -/
theorem card_centralizer_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] (e : G ≃* H)
    (z : G) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({(e z)} : Set H)) := by
  have hmap : (Subgroup.centralizer ({z} : Set G)).map (e : G →* H) =
      Subgroup.centralizer ({e z} : Set H) := by
    refine le_antisymm ?_ ?_
    · simpa using Subgroup.map_centralizer_le_centralizer_image ({z} : Set G) (e : G →* H)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h1 := hy (e w) (by simp)
      exact e.injective (by simpa using h1)
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

/-- The divisors of `315` that are divisible by `3`. -/
theorem divisors_315 (m : ℕ) (h1 : m ∣ 315) (h2 : 3 ∣ m) :
    m ∈ ({3, 9, 15, 21, 45, 63, 105, 315} : Finset ℕ) := by
  obtain ⟨k, hk⟩ := h2
  have hk105 : k ∣ 105 := by
    rw [hk] at h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using h1)
  have hkle : k ≤ 105 := Nat.le_of_dvd (by norm_num) hk105
  interval_cases k <;> simp_all <;> omega

/-- **A finite group of order `15` has a unique subgroup of order `3`.** -/
theorem card_three_unique_of_card_fifteen {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 15) {A B : Subgroup H} (hA : Nat.card A = 3) (hB : Nat.card B = 3) :
    A = B := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac : (Nat.card H).factorization 3 = 1 := by
    rw [hH, show (15 : ℕ) = 3 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 5)]
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := H)
  haveI : Finite (Sylow 3 H) := Sylow.finite_of_finiteIndex P
  have hcardP : Nat.card ↥(P : Subgroup H) = 3 := by
    rw [Sylow.card_eq_multiplicity P, hfac, pow_one]
  have hidx5 : (P : Subgroup H).index = 5 := by
    have h := Subgroup.card_mul_index (P : Subgroup H)
    rw [hcardP, hH] at h
    omega
  have hdvd : Nat.card (Sylow 3 H) ∣ 15 := by
    have h2 : (Subgroup.normalizer ((P : Subgroup H) : Set H)).index ∣ 15 := by
      have h3 := Subgroup.index_dvd_card (Subgroup.normalizer ((P : Subgroup H) : Set H))
      rwa [hH] at h3
    rwa [Sylow.card_eq_index_normalizer P]
  have huniq : Nat.card (Sylow 3 H) = 1 := by
    have hmem : Nat.card (Sylow 3 H) ∈ (15 : ℕ).divisors :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hmod : Nat.card (Sylow 3 H) % 3 = 1 := by
      have := card_sylow_modEq_one 3 H
      simpa [Nat.ModEq] using this
    have hlist : (15 : ℕ).divisors.filter (fun k => k % 3 = 1) = {1} := by decide
    have hmem' : Nat.card (Sylow 3 H) ∈ (15 : ℕ).divisors.filter (fun k => k % 3 = 1) :=
      Finset.mem_filter.mpr ⟨hmem, hmod⟩
    rw [hlist] at hmem'
    simpa using hmem'
  haveI : Subsingleton (Sylow 3 H) := by
    haveI : Fintype (Sylow 3 H) := Fintype.ofFinite _
    exact Fintype.card_le_one_iff_subsingleton.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have key : ∀ {A : Subgroup H}, Nat.card A = 3 → A = (P : Subgroup H) := by
    intro A hA3
    obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 H, A ≤ (Q : Subgroup H) := by
      have hAp : IsPGroup 3 ↥A := IsPGroup.iff_card.mpr ⟨1, by rw [hA3]; norm_num⟩
      exact hAp.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    rw [hQP] at hQ
    exact Subgroup.eq_of_le_of_card_ge hQ (by rw [hA3, hcardP])
  rw [key hA, key hB]

/-- **In a subgroup of order `15`, any two subgroups of order `3` coincide.** -/
theorem card_three_unique_of_le_of_card_fifteen {G : Type*} [Group G] [Finite G] {O : Subgroup G}
    (hO : Nat.card O = 15) {A B : Subgroup G} (hA : A ≤ O) (hB : B ≤ O)
    (hAc : Nat.card A = 3) (hBc : Nat.card B = 3) : A = B := by
  have hH : Nat.card ↥O = 15 := hO
  have hA' : Nat.card ↥(A.subgroupOf O) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]
  have hB' : Nat.card ↥(B.subgroupOf O) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hBc]
  have h := card_three_unique_of_card_fifteen hH hA' hB'
  rw [← Subgroup.map_subgroupOf_eq_of_le hA, ← Subgroup.map_subgroupOf_eq_of_le hB, h]

/-- **A finite group of order `21` has a unique subgroup of order `7`.** -/
theorem card_seven_unique_of_card_twentyone {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 21) {A B : Subgroup H} (hA : Nat.card A = 7) (hB : Nat.card B = 7) :
    A = B := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card H).factorization 7 = 1 := by
    rw [hH, show (21 : ℕ) = 3 * 7 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 7),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (7 : ℕ) ∣ 3)]
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := H)
  haveI : Finite (Sylow 7 H) := Sylow.finite_of_finiteIndex P
  have hcardP : Nat.card ↥(P : Subgroup H) = 7 := by
    rw [Sylow.card_eq_multiplicity P, hfac, pow_one]
  have hidx3 : (P : Subgroup H).index = 3 := by
    have h := Subgroup.card_mul_index (P : Subgroup H)
    rw [hcardP, hH] at h
    omega
  have hdvd : Nat.card (Sylow 7 H) ∣ 21 := by
    have h2 : (Subgroup.normalizer ((P : Subgroup H) : Set H)).index ∣ 21 := by
      have h3 := Subgroup.index_dvd_card (Subgroup.normalizer ((P : Subgroup H) : Set H))
      rwa [hH] at h3
    rwa [Sylow.card_eq_index_normalizer P]
  have huniq : Nat.card (Sylow 7 H) = 1 := by
    have hmem : Nat.card (Sylow 7 H) ∈ (21 : ℕ).divisors :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hmod : Nat.card (Sylow 7 H) % 7 = 1 := by
      have := card_sylow_modEq_one 7 H
      simpa [Nat.ModEq] using this
    have hlist : (21 : ℕ).divisors.filter (fun k => k % 7 = 1) = {1} := by decide
    have hmem' : Nat.card (Sylow 7 H) ∈ (21 : ℕ).divisors.filter (fun k => k % 7 = 1) :=
      Finset.mem_filter.mpr ⟨hmem, hmod⟩
    rw [hlist] at hmem'
    simpa using hmem'
  haveI : Subsingleton (Sylow 7 H) := by
    haveI : Fintype (Sylow 7 H) := Fintype.ofFinite _
    exact Fintype.card_le_one_iff_subsingleton.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have key : ∀ {A : Subgroup H}, Nat.card A = 7 → A = (P : Subgroup H) := by
    intro A hA7
    obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 7 H, A ≤ (Q : Subgroup H) := by
      have hAp : IsPGroup 7 ↥A := IsPGroup.iff_card.mpr ⟨1, by rw [hA7]; norm_num⟩
      exact hAp.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    rw [hQP] at hQ
    exact Subgroup.eq_of_le_of_card_ge hQ (by rw [hA7, hcardP])
  rw [key hA, key hB]

/-- **In a subgroup of order `21`, any two subgroups of order `7` coincide.** -/
theorem card_seven_unique_of_le_of_card_twentyone {G : Type*} [Group G] [Finite G]
    {O : Subgroup G} (hO : Nat.card O = 21) {A B : Subgroup G} (hA : A ≤ O) (hB : B ≤ O)
    (hAc : Nat.card A = 7) (hBc : Nat.card B = 7) : A = B := by
  have hH : Nat.card ↥O = 21 := hO
  have hA' : Nat.card ↥(A.subgroupOf O) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]
  have hB' : Nat.card ↥(B.subgroupOf O) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hBc]
  have h := card_seven_unique_of_card_twentyone hH hA' hB'
  rw [← Subgroup.map_subgroupOf_eq_of_le hA, ← Subgroup.map_subgroupOf_eq_of_le hB, h]

/-- The `3`-adic valuation of `2520 = 2^3 · 3^2 · 5 · 7`. -/
theorem factorization_2520_three : (2520 : ℕ).factorization 3 = 2 := by
  have h : (2520 : ℕ) = 2 ^ 3 * (3 ^ 2 * (5 ^ 1 * 7 ^ 1)) := by norm_num
  conv_lhs => rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7)]
  simp

/-- The `7`-adic valuation of `2520 = 2^3 · 3^2 · 5 · 7`. -/
theorem factorization_2520_seven : (2520 : ℕ).factorization 7 = 1 := by
  have h : (2520 : ℕ) = 2 ^ 3 * (3 ^ 2 * (5 ^ 1 * 7 ^ 1)) := by norm_num
  conv_lhs => rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5),
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7)]
  simp

/-- Let `t` be an involution which normalizes the cyclic subgroup generated by an element `x` of
prime order `p`.  If `t` does not centralize `x`, then `t` inverts `x`. -/
theorem involution_conj_eq_inv_of_prime {G : Type*} [Group G] {x t : G} {p : ℕ} (hp : Nat.Prime p)
    (hx : orderOf x = p) (ht : t * t = 1) (hN : t * x * t⁻¹ ∈ Subgroup.zpowers x)
    (hC : t * x * t⁻¹ ≠ x) : t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hN
  have hconj : ∀ n : ℤ, t * x ^ n * t⁻¹ = (t * x * t⁻¹) ^ n := by
    intro n
    have := map_zpow (MulAut.conj t) x n
    simpa [MulAut.conj_apply] using this
  have h1 : x ^ (k * k) = x ^ (1 : ℤ) := by
    calc x ^ (k * k) = (x ^ k) ^ k := zpow_mul x k k
      _ = (t * x * t⁻¹) ^ k := by rw [hk]
      _ = t * x ^ k * t⁻¹ := (hconj k).symm
      _ = t * (t * x * t⁻¹) * t⁻¹ := by rw [hk]
      _ = x ^ (1 : ℤ) := by
        rw [zpow_one,
          show t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) by group, ht,
          ← mul_inv_rev, ht, inv_one, one_mul, mul_one]
  have hx1 : x ^ (k * k - 1) = 1 := by
    rw [zpow_sub_one, h1, zpow_one, mul_inv_cancel]
  have hdvd : (p : ℤ) ∣ k * k - 1 := by
    rw [← hx, orderOf_dvd_iff_zpow_eq_one]
    exact hx1
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hfac : k * k - 1 = (k - 1) * (k + 1) := by ring
  rw [hfac] at hdvd
  rcases hpZ.dvd_mul.mp hdvd with h | h
  · exfalso
    apply hC
    rw [← hk]
    have hx1' : x ^ (k - 1) = 1 := by
      rw [← hx] at h
      exact orderOf_dvd_iff_zpow_eq_one.mp h
    calc x ^ k = x ^ ((k - 1) + 1) := by ring_nf
      _ = x ^ (k - 1) * x ^ (1 : ℤ) := zpow_add x (k - 1) 1
      _ = x := by rw [hx1', one_mul, zpow_one]
  · rw [← hk]
    have hx1' : x ^ (k + 1) = 1 := by
      rw [← hx] at h
      exact orderOf_dvd_iff_zpow_eq_one.mp h
    calc x ^ k = x ^ k * x * x⁻¹ := by group
      _ = x ^ (k + 1) * x⁻¹ := by rw [zpow_add_one]
      _ = x⁻¹ := by rw [hx1', one_mul]

/-- The subgroup generated by a conjugation-invariant set is normal. -/
theorem normal_closure_of_conj_invariant {G : Type*} [Group G] {s : Set G}
    (hs : ∀ g x : G, x ∈ s → g * x * g⁻¹ ∈ s) : (Subgroup.closure s).Normal :=
  Subgroup.Normal.mk fun x hx g =>
    Subgroup.closure_induction (p := fun y _ => g * y * g⁻¹ ∈ Subgroup.closure s)
      (fun y hy => Subgroup.subset_closure (hs g y hy))
      (by simp)
      (fun a b _ _ ha hb => by
        rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) from by group]
        exact Subgroup.mul_mem _ ha hb)
      (fun a _ ha => by
        rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ from by group]
        exact Subgroup.inv_mem _ ha)
      hx

/-- An element of a group whose square is `1` and which is not `1` has order `2`. -/
theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {x : G} (h : x * x = 1) (h1 : x ≠ 1) :
    orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := by
    refine orderOf_dvd_iff_pow_eq_one.mpr ?_
    rw [pow_two]
    exact h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
  · exact absurd (orderOf_eq_one_iff.mp h') h1
  · exact h'

/-- **`|C_G(z)| = 24` for the central involution `z` of a Sylow `2`-subgroup of a simple group
of order `2520`.**

`G` is a finite simple group with `|G| = 2520`, `S : Sylow 2 G` is dihedral of order `8`,
`z ∈ S` has order `2`, and `C_G(z) = U ⊔ S` with `|U| = 3`.  Then `|C_G(z)| = 24`.

WARNING about a tempting but WRONG shortcut: it is NOT true that `U ⊔ S = U · S`; the product
formula `|U · S| = |U|·|S|/|U ⊓ S| = 24` only gives `24 ≤ |U ⊔ S|`.  Concretely the group
`SmallGroup(72,22) = (C₆ × S₃) : C₂` carries the *whole* local configuration (central involution
`z`, Sylow `2`-subgroup `S ≅ D₈` with `z ∈ S`, subgroup `U` of order `3` with `⟨U, S⟩ = G`, and
`π` of order `4` with `C_G(π) = ⟨π⟩`) and `|C_G(z)| = 72`.  So the hypothesis `hC` does **not**
already give the conclusion, and the proof must use `|G| = 2520` and simplicity (equivalently:
the only simple group of order `2520` is `A₇`, in which every involution centralizer has order
`24`).

A workable route: prove that a simple group of order `2520` has a subgroup of index `7`
(see `Work.A7REC.Char.indexSevenOfSimple2520`, currently a stub; equivalently exclude the minimal
indices `8, …, 70` as in the sibling `Case*.lean` files), then
`Work.A7REC.mulEquiv_A7_of_index_seven` gives `G ≃* A₇`, and one computes in `A₇` that every
involution has centralizer order `24` (all involutions of `A₇` have cycle type `2²1³`).
Alternatively exclude `|C_G(z)| ∈ {72, 120, 168, 360}` directly: with `|G| = 2520`, every
element of order `4` is self-centralizing and all order-`4` elements are conjugate, each lying in
a unique Sylow `2`-subgroup, so `|C_G(z)| = 8m` with `m` odd, `3 ∣ m`, `m ∣ 315`, and the coset
action on `G ⧸ C_G(z)` embeds `G` into `A_{315/m}`, giving `m ∈ {3, 9, 15, 21, 45}`. -/
theorem cardCentralizerZSimple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 2520) (S : Sylow 2 G) (z : G) (U : Subgroup G)
    (hzS : z ∈ (S : Subgroup G)) (hz2 : orderOf z = 2)
    (hC : Subgroup.centralizer ({z} : Set G) = U ⊔ (S : Subgroup G)) (hU3 : Nat.card U = 3)
    (hSdih : Nonempty ((S : Subgroup G) ≃* DihedralGroup 4)) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 24 := by
  classical
  -- ## 0. Notation and first consequences
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  set O : Subgroup G := Work.GW2.oddCoreIn C with hOdef
  have hS8 : Nat.card (S : Subgroup G) = 8 := card_of_sylow_two_dihedral S hSdih
  have hSC : (S : Subgroup G) ≤ C := by rw [hC]; exact le_sup_right
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzcen : ∀ x ∈ (S : Subgroup G), x * z = z * x := by
    intro x hx
    have h : x ∈ Subgroup.centralizer ({z} : Set G) := hSC hx
    exact (Subgroup.mem_centralizer_iff.mp h z rfl).symm
  -- `G` has no normal subgroup of index `2` (it is simple), so by area `FUS` all involutions
  -- of `G` are conjugate.
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · have h2 := Subgroup.card_mul_index (⊥ : Subgroup G)
      rw [hbot] at hidx
      rw [hidx, Subgroup.card_bot, one_mul, hcard] at h2
      omega
    · have h2 := Subgroup.card_mul_index (⊤ : Subgroup G)
      rw [htop] at hidx
      rw [hidx, Subgroup.card_top, hcard] at h2
      omega
  have hInvConj : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    Work.FUS.involutions_conj S 4 (by norm_num) hSdih hnoN
  -- ## 1. `C = O(C) ⋊ S` (Frobenius' normal `p`-complement theorem, area FUS)
  obtain ⟨N, hNnorm, hNcomp⟩ :=
    Work.FUS.centralizer_has_normal_two_complement S 4 (by norm_num) hSdih z hzS hz2 hzcen
  haveI : N.Normal := hNnorm
  let P : Sylow 2 ↥C := S.subtype hSC
  have hcomp := hNcomp P
  have hsup : N ⊔ (P : Subgroup ↥C) = ⊤ := hcomp.sup_eq_top
  have hPcoecarrier : (P : Subgroup ↥C) = (S : Subgroup G).subgroupOf C :=
    Sylow.coe_subtype (P := S) (N := C) hSC
  have hPcard : Nat.card ↥(P : Subgroup ↥C) = 8 := by
    rw [hPcoecarrier]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, hS8]
  have hNodd : Odd (Nat.card N) := by
    have hidx : Nat.card N = (P : Subgroup ↥C).index := hcomp.index_eq_card.symm
    rw [hidx]
    have hrel : (P : Subgroup ↥C).index = (S : Subgroup G).relIndex C := by
      rw [hPcoecarrier]; rfl
    rw [hrel]
    have hmul : (S : Subgroup G).relIndex C * C.index = (S : Subgroup G).index :=
      Subgroup.relIndex_mul_index hSC
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSodd : Odd (S : Subgroup G).index := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      exact S.not_dvd_index (even_iff_two_dvd.mp hev)
    rcases Nat.even_or_odd ((S : Subgroup G).relIndex C) with hev | hodd
    · exfalso
      rw [even_iff_two_dvd] at hev
      have h2 : (2 : ℕ) ∣ (S : Subgroup G).relIndex C * C.index := dvd_mul_of_dvd_left hev _
      rw [hmul] at h2
      exact (Nat.not_even_iff_odd.mpr hSodd) (even_iff_two_dvd.mpr h2)
    · exact hodd
  have hNle : N ≤ Work.GW2.oddCore ↥C :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNnorm, hNodd⟩)
  have htop : Work.GW2.oddCore ↥C ⊔ (P : Subgroup ↥C) = ⊤ :=
    top_le_iff.mp (hsup ▸ sup_le_sup_right hNle (P : Subgroup ↥C))
  have hmap := congrArg (Subgroup.map C.subtype) htop
  simp only [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hPS : (P : Subgroup ↥C).map C.subtype = (S : Subgroup G) := by
    rw [hPcoecarrier, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSC]
  rw [hPS] at hmap
  have hsplit : O ⊔ (S : Subgroup G) = C := by
    rw [hOdef, Work.GW2.oddCoreIn]; exact hmap
  have hOle : O ≤ C := by
    rw [hOdef, Work.GW2.oddCoreIn]; exact Subgroup.map_subtype_le _
  -- ## 2. `|C| = 8 * |O(C)|`
  set Oc : Subgroup ↥C := Work.GW2.oddCore ↥C with hOcdef
  have hOcN : Oc.Normal := Work.GW2.oddCore_normal _
  have hOcodd : Odd (Nat.card Oc) := Work.ASM.oddCore_odd _
  have hOcdisj : Disjoint Oc (P : Subgroup ↥C) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    have hcop : Nat.Coprime (Nat.card Oc) 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 (hOcodd.coprime_two_right)
    rwa [hPcard]
  have hPnorm : (P : Subgroup ↥C) ≤ Subgroup.normalizer (Oc : Set ↥C) := by
    rw [(Subgroup.normalizer_eq_top_iff).mpr hOcN]
    exact le_top
  have hcardC : Nat.card ↥C = Nat.card Oc * 8 := by
    have h1 : Nat.card ↥(⊤ : Subgroup ↥C) = Nat.card Oc * 8 := by
      rw [← htop]
      rw [Work.A7REC.Basic.card_sup_mul_card_of_le_normalizer_of_disjoint hPnorm hOcdisj, hPcard]
    simpa using h1
  -- ## 3. Every element of `C` of order `3` lies in `O(C)` (odd order subgroups of `C` are
  -- contained in the odd core, since `↥C ⧸ O(C)` is a `2`-group).
  have hUC : U ≤ C := by rw [hC]; exact le_sup_left
  have hodd_mem_O : ∀ x ∈ C, Odd (orderOf x) → x ∈ O := by
    intro x hxC hxodd
    haveI : Oc.Normal := hOcN
    have hq8 : Nat.card (↥C ⧸ Oc) = 8 := by
      rw [← Subgroup.index_eq_card Oc]
      have hmul := Subgroup.card_mul_index Oc
      rw [hcardC] at hmul
      exact Nat.mul_left_cancel Nat.card_pos hmul
    have hdvd1 : orderOf ((QuotientGroup.mk' Oc) ⟨x, hxC⟩) ∣ orderOf x := by
      have h := orderOf_map_dvd (QuotientGroup.mk' Oc) (⟨x, hxC⟩ : ↥C)
      rwa [← Subgroup.orderOf_coe] at h
    have hdvd8 : orderOf ((QuotientGroup.mk' Oc) ⟨x, hxC⟩) ∣ 8 := by
      have h := Subgroup.card_dvd_of_le
        (show Subgroup.zpowers ((QuotientGroup.mk' Oc) ⟨x, hxC⟩) ≤ ⊤ from le_top)
      rw [Subgroup.card_top, Nat.card_zpowers, hq8] at h
      exact h
    have horder1 : orderOf ((QuotientGroup.mk' Oc) ⟨x, hxC⟩) = 1 := by
      have hdvd : orderOf ((QuotientGroup.mk' Oc) ⟨x, hxC⟩) ∣ 1 := by
        have hgcd : Nat.gcd (orderOf x) 8 = 1 := by
          have hcop : Nat.Coprime (orderOf x) 8 := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
            exact Nat.Coprime.pow_right 3 hxodd.coprime_two_right
          exact hcop
        rw [← hgcd]
        exact Nat.dvd_gcd hdvd1 hdvd8
      exact Nat.dvd_one.mp hdvd
    have hxq : (QuotientGroup.mk' Oc) ⟨x, hxC⟩ = 1 := by
      rw [← orderOf_eq_one_iff]; exact horder1
    rw [QuotientGroup.mk'_apply] at hxq
    rw [QuotientGroup.eq_one_iff] at hxq
    rw [hOdef, Work.GW2.oddCoreIn]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hxq, rfl⟩
  have horder3_mem_O : ∀ x ∈ C, orderOf x = 3 → x ∈ O :=
    fun x hx h => hodd_mem_O x hx (by rw [h]; norm_num)
  have horder7_mem_O : ∀ x ∈ C, orderOf x = 7 → x ∈ O :=
    fun x hx h => hodd_mem_O x hx (by rw [h]; norm_num)
  have hUleO : U ≤ O := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact O.one_mem
    · refine horder3_mem_O x (hUC hx) ?_
      have h : orderOf x ∣ Nat.card U := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
      rw [hU3] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h3
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, Work.GW2.oddCoreIn, Subgroup.card_map_of_injective Subtype.coe_injective]
    exact Work.ASM.oddCore_odd _
  have hcardO : Nat.card O = Nat.card Oc := by
    rw [hOdef, Work.GW2.oddCoreIn, Subgroup.card_map_of_injective Subtype.coe_injective, hOcdef]
  have hdisjO : Disjoint O (S : Subgroup G) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    have hcop : Nat.Coprime (Nat.card O) 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 (hOodd.coprime_two_right)
    rwa [hS8]
  -- ## 5. Arithmetic on `m = |O(C)|`
  set m : ℕ := Nat.card Oc with hmdef
  have hcardC8 : Nat.card ↥C = 8 * m := by rw [hcardC, hmdef, mul_comm]
  have hm315 : m ∣ 315 := by
    have h1 : Nat.card C ∣ Nat.card G := by
      have h := Subgroup.card_dvd_of_le (show C ≤ ⊤ from le_top)
      rwa [Subgroup.card_top] at h
    rw [hcard] at h1
    rw [hcardC8] at h1
    have h1' : 8 * m ∣ 8 * 315 := by simpa [mul_comm] using h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8)).mp h1'
  have hm3 : 3 ∣ m := by
    have h1 : Nat.card U ∣ Nat.card C := Subgroup.card_dvd_of_le hUC
    rw [hU3, hcardC8] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 8) h1
  have hmodd : Odd m := by rw [hmdef]; exact hOcodd
  -- ## 6. Case analysis: `m ∈ {3,9,15,21,45,63,105,315}` and only `m = 3` survives
  have hCindex : Nat.card C * C.index = 2520 := by
    have h := Subgroup.card_mul_index C
    rwa [hcard] at h
  have hmcases := divisors_315 m hm315 hm3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmcases
  rcases hmcases with h3 | h9 | h15 | h21 | h45 | h63 | h105 | h315
  · -- `m = 3`: done
    rw [hcardC8, h3]
  · -- `m = 9`: `O` is a Sylow `3`-subgroup of `G` and `C ≤ N_G(O)`
    exfalso
    have hO9 : Nat.card O = 9 := by rw [hcardO, h9]
    -- `C` normalizes `O`, since `O` is the odd core of `C`
    have hsub : O.subgroupOf C = Work.GW2.oddCore ↥C := by
      have hmap : O = (Work.GW2.oddCore ↥C).map C.subtype := by
        rw [hOdef, Work.GW2.oddCoreIn]
      rw [hmap, ← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    have hC_le_N : C ≤ Subgroup.normalizer (O : Set G) := by
      have hN : (O.subgroupOf C).Normal := by
        rw [hsub]; exact Work.GW2.oddCore_normal _
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hN
    have hdvd72 : 72 ∣ Nat.card (Subgroup.normalizer (O : Set G)) := by
      have h := Subgroup.card_dvd_of_le hC_le_N
      rw [hcardC8, h9] at h
      norm_num at h
      exact h
    have hn3dvd : (Subgroup.normalizer (O : Set G)).index ∣ 35 := by
      obtain ⟨t, ht⟩ := hdvd72
      have hmul := Subgroup.card_mul_index (Subgroup.normalizer (O : Set G))
      rw [hcard, ht] at hmul
      have h72 : 72 * (t * (Subgroup.normalizer (O : Set G)).index) = 72 * 35 := by
        rw [← mul_assoc, hmul]
      have hcancel := Nat.mul_left_cancel (show (0 : ℕ) < 72 by norm_num) h72
      exact ⟨t, by rw [mul_comm]; exact hcancel.symm⟩
    -- `O` is a Sylow `3`-subgroup of `G`, so `n₃ ≡ 1 mod 3`
    have hmod3 : (Subgroup.normalizer (O : Set G)).index % 3 = 1 := by
      have hcard' : Nat.card O = 3 ^ (Nat.card G).factorization 3 := by
        rw [hcard, factorization_2520_three, hO9]
        norm_num
      have hcoe : (↑(Sylow.ofCard (p := 3) O hcard') : Subgroup G) = O :=
        Sylow.coe_ofCard O hcard'
      haveI : Finite (Sylow 3 G) :=
        Sylow.finite_of_finiteIndex (Sylow.ofCard (p := 3) O hcard')
      have hidx : Nat.card (Sylow 3 G) = (Subgroup.normalizer (O : Set G)).index := by
        rw [← hcoe]
        exact Sylow.card_eq_index_normalizer _
      have h := card_sylow_modEq_one 3 G
      rw [hidx] at h
      simpa [Nat.ModEq] using h
    have hcases : (Subgroup.normalizer (O : Set G)).index ∈ ({1, 7} : Finset ℕ) := by
      have hmem : (Subgroup.normalizer (O : Set G)).index ∈ (35 : ℕ).divisors :=
        Nat.mem_divisors.mpr ⟨hn3dvd, by norm_num⟩
      have hlist : (35 : ℕ).divisors.filter (fun k => k % 3 = 1) = {1, 7} := by decide
      have hmem' : (Subgroup.normalizer (O : Set G)).index ∈
          (35 : ℕ).divisors.filter (fun k => k % 3 = 1) :=
        Finset.mem_filter.mpr ⟨hmem, hmod3⟩
      rwa [hlist] at hmem'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
    rcases hcases with h1 | h7
    · -- `n₃ = 1`, so `O ⊴ G`
      have htop : Subgroup.normalizer (O : Set G) = ⊤ := (Subgroup.index_eq_one).mp h1
      have hOnorm : O.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal O with hbot | htop'
      · rw [hbot, Subgroup.card_bot] at hO9
        omega
      · rw [htop', Subgroup.card_top, hcard] at hO9
        omega
    · -- `n₃ = 7`: `G` has a subgroup of index `7`, hence `G ≃* A₇`
      obtain ⟨e⟩ :=
        Work.A7REC.mulEquiv_A7_of_index_seven G hcard (Subgroup.normalizer (O : Set G)) h7
      have h24 : Nat.card
          (Subgroup.centralizer ({(e z)} : Set (alternatingGroup (Fin 7)))) = 24 :=
        Work.AUTA7.A7.CentralizerInvolution (by
            rw [← map_mul, ← map_one e]
            congr 1
            rw [← pow_two, ← hz2, pow_orderOf_eq_one]) (by
            intro h
            have hz1' : z = 1 := e.injective (by rw [map_one]; exact h)
            rw [hz1', orderOf_one] at hz2
            omega)
      have h24' := card_centralizer_mulEquiv e z
      rw [h24, ← hCdef] at h24'
      have hC72 : Nat.card C = 72 := by rw [hcardC8, h9]
      omega
  · -- `m = 15`: `|C| = 120`, `|O| = 15`; the subgroup of order `5` of `O` is normal in `C`
    exfalso
    have hO15 : Nat.card O = 15 := by rw [hcardO, h15]
    have hsub : O.subgroupOf C = Work.GW2.oddCore ↥C := by
      have hmap : O = (Work.GW2.oddCore ↥C).map C.subtype := by
        rw [hOdef, Work.GW2.oddCoreIn]
      rw [hmap, ← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    have hC_le_N : C ≤ Subgroup.normalizer (O : Set G) := by
      have hN : (O.subgroupOf C).Normal := by
        rw [hsub]; exact Work.GW2.oddCore_normal _
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hN
    -- an element of `O` of order `5`, and the subgroup `M` it generates
    obtain ⟨y5, hy5⟩ : ∃ y : ↥O, orderOf y = 5 := by
      haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have h5 : 5 ∣ Nat.card ↥O := by rw [hO15]; norm_num
      exact exists_prime_orderOf_dvd_card' 5 h5
    set M : Subgroup G := Subgroup.zpowers (y5 : G) with hMdef
    have hMle : M ≤ O := Subgroup.zpowers_le.mpr y5.2
    have hMcard : Nat.card M = 5 := by
      rw [hMdef, Nat.card_zpowers, Subgroup.orderOf_coe, hy5]
    have hMuniq : ∀ A : Subgroup G, A ≤ O → Nat.card A = 5 → A = M := by
      intro A hA hAcard
      have hA' : Nat.card ↥(A.subgroupOf O) = 5 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAcard]
      have hM' : Nat.card ↥(M.subgroupOf O) = 5 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMle).toEquiv, hMcard]
      have h := eq_of_card_five_of_card_fifteen hO15 hA' hM'
      rw [← Subgroup.map_subgroupOf_eq_of_le hA, ← Subgroup.map_subgroupOf_eq_of_le hMle, h]
    have hMnormC : C ≤ Subgroup.normalizer (M : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hAle : M.map (MulAut.conj c).toMonoidHom ≤ O := by
        rintro z hz
        rw [Subgroup.mem_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        have hiff := Subgroup.mem_normalizer_iff.mp (hC_le_N hc)
        have hcw : (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ := by simp [MulAut.conj_apply]
        rw [hcw]
        exact (hiff w).mp (hMle hw)
      have hA5 : Nat.card (M.map (MulAut.conj c).toMonoidHom) = 5 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hMcard]
      exact hMuniq _ hAle hA5
    have hdvd120 : 120 ∣ Nat.card (Subgroup.normalizer (M : Set G)) := by
      have h := Subgroup.card_dvd_of_le hMnormC
      rw [hcardC8, h15] at h
      norm_num at h
      exact h
    have hn5dvd : (Subgroup.normalizer (M : Set G)).index ∣ 21 := by
      obtain ⟨t, ht⟩ := hdvd120
      have hmul := Subgroup.card_mul_index (Subgroup.normalizer (M : Set G))
      rw [hcard, ht] at hmul
      have h120 : 120 * (t * (Subgroup.normalizer (M : Set G)).index) = 120 * 21 := by
        rw [← mul_assoc, hmul]
      have hcancel := Nat.mul_left_cancel (show (0 : ℕ) < 120 by norm_num) h120
      exact ⟨t, by rw [mul_comm]; exact hcancel.symm⟩
    have hcases : (Subgroup.normalizer (M : Set G)).index ∈ ({1, 3, 7, 21} : Finset ℕ) := by
      have hmem : (Subgroup.normalizer (M : Set G)).index ∈ (21 : ℕ).divisors :=
        Nat.mem_divisors.mpr ⟨hn5dvd, by norm_num⟩
      have hlist : (21 : ℕ).divisors = {1, 3, 7, 21} := by decide
      rwa [hlist] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
    rcases hcases with h1 | h3 | h7 | h21
    · -- `n = 1`: `M ⊴ G`
      have htop : Subgroup.normalizer (M : Set G) = ⊤ := (Subgroup.index_eq_one).mp h1
      have hMnormal : M.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop'
      · rw [hbot, Subgroup.card_bot] at hMcard
        omega
      · rw [htop', Subgroup.card_top, hcard] at hMcard
        omega
    · -- `n = 3`: index `3`
      have hne : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
        intro htop
        rw [htop, Subgroup.index_top] at h3
        omega
      have := Work.A7REC.Char.no_small_index hcard (Subgroup.normalizer (M : Set G)) hne
      omega
    · -- `n = 7`: `G ≃* A₇`, so `|C| = 24 ≠ 120`
      obtain ⟨e⟩ :=
        Work.A7REC.mulEquiv_A7_of_index_seven G hcard (Subgroup.normalizer (M : Set G)) h7
      have h24 : Nat.card
          (Subgroup.centralizer ({(e z)} : Set (alternatingGroup (Fin 7)))) = 24 :=
        Work.AUTA7.A7.CentralizerInvolution (by
            rw [← map_mul, ← map_one e]
            congr 1
            rw [← pow_two, ← hz2, pow_orderOf_eq_one]) (by
            intro h
            have hz1' : z = 1 := e.injective (by rw [map_one]; exact h)
            rw [hz1', orderOf_one] at hz2
            omega)
      have h24' := card_centralizer_mulEquiv e z
      rw [h24, ← hCdef] at h24'
      have hC120 : Nat.card C = 120 := by rw [hcardC8, h15]
      omega
    · -- `n = 21`: `C = N_G(M)`
      have hNeq : Nat.card (Subgroup.normalizer (M : Set G)) = 120 := by
        have hmul := Subgroup.card_mul_index (Subgroup.normalizer (M : Set G))
        rw [hcard, h21] at hmul
        omega
      have hcardC120 : Nat.card C = 120 := by rw [hcardC8, h15]
      have hCeq : Subgroup.normalizer (M : Set G) = C :=
        (Subgroup.eq_of_le_of_card_ge hMnormC (by rw [hcardC120, hNeq])).symm
      -- the subgroups of order `5` of `C` are all equal to `M`
      have hC_unique : ∀ M' : Subgroup G, M' ≤ C → Nat.card M' = 5 → M' = M := by
        intro M' hM' hM'card
        have hM'O : M' ≤ O := by
          intro q hq
          have hqC : q ∈ C := hM' hq
          by_cases hq1 : q = 1
          · rw [hq1]; exact O.one_mem
          · have hdvd : orderOf q ∣ 5 := by
              rw [← hM'card]
              rw [← Nat.card_zpowers]
              exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hq)
            rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
            · exact absurd (orderOf_eq_one_iff.mp h) hq1
            · exact hodd_mem_O q hqC (by rw [h]; norm_num)
        exact hMuniq M' hM'O hM'card
      -- every involution of `C_G(M)` equals `z`
      have huniq_inv : ∀ u : G, orderOf u = 2 → u ∈ Subgroup.centralizer (M : Set G) → u = z := by
        intro u hu2 huC
        obtain ⟨g, hg⟩ := isConj_iff.mp (hInvConj u z hu2 hz2)
        have hu_eq : u = g⁻¹ * z * g := by
          have h := congrArg (fun w => g⁻¹ * w * g) hg
          simpa [mul_assoc] using h
        have hMle2 : M.map (MulAut.conj g).toMonoidHom ≤ C := by
          rintro w hw
          rw [Subgroup.mem_map] at hw
          obtain ⟨q, hq, rfl⟩ := hw
          have hcq : (MulAut.conj g).toMonoidHom q = g * q * g⁻¹ := by simp [MulAut.conj_apply]
          rw [hcq, Subgroup.mem_centralizer_iff]
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          have hcomm : q * u = u * q := Subgroup.mem_centralizer_iff.mp huC q hq
          have hconj := congrArg (fun w => g * w * g⁻¹) hcomm
          rw [hu_eq] at hconj
          simpa [mul_assoc] using hconj.symm
        have hcard5 : Nat.card ↥(M.map (MulAut.conj g).toMonoidHom) = 5 := by
          rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hMcard]
        have hMeq : M.map (MulAut.conj g).toMonoidHom = M := hC_unique _ hMle2 hcard5
        have hgC : g ∈ C := hCeq ▸ Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq
        rw [hu_eq]
        have hcomm := (Subgroup.mem_centralizer_iff.mp (C.inv_mem hgC)) z rfl
        rw [← hcomm]
        group
      -- the four reflections of `S` are involutions different from `z`
      obtain ⟨e⟩ := hSdih
      have hzcmem : (⟨z, hzS⟩ : ↥(S : Subgroup G)) ∈
          Subgroup.center ↥(S : Subgroup G) := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact Subtype.ext (hzcen x.1 x.2)
      have hzsr : ∀ i : ZMod 4, DihedralGroup.sr i ≠ e ⟨z, hzS⟩ := by
        intro i hi
        have hcent : e ⟨z, hzS⟩ ∈ Subgroup.center (DihedralGroup 4) := by
          rw [Subgroup.mem_center_iff]
          intro x
          have h := Subgroup.mem_center_iff.mp hzcmem (e.symm x)
          have h1 : e (⟨z, hzS⟩ * e.symm x) = e (e.symm x * ⟨z, hzS⟩) := by rw [h]
          simpa using h1.symm
        rw [← hi] at hcent
        rw [Subgroup.mem_center_iff] at hcent
        have hcomm' := (hcent (DihedralGroup.r 1)).symm
        rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at hcomm'
        have h1 : (1 : ZMod 4) = -1 := by
          have := congrArg (fun t : ZMod 4 => t - i) (DihedralGroup.sr.inj hcomm')
          simpa using this
        have h2 : (1 + 1 : ZMod 4) = 0 := by
          have h3 := congrArg (fun t : ZMod 4 => t + 1) h1
          rw [neg_add_cancel] at h3
          exact h3
        exact absurd h2 (by decide)
      have htord : ∀ i : ZMod 4,
          orderOf ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) = 2 := by
        intro i
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm (DihedralGroup.sr i),
          DihedralGroup.orderOf_sr]
      have ht2 : ∀ i : ZMod 4, ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
          ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) = 1 := by
        intro i
        have h := pow_orderOf_eq_one ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)
        rw [htord i, pow_two] at h
        exact h
      have htS : ∀ i : ZMod 4,
          ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ∈ (S : Subgroup G) :=
        fun i => (e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)).2
      have htz : ∀ i : ZMod 4, ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ≠ z := by
        intro i h
        have h3 : e ⟨z, hzS⟩ = DihedralGroup.sr i := by
          have h4 : (e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) = ⟨z, hzS⟩ := Subtype.ext h
          rw [← h4, MulEquiv.apply_symm_apply]
        exact hzsr i h3.symm
      -- each of them inverts the generator `y5` of `M`
      have htinv : ∀ i : ZMod 4, ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
          (y5 : G) * (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ = (y5 : G)⁻¹ := by
        intro i
        have hN : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ ∈
            Subgroup.zpowers (y5 : G) := by
          have hmem : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ∈
              Subgroup.normalizer (M : Set G) := hMnormC (hSC (htS i))
          have h5 := (Subgroup.mem_normalizer_iff.mp hmem (y5 : G)).mp
            (Subgroup.mem_zpowers (y5 : G))
          simpa only [hMdef] using h5
        have hne : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ ≠ (y5 : G) := by
          intro hconj
          have hcen : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ∈
              Subgroup.centralizer (M : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro w hw
            have hwz : w ∈ Subgroup.zpowers (y5 : G) := hMdef ▸ hw
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
            rw [← hn]
            have h6 : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) ^ n *
                (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ = (y5 : G) ^ n := by
              have h7 := map_zpow
                (MulAut.conj ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) (y5 : G) n
              simpa [MulAut.conj_apply, hconj] using h7
            calc (y5 : G) ^ n * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)
                = (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) ^ n *
                  (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹) *
                  ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) := by rw [h6]
              _ = ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) ^ n := by group
          exact htz i (huniq_inv _ (htord i) hcen)
        exact involution_conj_eq_inv_of_prime Nat.prime_five
          (by rw [Subgroup.orderOf_coe]; exact hy5) (ht2 i) hN hne
      -- hence the products `w · t` with `w ∈ M` are involutions
      have hwt : ∀ (i : ZMod 4) (w : G), w ∈ M →
          ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * w *
          (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ = w⁻¹ := by
        intro i w hw
        have hwz : w ∈ Subgroup.zpowers (y5 : G) := hMdef ▸ hw
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
        rw [← hn]
        have h5 : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) ^ n *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ =
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y5 : G) *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹) ^ n := by
          have h6 := map_zpow
            (MulAut.conj ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) (y5 : G) n
          simpa [MulAut.conj_apply] using h6
        rw [h5, htinv i, inv_zpow]
      have hwt2 : ∀ (i : ZMod 4) (w : G), w ∈ M →
          (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) *
          (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) = 1 := by
        intro i w hw
        calc (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) *
              (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))
            = w * (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * w *
              (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹) *
              (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
              ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) := by group
          _ = w * w⁻¹ * 1 := by rw [hwt i w hw, ht2 i]
          _ = 1 := by rw [mul_inv_cancel, one_mul]
      have hne1 : ∀ (i : ZMod 4) (w : G), w ∈ M →
          w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ≠ 1 := by
        intro i w hw h1
        have h2 : w = (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ := by
          calc w = w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
                (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ := by group
            _ = 1 * (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ := by rw [h1]
            _ = (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ := by rw [one_mul]
        have htt : (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ =
            ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) := by
          calc (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹
              = (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ *
                (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
                ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) := by
                rw [ht2 i, mul_one]
            _ = ((((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ *
                ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) *
                ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) := by group
            _ = ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) := by
                rw [inv_mul_cancel, one_mul]
        rw [htt] at h2
        have h3 : w ∈ (S : Subgroup G) := h2 ▸ htS i
        have hmem : w ∈ O ⊓ (S : Subgroup G) := ⟨hMle hw, h3⟩
        rw [disjoint_iff.mp hdisjO, Subgroup.mem_bot] at hmem
        rw [hmem, one_mul] at h1
        exact absurd (htord i) (by rw [h1, orderOf_one]; norm_num)
      -- the `21` involutions `z` and `w · t`
      have hMcard_prod : Nat.card (↥M × ZMod 4) = 20 := by
        rw [Nat.card_prod, hMcard]
        norm_num [Nat.card_eq_fintype_card, ZMod.card]
      let F : (↥M × ZMod 4) ⊕ Fin 1 → {w : G // orderOf w = 2} :=
        Sum.elim (fun s : ↥M × ZMod 4 =>
            (⟨(s.1 : G) * ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G), by
              refine orderOf_eq_two_of_mul_self (hwt2 s.2 s.1 s.1.2) ?_
              exact hne1 s.2 s.1 s.1.2⟩ : {w : G // orderOf w = 2}))
          (fun _ : Fin 1 => (⟨z, hz2⟩ : {w : G // orderOf w = 2}))
      have hFinl : ∀ s : ↥M × ZMod 4, (F (Sum.inl s)).1 =
          (s.1 : G) * ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G) := fun _ => rfl
      have hFinr : ∀ u : Fin 1, (F (Sum.inr u)).1 = z := fun _ => rfl
      have hinj : Function.Injective F := by
        rintro (s | s) (t | t) heq
        · -- two products
          have h1 : (s.1 : G) * ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G) =
              (t.1 : G) * ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G) := by
            have h := congrArg Subtype.val heq
            rwa [hFinl s, hFinl t] at h
          have hone : (t.1 : G)⁻¹ * (s.1 : G) = 1 := by
            have hO : (t.1 : G)⁻¹ * (s.1 : G) ∈ O :=
              O.mul_mem (O.inv_mem (hMle t.1.2)) (hMle s.1.2)
            have hS : (t.1 : G)⁻¹ * (s.1 : G) ∈ (S : Subgroup G) := by
              have h2 : (t.1 : G)⁻¹ * (s.1 : G) =
                  ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G) *
                  (((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G))⁻¹ := by
                have h3 : (t.1 : G)⁻¹ * (s.1 : G) *
                    ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G) =
                    ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G) := by
                  calc (t.1 : G)⁻¹ * (s.1 : G) *
                        ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G)
                      = (t.1 : G)⁻¹ * ((s.1 : G) *
                        ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G)) := by group
                    _ = (t.1 : G)⁻¹ * ((t.1 : G) *
                        ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G)) := by rw [h1]
                    _ = ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G) := by group
                rw [← h3]; group
              rw [h2]
              exact (S : Subgroup G).mul_mem (htS t.2) ((S : Subgroup G).inv_mem (htS s.2))
            have hmem : (t.1 : G)⁻¹ * (s.1 : G) ∈ O ⊓ (S : Subgroup G) := ⟨hO, hS⟩
            rwa [disjoint_iff.mp hdisjO, Subgroup.mem_bot] at hmem
          have hs : s.1 = t.1 := by
            refine Subtype.ext ?_
            have h2 := congrArg (fun z => (t.1 : G) * z) hone
            simpa [mul_assoc] using h2
          have ht_eq : ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G) =
              ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G) := by
            have h2 := h1
            rw [hs] at h2
            exact mul_left_cancel h2
          have h3 : (e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) =
              (e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) := Subtype.ext ht_eq
          have h4 : s.2 = t.2 := DihedralGroup.sr.inj (e.symm.injective h3)
          exact congrArg Sum.inl (Prod.ext hs h4)
        · -- a product equals `z`
          exfalso
          have h1 : (s.1 : G) * ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G) = z := by
            have h := congrArg Subtype.val heq
            rwa [hFinl s, hFinr t] at h
          have h2 : (s.1 : G) = z * (((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G))⁻¹ := by
            calc (s.1 : G) = (s.1 : G) *
                  ((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G) *
                  (((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G))⁻¹ := by group
              _ = z * (((e.symm (DihedralGroup.sr s.2) : ↥(S : Subgroup G)) : G))⁻¹ := by rw [h1]
          have h3 : (s.1 : G) ∈ (S : Subgroup G) :=
            h2 ▸ (S : Subgroup G).mul_mem hzS ((S : Subgroup G).inv_mem (htS s.2))
          have hmem : (s.1 : G) ∈ O ⊓ (S : Subgroup G) := ⟨hMle s.1.2, h3⟩
          rw [disjoint_iff.mp hdisjO, Subgroup.mem_bot] at hmem
          rw [hmem, one_mul] at h1
          exact htz s.2 h1
        · -- `z` equals a product
          exfalso
          have h1 : z = (t.1 : G) * ((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G) := by
            have h := congrArg Subtype.val heq
            rwa [hFinr s, hFinl t] at h
          have h2 : (t.1 : G) = z * (((e.symm (DihedralGroup.sr t.2) : ↥(S : Subgroup G)) : G))⁻¹ := by
            rw [h1]; group
          have h3 : (t.1 : G) ∈ (S : Subgroup G) :=
            h2 ▸ (S : Subgroup G).mul_mem hzS ((S : Subgroup G).inv_mem (htS t.2))
          have hmem : (t.1 : G) ∈ O ⊓ (S : Subgroup G) := ⟨hMle t.1.2, h3⟩
          rw [disjoint_iff.mp hdisjO, Subgroup.mem_bot] at hmem
          rw [hmem, one_mul] at h1
          exact htz t.2 h1.symm
        · exact congrArg Sum.inr (Subsingleton.elim s t)
      have hdom : Nat.card ((↥M × ZMod 4) ⊕ Fin 1) = 21 := by
        rw [Nat.card_sum, hMcard_prod, Nat.card_fin]
      have h21le : 21 ≤ Nat.card {w : G // orderOf w = 2} := by
        have hle := Nat.card_le_card_of_injective F hinj
        omega
      -- `|{involutions}| = |G : C_G(z)| = 21`
      have hInv_eq : Nat.card {w : G // orderOf w = 2} = C.index := by
        have hidx : (Subgroup.centralizer ({z} : Set G)).index =
            (MulAction.stabilizer (ConjAct G) z).index := by
          rw [Subgroup.centralizer_eq_comap_stabilizer z]
          exact Subgroup.index_comap_of_surjective (H := MulAction.stabilizer (ConjAct G) z)
            (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom) ConjAct.toConjAct.surjective
        have hstab : (MulAction.stabilizer (ConjAct G) z).index =
            (MulAction.orbit (ConjAct G) z).ncard :=
          MulAction.index_stabilizer (G := ConjAct G) (X := G) z
        have horb : Nat.card {w : G // IsConj w z} = (MulAction.orbit (ConjAct G) z).ncard := by
          rw [← Nat.card_coe_set_eq (MulAction.orbit (ConjAct G) z)]
          refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
          simp only [ConjAct.mem_orbit_conjAct]
        have hsame : Nat.card {w : G // orderOf w = 2} = Nat.card {w : G // IsConj w z} := by
          refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
          constructor
          · intro hw
            exact hInvConj w z hw hz2
          · intro hw
            obtain ⟨c, hc⟩ := isConj_iff.mp hw
            rw [← MulAut.conj_apply] at hc
            rw [← MulEquiv.orderOf_eq (MulAut.conj c) w, hc, hz2]
        calc Nat.card {w : G // orderOf w = 2} = Nat.card {w : G // IsConj w z} := hsame
          _ = (MulAction.orbit (ConjAct G) z).ncard := horb
          _ = (MulAction.stabilizer (ConjAct G) z).index := hstab.symm
          _ = (Subgroup.centralizer ({z} : Set G)).index := hidx.symm
          _ = C.index := by rw [← hCdef]
      have hCidx21 : C.index = 21 := by
        have hmul := Subgroup.card_mul_index C
        rw [hcard, hcardC8, h15] at hmul
        omega
      -- every involution of `G` lies in `C`: they are exactly the `21` elements above
      have hall : ∀ w : G, orderOf w = 2 → w ∈ C := by
        intro w hw
        haveI : Fintype {w : G // orderOf w = 2} := Fintype.ofFinite _
        haveI : Fintype ((↥M × ZMod 4) ⊕ Fin 1) := Fintype.ofFinite _
        have hcardF : Fintype.card ((↥M × ZMod 4) ⊕ Fin 1) =
            Fintype.card {w : G // orderOf w = 2} := by
          rw [← Nat.card_eq_fintype_card (α := (↥M × ZMod 4) ⊕ Fin 1),
            ← Nat.card_eq_fintype_card (α := {w : G // orderOf w = 2})]
          omega
        have hsurj : Function.Surjective F :=
          (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcardF)).mp hinj
        obtain ⟨p, hp⟩ := hsurj ⟨w, hw⟩
        have hpw : (F p).1 = w := by
          have h := congrArg Subtype.val hp
          simpa using h
        rcases p with s | s
        · rw [← hpw, hFinl s]
          exact C.mul_mem (hOle (hMle s.1.2)) (hSC (htS s.2))
        · rw [← hpw, hFinr s]
          exact hSC hzS
      have hcard_eq : Nat.card {w : G // orderOf w = 2} = Nat.card {w : ↥C // orderOf w = 2} := by
        refine le_antisymm ?_ ?_
        · refine Nat.card_le_card_of_injective
            (fun x : {w : G // orderOf w = 2} =>
              (⟨⟨(x.1 : G), hall x.1 x.2⟩, by rw [← Subgroup.orderOf_coe]; exact x.2⟩ :
                {w : ↥C // orderOf w = 2})) ?_
          intro x y hxy
          have h1 : (⟨(x.1 : G), hall x.1 x.2⟩ : ↥C) = ⟨(y.1 : G), hall y.1 y.2⟩ :=
            congrArg (fun v : {w : ↥C // orderOf w = 2} => (v.1 : ↥C)) hxy
          exact Subtype.ext (congrArg (fun v : ↥C => (v : G)) h1)
        · refine Nat.card_le_card_of_injective
            (fun x : {w : ↥C // orderOf w = 2} =>
              (⟨(x.1 : G), by rw [Subgroup.orderOf_coe]; exact x.2⟩ : {w : G // orderOf w = 2})) ?_
          intro x y hxy
          have h1 : (x.1 : G) = (y.1 : G) :=
            congrArg (fun v : {w : G // orderOf w = 2} => (v.1 : G)) hxy
          exact Subtype.ext (Subtype.ext h1)
      -- every involution commutes with `z`
      have hcomm_inv : ∀ w : G, orderOf w = 2 → w * z = z * w :=
        fun w hw => ((Subgroup.mem_centralizer_iff.mp (hall w hw)) z rfl).symm
      -- the subgroup generated by the involutions is normal and lies in `C_G(z)`
      have hNnorm : (Subgroup.closure {w : G | orderOf w = 2}).Normal :=
        normal_closure_of_conj_invariant (fun g x hx => by
          show orderOf (g * x * g⁻¹) = 2
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj g) x]
          exact hx)
      have hNle : Subgroup.closure {w : G | orderOf w = 2} ≤ C :=
        (Subgroup.closure_le C).mpr (fun x hx => hall x hx)
      have hNtop : Subgroup.closure {w : G | orderOf w = 2} = ⊤ := by
        haveI : (Subgroup.closure {w : G | orderOf w = 2}).Normal := hNnorm
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.closure {w : G | orderOf w = 2}) with hbot | htop
        · exfalso
          have hzm : z ∈ (⊥ : Subgroup G) :=
            hbot ▸ Subgroup.subset_closure (show z ∈ {w : G | orderOf w = 2} from hz2)
          exact hz1 (Subgroup.mem_bot.mp hzm)
        · exact htop
      -- hence `z` is central, and `⟨z⟩ ⊴ G` has order `2`, contradicting simplicity
      have hzZ : z ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ C := hNle (hNtop ▸ Subgroup.mem_top g)
        exact ((Subgroup.mem_centralizer_iff.mp hg) z rfl).symm
      haveI : (Subgroup.zpowers z).Normal := by
        constructor
        intro x hx g
        have hxZ : x ∈ Subgroup.center G := Subgroup.zpowers_le.mpr hzZ hx
        have hcomm' : g * x = x * g := (Subgroup.mem_center_iff.mp hxZ) g
        rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
        exact hx
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with h2 | h2
      · exact hz1 (Subgroup.zpowers_eq_bot.mp h2)
      · have hc : Nat.card (Subgroup.zpowers z) = 2520 := by
          rw [h2, Subgroup.card_top, hcard]
        rw [Nat.card_zpowers, hz2] at hc
        omega
  · -- `m = 21`
    exfalso
    have hO21 : Nat.card O = 21 := by rw [hcardO, h21]
    -- `O ⊴ C`, so `C ≤ N_G(O)`
    have hsub : O.subgroupOf C = Work.GW2.oddCore ↥C := by
      have hmap : O = (Work.GW2.oddCore ↥C).map C.subtype := by
        rw [hOdef, Work.GW2.oddCoreIn]
      rw [hmap, ← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    have hC_le_N : C ≤ Subgroup.normalizer (O : Set G) := by
      have hN : (O.subgroupOf C).Normal := by
        rw [hsub]; exact Work.GW2.oddCore_normal _
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hN
    -- an element of `O` of order `7`, and the subgroup `P` it generates
    obtain ⟨y, hy⟩ : ∃ y : ↥O, orderOf y = 7 := by
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have h7 : 7 ∣ Nat.card ↥O := by rw [hO21]; norm_num
      exact exists_prime_orderOf_dvd_card' 7 h7
    set P : Subgroup G := Subgroup.zpowers (y : G) with hPdef
    have hPle : P ≤ O := Subgroup.zpowers_le.mpr y.2
    have hPcard : Nat.card P = 7 := by
      rw [hPdef, Nat.card_zpowers, Subgroup.orderOf_coe, hy]
    -- the subgroups of order `7` of `C` are all equal to `P`
    have hC_unique : ∀ Q : Subgroup G, Q ≤ C → Nat.card Q = 7 → Q = P := by
      intro Q hQ hQcard
      have hQO : Q ≤ O := by
        intro q hq
        have hqC : q ∈ C := hQ hq
        by_cases hq1 : q = 1
        · rw [hq1]; exact O.one_mem
        · refine horder7_mem_O q hqC ?_
          have hdvd : orderOf q ∣ 7 := by
            rw [← hQcard]
            rw [← Nat.card_zpowers]
            exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hq)
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hq1
          · exact h
      exact card_seven_unique_of_le_of_card_twentyone hO21 hQO hPle hQcard hPcard
    -- `P ⊴ C`
    have hPnormC : C ≤ Subgroup.normalizer (P : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hQle : P.map (MulAut.conj c).toMonoidHom ≤ O := by
        rintro z hz
        rw [Subgroup.mem_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        have hiff := Subgroup.mem_normalizer_iff.mp (hC_le_N hc)
        have hcw : (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hcw]
        exact (hiff w).mp (hPle hw)
      have hQcard : Nat.card (P.map (MulAut.conj c).toMonoidHom) = 7 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hPcard]
      exact (card_seven_unique_of_le_of_card_twentyone hO21 hPle hQle hPcard hQcard).symm
    -- `168 · n₇ ∣ 2520`, where `n₇ = |G : N_G(P)|`
    have hdvd168 : 168 ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
      have h := Subgroup.card_dvd_of_le hPnormC
      rw [hcardC8, h21] at h
      norm_num at h
      exact h
    have hn7dvd : (Subgroup.normalizer (P : Set G)).index ∣ 15 := by
      obtain ⟨t, ht⟩ := hdvd168
      have hmul := Subgroup.card_mul_index (Subgroup.normalizer (P : Set G))
      rw [hcard, ht] at hmul
      have h168 : 168 * (t * (Subgroup.normalizer (P : Set G)).index) = 168 * 15 := by
        rw [← mul_assoc, hmul]
      have hcancel := Nat.mul_left_cancel (show (0 : ℕ) < 168 by norm_num) h168
      exact ⟨t, by rw [mul_comm]; exact hcancel.symm⟩
    have hmod7 : (Subgroup.normalizer (P : Set G)).index % 7 = 1 := by
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hcard' : Nat.card P = 7 ^ (Nat.card G).factorization 7 := by
        rw [hcard, factorization_2520_seven, hPcard]
        norm_num
      have hcoe : (↑(Sylow.ofCard (p := 7) P hcard') : Subgroup G) = P :=
        Sylow.coe_ofCard P hcard'
      haveI : Finite (Sylow 7 G) :=
        Sylow.finite_of_finiteIndex (Sylow.ofCard (p := 7) P hcard')
      have hidx : Nat.card (Sylow 7 G) = (Subgroup.normalizer (P : Set G)).index := by
        rw [← hcoe]
        exact Sylow.card_eq_index_normalizer _
      have h := card_sylow_modEq_one 7 G
      rw [hidx] at h
      simpa [Nat.ModEq] using h
    have hcases : (Subgroup.normalizer (P : Set G)).index ∈ ({1, 15} : Finset ℕ) := by
      have hmem : (Subgroup.normalizer (P : Set G)).index ∈ (15 : ℕ).divisors :=
        Nat.mem_divisors.mpr ⟨hn7dvd, by norm_num⟩
      have hlist : (15 : ℕ).divisors.filter (fun k => k % 7 = 1) = {1, 15} := by decide
      have hmem' : (Subgroup.normalizer (P : Set G)).index ∈
          (15 : ℕ).divisors.filter (fun k => k % 7 = 1) :=
        Finset.mem_filter.mpr ⟨hmem, hmod7⟩
      rwa [hlist] at hmem'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
    rcases hcases with h1 | h15
    · -- `n₇ = 1`, so `P ⊴ G`
      have htop : Subgroup.normalizer (P : Set G) = ⊤ := (Subgroup.index_eq_one).mp h1
      have hPnormal : P.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hbot | htop'
      · rw [hbot, Subgroup.card_bot] at hPcard
        omega
      · rw [htop', Subgroup.card_top, hcard] at hPcard
        omega
    · -- `n₇ = 15`: `C = N_G(P)`, and `C_G(P)` has a unique involution
      have hNeq : Nat.card (Subgroup.normalizer (P : Set G)) = 168 := by
        have hmul := Subgroup.card_mul_index (Subgroup.normalizer (P : Set G))
        rw [hcard, h15] at hmul
        omega
      have hcardC168 : Nat.card C = 168 := by rw [hcardC8, h21]
      have hCeq : Subgroup.normalizer (P : Set G) = C :=
        (Subgroup.eq_of_le_of_card_ge hPnormC (by rw [hcardC168, hNeq])).symm
      -- every involution of `C_G(P)` equals `z`
      have huniq_inv : ∀ u : G, orderOf u = 2 → u ∈ Subgroup.centralizer (P : Set G) → u = z := by
        intro u hu2 huC
        obtain ⟨g, hg⟩ := isConj_iff.mp (hInvConj u z hu2 hz2)
        have hu_eq : u = g⁻¹ * z * g := by
          have h := congrArg (fun w => g⁻¹ * w * g) hg
          simpa [mul_assoc] using h
        have hPle2 : P.map (MulAut.conj g).toMonoidHom ≤ C := by
          rintro w hw
          rw [Subgroup.mem_map] at hw
          obtain ⟨q, hq, rfl⟩ := hw
          have hcq : (MulAut.conj g).toMonoidHom q = g * q * g⁻¹ := by
            simp [MulAut.conj_apply]
          rw [hcq, Subgroup.mem_centralizer_iff]
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          have hcomm : q * u = u * q := Subgroup.mem_centralizer_iff.mp huC q hq
          have hconj := congrArg (fun w => g * w * g⁻¹) hcomm
          rw [hu_eq] at hconj
          simpa [mul_assoc] using hconj.symm
        have hcard7 : Nat.card ↥(P.map (MulAut.conj g).toMonoidHom) = 7 := by
          rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard]
        have hPeq : P.map (MulAut.conj g).toMonoidHom = P := hC_unique _ hPle2 hcard7
        -- `P^g = P` means `g ∈ N_G(P) = C`, hence `u = z^g = z`
        have hgC : g ∈ C := hCeq ▸ Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPeq
        rw [hu_eq]
        have hcomm := (Subgroup.mem_centralizer_iff.mp (C.inv_mem hgC)) z rfl
        rw [← hcomm]
        group
      -- the four involutions `e.symm (sr i)` of `S`
      obtain ⟨e⟩ := hSdih
      have hzcmem : (⟨z, hzS⟩ : ↥(S : Subgroup G)) ∈
          Subgroup.center ↥(S : Subgroup G) := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact Subtype.ext (hzcen x.1 x.2)
      have hzsr : ∀ i : ZMod 4, DihedralGroup.sr i ≠ e ⟨z, hzS⟩ := by
        intro i hi
        have hcent : e ⟨z, hzS⟩ ∈ Subgroup.center (DihedralGroup 4) := by
          rw [Subgroup.mem_center_iff]
          intro x
          have h := Subgroup.mem_center_iff.mp hzcmem (e.symm x)
          have h1 : e (⟨z, hzS⟩ * e.symm x) = e (e.symm x * ⟨z, hzS⟩) := by rw [h]
          simpa using h1.symm
        rw [← hi] at hcent
        -- `sr i` is never central
        rw [Subgroup.mem_center_iff] at hcent
        have hcomm' := (hcent (DihedralGroup.r 1)).symm
        rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at hcomm'
        have h1 : (1 : ZMod 4) = -1 := by
          have := congrArg (fun t : ZMod 4 => t - i) (DihedralGroup.sr.inj hcomm')
          simpa using this
        have h2 : (1 + 1 : ZMod 4) = 0 := by
          have h3 := congrArg (fun t : ZMod 4 => t + 1) h1
          rw [neg_add_cancel] at h3
          exact h3
        exact absurd h2 (by decide)
      -- the four elements `e.symm (sr i)` of `S` are involutions different from `z`
      have htord : ∀ i : ZMod 4,
          orderOf ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) = 2 := by
        intro i
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm (DihedralGroup.sr i),
          DihedralGroup.orderOf_sr]
      have ht2 : ∀ i : ZMod 4, ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
          ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) = 1 := by
        intro i
        have h := pow_orderOf_eq_one ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)
        rw [htord i, pow_two] at h
        exact h
      have htS : ∀ i : ZMod 4,
          ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ∈ (S : Subgroup G) :=
        fun i => (e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)).2
      have htz : ∀ i : ZMod 4, ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ≠ z := by
        intro i h
        have h3 : e ⟨z, hzS⟩ = DihedralGroup.sr i := by
          have h4 : (e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) = ⟨z, hzS⟩ := Subtype.ext h
          rw [← h4, MulEquiv.apply_symm_apply]
        exact hzsr i h3.symm
      -- each of them inverts the generator `y` of `P`
      have htinv : ∀ i : ZMod 4, ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
          (y : G) * (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ = (y : G)⁻¹ := by
        intro i
        have hN : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ ∈
            Subgroup.zpowers (y : G) := by
          have hmem : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ∈
              Subgroup.normalizer (P : Set G) := hPnormC (hSC (htS i))
          have h5 := (Subgroup.mem_normalizer_iff.mp hmem (y : G)).mp
            (Subgroup.mem_zpowers (y : G))
          simpa only [hPdef] using h5
        have hne : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ ≠ (y : G) := by
          intro hconj
          have hcen : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) ∈
              Subgroup.centralizer (P : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro w hw
            have hwz : w ∈ Subgroup.zpowers (y : G) := hPdef ▸ hw
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
            rw [← hn]
            have h6 : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) ^ n *
                (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ = (y : G) ^ n := by
              have h7 := map_zpow
                (MulAut.conj ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) (y : G) n
              simpa [MulAut.conj_apply, hconj] using h7
            calc (y : G) ^ n * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)
                = (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) ^ n *
                  (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹) *
                  ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) := by rw [h6]
              _ = ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) ^ n := by group
          exact htz i (huniq_inv _ (htord i) hcen)
        exact involution_conj_eq_inv_of_prime Nat.prime_seven
          (by rw [Subgroup.orderOf_coe]; exact hy) (ht2 i) hN hne
      -- hence the products `w · t` with `w ∈ P` are involutions
      have hwt : ∀ (i : ZMod 4) (w : G), w ∈ P →
          ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * w *
          (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ = w⁻¹ := by
        intro i w hw
        have hwz : w ∈ Subgroup.zpowers (y : G) := hPdef ▸ hw
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
        rw [← hn]
        have h5 : ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) ^ n *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹ =
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * (y : G) *
            (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹) ^ n := by
          have h6 := map_zpow
            (MulAut.conj ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) (y : G) n
          simpa [MulAut.conj_apply] using h6
        rw [h5, htinv i, inv_zpow]
      have hwt2 : ∀ (i : ZMod 4) (w : G), w ∈ P →
          (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) *
          (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) = 1 := by
        intro i w hw
        calc (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) *
              (w * ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))
            = w * (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) * w *
              (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G))⁻¹) *
              (((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G) *
              ((e.symm (DihedralGroup.sr i) : ↥(S : Subgroup G)) : G)) := by group
          _ = w * w⁻¹ * 1 := by rw [hwt i w hw, ht2 i]
          _ = 1 := by rw [mul_inv_cancel, one_mul]
      have hinj : Function.Injective (fun p : ↥P × ZMod 4 =>
          (⟨(p.1 : G) * ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G), by
            refine orderOf_eq_two_of_mul_self (hwt2 p.2 p.1 p.1.2) ?_
            intro h1
            have h2 : (p.1 : G) =
                (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ := by
              calc (p.1 : G) = (p.1 : G) *
                    ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G) *
                    (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ := by group
                _ = 1 * (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ := by rw [h1]
                _ = (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ := by rw [one_mul]
            have htt : (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ =
                ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G) := by
              calc (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹
                  = (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ *
                    (((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G) *
                    ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G)) := by
                    rw [ht2 p.2, mul_one]
                _ = ((((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G))⁻¹ *
                    ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G)) *
                    ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G) := by group
                _ = ((e.symm (DihedralGroup.sr p.2) : ↥(S : Subgroup G)) : G) := by
                    rw [inv_mul_cancel, one_mul]
            rw [htt] at h2
            have h3 : (p.1 : G) ∈ (S : Subgroup G) := h2 ▸ (htS p.2)
            have hmem : (p.1 : G) ∈ O ⊓ (S : Subgroup G) := ⟨hPle p.1.2, h3⟩
            rw [disjoint_iff.mp hdisjO, Subgroup.mem_bot] at hmem
            rw [hmem, one_mul] at h1
            exact absurd (htord p.2) (by rw [h1, orderOf_one]; norm_num)⟩ :
          {w : G // orderOf w = 2})) := by
        rintro ⟨p1, p2⟩ ⟨q1, q2⟩ heq
        have h1 : (p1 : G) * ((e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) : G) =
            (q1 : G) * ((e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) : G) :=
          congrArg Subtype.val heq
        have hone : (q1 : G)⁻¹ * (p1 : G) = 1 := by
          have hO : (q1 : G)⁻¹ * (p1 : G) ∈ O :=
            O.mul_mem (O.inv_mem (hPle q1.2)) (hPle p1.2)
          have hS : (q1 : G)⁻¹ * (p1 : G) ∈ (S : Subgroup G) := by
            have h2 : (q1 : G)⁻¹ * (p1 : G) =
                ((e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) : G) *
                (((e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) : G))⁻¹ := by
              have h3 : (q1 : G)⁻¹ * (p1 : G) *
                  ((e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) : G) =
                  ((e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) : G) := by
                calc (q1 : G)⁻¹ * (p1 : G) *
                      ((e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) : G)
                    = (q1 : G)⁻¹ * ((p1 : G) *
                      ((e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) : G)) := by group
                  _ = (q1 : G)⁻¹ * ((q1 : G) *
                      ((e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) : G)) := by rw [h1]
                  _ = ((e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) : G) := by group
              rw [← h3]; group
            rw [h2]
            exact (S : Subgroup G).mul_mem (htS q2) ((S : Subgroup G).inv_mem (htS p2))
          have hmem : (q1 : G)⁻¹ * (p1 : G) ∈ O ⊓ (S : Subgroup G) := ⟨hO, hS⟩
          rwa [disjoint_iff.mp hdisjO, Subgroup.mem_bot] at hmem
        have hq : p1 = q1 := by
          refine Subtype.ext ?_
          have h2 := congrArg (fun z => (q1 : G) * z) hone
          simpa [mul_assoc] using h2
        have ht_eq : ((e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) : G) =
            ((e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) : G) := by
          have h2 := h1
          rw [hq] at h2
          exact mul_left_cancel h2
        have h3 : (e.symm (DihedralGroup.sr p2) : ↥(S : Subgroup G)) =
            (e.symm (DihedralGroup.sr q2) : ↥(S : Subgroup G)) := Subtype.ext ht_eq
        have h4 : p2 = q2 := DihedralGroup.sr.inj (e.symm.injective h3)
        exact Prod.ext hq h4
      have h28le : 28 ≤ Nat.card {w : G // orderOf w = 2} := by
        have hle := Nat.card_le_card_of_injective _ hinj
        have hdom : Nat.card (↥P × ZMod 4) = 28 := by
          rw [Nat.card_prod, hPcard]
          norm_num [Nat.card_eq_fintype_card, ZMod.card]
        omega
      -- and `|{involutions}| = |G : C_G(z)| = 15`
      have hInv15 : Nat.card {w : G // orderOf w = 2} ≤ 15 := by
        have hidx : (Subgroup.centralizer ({z} : Set G)).index =
            (MulAction.stabilizer (ConjAct G) z).index := by
          rw [Subgroup.centralizer_eq_comap_stabilizer z]
          exact Subgroup.index_comap_of_surjective (H := MulAction.stabilizer (ConjAct G) z)
            (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom) ConjAct.toConjAct.surjective
        have hstab : (MulAction.stabilizer (ConjAct G) z).index =
            (MulAction.orbit (ConjAct G) z).ncard :=
          MulAction.index_stabilizer (G := ConjAct G) (X := G) z
        have horb : Nat.card {w : G // IsConj w z} = (MulAction.orbit (ConjAct G) z).ncard := by
          rw [← Nat.card_coe_set_eq (MulAction.orbit (ConjAct G) z)]
          refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
          simp only [ConjAct.mem_orbit_conjAct]
        have hsame : Nat.card {w : G // orderOf w = 2} = Nat.card {w : G // IsConj w z} := by
          refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
          constructor
          · intro hw
            exact hInvConj w z hw hz2
          · intro hw
            obtain ⟨c, hc⟩ := isConj_iff.mp hw
            rw [← MulAut.conj_apply] at hc
            rw [← MulEquiv.orderOf_eq (MulAut.conj c) w, hc, hz2]
        have hCidx : (Subgroup.centralizer ({z} : Set G)).index = 15 := by
          rw [← hCdef]
          have hmul := Subgroup.card_mul_index C
          rw [hcard, hcardC8, h21] at hmul
          omega
        have heq : Nat.card {w : G // orderOf w = 2} = 15 := by
          calc Nat.card {w : G // orderOf w = 2} = Nat.card {w : G // IsConj w z} := hsame
            _ = (MulAction.orbit (ConjAct G) z).ncard := horb
            _ = (MulAction.stabilizer (ConjAct G) z).index := hstab.symm
            _ = (Subgroup.centralizer ({z} : Set G)).index := hidx.symm
            _ = 15 := hCidx
        exact le_of_eq heq
      omega
  · -- `m = 45`: index 7 gives `G ≃* A₇`, where all involution centralizers have order `24`
    exfalso
    have hcard360 : Nat.card C = 360 := by rw [hcardC8, h45]
    have hidx7 : C.index = 7 := by
      have h := hCindex
      rw [hcard360] at h
      omega
    obtain ⟨e⟩ := Work.A7REC.mulEquiv_A7_of_index_seven G hcard C hidx7
    have h24 : Nat.card
        (Subgroup.centralizer ({(e z)} : Set (alternatingGroup (Fin 7)))) = 24 :=
      Work.AUTA7.A7.CentralizerInvolution (by
          rw [← map_mul, ← map_one e]
          congr 1
          rw [← pow_two, ← hz2, pow_orderOf_eq_one]) (by
          intro h
          have hz1' : z = 1 := e.injective (by rw [map_one]; exact h)
          rw [hz1', orderOf_one] at hz2
          omega)
    have h24' := card_centralizer_mulEquiv e z
    rw [h24, ← hCdef] at h24'
    omega
  · -- `m = 63`: `|C| = 504`, so `[G : C] = 5`
    exfalso
    have hcard504 : Nat.card C = 504 := by rw [hcardC8, h63]
    have hCne : C ≠ ⊤ := by
      intro htop
      have h : Nat.card C = 2520 := by rw [htop, Subgroup.card_top]; exact hcard
      omega
    have : C.index = 5 := by
      have h := hCindex
      rw [hcard504] at h
      omega
    have := Work.A7REC.Char.no_small_index hcard C hCne
    omega
  · -- `m = 105`: `|C| = 840`, so `[G : C] = 3`
    exfalso
    have hcard840 : Nat.card C = 840 := by rw [hcardC8, h105]
    have hCne : C ≠ ⊤ := by
      intro htop
      have h : Nat.card C = 2520 := by rw [htop, Subgroup.card_top]; exact hcard
      omega
    have : C.index = 3 := by
      have h := hCindex
      rw [hcard840] at h
      omega
    have := Work.A7REC.Char.no_small_index hcard C hCne
    omega
  · -- `m = 315`: `|C| = 2520`, so `C = ⊤` and `z` is central in `G`
    exfalso
    have hcard2520 : Nat.card C = 2520 := by rw [hcardC8, h315]
    have hCtop : C = ⊤ := by
      have h := hCindex
      rw [hcard2520] at h
      exact (Subgroup.index_eq_one).mp (by omega)
    have hzC : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := by rw [hCtop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg z rfl).symm
    have hcenter_ne_bot : Subgroup.center G ≠ ⊥ := by
      intro hbot
      have hmem : z ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hzC
      exact hz1 (Subgroup.mem_bot.mp hmem)
    haveI : (Subgroup.center G).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact hcenter_ne_bot h
    · have hcomm : ∀ a b : G, a * b = b * a := by
        intro a b
        have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm
      haveI hzp : (Subgroup.zpowers z).Normal := by
        constructor
        intro x hx g
        have hconj : g * x * g⁻¹ = x := by
          rw [hcomm g x, mul_assoc, mul_inv_cancel, mul_one]
        rwa [hconj]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with h2 | h2
      · exact hz1 (Subgroup.zpowers_eq_bot.mp h2)
      · have hc : Nat.card (Subgroup.zpowers z) = 2520 := by
          rw [h2, Subgroup.card_top, hcard]
        rw [Nat.card_zpowers, hz2] at hc
        omega

end Work.A7REC.Char
