import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.ncard_range_conj_mul_card_centralizer
import Submission.Work.CORE4.conj_mul_eq_of_odd_order
import Submission.Work.CORE4.exists_conj_mul_of_fourGroup_relIndex_two

namespace Work.CORE4

open Subgroup

/-- A subgroup of order four in which every element squares to `1` is abelian
(a Klein four group). -/
private lemma fourGroup_comm {G : Type*} [Group G] (V : Subgroup G)
    (hV4 : Work.GW2.IsFourGroup V) : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
  intro a ha b hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hV4.2 a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hV4.2 b hb)
  have h2 : (a * b) * (a * b) = 1 := by
    rw [← pow_two]; exact hV4.2 (a * b) (V.mul_mem ha hb)
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left h2
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

/-- If `V` is a normal Klein four subgroup of `N` of odd index in `N`, then every
`2`-subgroup of `N` is contained in `V`; in particular every element of `N` of `2`-power
order lies in `V`. -/
private lemma mem_of_isPGroup_zpowers {G : Type*} [Group G] [Finite G] {N V : Subgroup G}
    (hVN : V ≤ N) (hVnorm : N ≤ Subgroup.normalizer (V : Set G))
    (hV4 : Work.GW2.IsFourGroup V) (hodd : Odd (V.relIndex N)) :
    ∀ x ∈ N, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ V := by
  have hVcard : Nat.card V = 4 := hV4.1
  have hV2 : IsPGroup 2 ↥V :=
    IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hNcard : Nat.card N = 4 * V.relIndex N := by
    have h := Subgroup.relIndex_mul_card V N
    rw [inf_eq_left.mpr hVN, hVcard] at h
    rw [← h, mul_comm]
  intro x hxN hx2
  obtain ⟨j, hj⟩ := IsPGroup.exists_card_eq
    (IsPGroup.to_sup_of_normal_left' hV2 hx2
      (le_trans (Subgroup.zpowers_le.mpr hxN) hVnorm))
  have hle : V ≤ V ⊔ Subgroup.zpowers x := le_sup_left
  have hdvd : Nat.card ↥(V ⊔ Subgroup.zpowers x) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le (sup_le hVN (Subgroup.zpowers_le.mpr hxN))
  have hcop : Nat.Coprime (2 ^ j) (V.relIndex N) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  have hdvd4 : 2 ^ j ∣ 4 := by
    rw [hNcard, hj] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hle4 : 2 ^ j ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  have hge4 : 4 ≤ 2 ^ j := by
    have h := Subgroup.card_le_of_le hle
    rw [hVcard] at h
    rwa [hj] at h
  have hQcard : 2 ^ j = 4 := le_antisymm hle4 hge4
  have hQV : V ⊔ Subgroup.zpowers x = V :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hj, hQcard, hVcard])).symm
  rw [← hQV]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

/-- **The structure of an involutive automorphism of a Klein four group.**  Let `V` be a
Klein four group (order `4`, exponent `2`), let `y` be an involution normalising `V`, let
`a ∈ V` be a non-trivial fixed point of `v ↦ y * v * y⁻¹` and let `b ∈ V` be moved by it.
Then the product of `b` with its image is `a`. -/
private lemma fourGroup_prod_fixed {G : Type*} [Group G] [Finite G] (V : Subgroup G) (y : G)
    (hV4 : Work.GW2.IsFourGroup V) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hy2 : y * y = 1) :
    ∀ a ∈ V, a ≠ 1 → y * a * y⁻¹ = a →
      ∀ b ∈ V, y * b * y⁻¹ ≠ b → b * (y * b * y⁻¹) = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVcard : Nat.card V = 4 := hV4.1
  have hVinvol : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hV4.2 v hv
  have hVinv : ∀ v ∈ V, v⁻¹ = v := fun v hv => inv_eq_of_mul_eq_one_left (hVinvol v hv)
  have hVcomm : ∀ p ∈ V, ∀ q ∈ V, p * q = q * p := fourGroup_comm V hV4
  have hY : ∀ x ∈ V, y * x * y⁻¹ ∈ V :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hyV x).mp hx
  have hVsig : ∀ x : G, y * (y * x * y⁻¹) * y⁻¹ = x := by
    intro x
    have h1 : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hy2, inv_one]
    calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y⁻¹ * y⁻¹) := by group
      _ = 1 * x * 1 := by rw [hy2, h1]
      _ = x := by rw [one_mul, mul_one]
  intro a haV ha1 hafix b hbV hbmove
  have haord : orderOf a = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hVinvol a haV
    · exact ha1
  have ha2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    exact hVinvol a haV
  have hδne1 : b * (y * b * y⁻¹) ≠ 1 := by
    intro h
    apply hbmove
    have h2 : y * b * y⁻¹ = b⁻¹ := eq_inv_of_mul_eq_one_right h
    rwa [hVinv b hbV] at h2
  have haF : a ∈ V ⊓ Subgroup.centralizer ({y} : Set G) :=
    ⟨haV, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hafix).symm⟩
  have hbF : b * (y * b * y⁻¹) ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by
    refine ⟨V.mul_mem hbV (hY b hbV), ?_⟩
    have hd : y * (b * (y * b * y⁻¹)) * y⁻¹ = b * (y * b * y⁻¹) := by
      calc y * (b * (y * b * y⁻¹)) * y⁻¹
          = (y * b * y⁻¹) * (y * (y * b * y⁻¹) * y⁻¹) := by group
        _ = (y * b * y⁻¹) * b := by rw [hVsig b]
        _ = b * (y * b * y⁻¹) := hVcomm (y * b * y⁻¹) (hY b hbV) b hbV
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hd).symm
  have hle : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 4 := by
    have h := Subgroup.card_le_of_le (inf_le_left : V ⊓ Subgroup.centralizer ({y} : Set G) ≤ V)
    rwa [hVcard] at h
  have hdvd2 : 2 ∣ Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) := by
    have hz : Subgroup.zpowers (b * (y * b * y⁻¹)) ≤
        V ⊓ Subgroup.centralizer ({y} : Set G) := Subgroup.zpowers_le.mpr hbF
    have h := Subgroup.card_dvd_of_le hz
    rw [Nat.card_zpowers] at h
    have hord : orderOf (b * (y * b * y⁻¹)) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two]; exact hVinvol (b * (y * b * y⁻¹)) (V.mul_mem hbV (hY b hbV))
      · exact hδne1
    rwa [hord] at h
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) := Nat.card_pos
  have hne4 : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ≠ 4 := by
    intro h4
    have hFV : V ⊓ Subgroup.centralizer ({y} : Set G) = V :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : _ ≤ V) (by rw [h4, hVcard])
    have hbF2 : b ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by rw [hFV]; exact hbV
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hbF2.2
    exact hbmove (mul_inv_eq_iff_eq_mul.mpr hcomm.symm)
  have hF2 : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) = 2 := by
    obtain ⟨c, hc⟩ := hdvd2
    omega
  have hzFa : Subgroup.zpowers a = V ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haF)
    rw [Nat.card_zpowers, haord, hF2]
  have hmem : b * (y * b * y⁻¹) ∈ Subgroup.zpowers a := by
    rw [hzFa]; exact hbF
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  rcases zpow_eq_one_or_self_of_sq_eq_one ha2 k with h1 | h1
  · exact absurd (by rw [← hk, h1] : b * (y * b * y⁻¹) = 1) hδne1
  · rw [← hk, h1]

theorem InvSetCountNormalFourB {G : Type} [Group G] [Finite G] (N V : Subgroup G) (y : G)
    (hVN : V ≤ N) (hVnorm : N ≤ Subgroup.normalizer (V : Set G))
    (hV4 : Work.GW2.IsFourGroup V) (hodd : Odd (V.relIndex N))
    (hyN : y ∈ Subgroup.normalizer (N : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hy2 : y * y = 1) (hyN' : y ∉ N)
    (hact : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    (Work.GW2.invSet N y).ncard *
      Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) = Nat.card ↥N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVcard : Nat.card V = 4 := hV4.1
  have hVinvol : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hV4.2 v hv
  have hVinv : ∀ v ∈ V, v⁻¹ = v := fun v hv => inv_eq_of_mul_eq_one_left (hVinvol v hv)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hYV : ∀ x ∈ V, y * x * y⁻¹ ∈ V :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hyV x).mp hx
  have hYN : ∀ x ∈ N, y * x * y⁻¹ ∈ N :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hyN x).mp hx
  have h2subV := mem_of_isPGroup_zpowers hVN hVnorm hV4 hodd
  -- ## The fusion statement
  have fusion : ∀ n ∈ N, y * n * y⁻¹ = n⁻¹ → ∃ g ∈ N, g * y * g⁻¹ = n * y := by
    intro n hn hninv
    have key_id : ∀ g : G, g * y * g⁻¹ = g * (y * g⁻¹ * y) * y := by
      intro g
      have h : g * (y * g⁻¹ * y) * y = g * y * g⁻¹ * (y * y) := by group
      rw [h, hy2, mul_one]
    have hyconj : ∀ k : ℕ, y * (n ^ k)⁻¹ * y⁻¹ = n ^ k := by
      intro k
      have h6 : y * (n ^ k)⁻¹ * y⁻¹ = (y * n ^ k * y⁻¹)⁻¹ := by group
      rw [h6, Work.CORE4.conj_pow_eq_inv_pow y n hninv k, inv_inv]
    have hyconj' : ∀ k : ℕ, y * (n ^ k)⁻¹ * y = n ^ k := by
      intro k
      have h := hyconj k
      rwa [hyinv] at h
    have hnpj : ∀ k : ℕ, n ^ k * y * (n ^ k)⁻¹ = n ^ (2 * k) * y := by
      intro k
      have hyz : y * (n ^ k)⁻¹ = n ^ k * y := by
        calc y * (n ^ k)⁻¹ = y * (n ^ k)⁻¹ * (y * y) := by rw [hy2, mul_one]
          _ = (y * (n ^ k)⁻¹ * y) * y := by group
          _ = n ^ k * y := by rw [hyconj' k]
      calc n ^ k * y * (n ^ k)⁻¹ = n ^ k * (y * (n ^ k)⁻¹) := by group
        _ = n ^ k * (n ^ k * y) := by rw [hyz]
        _ = n ^ (2 * k) * y := by rw [← mul_assoc, ← pow_add, two_mul]
    by_cases hoddn : Odd (orderOf n)
    · obtain ⟨t, ht⟩ := hoddn
      set k := (orderOf n + 1) / 2 with hkdef
      have hk2 : 2 * k = orderOf n + 1 := by
        rw [hkdef]; omega
      have hnp : n ^ (2 * k) = n := by
        rw [hk2, pow_succ, pow_orderOf_eq_one, one_mul]
      refine ⟨n ^ k, Subgroup.pow_mem N hn k, ?_⟩
      calc n ^ k * y * (n ^ k)⁻¹ = n ^ (2 * k) * y := hnpj k
        _ = n * y := by rw [hnp]
    · have heven : Even (orderOf n) := Nat.not_odd_iff_even.mp hoddn
      obtain ⟨m, hm⟩ := even_iff_two_dvd.mp heven
      have hm_pos : 0 < m := by have h := orderOf_pos n; omega
      have hmodd : Odd m := by
        rw [← Nat.not_even_iff_odd]
        intro hmev
        obtain ⟨s, hs⟩ := even_iff_two_dvd.mp hmev
        obtain ⟨s', hs'⟩ := (show 4 ∣ orderOf n from ⟨s, by rw [hm, hs]; ring⟩)
        have hs'_pos : 0 < s' := by
          rcases Nat.eq_zero_or_pos s' with h | h
          · rw [h, mul_zero] at hs'
            exact absurd hs' (orderOf_pos n).ne'
          · exact h
        have hu : orderOf (n ^ s') = 4 := by
          rw [orderOf_eq_iff (by norm_num : 0 < 4)]
          refine ⟨?_, ?_⟩
          · rw [← pow_mul, show s' * 4 = orderOf n by rw [hs']; ring, pow_orderOf_eq_one]
          · intro mm hmm hmm4 hcon
            have hd : orderOf n ∣ s' * mm := by
              rw [orderOf_dvd_iff_pow_eq_one, pow_mul]; exact hcon
            have hle : orderOf n ≤ s' * mm :=
              Nat.le_of_dvd (Nat.mul_pos hs'_pos hmm4) hd
            have hlt : s' * mm < orderOf n := by
              rw [hs']
              calc s' * mm < s' * 4 := Nat.mul_lt_mul_of_pos_left hmm hs'_pos
                _ = 4 * s' := by rw [mul_comm]
            exact absurd hle (not_le.mpr hlt)
        have hmem : n ^ s' ∈ V :=
          h2subV (n ^ s') (Subgroup.pow_mem N hn s')
            (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu]; norm_num))
        have hdvd : orderOf (n ^ s') ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hVinvol (n ^ s') hmem
        rw [hu] at hdvd
        norm_num at hdvd
      obtain ⟨β, hβV, hβnc⟩ := hact
      have hα2 : (n ^ m) * (n ^ m) = 1 := by
        rw [← pow_two, ← pow_mul, show m * 2 = orderOf n by omega, pow_orderOf_eq_one]
      have hαinv : (n ^ m)⁻¹ = n ^ m := inv_eq_of_mul_eq_one_left hα2
      have hαne1 : n ^ m ≠ 1 := by
        intro h
        have hdd : orderOf n ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
        have hle := Nat.le_of_dvd hm_pos hdd
        omega
      have hαord : orderOf (n ^ m) = 2 := by
        apply orderOf_eq_prime
        · rw [pow_two]; exact hα2
        · exact hαne1
      have hαV : n ^ m ∈ V :=
        h2subV (n ^ m) (Subgroup.pow_mem N hn m)
          (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hαord]; norm_num))
      have hsiga : y * (n ^ m) * y⁻¹ = n ^ m := by
        have hconj : (MulAut.conj y) n = n⁻¹ := by rw [MulAut.conj_apply]; exact hninv
        have h1 : y * n ^ m * y⁻¹ = (n ^ m)⁻¹ := by
          rw [← MulAut.conj_apply, map_pow, hconj, ← inv_pow]
        rw [h1, hαinv]
      have hβδ : β * (y * β * y⁻¹) = n ^ m :=
        fourGroup_prod_fixed V y hV4 hyV hy2 (n ^ m) hαV hαne1 hsiga β hβV hβnc
      set j := (m + 1) / 2 with hjdef
      have hj2 : 2 * j = m + 1 := by
        obtain ⟨t, ht⟩ := hmodd
        rw [hjdef]; omega
      have hβδ' : β * (y * β * y) = n ^ m := by
        have h := hβδ
        rwa [hyinv] at h
      have hstep1 : β * y * β⁻¹ = n ^ m * y := by
        rw [key_id β, hVinv β hβV, hβδ']
      have hstep2 : y * (n ^ j)⁻¹ = n ^ j * y := by
        calc y * (n ^ j)⁻¹ = y * (n ^ j)⁻¹ * (y * y) := by rw [hy2, mul_one]
          _ = (y * (n ^ j)⁻¹ * y) * y := by group
          _ = n ^ j * y := by rw [hyconj' j]
      have hmain : (n ^ j * β) * y * (n ^ j * β)⁻¹ = n ^ (m + 2 * j) * y := by
        have h1 : (n ^ j * β) * y * (n ^ j * β)⁻¹
            = n ^ j * (β * y * β⁻¹) * (n ^ j)⁻¹ := by group
        rw [h1, hstep1]
        have h2 : n ^ j * (n ^ m * y) * (n ^ j)⁻¹
            = n ^ (j + m) * (y * (n ^ j)⁻¹) := by group
        rw [h2, hstep2, ← mul_assoc, ← pow_add,
          show (j + m) + j = m + 2 * j by ring]
      have hfin : n ^ (m + 2 * j) = n := by
        have hexp : m + 2 * j = 2 * m + 1 := by omega
        rw [hexp, pow_succ, ← hm, pow_orderOf_eq_one, one_mul]
      refine ⟨n ^ j * β, N.mul_mem (Subgroup.pow_mem N hn j) (hVN hβV), ?_⟩
      rw [hmain, hfin]
  -- ## The bijection between `I_N(y)` and the involutions of the coset `Ny`
  have hbij : Set.BijOn (fun x : G => x * y) (Work.GW2.invSet N y)
      {z : G | z * z = 1 ∧ ∃ n : ↥N, z = (n : G) * y} := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Work.GW2.invSet, Set.mem_setOf_eq] at hx
      obtain ⟨hxN, hxinv⟩ := hx
      refine ⟨?_, ⟨⟨x, hxN⟩, rfl⟩⟩
      have h : (x * y) * (x * y) = x * (y * x * y⁻¹) := by rw [hyinv]; group
      rw [h, hxinv, mul_inv_cancel]
    · intro a _ b _ hab
      exact mul_right_cancel hab
    · intro z hz
      simp only [Set.mem_setOf_eq] at hz
      obtain ⟨hz2, n, hnz⟩ := hz
      refine ⟨(n : G), ?_, ?_⟩
      · rw [Work.GW2.invSet, Set.mem_setOf_eq]
        refine ⟨n.2, ?_⟩
        have h : ((n : G) * y) * ((n : G) * y) = 1 := by rw [← hnz]; exact hz2
        have e : ((n : G) * y) * ((n : G) * y)
            = (n : G) * (y * (n : G) * y⁻¹) := by rw [hyinv]; group
        rw [e] at h
        exact eq_inv_of_mul_eq_one_right h
      · rw [hnz]
  rw [Set.BijOn.ncard_eq hbij]
  -- ## The involutions of the coset are exactly the `N`-orbit of `y`
  have hS : {z : G | z * z = 1 ∧ ∃ n : ↥N, z = (n : G) * y}
      = Set.range (fun n : ↥N => (n : G) * y * (n : G)⁻¹) := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_setOf_eq] at hz
      obtain ⟨hz2, n, hnz⟩ := hz
      rw [Set.mem_range]
      have hzinv : y * (n : G) * y⁻¹ = (n : G)⁻¹ := by
        have h : ((n : G) * y) * ((n : G) * y) = 1 := by rw [← hnz]; exact hz2
        have e : ((n : G) * y) * ((n : G) * y)
            = (n : G) * (y * (n : G) * y⁻¹) := by rw [hyinv]; group
        rw [e] at h
        exact eq_inv_of_mul_eq_one_right h
      obtain ⟨g, hgN, hg⟩ := fusion (n : G) n.2 hzinv
      exact ⟨⟨g, hgN⟩, by rw [hnz]; exact hg⟩
    · intro hz
      rw [Set.mem_range] at hz
      obtain ⟨n, hn⟩ := hz
      refine ⟨?_, ⟨⟨(n : G) * (y * (n : G)⁻¹ * y⁻¹),
        N.mul_mem n.2 (hYN (n : G)⁻¹ (N.inv_mem n.2))⟩, ?_⟩⟩
      · rw [← hn]
        show ((n : G) * y * (n : G)⁻¹) * ((n : G) * y * (n : G)⁻¹) = 1
        rw [show ((n : G) * y * (n : G)⁻¹) * ((n : G) * y * (n : G)⁻¹)
            = (n : G) * (y * y) * (n : G)⁻¹ by group, hy2, mul_one, mul_inv_cancel]
      · rw [← hn]
        group
  rw [hS]
  exact Work.CORE4.ncard_range_conj_mul_card_centralizer N y

end Work.CORE4
