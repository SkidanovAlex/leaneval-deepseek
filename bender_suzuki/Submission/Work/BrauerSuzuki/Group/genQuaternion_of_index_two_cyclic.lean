import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.exists_mul_add_dvd_iff
import Submission.Work.BrauerSuzuki.Quaternion.twoAdic_core
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Group

/-! ## The nonabelian case of Huppert III.8.2 with a cyclic subgroup of index two

Let `P` be a finite `2`-group with a unique involution, `A ≤ P` a cyclic subgroup of index `2`
(hence normal), and suppose `P` is not commutative.  Write `A = ⟨a⟩`, `orderOf a = 2 ^ m`
(so `m ≥ 2`, because `|P| = 2 ^ (m+1)` and groups of order `≤ 4` are commutative), and pick
`x ∈ P \ A`; put `x ^ 2 = a ^ s` and `x * a * x⁻¹ = a ^ t` (both exist since `A` has index two,
so `x ^ 2 ∈ A`, and `A` is normal).  Conjugation by `x ^ 2 = a ^ s` is trivial on the abelian
group `A`, while conjugation by `x` sends `a` to `a ^ t`, so `2 ^ m ∣ (t - 1) * (t + 1)`;
applying `x` to the relation `x ^ 2 = a ^ s` gives `a ^ (t * s) = a ^ s`, i.e. `2 ^ m ∣ (t - 1) * s`;
and `x * a ^ k` has square `a ^ ((t + 1) * k + s)`, so if `Nat.gcd (t + 1) (2 ^ m) ∣ s` then some
`x * a ^ k` is an involution lying outside `A`, contradicting uniqueness.  Since `2 ^ m ∤ t - 1`
(otherwise `x` commutes with `a` and `P = ⟨a, x⟩` is commutative), the two-adic fact
`Work.BrauerSuzuki.Quaternion.twoAdic_core` yields `2 ^ m ∣ t + 1` and `2 ^ (m - 1) ∣ s` with
`¬ 2 ^ m ∣ s`.  Hence `a ^ t = a⁻¹` and `x ^ 2 = a ^ s = a ^ (2 ^ (m - 1))`, and `P = ⟨a, x⟩`:
this is exactly `GenQuaternionData` with `n = m`, `tau = a`, `rho = x`. -/

/-- A finite `2`-group of order at most `4` is commutative. -/
private theorem isMulCommutative_of_isPGroup_card_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (h : Nat.card P ≤ 4) : IsMulCommutative P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hn2 : n ≤ 2 := by
    by_contra hlt
    push_neg at hlt
    have hle : 2 ^ n ≤ 4 := hn ▸ h
    have hge : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hge
    omega
  rcases n with _ | _ | _ | n
  · exact (isCyclic_of_card_dvd_prime (p := 2) (by rw [hn]; norm_num)).isMulCommutative
  · exact (isCyclic_of_card_dvd_prime (p := 2) (by rw [hn]; norm_num)).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hn
  · omega

theorem genQuaternion_of_index_two_cyclic {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hu : Work.BrauerSuzuki.HasUniqueInvolution P)
    (hnc : ¬ IsMulCommutative P) {A : Subgroup P} (hAcyc : IsCyclic A) (hAidx : A.index = 2) :
    Work.BrauerSuzuki.IsGenQuaternion P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAnorm : A.Normal := Subgroup.normal_of_index_eq_two hAidx
  -- A generator `a` of the cyclic subgroup `A`.
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hAcyc
  let a : P := (g : P)
  have hAeq : A = Subgroup.zpowers a := by
    apply le_antisymm
    · intro y hy
      have hy' : (⟨y, hy⟩ : A) ∈ Subgroup.zpowers g := by rw [hg]; trivial
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg (fun z : A => (z : P)) hk
      simpa using this
    · rw [Subgroup.zpowers_le]
      exact g.2
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hP.to_subgroup A)
  have ha_ord : orderOf a = 2 ^ m := by
    rw [← Nat.card_zpowers a, ← hAeq]
    exact hm
  have hcardP : Nat.card P = 2 ^ (m + 1) := by
    rw [← A.card_mul_index, hAidx, hm, ← pow_succ]
  -- `m ≥ 2` because otherwise `|P| ≤ 4`.
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hle : Nat.card P ≤ 4 := by
      rw [hcardP]
      calc 2 ^ (m + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    exact hnc (isMulCommutative_of_isPGroup_card_le_four hP hle)
  -- A coset representative `x ∉ A`.
  obtain ⟨x, hxA, hcoset⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hAidx
  obtain ⟨z, hz2, hzuniq⟩ := hu
  -- `s` with `x ^ 2 = a ^ s`.
  have hx2A : x ^ 2 ∈ A := Subgroup.sq_mem_of_index_two hAidx x
  have hmem_s : x ^ 2 ∈ Subgroup.zpowers a := by rw [← hAeq]; exact hx2A
  obtain ⟨ks, hks⟩ := Subgroup.mem_zpowers_iff.mp hmem_s
  obtain ⟨s, hs⟩ : ∃ s : ℕ, x ^ 2 = a ^ s := by
    refine ⟨(ks % (orderOf a : ℤ)).toNat, ?_⟩
    have hmod : a ^ ks = a ^ (ks % (orderOf a : ℤ)) :=
      zpow_eq_zpow_emod (x := a) ks (by rw [zpow_natCast, pow_orderOf_eq_one])
    have hcast : (((ks % (orderOf a : ℤ)).toNat : ℕ) : ℤ) = ks % (orderOf a : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [ha_ord]; positivity))
    rw [← hks, hmod]
    conv_lhs => rw [← hcast]
    rw [zpow_natCast]
  -- `t` with `x * a * x⁻¹ = a ^ t`.
  have hmem_t : x * a * x⁻¹ ∈ Subgroup.zpowers a := by
    rw [← hAeq]; exact hAnorm.conj_mem a g.2 x
  obtain ⟨kt, hkt⟩ := Subgroup.mem_zpowers_iff.mp hmem_t
  obtain ⟨t, ht⟩ : ∃ t : ℕ, x * a * x⁻¹ = a ^ t := by
    refine ⟨(kt % (orderOf a : ℤ)).toNat, ?_⟩
    have hmod : a ^ kt = a ^ (kt % (orderOf a : ℤ)) :=
      zpow_eq_zpow_emod (x := a) kt (by rw [zpow_natCast, pow_orderOf_eq_one])
    have hcast : (((kt % (orderOf a : ℤ)).toNat : ℕ) : ℤ) = kt % (orderOf a : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [ha_ord]; positivity))
    rw [← hkt, hmod]
    conv_lhs => rw [← hcast]
    rw [zpow_natCast]
  -- `t` is odd.
  have ht_odd : t % 2 = 1 := by
    have hord_at : orderOf (a ^ t) = orderOf a := by
      rw [← ht]; exact orderOf_conj_eq x a
    have hgcd1 : Nat.gcd (2 ^ m) t = 1 := by
      rw [orderOf_pow, ha_ord] at hord_at
      rcases Nat.div_eq_self.mp hord_at with h | h
      · exact absurd h (by positivity)
      · exact h
    rw [← Nat.two_dvd_ne_zero]
    intro h2t
    have h21 : 2 ∣ 1 := by
      rw [← hgcd1]
      exact Nat.dvd_gcd (dvd_pow_self 2 (by omega : m ≠ 0)) h2t
    have := Nat.le_of_dvd (by norm_num) h21
    omega
  have ht_pos : 0 < t := Nat.pos_of_ne_zero (by intro h; rw [h] at ht_odd; simp at ht_odd)
  -- `x ^ 2` commutes with `a`.
  have hx2comm : x ^ 2 * a = a * x ^ 2 := by
    rw [hs]
    exact ((Commute.refl a).pow_left s).eq
  -- The closure of `{a, x}` is everything.
  have hAc : A ≤ Subgroup.closure ({a, x} : Set P) := by
    rw [hAeq]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hclosure : Subgroup.closure ({a, x} : Set P) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    by_cases hy : y ∈ A
    · exact hAc hy
    · have hyx : y * x ∈ A := (hcoset y).resolve_right hy
      have h1 : y * x ∈ Subgroup.closure ({a, x} : Set P) := hAc hyx
      have h2 : x⁻¹ ∈ Subgroup.closure ({a, x} : Set P) :=
        Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      have : y = (y * x) * x⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ h1 h2
  -- Divisibility facts.
  have h1 : 2 ^ m ∣ (t - 1) * (t + 1) := by
    have htt1 : 1 ≤ t * t := by nlinarith [ht_pos]
    have hstepR : x * (x * a * x⁻¹) * x⁻¹ = a ^ (t * t) := by
      rw [show x * (x * a * x⁻¹) * x⁻¹ = x * a ^ t * x⁻¹ by rw [ht]]
      rw [show x * a ^ t * x⁻¹ = (x * a * x⁻¹) ^ t by
        rw [← MulAut.conj_apply x (a ^ t), map_pow, MulAut.conj_apply x a]]
      rw [ht, ← pow_mul]
    have hstepL : x * (x * a * x⁻¹) * x⁻¹ = a := by
      have e1 : x * (x * a * x⁻¹) * x⁻¹ = x ^ 2 * a * (x ^ 2)⁻¹ := by
        simp only [pow_two]; group
      rw [e1, hx2comm, mul_assoc, mul_inv_cancel, mul_one]
    have ht2eq : a ^ (t * t) = a := by rw [← hstepR, hstepL]
    have hmod1 : t * t ≡ 1 [MOD 2 ^ m] := by
      have := (pow_eq_pow_iff_modEq (x := a) (n := t * t) (m := 1)).mp (by rw [ht2eq, pow_one])
      rwa [ha_ord] at this
    have hdvd : 2 ^ m ∣ t * t - 1 := (Nat.modEq_iff_dvd' htt1).mp hmod1.symm
    have heq : t * t - 1 = (t - 1) * (t + 1) := by
      have h := Nat.sq_sub_sq t 1
      rw [pow_two, one_pow] at h
      rw [h]
      exact mul_comm (t + 1) (t - 1)
    rwa [heq] at hdvd
  have h2 : 2 ^ m ∣ (t - 1) * s := by
    have hst : s ≤ t * s := by
      calc s = 1 * s := (one_mul s).symm
        _ ≤ t * s := Nat.mul_le_mul_right s (by omega : 1 ≤ t)
    have hstepR : x * (x ^ 2) * x⁻¹ = a ^ (t * s) := by
      rw [show x * (x ^ 2) * x⁻¹ = x * a ^ s * x⁻¹ by rw [hs]]
      rw [show x * a ^ s * x⁻¹ = (x * a * x⁻¹) ^ s by
        rw [← MulAut.conj_apply x (a ^ s), map_pow, MulAut.conj_apply x a]]
      rw [ht, ← pow_mul]
    have hstepL : x * (x ^ 2) * x⁻¹ = a ^ s := by
      rw [show x * (x ^ 2) * x⁻¹ = x ^ 2 by group]
      exact hs
    have hts_eq : a ^ (t * s) = a ^ s := by rw [← hstepR, hstepL]
    have hmod2 : t * s ≡ s [MOD 2 ^ m] := by
      have := (pow_eq_pow_iff_modEq (x := a) (n := t * s) (m := s)).mp hts_eq
      rwa [ha_ord] at this
    have hdvd : 2 ^ m ∣ t * s - s := (Nat.modEq_iff_dvd' hst).mp hmod2.symm
    have heq : (t - 1) * s = t * s - s := by rw [Nat.sub_mul, one_mul]
    rw [heq]; exact hdvd
  have h3 : ¬ (2 ^ m ∣ t - 1) := by
    intro hdvd
    have hat : a ^ t = a := by
      have h1' : a ^ (t - 1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [ha_ord]; exact hdvd)
      have hdecomp : t = (t - 1) + 1 := by omega
      rw [hdecomp, pow_succ, h1', one_mul]
    have hxa : x * a * x⁻¹ = a := ht.trans hat
    have hcomm : x * a = a * x := by
      calc x * a = (x * a * x⁻¹) * x := by group
        _ = a * x := by rw [hxa]
    have hcomm_closure : IsMulCommutative (Subgroup.closure ({a, x} : Set P)) := by
      apply Subgroup.isMulCommutative_closure
      intro u hu v hv huv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl
      · rcases hv with rfl | rfl
        · exact absurd rfl huv
        · exact hcomm.symm
      · rcases hv with rfl | rfl
        · exact hcomm
        · exact absurd rfl huv
    have htop : IsMulCommutative (⊤ : Subgroup P) := by
      rw [← hclosure]; exact hcomm_closure
    have : IsMulCommutative P := by
      refine isMulCommutative_iff.mpr (fun u v => ?_)
      have h := (isMulCommutative_iff.mp htop) (⟨u, trivial⟩ : (⊤ : Subgroup P)) ⟨v, trivial⟩
      exact congrArg Subtype.val h
    exact hnc this
  have h4 : ¬ (Nat.gcd (t + 1) (2 ^ m) ∣ s) := by
    intro hgcd
    obtain ⟨k, hk⟩ :=
      (Work.BrauerSuzuki.Quaternion.exists_mul_add_dvd_iff (n := 2 ^ m) (a := t + 1) (b := s)
        (by positivity)).mpr hgcd
    have hxak : x * a ^ k * x⁻¹ = a ^ (t * k) := by
      rw [show x * a ^ k * x⁻¹ = (x * a * x⁻¹) ^ k by
        rw [← MulAut.conj_apply x (a ^ k), map_pow, MulAut.conj_apply x a]]
      rw [ht, ← pow_mul]
    have hy_sq : (x * a ^ k) ^ 2 = a ^ ((t + 1) * k + s) := by
      rw [pow_two, show x * a ^ k * (x * a ^ k) = (x * a ^ k * x⁻¹) * x ^ 2 * a ^ k by group,
        hxak, hs, ← pow_add, ← pow_add]
      congr 1; ring
    have hy : (x * a ^ k) ^ 2 = 1 := by
      rw [hy_sq]
      exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [ha_ord]; exact hk)
    have hy_ne : x * a ^ k ≠ 1 := by
      intro h
      apply hxA
      have he : x = (a ^ k)⁻¹ := eq_inv_iff_mul_eq_one.mpr h
      rw [he]
      exact Subgroup.inv_mem A (Subgroup.pow_mem A g.2 k)
    have hyA : x * a ^ k ∉ A := by
      intro hmem
      apply hxA
      have he : x = (x * a ^ k) * (a ^ k)⁻¹ := by group
      rw [he]
      exact Subgroup.mul_mem A hmem (Subgroup.inv_mem A (Subgroup.pow_mem A g.2 k))
    have hy2 : orderOf (x * a ^ k) = 2 := orderOf_eq_prime hy hy_ne
    have hw2 : orderOf (a ^ (2 ^ (m - 1))) = 2 := by
      rw [orderOf_pow, ha_ord]
      rw [Nat.gcd_eq_right (pow_dvd_pow 2 (by omega : m - 1 ≤ m))]
      rw [Nat.pow_div (by omega : m - 1 ≤ m) (by norm_num : 0 < 2),
        show m - (m - 1) = 1 by omega, pow_one]
    have hwA : a ^ (2 ^ (m - 1)) ∈ A := Subgroup.pow_mem A g.2 (2 ^ (m - 1))
    have heq : x * a ^ k = a ^ (2 ^ (m - 1)) := (hzuniq _ hy2).trans (hzuniq _ hw2).symm
    rw [← heq] at hwA
    exact hyA hwA
  -- Apply the two-adic core.
  obtain ⟨htp1, hsm1, hs_not⟩ :=
    Work.BrauerSuzuki.Quaternion.twoAdic_core hm2 ht_odd h1 h2 h3 h4
  have ha_inv : a ^ t = a⁻¹ := by
    have h : a ^ (t + 1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [ha_ord]; exact htp1)
    rw [pow_succ] at h
    exact eq_inv_iff_mul_eq_one.mpr h
  have has_eq : a ^ s = a ^ (2 ^ (m - 1)) := by
    obtain ⟨q, hq⟩ := hsm1
    have hw_sq : (a ^ (2 ^ (m - 1))) ^ 2 = 1 := by
      rw [← pow_mul, show 2 ^ (m - 1) * 2 = 2 ^ m by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]]
      rw [← ha_ord]
      exact pow_orderOf_eq_one a
    have hqodd : q % 2 = 1 := by
      rw [← Nat.two_dvd_ne_zero]
      intro h2q
      apply hs_not
      rw [hq]
      obtain ⟨q', rfl⟩ := h2q
      refine ⟨q', ?_⟩
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    obtain ⟨c, hc⟩ : ∃ c, q = 2 * c + 1 := by
      have := Nat.mod_add_div q 2
      rw [hqodd] at this
      exact ⟨q / 2, by omega⟩
    rw [hq, pow_mul, hc, pow_succ, pow_mul, hw_sq, one_pow, one_mul]
  exact ⟨m, hm2, a, x, ha_ord, by rw [ht, ha_inv], by rw [hs, has_eq], hclosure⟩

end Work.BrauerSuzuki.Group
