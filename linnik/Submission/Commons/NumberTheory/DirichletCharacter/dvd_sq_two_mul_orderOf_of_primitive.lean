import Mathlib
import Submission.Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow
import Submission.Commons.NumberTheory.Nat.prod_primeFactors_filter_factorization_mul_prime_pow
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime_order


open DirichletCharacter MulChar

namespace Commons.NumberTheory.DirichletCharacter

lemma pow_dvd_sq_two_mul_of_dvd {p a d : ℕ} (ha : 2 ≤ a) (h : p ^ (a-1) ∣ d) :
    p ^ a ∣ (2 * d) ^ 2 := by
  obtain ⟨k, rfl⟩ := h
  have h1 : p ^ a ∣ p ^ ((a-1)*2) * (4 * k ^ 2) :=
    dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _
  have h2 : (2 * (p ^ (a-1) * k)) ^ 2 = p ^ ((a-1)*2) * (4 * k^2) := by
    rw [mul_pow, mul_pow, ← pow_mul]; ring
  rw [h2]; exact h1

lemma two_pow_dvd_sq_two_mul_of_dvd {a d : ℕ} (ha : 2 ≤ a) (h : 2 ^ (a-2) ∣ d) :
    2 ^ a ∣ (2 * d) ^ 2 := by
  obtain ⟨k, rfl⟩ := h
  have h1 : 2 ^ a ∣ (2 ^ ((a-2)*2) * 4) * k ^ 2 := by
    refine dvd_mul_of_dvd_left ?_ (k^2)
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_add]
    exact pow_dvd_pow 2 (by omega)
  have h2 : (2 * (2 ^ (a-2) * k)) ^ 2 = (2 ^ ((a-2)*2) * 4) * k^2 := by
    rw [mul_pow, mul_pow, ← pow_mul]; ring
  rw [h2]; exact h1


lemma orderOf_prime_pow_odd_dvd {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a)
    (χ : DirichletCharacter ℂ (p^a)) (hχ : χ.IsPrimitive) :
    p ^ (a-1) ∣ orderOf χ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha1 : 1 ≤ a := by omega
  have hpa_ne : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ a) := ⟨hpa_ne⟩
  have hpn_ne : p ^ (a-1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ (a-1)) := ⟨hpn_ne⟩
  have hd : p ^ (a-1) ∣ p ^ a := pow_dvd_pow p (by omega)
  have hcop : Nat.Coprime (1 + p) (p ^ a) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_add_self_left).mpr (by simp)
  set u : (ZMod (p^a))ˣ := ZMod.unitOfCoprime (1 + p) hcop with hu
  have huval : (u : ZMod (p^a)) = 1 + p := by
    rw [hu, ZMod.coe_unitOfCoprime]; push_cast; rfl
  have hord_u : orderOf u = p ^ (a-1) := by
    rw [← orderOf_injective (Units.coeHom (ZMod (p^a))) Units.coeHom_injective u]
    change orderOf (↑u : ZMod (p^a)) = p ^ (a-1)
    rw [huval]
    have h := ZMod.orderOf_one_add_prime hp hp2 (a-1)
    rw [Nat.sub_add_cancel ha1] at h
    exact h
  set f : (ZMod (p^a))ˣ →* (ZMod (p^(a-1)))ˣ := ZMod.unitsMap hd with hf
  have hfu : orderOf (f u) = p ^ (a-2) := by
    rw [← orderOf_injective (Units.coeHom (ZMod (p^(a-1)))) Units.coeHom_injective (f u)]
    change orderOf (↑(f u) : ZMod (p^(a-1))) = p ^ (a-2)
    have hval : (↑(f u) : ZMod (p^(a-1))) = (1 + p : ZMod (p^(a-1))) := by
      rw [hf, ZMod.unitsMap_val, huval, ZMod.cast_add hd, ZMod.cast_one hd,
        ZMod.cast_natCast hd p]
    rw [hval]
    have h := ZMod.orderOf_one_add_prime hp hp2 (a-2)
    rw [show a - 2 + 1 = a - 1 by omega] at h
    exact h
  have hker_card : Nat.card f.ker = p := by
    rw [hf]
    exact Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow hp (by omega) hd
  set h0 : (ZMod (p^a))ˣ := u ^ (p ^ (a-2)) with hh0def
  have hord_h0 : orderOf h0 = p := by
    rw [hh0def, orderOf_pow, hord_u,
      Nat.gcd_eq_right (pow_dvd_pow p (by omega : a-2 ≤ a-1)),
      Nat.pow_div (by omega) hp.pos]
    rw [show a - 1 - (a-2) = 1 by omega, pow_one]
  have hmem_h0 : h0 ∈ f.ker := by
    rw [MonoidHom.mem_ker, hh0def, map_pow, ← hfu, pow_orderOf_eq_one]
  have hker_eq : Subgroup.zpowers h0 = f.ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hmem_h0
    · rw [Nat.card_zpowers, hord_h0, hker_card]
  have hnf : ¬ χ.FactorsThrough (p^(a-1)) := by
    intro hft
    have hcond : χ.conductor ∣ p^(a-1) :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hft
    rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hcond
    have hlt : p ^ (a-1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos hp.pos (a-1)) hcond) (not_le.mpr hlt)
  have hnotsub : ¬ (f.ker ≤ χ.toUnitHom.ker) := by
    rw [← (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hd)]
    exact hnf
  obtain ⟨x, hxmem, hxnotin⟩ := Set.not_subset.mp hnotsub
  have hh0ne : χ.toUnitHom h0 ≠ 1 := by
    intro hc
    apply hxnotin
    have hle : f.ker ≤ χ.toUnitHom.ker := by
      rw [← hker_eq]
      exact Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hc)
    exact hle hxmem
  have hpow1 : (χ.toUnitHom u) ^ (p^(a-1)) = 1 := by
    rw [← map_pow, ← hord_u, pow_orderOf_eq_one, map_one]
  have hpow2 : ¬ (χ.toUnitHom u) ^ (p^(a-2)) = 1 := by
    intro hc
    apply hh0ne
    rw [← map_pow] at hc
    rw [hh0def]
    exact hc
  have hord_tu : orderOf (χ.toUnitHom u) = p ^ (a-1) := by
    have h := orderOf_eq_prime_pow (p := p) (n := a-2) hpow2
      (by rw [show a - 2 + 1 = a - 1 by omega]; exact hpow1)
    rwa [show a - 2 + 1 = a - 1 by omega] at h
  have hto : orderOf (χ.toUnitHom u) ∣ orderOf χ := by
    rw [orderOf_dvd_iff_pow_eq_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one,
      ← MulChar.pow_apply_coe χ (orderOf χ) u, pow_orderOf_eq_one, MulChar.one_apply_coe]
  rwa [hord_tu] at hto

lemma dvd_sq_two_mul_orderOf_two_pow {a : ℕ} (ha : 3 ≤ a)
    (χ : DirichletCharacter ℂ (2^a)) (hχ : χ.IsPrimitive) :
    2 ^ a ∣ (2 * orderOf χ) ^ 2 := by
  have h2dvd : 2 ^ (a-2) ∣ orderOf χ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ha1 : 1 ≤ a := by omega
    have hpa_ne : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
    haveI : NeZero (2 ^ a) := ⟨hpa_ne⟩
    have hpn_ne : 2 ^ (a-1) ≠ 0 := pow_ne_zero _ (by norm_num)
    haveI : NeZero (2 ^ (a-1)) := ⟨hpn_ne⟩
    have hd : 2 ^ (a-1) ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have hcop : Nat.Coprime 5 (2 ^ a) := (by decide : Nat.Coprime 5 2).pow_right a
    set u : (ZMod (2^a))ˣ := ZMod.unitOfCoprime 5 hcop with hu
    have huval : (u : ZMod (2^a)) = ((5:ℕ) : ZMod (2^a)) := by
      rw [hu, ZMod.coe_unitOfCoprime]
    have hord_u : orderOf u = 2 ^ (a-2) := by
      rw [← orderOf_injective (Units.coeHom (ZMod (2^a))) Units.coeHom_injective u]
      change orderOf (↑u : ZMod (2^a)) = 2 ^ (a-2)
      rw [huval]
      have h := ZMod.orderOf_five (a-2)
      rw [show a - 2 + 2 = a by omega] at h
      exact h
    set f : (ZMod (2^a))ˣ →* (ZMod (2^(a-1)))ˣ := ZMod.unitsMap hd with hf
    have hfu : orderOf (f u) = 2 ^ (a-3) := by
      rw [← orderOf_injective (Units.coeHom (ZMod (2^(a-1)))) Units.coeHom_injective (f u)]
      change orderOf (↑(f u) : ZMod (2^(a-1))) = 2 ^ (a-3)
      have hval : (↑(f u) : ZMod (2^(a-1))) = ((5:ℕ) : ZMod (2^(a-1))) := by
        rw [hf, ZMod.unitsMap_val, huval, ZMod.cast_natCast hd 5]
      rw [hval]
      have h := ZMod.orderOf_five (a-3)
      rw [show a - 3 + 2 = a - 1 by omega] at h
      exact h
    have hker_card : Nat.card f.ker = 2 := by
      rw [hf]
      exact Commons.NumberTheory.ZMod.card_ker_unitsMap_prime_pow Nat.prime_two (by omega) hd
    set h0 : (ZMod (2^a))ˣ := u ^ (2 ^ (a-3)) with hh0def
    have hord_h0 : orderOf h0 = 2 := by
      rw [hh0def, orderOf_pow, hord_u,
        Nat.gcd_eq_right (pow_dvd_pow 2 (by omega : a-3 ≤ a-2)),
        Nat.pow_div (by omega) (by norm_num : 0 < 2)]
      rw [show a - 2 - (a-3) = 1 by omega, pow_one]
    have hmem_h0 : h0 ∈ f.ker := by
      rw [MonoidHom.mem_ker, hh0def, map_pow, ← hfu, pow_orderOf_eq_one]
    have hker_eq : Subgroup.zpowers h0 = f.ker := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hmem_h0
      · rw [Nat.card_zpowers, hord_h0, hker_card]
    have hnf : ¬ χ.FactorsThrough (2^(a-1)) := by
      intro hft
      have hcond : χ.conductor ∣ 2^(a-1) :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hft
      rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hcond
      have hlt : 2 ^ (a-1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact absurd (Nat.le_of_dvd (pow_pos (by norm_num) _) hcond) (not_le.mpr hlt)
    have hnotsub : ¬ (f.ker ≤ χ.toUnitHom.ker) := by
      rw [← (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hd)]
      exact hnf
    obtain ⟨x, hxmem, hxnotin⟩ := Set.not_subset.mp hnotsub
    have hh0ne : χ.toUnitHom h0 ≠ 1 := by
      intro hc
      apply hxnotin
      have hle : f.ker ≤ χ.toUnitHom.ker := by
        rw [← hker_eq]
        exact Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hc)
      exact hle hxmem
    have hpow1 : (χ.toUnitHom u) ^ (2^(a-2)) = 1 := by
      rw [← map_pow, ← hord_u, pow_orderOf_eq_one, map_one]
    have hpow2 : ¬ (χ.toUnitHom u) ^ (2^(a-3)) = 1 := by
      intro hc
      apply hh0ne
      rw [← map_pow] at hc
      rw [hh0def]
      exact hc
    have hord_tu : orderOf (χ.toUnitHom u) = 2 ^ (a-2) := by
      have h := orderOf_eq_prime_pow (p := 2) (n := a-3) hpow2
        (by rw [show a - 3 + 1 = a - 2 by omega]; exact hpow1)
      rwa [show a - 3 + 1 = a - 2 by omega] at h
    have hto : orderOf (χ.toUnitHom u) ∣ orderOf χ := by
      rw [orderOf_dvd_iff_pow_eq_one]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one,
        ← MulChar.pow_apply_coe χ (orderOf χ) u, pow_orderOf_eq_one, MulChar.one_apply_coe]
    rwa [hord_tu] at hto
  exact two_pow_dvd_sq_two_mul_of_dvd (by omega) h2dvd



lemma dvd_sq_two_mul_orderOf_prime_pow_odd {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 3 ≤ a)
    (χ : DirichletCharacter ℂ (p^a)) (hχ : χ.IsPrimitive) :
    p ^ a ∣ (2 * orderOf χ) ^ 2 :=
  pow_dvd_sq_two_mul_of_dvd (by omega) (orderOf_prime_pow_odd_dvd hp hp2 (by omega) χ hχ)

theorem dvd_sq_two_mul_orderOf_of_primitive_aux : ∀ q, q ≠ 0 → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    (∏ p ∈ q.primeFactors.filter (fun p => 3 ≤ q.factorization p), p ^ q.factorization p)
      ∣ (2 * orderOf χ) ^ 2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq χ hχ
    by_cases hS : (q.primeFactors.filter (fun p => 3 ≤ q.factorization p)).Nonempty
    · obtain ⟨p, hp_mem⟩ := hS
      rw [Finset.mem_filter] at hp_mem
      obtain ⟨hp_pf, hpge⟩ := hp_mem
      obtain ⟨hpprime, hpdvd, hqne0⟩ := Nat.mem_primeFactors.mp hp_pf
      obtain ⟨a, ha_eq, ha_ge⟩ : ∃ a, a = q.factorization p ∧ 3 ≤ a := ⟨_, rfl, hpge⟩
      obtain ⟨m, hm⟩ : ∃ m, q = p ^ a * m := by
        refine ⟨q / p ^ a, ?_⟩
        rw [ha_eq]
        exact (Nat.ordProj_mul_ordCompl_eq_self q p).symm
      subst hm
      have hm_ne : m ≠ 0 := fun h => hq (by rw [h, mul_zero])
      haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hpprime.ne_zero⟩
      haveI : NeZero m := ⟨hm_ne⟩
      have hnotdvd : ¬ p ∣ m := by
        intro hdvd
        have h1 : p ^ (a+1) ∣ p ^ a * m := by
          rw [pow_succ]; exact mul_dvd_mul_left _ hdvd
        have hle : a + 1 ≤ (p ^ a * m).factorization p :=
          (hpprime.pow_dvd_iff_le_factorization hq).mp h1
        rw [← ha_eq] at hle
        omega
      have hcop : Nat.Coprime p m := (hpprime.coprime_iff_not_dvd).mpr hnotdvd
      have hcopa : Nat.Coprime (p ^ a) m := hcop.pow_left a
      obtain ⟨χp, χm, hχp, hχm, heq, hdp, hdm⟩ :=
        Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime_order
          (u := p^a) (v := m) hcopa χ hχ
      have hP :=
        Commons.NumberTheory.Nat.prod_primeFactors_filter_factorization_mul_prime_pow
          hpprime ha_ge hm_ne hcop
      have hlocal : p ^ a ∣ (2 * orderOf χp) ^ 2 := by
        rcases eq_or_ne p 2 with hp2eq | hp2ne
        · subst hp2eq; exact dvd_sq_two_mul_orderOf_two_pow ha_ge χp hχp
        · exact dvd_sq_two_mul_orderOf_prime_pow_odd hpprime hp2ne ha_ge χp hχp
      have hpa1 : 1 < p ^ a := Nat.one_lt_pow (by omega) hpprime.one_lt
      have hm_lt : m < p ^ a * m := by
        have h1 : 1 * m < p ^ a * m :=
          Nat.mul_lt_mul_of_pos_right hpa1 (Nat.pos_of_ne_zero hm_ne)
        simpa using h1
      have hih := ih m hm_lt hm_ne χm hχm
      have hcopP : (p ^ a).Coprime
          (∏ q ∈ m.primeFactors.filter (fun q => 3 ≤ m.factorization q),
            q ^ m.factorization q) := by
        apply Nat.Coprime.prod_right
        intro q hq_f
        rw [Finset.mem_filter] at hq_f
        obtain ⟨hqm, _⟩ := hq_f
        obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hqm
        have hpq : Nat.Coprime p q :=
          (Nat.coprime_primes hpprime hqprime).mpr (by rintro rfl; exact hnotdvd hqdvd)
        exact (hpq.pow_left a).pow_right (m.factorization q)
      have h1 : p ^ a ∣ (2 * orderOf χ) ^ 2 :=
        hlocal.trans (pow_dvd_pow_of_dvd (Nat.mul_dvd_mul (dvd_refl 2) hdp) 2)
      have h2 : (∏ q ∈ m.primeFactors.filter (fun q => 3 ≤ m.factorization q),
            q ^ m.factorization q) ∣ (2 * orderOf χ) ^ 2 :=
        hih.trans (pow_dvd_pow_of_dvd (Nat.mul_dvd_mul (dvd_refl 2) hdm) 2)
      have hcomb : p ^ a * (∏ q ∈ m.primeFactors.filter (fun q => 3 ≤ m.factorization q),
            q ^ m.factorization q) ∣ (2 * orderOf χ) ^ 2 := by
        rw [← hcopP.lcm_eq_mul]
        exact Nat.lcm_dvd h1 h2
      rw [hP]; exact hcomb
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp

theorem dvd_sq_two_mul_orderOf_of_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (∏ p ∈ q.primeFactors.filter (fun p => 3 ≤ q.factorization p), p ^ q.factorization p)
      ∣ (2 * orderOf χ) ^ 2 :=
  dvd_sq_two_mul_orderOf_of_primitive_aux q (NeZero.ne q) χ hχ

end Commons.NumberTheory.DirichletCharacter
