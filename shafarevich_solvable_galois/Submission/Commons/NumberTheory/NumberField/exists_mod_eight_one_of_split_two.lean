import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RamificationInertia.Basic
import Submission.Commons.NumberTheory.NumberField.no_inertiaDeg_one_two_of_mod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Commons.NumberTheory.NumberField


private lemma eq_of_sq_eq_of_sq_self {R : Type*} [CommRing R] [IsDomain R]
    (hR2 : (2 : R) = 0) {a c : R} (h1 : a ^ 2 = c) (h2 : c ^ 2 = c) : a = c := by
  have h : (a - c) ^ 2 = 0 := by
    calc (a - c) ^ 2 = a ^ 2 - 2 * a * c + c ^ 2 := by ring
      _ = a ^ 2 + c ^ 2 := by rw [hR2]; ring
      _ = c + c := by rw [h1, h2]
      _ = 0 := by rw [← two_mul, hR2, zero_mul]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)

private theorem sub_mem_of_sq_eq_of_mem_two {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ)
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ))
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal]
    (h2 : (2 : NumberField.RingOfIntegers K) ∈ P) :
    (u - algebraMap ℤ (NumberField.RingOfIntegers K) D) ∈ P := by
  let R := NumberField.RingOfIntegers K
  have huR : (u : R) ^ 2 = algebraMap ℤ R D := by
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    rw [map_pow]
    change ((u : K)) ^ 2 = algebraMap ℤ K D
    rw [hu]
    simp
  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  let φ : R →+* R ⧸ P := Ideal.Quotient.mk P
  have hchar : (2 : R ⧸ P) = 0 := by
    show Ideal.Quotient.mk P (2 : R) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  have h1 : (φ u) ^ 2 = φ (algebraMap ℤ R D) := by
    rw [← map_pow, huR]
  have hDmem : algebraMap ℤ R (D ^ 2 - D) ∈ P := by
    have hDfact : D ^ 2 - D = D * (D - 1) := by ring
    have hdeven : (2 : ℤ) ∣ D ^ 2 - D := by
      rw [hDfact]; exact even_iff_two_dvd.mp (Int.even_mul_pred_self D)
    obtain ⟨k, hk⟩ := hdeven
    rw [hk, map_mul, map_ofNat]
    exact Ideal.mul_mem_right _ _ h2
  have h2' : (φ (algebraMap ℤ R D)) ^ 2 = φ (algebraMap ℤ R D) := by
    have hEq : (algebraMap ℤ R D) ^ 2 - algebraMap ℤ R D = algebraMap ℤ R (D ^ 2 - D) := by
      rw [map_sub, map_pow]
    have hzero : (algebraMap ℤ R D) ^ 2 - algebraMap ℤ R D ∈ P := by rw [hEq]; exact hDmem
    have hsub : φ ((algebraMap ℤ R D) ^ 2 - algebraMap ℤ R D) = 0 := by
      show Ideal.Quotient.mk P _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]; exact hzero
    rw [map_sub, map_pow] at hsub
    exact sub_eq_zero.mp hsub
  have hsub : φ u = φ (algebraMap ℤ R D) := eq_of_sq_eq_of_sq_self hchar h1 h2'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub]
  exact sub_eq_zero.mpr hsub

/-- `finrank ℚ K ≤ 2` when `K = ℚ(u)` with `u^2 = D`. -/

private lemma finrank_rat_le_two {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ) (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ))
    (hgen : Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤) :
    Module.finrank ℚ K ≤ 2 := by
  have hdeg : (minpoly ℚ (u : K)).natDegree = Module.finrank ℚ K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq ℚ (u : K)).mp (by simpa using hgen)
  have hdvd : minpoly ℚ (u : K) ∣ (Polynomial.X ^ 2 - Polynomial.C (D : ℚ)) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hu]; ring
  have hnd : (Polynomial.X ^ 2 - Polynomial.C (D : ℚ) : Polynomial ℚ).natDegree = 2 := by
    rw [Polynomial.natDegree_X_pow_sub_C]
  have hne : (Polynomial.X ^ 2 - Polynomial.C (D : ℚ) : Polynomial ℚ) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hnd
    norm_num at hnd
  rw [← hdeg]
  calc (minpoly ℚ (u : K)).natDegree
        ≤ (Polynomial.X ^ 2 - Polynomial.C (D : ℚ) : Polynomial ℚ).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hne
    _ = 2 := hnd

private theorem sub_mem_span_two {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ)
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ))
    (hgen : Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤)
    (hsplit : (IsDedekindDomain.primesOverFinset (Ideal.span {(2 : ℤ)}) (NumberField.RingOfIntegers K)).card = 2) :
    (u - algebraMap ℤ (NumberField.RingOfIntegers K) D) ∈ Ideal.span {(2 : NumberField.RingOfIntegers K)} := by
  classical
  let R := NumberField.RingOfIntegers K
  let p0 : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hp0ne : p0 ≠ ⊥ := by
    dsimp [p0]; rw [Ideal.span_singleton_eq_bot]; norm_num
  haveI hp0prime : p0.IsPrime := by
    dsimp [p0]
    exact (Ideal.span_singleton_prime (by norm_num : (2:ℤ) ≠ 0)).mpr Int.prime_two
  have hp0max : p0.IsMaximal := hp0prime.isMaximal hp0ne
  haveI : p0.IsMaximal := hp0max
  let S := IsDedekindDomain.primesOverFinset p0 R
  have hScard : S.card = 2 := hsplit
  have hcard : Fintype.card (p0.primesOver R) = 2 := by
    rw [Set.fintypeCard_eq_ncard (p0.primesOver R)]
    rw [← IsDedekindDomain.coe_primesOverFinset (p := p0) hp0ne R]
    rw [Set.ncard_coe_finset]
    exact hScard
  have hle2 : Module.finrank ℚ K ≤ 2 := finrank_rat_le_two u D hu hgen
  have hsumfin : ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = Module.finrank ℚ K := by
    rw [Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := R) p0, NumberField.RingOfIntegers.rank K]
  have hterm_ge : ∀ q : p0.primesOver R, 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q
    exact Nat.succ_le_of_lt (Nat.mul_pos (Ideal.ramificationIdx_pos ℤ q.1) (Ideal.inertiaDeg_pos q.1 ℤ))
  have hge2 : 2 ≤ Module.finrank ℚ K := by
    rw [← hsumfin]
    calc 2 = Fintype.card (p0.primesOver R) := hcard.symm
      _ = ∑ _q : p0.primesOver R, (1:ℕ) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      _ ≤ ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
          Finset.sum_le_sum (fun q _ => hterm_ge q)
  have hfinrank : Module.finrank ℚ K = 2 := le_antisymm hle2 hge2
  have hsum2 : ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 2 := by
    rw [hsumfin, hfinrank]
  have hterm_eq : ∀ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    have hsub0 : ∑ r ∈ Finset.univ.erase q, r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ
        + q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 2 := by
      rw [Finset.sum_erase_add _ (fun r => r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ) (Finset.mem_univ q)]
      exact hsum2
    have hone : 1 ≤ ∑ r ∈ Finset.univ.erase q, r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      have hcarderase : (Finset.univ.erase q).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, hcard]
      calc 1 = (Finset.univ.erase q).card := hcarderase.symm
        _ = ∑ _r ∈ Finset.univ.erase q, (1:ℕ) := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun r _ => hterm_ge r)
    have hge1 := hterm_ge q
    omega
  have hram : ∀ q : p0.primesOver R, q.1.ramificationIdx ℤ = 1 := by
    intro q
    have h := hterm_eq q
    exact Nat.dvd_one.mp ⟨q.1.inertiaDeg ℤ, h.symm⟩
  -- product = 2 O_K
  have hmap : Ideal.map (algebraMap ℤ R) p0 = ∏ P ∈ (p0.primesOver R).toFinset, P := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow (p := p0) hp0ne]
    apply Finset.prod_congr rfl
    intro P hP
    have hP' : P ∈ p0.primesOver R := Set.mem_toFinset.mp hP
    have := hram ⟨P, hP'⟩
    rw [this, pow_one]
  have hspan : Ideal.span {(2 : R)} = Ideal.map (algebraMap ℤ R) p0 := by
    rw [Ideal.map_span, Set.image_singleton, map_ofNat]
  have hpair : ((p0.primesOver R).toFinset : Set (Ideal R)).Pairwise (Function.onFun IsCoprime fun P => P) := by
    intro P hP Q hQ hPQ
    have hP' : P ∈ p0.primesOver R := Set.mem_toFinset.mp hP
    have hQ' : Q ∈ p0.primesOver R := Set.mem_toFinset.mp hQ
    haveI : P.IsMaximal := hP'.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0ne hP')
    haveI : Q.IsMaximal := hQ'.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0ne hQ')
    exact Ideal.isCoprime_of_isMaximal hPQ
  have hmem_each : ∀ P ∈ p0.primesOver R, (u - algebraMap ℤ R D) ∈ P := by
    intro P hP
    haveI : P.IsMaximal := hP.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0ne hP)
    haveI : P.LiesOver p0 := hP.2
    have h2mem : (2 : R) ∈ P := by
      have := (Ideal.mem_of_liesOver (p := p0) (P := P) (2 : ℤ)).mp
        (Ideal.subset_span (by simp))
      simpa using this
    exact sub_mem_of_sq_eq_of_mem_two u D hu P h2mem
  have hmem_prod : (u - algebraMap ℤ R D) ∈ ∏ P ∈ (p0.primesOver R).toFinset, P := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hpair]
    rw [Ideal.mem_iInf]
    intro P
    rw [Ideal.mem_iInf]
    intro hPS
    exact hmem_each P (Set.mem_toFinset.mp hPS)
  rw [hspan, hmap]
  exact hmem_prod



private lemma four_dvd_mul_pred {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ)
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ))
    (hmem : (u - algebraMap ℤ (NumberField.RingOfIntegers K) D) ∈
      Ideal.span {(2 : NumberField.RingOfIntegers K)}) :
    (4 : ℤ) ∣ D * (D - 1) := by
  let R := NumberField.RingOfIntegers K
  have huR : (u : R) ^ 2 = algebraMap ℤ R D := by
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    rw [map_pow]
    change ((u : K)) ^ 2 = algebraMap ℤ K D
    rw [hu]; simp
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have hu' : u = algebraMap ℤ R D + 2 * c := by rw [← hc]; ring
  have key : algebraMap ℤ R D = (algebraMap ℤ R D + 2 * c) ^ 2 := by rw [← hu', huR]
  have h0 : algebraMap ℤ R D ^ 2 + 4 * (c * (algebraMap ℤ R D + c)) = algebraMap ℤ R D := by
    have h := key.symm
    rwa [show (algebraMap ℤ R D + 2 * c) ^ 2
        = algebraMap ℤ R D ^ 2 + 4 * (c * (algebraMap ℤ R D + c)) by ring] at h
  have hpoly : algebraMap ℤ R D * (algebraMap ℤ R D - 1)
      + 4 * (c * (algebraMap ℤ R D + c)) = 0 := by
    rw [show algebraMap ℤ R D * (algebraMap ℤ R D - 1)
        + 4 * (c * (algebraMap ℤ R D + c))
        = (algebraMap ℤ R D ^ 2 + 4 * (c * (algebraMap ℤ R D + c))) - algebraMap ℤ R D by ring,
      h0]
    ring
  set z : R := -(c * (algebraMap ℤ R D + c)) with hzdef
  have hz4 : algebraMap ℤ R (D * (D - 1)) = 4 * z := by
    have hdd : algebraMap ℤ R (D * (D - 1))
        = algebraMap ℤ R D * (algebraMap ℤ R D - 1) := by
      rw [map_mul, map_sub, map_one]
    rw [hzdef, hdd, mul_neg, eq_neg_iff_add_eq_zero]
    exact hpoly
  have hz4K : algebraMap ℤ K (D * (D - 1)) = 4 * (z : K) := by
    have h := congrArg (algebraMap R K) hz4
    rw [← IsScalarTower.algebraMap_apply ℤ R K] at h
    rw [show (algebraMap R K) (4 * z) = 4 * (z : K) by rw [map_mul, map_ofNat]] at h
    exact h
  have hqK : algebraMap ℚ K ((D : ℚ) * ((D : ℚ) - 1) / 4) = (z : K) := by
    have h1 : algebraMap ℚ K ((D : ℚ) * ((D : ℚ) - 1) / 4)
        = algebraMap ℤ K (D * (D - 1)) / 4 := by
      rw [map_div₀, map_ofNat]
      congr 1
      rw [show (D : ℚ) * ((D : ℚ) - 1) = (((D * (D - 1) : ℤ)) : ℚ) by push_cast; ring]
      simp
    rw [h1, hz4K]
    rw [show 4 * (z : K) / 4 = (z : K) by field_simp]
  have hqint : IsIntegral ℤ ((D : ℚ) * ((D : ℚ) - 1) / 4) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K)
      (algebraMap ℚ K).injective).mp
      (hqK.symm ▸ (NumberField.RingOfIntegers.isIntegral z).algebraMap)
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hqint
  have hmulZ : (4 * m : ℤ) = D * (D - 1) := by
    have h : ((4 * m : ℤ) : ℚ) = ((D * (D - 1) : ℤ) : ℚ) := by
      push_cast
      rw [show (↑m : ℚ) = (↑D : ℚ) * ((↑D : ℚ) - 1) / 4 from hm]
      ring
    exact_mod_cast h
  exact ⟨m, hmulZ.symm⟩


private lemma mod_four_eq_zero_or_one_of_dvd {D : ℤ} (h : (4 : ℤ) ∣ D * (D - 1)) :
    D % 4 = 0 ∨ D % 4 = 1 := by
  obtain ⟨k, hk⟩ := h
  have hlt : D % 4 < 4 := Int.emod_lt_of_pos D (by norm_num)
  have hnn : 0 ≤ D % 4 := Int.emod_nonneg D (by norm_num)
  have hr : D % 4 = 0 ∨ D % 4 = 1 ∨ D % 4 = 2 ∨ D % 4 = 3 := by omega
  rcases hr with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exact Or.inr h1
  · exfalso
    have hD2 : D = 4 * (D / 4) + 2 := by omega
    rw [hD2] at hk
    set w : ℤ := 4 * (D / 4) ^ 2 + 3 * (D / 4) with hw
    have hkey : (4 * (D / 4) + 2) * (4 * (D / 4) + 2 - 1) = 4 * w + 2 := by rw [hw]; ring
    rw [hkey] at hk
    omega
  · exfalso
    have hD3 : D = 4 * (D / 4) + 3 := by omega
    rw [hD3] at hk
    set w : ℤ := 4 * (D / 4) ^ 2 + 5 * (D / 4) with hw
    have hkey : (4 * (D / 4) + 3) * (4 * (D / 4) + 3 - 1) = 4 * w + 6 := by rw [hw]; ring
    rw [hkey] at hk
    omega

private lemma mod_eight_eq_one_of_odd {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ)
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ))
    (hgen : Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤)
    (h4 : D % 4 = 1)
    (hsplit : (IsDedekindDomain.primesOverFinset (Ideal.span {(2 : ℤ)})
        (NumberField.RingOfIntegers K)).card = 2) :
    D % 8 = 1 := by
  classical
  by_contra h8
  have h85 : D % 8 = 5 := by omega
  have hno := no_inertiaDeg_one_two_of_mod u D hu hgen h4 h85
  let R := NumberField.RingOfIntegers K
  let p0 : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hp0ne : p0 ≠ ⊥ := by
    dsimp [p0]; rw [Ideal.span_singleton_eq_bot]; norm_num
  haveI hp0prime : p0.IsPrime := by
    dsimp [p0]
    exact (Ideal.span_singleton_prime (by norm_num : (2:ℤ) ≠ 0)).mpr Int.prime_two
  have hp0max : p0.IsMaximal := hp0prime.isMaximal hp0ne
  haveI : p0.IsMaximal := hp0max
  have hScard : (IsDedekindDomain.primesOverFinset p0 R).card = 2 := hsplit
  have hcard : Fintype.card (p0.primesOver R) = 2 := by
    rw [Set.fintypeCard_eq_ncard (p0.primesOver R)]
    rw [← IsDedekindDomain.coe_primesOverFinset (p := p0) hp0ne R]
    rw [Set.ncard_coe_finset]
    exact hScard
  have hle2 : Module.finrank ℚ K ≤ 2 := finrank_rat_le_two u D hu hgen
  have hsumfin : ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ
      = Module.finrank ℚ K := by
    rw [Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := R) p0,
      NumberField.RingOfIntegers.rank K]
  have hsum2 : ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 2 := by
    rw [hsumfin]
    have hterm_ge : ∀ q : p0.primesOver R, 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
      intro q
      exact Nat.succ_le_of_lt (Nat.mul_pos (Ideal.ramificationIdx_pos ℤ q.1) (Ideal.inertiaDeg_pos q.1 ℤ))
    have hge2 : 2 ≤ Module.finrank ℚ K := by
      calc 2 = Fintype.card (p0.primesOver R) := hcard.symm
        _ = ∑ _q : p0.primesOver R, (1:ℕ) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        _ ≤ ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
            Finset.sum_le_sum (fun q _ => hterm_ge q)
        _ = Module.finrank ℚ K := hsumfin
    exact le_antisymm hle2 hge2
  have hterm_ge : ∀ q : p0.primesOver R, 2 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q
    have hne : q.1.inertiaDeg ℤ ≠ 1 := hno q.1
      ((IsDedekindDomain.mem_primesOverFinset_iff (p := p0) hp0ne R).mpr q.2)
    have hf : 2 ≤ q.1.inertiaDeg ℤ := by
      have := Ideal.inertiaDeg_pos q.1 ℤ
      omega
    have he : 1 ≤ q.1.ramificationIdx ℤ := Nat.succ_le_of_lt (Ideal.ramificationIdx_pos ℤ q.1)
    calc 2 = 1 * 2 := by norm_num
      _ ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := Nat.mul_le_mul he hf
  have h4le : 4 ≤ ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    calc 4 = Fintype.card (p0.primesOver R) * 2 := by rw [hcard]
      _ = ∑ _q : p0.primesOver R, (2:ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ q : p0.primesOver R, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
          Finset.sum_le_sum (fun q _ => hterm_ge q)
  omega

theorem exists_mod_eight_one_of_split_two {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ)
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ)) (hgen : Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤)
    (hD : D ≠ 0)
    (hsplit : (IsDedekindDomain.primesOverFinset (Ideal.span {(2 : ℤ)}) (NumberField.RingOfIntegers K)).card = 2) :
    ∃ j : ℕ, ∃ D' : ℤ, D = 4 ^ j * D' ∧ D' % 2 = 1 ∧ D' % 8 = 1 := by
  classical
  let R := NumberField.RingOfIntegers K
  suffices hmain : ∀ n : ℕ, ∀ (u : R) (D : ℤ), D.natAbs = n →
      ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ) →
      Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤ → D ≠ 0 →
      (IsDedekindDomain.primesOverFinset (Ideal.span {(2 : ℤ)}) R).card = 2 →
      ∃ j : ℕ, ∃ D' : ℤ, D = 4 ^ j * D' ∧ D' % 2 = 1 ∧ D' % 8 = 1 by
    exact hmain D.natAbs u D rfl hu hgen hD hsplit
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u D hDn hu hgen hD hsplit
    have hmemsub := sub_mem_span_two u D hu hgen hsplit
    have hdvd : (4 : ℤ) ∣ D * (D - 1) := four_dvd_mul_pred u D hu hmemsub
    rcases mod_four_eq_zero_or_one_of_dvd hdvd with h0 | h1
    · obtain ⟨D₁, hD₁⟩ := Int.dvd_of_emod_eq_zero h0
      have hD₁ne : D₁ ≠ 0 := by rintro rfl; simp at hD₁; exact hD hD₁
      have h2mem : (2 : R) ∈ Ideal.span {(2 : R)} := Ideal.mem_span_singleton_self (2 : R)
      have hDmem : algebraMap ℤ R D ∈ Ideal.span {(2 : R)} := by
        rw [show algebraMap ℤ R D = (2 : R) * (2 * algebraMap ℤ R D₁) by
          rw [hD₁, map_mul, map_ofNat]; ring]
        exact Ideal.mul_mem_right _ _ h2mem
      have hu2 : u ∈ Ideal.span {(2 : R)} := by
        have := Ideal.add_mem (Ideal.span {(2 : R)}) hmemsub hDmem
        rwa [sub_add_cancel] at this
      obtain ⟨u₁, hu₁eq⟩ := Ideal.mem_span_singleton.mp hu2
      have hnatlt : D₁.natAbs < n := by
        have hnat : D.natAbs = 4 * D₁.natAbs := by
          rw [hD₁, Int.natAbs_mul]; norm_num
        omega
      have hu₁K : (u : K) = 2 * (u₁ : K) := by
        rw [hu₁eq]
        change algebraMap (NumberField.RingOfIntegers K) K (2 * u₁)
          = 2 * algebraMap (NumberField.RingOfIntegers K) K u₁
        rw [map_mul, map_ofNat]
      have hu₁ : ((u₁ : K)) ^ 2 = algebraMap ℚ K (D₁ : ℚ) := by
        have hDq : (D : ℚ) = 4 * (D₁ : ℚ) := by rw [hD₁]; push_cast; ring
        have key : (4 : K) * ((u₁ : K)) ^ 2 = (4 : K) * algebraMap ℚ K (D₁ : ℚ) := by
          calc (4 : K) * ((u₁ : K)) ^ 2 = (2 * (u₁ : K)) ^ 2 := by ring
            _ = (u : K) ^ 2 := by rw [hu₁K]
            _ = algebraMap ℚ K (D : ℚ) := hu
            _ = algebraMap ℚ K (4 * (D₁ : ℚ)) := by rw [← hDq]
            _ = (4 : K) * algebraMap ℚ K (D₁ : ℚ) := by rw [map_mul, map_ofNat]
        exact mul_left_cancel₀ (by norm_num : (4 : K) ≠ 0) key
      have hgen₁ : Algebra.adjoin ℚ ({(u₁ : K)} : Set K) = ⊤ := by
        have hsmul1 : algebraMap ℚ K ((2 : ℚ)⁻¹) * (u : K) = (u₁ : K) := by
          rw [map_inv₀, map_ofNat, hu₁K]
          rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : K) ≠ 0), one_mul]
        have hsmul2 : algebraMap ℚ K (2 : ℚ) * (u₁ : K) = (u : K) := by
          rw [map_ofNat, hu₁K]
        have hle1 : Algebra.adjoin ℚ ({(u₁ : K)} : Set K)
            ≤ Algebra.adjoin ℚ ({(u : K)} : Set K) := by
          rw [Algebra.adjoin_le_iff]
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx, ← hsmul1]
          exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
            (Algebra.subset_adjoin (by simp))
        have hle2 : Algebra.adjoin ℚ ({(u : K)} : Set K)
            ≤ Algebra.adjoin ℚ ({(u₁ : K)} : Set K) := by
          rw [Algebra.adjoin_le_iff]
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx, ← hsmul2]
          exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
            (Algebra.subset_adjoin (by simp))
        rw [eq_top_iff, ← hgen]
        exact hle2
      obtain ⟨j₁, D', hD', h2', h8'⟩ := ih D₁.natAbs hnatlt u₁ D₁ rfl hu₁ hgen₁ hD₁ne hsplit
      refine ⟨j₁ + 1, D', ?_, h2', h8'⟩
      rw [hD₁, hD', pow_succ]; ring
    · have h8 : D % 8 = 1 := mod_eight_eq_one_of_odd u D hu hgen h1 hsplit
      exact ⟨0, D, by simp, by omega, h8⟩

end Commons.NumberTheory.NumberField