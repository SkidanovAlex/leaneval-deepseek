import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Submission.Commons.NumberTheory.Moebius.sum_pairwise_divisors_moebius_lcm_cpow
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.Combinatorics.Finset.prod_ite_eq_add_sum_ite

namespace Commons.NumberTheory.Moebius

open scoped BigOperators

private noncomputable def kern (a b : ℂ) (d d' : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((ArithmeticFunction.moebius d' : ℤ) : ℂ) *
    (((Nat.lcm d d').totient : ℂ))⁻¹ * (d : ℂ) ^ (-a) * (d' : ℂ) ^ (-b)

private lemma kern_one_one (a b : ℂ) : kern a b 1 1 = 1 := by
  simp [kern]

private lemma kern_prime_one {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    kern a b p 1 = -((p : ℂ) ^ (-a) * (((p - 1 : ℕ) : ℂ))⁻¹) := by
  simp only [kern, ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
    Nat.lcm_one_right, Nat.cast_one, Int.cast_neg, Int.cast_one, mul_one,
    Complex.one_cpow, Nat.totient_prime hp]
  ring

private lemma kern_one_prime {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    kern a b 1 p = -((p : ℂ) ^ (-b) * (((p - 1 : ℕ) : ℂ))⁻¹) := by
  simp only [kern, ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
    Nat.lcm_one_left, Nat.cast_one, Int.cast_neg, Int.cast_one, mul_one, one_mul,
    Complex.one_cpow, Nat.totient_prime hp]
  ring

private lemma kern_prime_prime {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    kern a b p p = (p : ℂ) ^ (-(a + b)) * (((p - 1 : ℕ) : ℂ))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmain : (p : ℂ) ^ (-a) * (p : ℂ) ^ (-b) = (p : ℂ) ^ (-(a + b)) := by
    rw [← Complex.cpow_add (-a) (-b) hp0, show -a + -b = -(a + b) by ring]
  simp only [kern, ArithmeticFunction.moebius_apply_prime hp, Nat.lcm_self, Int.cast_neg,
    Int.cast_one, Nat.totient_prime hp]
  rw [show ((-1 : ℂ) * -1) = 1 by ring, one_mul, mul_assoc, hmain, mul_comm]

private lemma disj_factor (p a b : ℕ) (h : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a.factorization p ⊓ b.factorization p = 0 := by
  have hg : a.factorization ⊓ b.factorization = 0 := by
    rw [← Nat.factorization_gcd ha hb, h.gcd_eq_one]
    simp
  have := congrFun (congrArg DFunLike.coe hg) p
  simpa using this

private lemma lcm_mul_mul_eq {u u' v v' : ℕ} (hu : u ≠ 0) (hu' : u' ≠ 0) (hv : v ≠ 0)
    (hv' : v' ≠ 0) (huv : u.Coprime v) (huv' : u.Coprime v') (hu'v : u'.Coprime v)
    (hu'v' : u'.Coprime v') :
    Nat.lcm (u * v) (u' * v') = Nat.lcm u u' * Nat.lcm v v' := by
  apply Nat.eq_of_factorization_eq
    (Nat.lcm_ne_zero (Nat.mul_ne_zero hu hv) (Nat.mul_ne_zero hu' hv'))
    (Nat.mul_ne_zero (Nat.lcm_ne_zero hu hu') (Nat.lcm_ne_zero hv hv'))
  intro p
  rw [Nat.factorization_lcm (Nat.mul_ne_zero hu hv) (Nat.mul_ne_zero hu' hv'),
      Nat.factorization_mul hu hv, Nat.factorization_mul hu' hv',
      Nat.factorization_mul (Nat.lcm_ne_zero hu hu') (Nat.lcm_ne_zero hv hv'),
      Nat.factorization_lcm hu hu', Nat.factorization_lcm hv hv']
  simp only [Finsupp.sup_apply, Finsupp.add_apply]
  have d1 := disj_factor p u v huv hu hv
  have d2 := disj_factor p u v' huv' hu hv'
  have d3 := disj_factor p u' v hu'v hu' hv
  have d4 := disj_factor p u' v' hu'v' hu' hv'
  omega

private lemma kern_mul {m n u u' v v' : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n)
    (hu : u ∣ m) (hu' : u' ∣ m) (hv : v ∣ n) (hv' : v' ∣ n) (a b : ℂ) :
    kern a b (u * v) (u' * v') = kern a b u u' * kern a b v v' := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hm (zero_dvd_iff.mp hu)
  have hu0' : u' ≠ 0 := by rintro rfl; exact hm (zero_dvd_iff.mp hu')
  have hv0 : v ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hv)
  have hv0' : v' ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hv')
  have huv : u.Coprime v := (hmn.coprime_dvd_left hu).coprime_dvd_right hv
  have huv' : u.Coprime v' := (hmn.coprime_dvd_left hu).coprime_dvd_right hv'
  have hu'v : u'.Coprime v := (hmn.coprime_dvd_left hu').coprime_dvd_right hv
  have hu'v' : u'.Coprime v' := (hmn.coprime_dvd_left hu').coprime_dvd_right hv'
  have hmu1 : ((ArithmeticFunction.moebius (u * v) : ℤ) : ℂ) =
      ((ArithmeticFunction.moebius u : ℤ) : ℂ) * ((ArithmeticFunction.moebius v : ℤ) : ℂ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime huv]; push_cast; ring
  have hmu2 : ((ArithmeticFunction.moebius (u' * v') : ℤ) : ℂ) =
      ((ArithmeticFunction.moebius u' : ℤ) : ℂ) * ((ArithmeticFunction.moebius v' : ℤ) : ℂ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hu'v']; push_cast; ring
  have hlc : Nat.lcm (u * v) (u' * v') = Nat.lcm u u' * Nat.lcm v v' :=
    lcm_mul_mul_eq hu0 hu0' hv0 hv0' huv huv' hu'v hu'v'
  have hcop_lcm : (Nat.lcm u u').Coprime (Nat.lcm v v') :=
    (hmn.coprime_dvd_left (Nat.lcm_dvd hu hu')).coprime_dvd_right (Nat.lcm_dvd hv hv')
  have htot : (Nat.lcm (u * v) (u' * v')).totient
      = (Nat.lcm u u').totient * (Nat.lcm v v').totient := by
    rw [hlc, Nat.totient_mul hcop_lcm]
  have htv : (((Nat.lcm (u * v) (u' * v')).totient : ℂ))⁻¹
      = (((Nat.lcm u u').totient : ℂ))⁻¹ * (((Nat.lcm v v').totient : ℂ))⁻¹ := by
    rw [htot, Nat.cast_mul, mul_inv]
  have hcu : ((u * v : ℕ) : ℂ) ^ (-a) = (u : ℂ) ^ (-a) * (v : ℂ) ^ (-a) := by
    rw [show ((u * v : ℕ) : ℂ) = (u : ℂ) * (v : ℂ) by push_cast; ring]
    exact Complex.natCast_mul_natCast_cpow u v (-a)
  have hcv : ((u' * v' : ℕ) : ℂ) ^ (-b) = (u' : ℂ) ^ (-b) * (v' : ℂ) ^ (-b) := by
    rw [show ((u' * v' : ℕ) : ℂ) = (u' : ℂ) * (v' : ℂ) by push_cast; ring]
    exact Complex.natCast_mul_natCast_cpow u' v' (-b)
  simp only [kern]
  rw [hmu1, hmu2, htv, hcu, hcv]
  ring_nf

private noncomputable def Vset {k : ℕ} (m : ℕ) : Finset (Fin k → ℕ × ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => m.divisors ×ˢ m.divisors)).filter
    (fun x => ∀ i j : Fin k, i ≠ j →
      (Nat.lcm (x i).1 (x i).2).Coprime (Nat.lcm (x j).1 (x j).2))

private noncomputable def G {k : ℕ} (a b : Fin k → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ Vset m, ∏ j : Fin k, kern (a j) (b j) (x j).1 (x j).2

/-- Split a pair by coprime moduli: `(α, γ) ↦ (α₁γ₁, α₂γ₂)`. -/
private def PhiFn {k : ℕ} (z : (Fin k → ℕ × ℕ) × (Fin k → ℕ × ℕ)) : Fin k → ℕ × ℕ :=
  fun j => ((z.1 j).1 * (z.2 j).1, (z.1 j).2 * (z.2 j).2)

/-- The inverse of `PhiFn`: take gcd with `M` resp. `N` coordinatewise. -/
private def InvFn {k : ℕ} (M N : ℕ) (x : Fin k → ℕ × ℕ) :
    (Fin k → ℕ × ℕ) × (Fin k → ℕ × ℕ) :=
  (fun j => ((x j).1.gcd M, (x j).2.gcd M), fun j => ((x j).1.gcd N, (x j).2.gcd N))

private lemma coprime_mul_mul {p q r s : ℕ} (hpr : p.Coprime r) (hps : p.Coprime s)
    (hqr : q.Coprime r) (hqs : q.Coprime s) : (p * q).Coprime (r * s) :=
  Nat.Coprime.mul_left (hpr.mul_right hps) (hqr.mul_right hqs)

private lemma lcm_gcd_dvd (M a b : ℕ) :
    Nat.lcm (a.gcd M) (b.gcd M) ∣ Nat.lcm a b :=
  Nat.lcm_dvd (dvd_trans (Nat.gcd_dvd_left a M) (Nat.dvd_lcm_left a b))
              (dvd_trans (Nat.gcd_dvd_left b M) (Nat.dvd_lcm_right a b))

private lemma lcm_pair_split {M N : ℕ} (hMN : M.Coprime N) (hM : M ≠ 0) (hN : N ≠ 0)
    {a a' c c' : ℕ} (ha : a ∣ M) (ha' : a' ∣ M) (hc : c ∣ N) (hc' : c' ∣ N) :
    Nat.lcm (a * c) (a' * c') = Nat.lcm a a' * Nat.lcm c c' := by
  have ha0 : a ≠ 0 := by rintro rfl; exact hM (zero_dvd_iff.mp ha)
  have ha0' : a' ≠ 0 := by rintro rfl; exact hM (zero_dvd_iff.mp ha')
  have hc0 : c ≠ 0 := by rintro rfl; exact hN (zero_dvd_iff.mp hc)
  have hc0' : c' ≠ 0 := by rintro rfl; exact hN (zero_dvd_iff.mp hc')
  exact lcm_mul_mul_eq ha0 ha0' hc0 hc0'
    ((hMN.coprime_dvd_left ha).coprime_dvd_right hc)
    ((hMN.coprime_dvd_left ha).coprime_dvd_right hc')
    ((hMN.coprime_dvd_left ha').coprime_dvd_right hc)
    ((hMN.coprime_dvd_left ha').coprime_dvd_right hc')

private lemma G_mul {k : ℕ} (a b : Fin k → ℂ) {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (hMN : M.Coprime N) : G a b (M * N) = G a b M * G a b N := by
  rw [G, G, G, Finset.sum_mul_sum]
  rw [← Finset.sum_product (Vset M) (Vset N)
    (fun z => (∏ j : Fin k, kern (a j) (b j) (z.1 j).1 (z.1 j).2) *
              (∏ j : Fin k, kern (a j) (b j) (z.2 j).1 (z.2 j).2))]
  refine Finset.sum_bij' (fun x _ => InvFn M N x) (fun z _ => PhiFn z) ?_ ?_ ?_ ?_ ?_
  · -- hi
    intro x hx
    rw [Vset, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hxpi, hxcond⟩ := hx
    rw [Finset.mem_product]
    constructor
    · rw [Vset, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, fun i j hij => ?_⟩
      · exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hM⟩,
            Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hM⟩⟩
      · exact ((hxcond i j hij).coprime_dvd_left (lcm_gcd_dvd M (x i).1 (x i).2)).coprime_dvd_right
          (lcm_gcd_dvd M (x j).1 (x j).2)
    · rw [Vset, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, fun i j hij => ?_⟩
      · exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hN⟩,
            Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hN⟩⟩
      · exact ((hxcond i j hij).coprime_dvd_left (lcm_gcd_dvd N (x i).1 (x i).2)).coprime_dvd_right
          (lcm_gcd_dvd N (x j).1 (x j).2)
  · -- hj
    intro z hz
    rw [Finset.mem_product] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Vset, Finset.mem_filter, Fintype.mem_piFinset] at hz1 hz2
    obtain ⟨hz1pi, hz1cond⟩ := hz1
    obtain ⟨hz2pi, hz2cond⟩ := hz2
    rw [Vset, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => ?_, fun i j hij => ?_⟩
    · have h1 := Finset.mem_product.mp (hz1pi j)
      have h2 := Finset.mem_product.mp (hz2pi j)
      exact Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr
            ⟨mul_dvd_mul (Nat.dvd_of_mem_divisors h1.1) (Nat.dvd_of_mem_divisors h2.1),
             mul_ne_zero hM hN⟩,
         Nat.mem_divisors.mpr
            ⟨mul_dvd_mul (Nat.dvd_of_mem_divisors h1.2) (Nat.dvd_of_mem_divisors h2.2),
             mul_ne_zero hM hN⟩⟩
    · have h1i := Finset.mem_product.mp (hz1pi i)
      have h2i := Finset.mem_product.mp (hz2pi i)
      have h1j := Finset.mem_product.mp (hz1pi j)
      have h2j := Finset.mem_product.mp (hz2pi j)
      simp only [PhiFn]
      rw [lcm_pair_split hMN hM hN (Nat.dvd_of_mem_divisors h1i.1) (Nat.dvd_of_mem_divisors h1i.2)
            (Nat.dvd_of_mem_divisors h2i.1) (Nat.dvd_of_mem_divisors h2i.2),
          lcm_pair_split hMN hM hN (Nat.dvd_of_mem_divisors h1j.1) (Nat.dvd_of_mem_divisors h1j.2)
            (Nat.dvd_of_mem_divisors h2j.1) (Nat.dvd_of_mem_divisors h2j.2)]
      exact coprime_mul_mul (hz1cond i j hij)
        ((hMN.coprime_dvd_left (Nat.lcm_dvd (Nat.dvd_of_mem_divisors h1i.1) (Nat.dvd_of_mem_divisors h1i.2))).coprime_dvd_right
          (Nat.lcm_dvd (Nat.dvd_of_mem_divisors h2j.1) (Nat.dvd_of_mem_divisors h2j.2)))
        ((hMN.symm.coprime_dvd_left (Nat.lcm_dvd (Nat.dvd_of_mem_divisors h2i.1) (Nat.dvd_of_mem_divisors h2i.2))).coprime_dvd_right
          (Nat.lcm_dvd (Nat.dvd_of_mem_divisors h1j.1) (Nat.dvd_of_mem_divisors h1j.2)))
        (hz2cond i j hij)
  · -- left_inv
    intro x hx
    rw [Vset, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hxpi, _⟩ := hx
    funext j
    have hmem := Finset.mem_product.mp (hxpi j)
    have hw1 : (x j).1 ∣ M * N := Nat.dvd_of_mem_divisors hmem.1
    have hw2 : (x j).2 ∣ M * N := Nat.dvd_of_mem_divisors hmem.2
    have e1 : (x j).1.gcd M * (x j).1.gcd N = (x j).1 := by
      rw [← hMN.gcd_mul ((x j).1), (Nat.gcd_eq_left_iff_dvd).mpr hw1]
    have e2 : (x j).2.gcd M * (x j).2.gcd N = (x j).2 := by
      rw [← hMN.gcd_mul ((x j).2), (Nat.gcd_eq_left_iff_dvd).mpr hw2]
    simp only [PhiFn, InvFn]
    exact Prod.ext e1 e2
  · -- right_inv
    intro z hz
    rw [Finset.mem_product] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Vset, Finset.mem_filter, Fintype.mem_piFinset] at hz1 hz2
    obtain ⟨hz1pi, _⟩ := hz1
    obtain ⟨hz2pi, _⟩ := hz2
    apply Prod.ext
    · funext j
      have h1 := Finset.mem_product.mp (hz1pi j)
      have h2 := Finset.mem_product.mp (hz2pi j)
      have d1 : (z.1 j).1 ∣ M := Nat.dvd_of_mem_divisors h1.1
      have d1' : (z.1 j).2 ∣ M := Nat.dvd_of_mem_divisors h1.2
      have d2 : (z.2 j).1 ∣ N := Nat.dvd_of_mem_divisors h2.1
      have d2' : (z.2 j).2 ∣ N := Nat.dvd_of_mem_divisors h2.2
      have c1 : ((z.2 j).1).Coprime M := (hMN.symm.coprime_dvd_left d2)
      have c1' : ((z.2 j).2).Coprime M := (hMN.symm.coprime_dvd_left d2')
      have c2 : ((z.1 j).1).Coprime N := (hMN.coprime_dvd_left d1)
      have c2' : ((z.1 j).2).Coprime N := (hMN.coprime_dvd_left d1')
      have e1 : ((z.1 j).1 * (z.2 j).1).gcd M = (z.1 j).1 := by
        rw [mul_comm (z.1 j).1 (z.2 j).1]; exact Nat.gcd_mul_of_coprime_of_dvd c1 d1
      have e1' : ((z.1 j).2 * (z.2 j).2).gcd M = (z.1 j).2 := by
        rw [mul_comm (z.1 j).2 (z.2 j).2]; exact Nat.gcd_mul_of_coprime_of_dvd c1' d1'
      simp only [InvFn, PhiFn]
      exact Prod.ext e1 e1'
    · funext j
      have h1 := Finset.mem_product.mp (hz1pi j)
      have h2 := Finset.mem_product.mp (hz2pi j)
      have d1 : (z.1 j).1 ∣ M := Nat.dvd_of_mem_divisors h1.1
      have d1' : (z.1 j).2 ∣ M := Nat.dvd_of_mem_divisors h1.2
      have d2 : (z.2 j).1 ∣ N := Nat.dvd_of_mem_divisors h2.1
      have d2' : (z.2 j).2 ∣ N := Nat.dvd_of_mem_divisors h2.2
      have c2 : ((z.1 j).1).Coprime N := (hMN.coprime_dvd_left d1)
      have c2' : ((z.1 j).2).Coprime N := (hMN.coprime_dvd_left d1')
      have e2 : ((z.1 j).1 * (z.2 j).1).gcd N = (z.2 j).1 :=
        Nat.gcd_mul_of_coprime_of_dvd c2 d2
      have e2' : ((z.1 j).2 * (z.2 j).2).gcd N = (z.2 j).2 :=
        Nat.gcd_mul_of_coprime_of_dvd c2' d2'
      simp only [InvFn, PhiFn]
      exact Prod.ext e2 e2'
  · -- h
    intro x hx
    rw [Vset, Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hxpi, _⟩ := hx
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hmem := Finset.mem_product.mp (hxpi j)
    have hw1 : (x j).1 ∣ M * N := Nat.dvd_of_mem_divisors hmem.1
    have hw2 : (x j).2 ∣ M * N := Nat.dvd_of_mem_divisors hmem.2
    have e1 : (x j).1.gcd M * (x j).1.gcd N = (x j).1 := by
      rw [← hMN.gcd_mul ((x j).1), (Nat.gcd_eq_left_iff_dvd).mpr hw1]
    have e2 : (x j).2.gcd M * (x j).2.gcd N = (x j).2 := by
      rw [← hMN.gcd_mul ((x j).2), (Nat.gcd_eq_left_iff_dvd).mpr hw2]
    simp only [InvFn]
    rw [← kern_mul hM hN hMN (Nat.gcd_dvd_right (x j).1 M) (Nat.gcd_dvd_right (x j).2 M)
          (Nat.gcd_dvd_right (x j).1 N) (Nat.gcd_dvd_right (x j).2 N), e1, e2]

private lemma prime_comp1 {p : ℕ} (hp : p.Prime) {z : ℕ × ℕ}
    (hz : z ∈ p.divisors ×ˢ p.divisors) : z.1 = 1 ∨ z.1 = p := by
  have h := (Finset.mem_product.mp hz).1
  rw [Nat.Prime.divisors hp, Finset.mem_insert, Finset.mem_singleton] at h
  exact h

private lemma prime_comp2 {p : ℕ} (hp : p.Prime) {z : ℕ × ℕ}
    (hz : z ∈ p.divisors ×ˢ p.divisors) : z.2 = 1 ∨ z.2 = p := by
  have h := (Finset.mem_product.mp hz).2
  rw [Nat.Prime.divisors hp, Finset.mem_insert, Finset.mem_singleton] at h
  exact h

private lemma lcm_pair_mem {p : ℕ} (hp : p.Prime) {z : ℕ × ℕ}
    (hz : z ∈ p.divisors ×ˢ p.divisors) : Nat.lcm z.1 z.2 = 1 ∨ Nat.lcm z.1 z.2 = p := by
  rcases prime_comp1 hp hz with h1 | h1 <;> rcases prime_comp2 hp hz with h2 | h2
  · left; simp [h1, h2]
  · right; simp [h1, h2]
  · right; simp [h1, h2]
  · right; simp [h1, h2]

private lemma lcm_pair_iff {p : ℕ} (hp : p.Prime) {z : ℕ × ℕ}
    (hz : z ∈ p.divisors ×ˢ p.divisors) : Nat.lcm z.1 z.2 = p ↔ z ≠ (1, 1) := by
  constructor
  · intro h hz1
    rw [hz1] at h
    simp [Nat.lcm] at h
    exact hp.ne_one h.symm
  · intro hz1
    rcases prime_comp1 hp hz with h1 | h1 <;> rcases prime_comp2 hp hz with h2 | h2
    · exact absurd (Prod.ext h1 h2) hz1
    · rw [h1, h2]; simp
    · rw [h1, h2]; simp
    · rw [h1, h2]; simp

private lemma coprime_two_iff {p u v : ℕ} (hp : p.Prime) (hu : u = 1 ∨ u = p)
    (hv : v = 1 ∨ v = p) : u.Coprime v ↔ ¬(u = p ∧ v = p) := by
  have h1p : (1 : ℕ) ≠ p := ne_of_lt hp.one_lt
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    rw [hu, hv] <;> simp [Nat.Coprime, Nat.gcd_self, hp.ne_one, h1p]

private lemma coprime_lcm_pair {p : ℕ} (hp : p.Prime) {z w : ℕ × ℕ}
    (hz : z ∈ p.divisors ×ˢ p.divisors) (hw : w ∈ p.divisors ×ˢ p.divisors) :
    (Nat.lcm z.1 z.2).Coprime (Nat.lcm w.1 w.2) ↔ ¬(z ≠ (1, 1) ∧ w ≠ (1, 1)) := by
  rw [coprime_two_iff hp (lcm_pair_mem hp hz) (lcm_pair_mem hp hw),
    lcm_pair_iff hp hz, lcm_pair_iff hp hw]

private lemma pairCond_iff_card {k : ℕ} {p : ℕ} (hp : p.Prime) {x : Fin k → ℕ × ℕ}
    (hx : x ∈ Fintype.piFinset (fun _ : Fin k => p.divisors ×ˢ p.divisors)) :
    (∀ i j : Fin k, i ≠ j →
        (Nat.lcm (x i).1 (x i).2).Coprime (Nat.lcm (x j).1 (x j).2))
      ↔ (Finset.univ.filter (fun j => x j ≠ (1, 1))).card ≤ 1 := by
  have hxmem : ∀ j : Fin k, x j ∈ p.divisors ×ˢ p.divisors := Fintype.mem_piFinset.mp hx
  rw [Finset.card_le_one]
  constructor
  · intro h a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact (coprime_lcm_pair hp (hxmem a) (hxmem b)).mp (h a b hab) ⟨ha.2, hb.2⟩
  · intro h i j hij
    rw [coprime_lcm_pair hp (hxmem i) (hxmem j)]
    rintro ⟨hi1, hj1⟩
    exact hij (h i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi1⟩) j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1⟩))

private lemma sum_pair_kern {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    (∑ v ∈ p.divisors ×ˢ p.divisors, kern a b v.1 v.2)
      = kern a b 1 1 + kern a b 1 p + kern a b p 1 + kern a b p p := by
  rw [Nat.Prime.divisors hp, Finset.sum_product,
    Finset.sum_pair (ne_of_lt hp.one_lt), Finset.sum_pair (ne_of_lt hp.one_lt),
    Finset.sum_pair (ne_of_lt hp.one_lt)]
  ring

private lemma sum_erase_kern {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    (∑ v ∈ (p.divisors ×ˢ p.divisors).erase (1, 1), kern a b v.1 v.2)
      = kern a b p 1 + kern a b 1 p + kern a b p p := by
  have hmem : (1, 1) ∈ p.divisors ×ˢ p.divisors := by
    rw [Nat.Prime.divisors hp]
    exact Finset.mem_product.mpr ⟨by simp, by simp⟩
  rw [Finset.sum_erase_eq_sub hmem, sum_pair_kern hp a b, kern_one_one]
  ring

private lemma sum_piFinset_card_le_one_local {k : ℕ} {S : Finset (ℕ × ℕ)} {o : ℕ × ℕ}
    (ho : o ∈ S) (f : Fin k → ℕ × ℕ → ℂ) :
    (∑ x ∈ (Fintype.piFinset (fun _ : Fin k => S)).filter
        (fun x => (Finset.univ.filter (fun j => x j ≠ o)).card ≤ 1),
      ∏ j : Fin k, f j (x j))
      = (∏ j, f j o) + ∑ i : Fin k, (∑ v ∈ S.erase o, f i v) *
          (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j o) := by
  classical
  rw [Finset.sum_filter]
  have key1 : ∀ x : Fin k → ℕ × ℕ,
      (if (Finset.univ.filter (fun j => x j ≠ o)).card ≤ 1
        then ∏ j : Fin k, f j (x j) else 0)
      = (∏ j, (if x j = o then (1 : ℂ) else 0)) * (∏ j : Fin k, f j (x j))
        + (∑ i, (if x i = o then (0 : ℂ) else 1) *
              (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : ℂ) else 0)))
          * (∏ j : Fin k, f j (x j)) := by
    intro x
    have h1 : (if (Finset.univ.filter (fun j => x j ≠ o)).card ≤ 1
          then ∏ j : Fin k, f j (x j) else 0)
        = (if (Finset.univ.filter (fun j => x j ≠ o)).card ≤ 1 then (1 : ℂ) else 0)
          * (∏ j : Fin k, f j (x j)) := by
      by_cases h : (Finset.univ.filter (fun j => x j ≠ o)).card ≤ 1 <;> simp [h]
    rw [h1, ← Commons.Combinatorics.Finset.prod_ite_eq_add_sum_ite (R := ℂ) x o, add_mul]
  rw [Finset.sum_congr rfl (fun x _ => key1 x), Finset.sum_add_distrib]
  have hI : (∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
        (∏ j, (if x j = o then (1 : ℂ) else 0)) * (∏ j : Fin k, f j (x j))) = ∏ j, f j o := by
    have e : (∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
          (∏ j, (if x j = o then (1 : ℂ) else 0)) * (∏ j : Fin k, f j (x j)))
        = ∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
            ∏ j, (if x j = o then (1 : ℂ) else 0) * f j (x j) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    rw [e, Finset.sum_prod_piFinset S (fun j v => (if v = o then (1 : ℂ) else 0) * f j v)]
    apply Finset.prod_congr rfl
    intro j _
    have e3 : (∑ v ∈ S, (if v = o then (1 : ℂ) else 0) * f j v)
        = ∑ v ∈ S, (if v = o then f j v else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v = o <;> simp [hv]
    rw [e3, Finset.sum_ite_eq' S o (fun v => f j v), if_pos ho]
  have hII : (∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
        (∑ i, (if x i = o then (0 : ℂ) else 1) *
              (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : ℂ) else 0)))
            * (∏ j : Fin k, f j (x j)))
      = ∑ i : Fin k, (∑ v ∈ S.erase o, f i v) *
          (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j o) := by
    have e : (∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
          (∑ i, (if x i = o then (0 : ℂ) else 1) *
                (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : ℂ) else 0)))
              * (∏ j : Fin k, f j (x j)))
        = ∑ i : Fin k, ∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
            ((if x i = o then (0 : ℂ) else 1) *
                (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : ℂ) else 0)))
              * (∏ j : Fin k, f j (x j)) := by
      rw [Finset.sum_congr rfl (fun x _ => Finset.sum_mul Finset.univ
        (fun i => (if x i = o then (0 : ℂ) else 1) *
          (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : ℂ) else 0)))
        (∏ j : Fin k, f j (x j)))]
      rw [Finset.sum_comm]
    rw [e]
    apply Finset.sum_congr rfl
    intro i _
    have e2 : (∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
            ((if x i = o then (0 : ℂ) else 1) *
                (∏ j ∈ Finset.univ.erase i, (if x j = o then (1 : ℂ) else 0)))
              * (∏ j : Fin k, f j (x j)))
        = ∑ x ∈ Fintype.piFinset (fun _ : Fin k => S),
            ∏ j, (if j = i then (if x j = o then (0 : ℂ) else 1) * f j (x j)
                     else (if x j = o then (1 : ℂ) else 0) * f j (x j)) := by
      apply Finset.sum_congr rfl
      intro x _
      have hP2 : (∏ j : Fin k, f j (x j))
          = f i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j) :=
        (Finset.mul_prod_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)).symm
      have hsplit : (∏ j : Fin k, (if j = i then (if x j = o then (0 : ℂ) else 1) * f j (x j)
              else (if x j = o then (1 : ℂ) else 0) * f j (x j)))
          = ((if x i = o then (0 : ℂ) else 1) * f i (x i))
            * ∏ j ∈ Finset.univ.erase i, ((if x j = o then (1 : ℂ) else 0) * f j (x j)) := by
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => (if j = i then (if x j = o then (0 : ℂ) else 1) * f j (x j)
                     else (if x j = o then (1 : ℂ) else 0) * f j (x j)))
          (Finset.mem_univ i)]
        rw [if_pos rfl]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_erase] at hj
        exact if_neg hj.1
      rw [hP2, hsplit, Finset.prod_mul_distrib]
      ring
    rw [e2, Finset.sum_prod_piFinset S (fun j v => if j = i then (if v = o then (0 : ℂ) else 1) * f j v
        else (if v = o then (1 : ℂ) else 0) * f j v)]
    have hsum_i : (∑ v ∈ S, (if i = i then (if v = o then (0 : ℂ) else 1) * f i v
        else (if v = o then (1 : ℂ) else 0) * f i v)) = ∑ v ∈ S.erase o, f i v := by
      have t1 : (∑ v ∈ S, (if i = i then (if v = o then (0 : ℂ) else 1) * f i v
            else (if v = o then (1 : ℂ) else 0) * f i v))
          = ∑ v ∈ S, (if v = o then (0 : ℂ) else 1) * f i v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [if_pos rfl]
      have t2 : (∑ v ∈ S, (if v = o then (0 : ℂ) else 1) * f i v)
          = ∑ v ∈ S, (if v = o then (0 : ℂ) else f i v) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v = o <;> simp [hv]
      rw [t1, t2,
        ← Finset.sum_erase (s := S) (f := fun v => if v = o then (0 : ℂ) else f i v)
          (a := o) (by simp)]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mem_erase] at hv
      rw [if_neg hv.1]
    have hsum_j : ∀ j, j ≠ i → (∑ v ∈ S, (if j = i then (if v = o then (0 : ℂ) else 1) * f j v
            else (if v = o then (1 : ℂ) else 0) * f j v)) = f j o := by
      intro j hji
      have t1 : (∑ v ∈ S, (if j = i then (if v = o then (0 : ℂ) else 1) * f j v
            else (if v = o then (1 : ℂ) else 0) * f j v))
          = ∑ v ∈ S, (if v = o then (1 : ℂ) else 0) * f j v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [if_neg hji]
      have t2 : (∑ v ∈ S, (if v = o then (1 : ℂ) else 0) * f j v)
          = ∑ v ∈ S, (if v = o then f j v else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v = o <;> simp [hv]
      rw [t1, t2, Finset.sum_ite_eq' S o (fun v => f j v), if_pos ho]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => ∑ v ∈ S, (if j = i then (if v = o then (0 : ℂ) else 1) * f j v
        else (if v = o then (1 : ℂ) else 0) * f j v)) (Finset.mem_univ i), hsum_i]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_erase] at hj
    exact hsum_j j hj.1
  rw [hI, hII]

private lemma G_prime {k : ℕ} (a b : Fin k → ℂ) {p : ℕ} (hp : p.Prime) :
    G a b p = 1 + ∑ j : Fin k,
      (kern (a j) (b j) p 1 + kern (a j) (b j) 1 p + kern (a j) (b j) p p) := by
  classical
  rw [G]
  have hV : Vset p = (Fintype.piFinset (fun _ : Fin k => p.divisors ×ˢ p.divisors)).filter
      (fun x => (Finset.univ.filter (fun j => x j ≠ (1, 1))).card ≤ 1) := by
    ext x
    simp only [Vset, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hcond⟩
      exact ⟨hx, (pairCond_iff_card hp hx).mp hcond⟩
    · rintro ⟨hx, hcond⟩
      exact ⟨hx, (pairCond_iff_card hp hx).mpr hcond⟩
  rw [hV, sum_piFinset_card_le_one_local
    (Finset.mem_product.mpr ⟨Nat.one_mem_divisors.mpr hp.ne_zero,
      Nat.one_mem_divisors.mpr hp.ne_zero⟩) (fun j v => kern (a j) (b j) v.1 v.2)]
  have h1 : (∏ j : Fin k, kern (a j) (b j) 1 1) = 1 := by
    simp only [kern_one_one, Finset.prod_const_one]
  have h2 : ∀ i : Fin k, (∑ v ∈ (p.divisors ×ˢ p.divisors).erase (1, 1),
        kern (a i) (b i) v.1 v.2)
      * (∏ j ∈ Finset.univ.erase i, kern (a j) (b j) 1 1)
      = kern (a i) (b i) p 1 + kern (a i) (b i) 1 p + kern (a i) (b i) p p := by
    intro i
    rw [sum_erase_kern hp (a i) (b i)]
    simp only [kern_one_one, Finset.prod_const_one, mul_one]
  rw [h1, Finset.sum_congr rfl (fun i _ => h2 i)]

private lemma G_one {k : ℕ} (a b : Fin k → ℂ) : G a b 1 = 1 := by
  rw [G]
  have hV : Vset (1 : ℕ) = {fun _ : Fin k => (1, 1)} := by
    ext x
    constructor
    · intro hx
      rw [Vset, Finset.mem_filter, Fintype.mem_piFinset] at hx
      rw [Finset.mem_singleton]
      funext j
      have h := Finset.mem_product.mp (hx.1 j)
      rw [Nat.divisors_one] at h
      exact Prod.ext (Finset.mem_singleton.mp h.1) (Finset.mem_singleton.mp h.2)
    · intro hx
      rw [Finset.mem_singleton] at hx
      rw [hx, Vset, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, fun i j _ => ?_⟩
      · rw [Nat.divisors_one]
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr rfl, Finset.mem_singleton.mpr rfl⟩
      · simp [Nat.lcm]
  rw [hV, Finset.sum_singleton]
  simp [kern_one_one]

private lemma G_prod_of_pairwise {k : ℕ} (a b : Fin k → ℂ) (s : Finset ℕ)
    (hpos : ∀ p ∈ s, 0 < p) (h : (s : Set ℕ).Pairwise Nat.Coprime) :
    G a b (∏ p ∈ s, p) = ∏ p ∈ s, G a b p := by
  revert hpos h
  refine Finset.induction_on s ?_ ?_
  · intro hpos h
    simp only [Finset.prod_empty]
    exact G_one a b
  · intro p t hpt ih hpos h
    rw [Finset.prod_insert hpt, Finset.prod_insert hpt]
    simp only [Finset.coe_insert, Set.pairwise_insert] at h
    obtain ⟨ht, hpall⟩ := h
    have hpt0 : ∀ q ∈ t, 0 < q := fun q hq => hpos q (Finset.mem_insert_of_mem hq)
    have hp0 : p ≠ 0 := (hpos p (Finset.mem_insert_self p t)).ne'
    have ht0 : (∏ q ∈ t, q) ≠ 0 := (Finset.prod_pos hpt0).ne'
    have hcop : p.Coprime (∏ q ∈ t, q) :=
      Nat.Coprime.prod_right fun q hq => (hpall q hq (fun hpq => hpt (hpq ▸ hq))).1
    rw [G_mul a b hp0 ht0 hcop, ih hpt0 ht]

theorem sum_pairwise_divisors_moebius_totient_lcm_cpow (m : ℕ) (hm : Squarefree m) (k : ℕ)
    (a b : Fin k → ℂ) :
    (∑ x ∈ (Fintype.piFinset (fun _ : Fin k => m.divisors ×ˢ m.divisors)).filter
        (fun x => ∀ i j : Fin k, i ≠ j →
          (Nat.lcm (x i).1 (x i).2).Coprime (Nat.lcm (x j).1 (x j).2)),
      ∏ j : Fin k,
        (((ArithmeticFunction.moebius (x j).1 : ℤ) : ℂ) *
          ((ArithmeticFunction.moebius (x j).2 : ℤ) : ℂ) *
          (((Nat.lcm (x j).1 (x j).2).totient : ℂ))⁻¹ * ((x j).1 : ℂ) ^ (-(a j)) *
          ((x j).2 : ℂ) ^ (-(b j))))
      = ∏ p ∈ m.primeFactors,
          (1 + ∑ j : Fin k, (-(((p : ℂ) ^ (-(a j))) * (((p - 1 : ℕ) : ℂ))⁻¹) -
            (((p : ℂ) ^ (-(b j))) * (((p - 1 : ℕ) : ℂ))⁻¹) +
            (((p : ℂ) ^ (-(a j + b j))) * (((p - 1 : ℕ) : ℂ))⁻¹))) := by
  change G a b m = ∏ p ∈ m.primeFactors,
    (1 + ∑ j : Fin k, (-(((p : ℂ) ^ (-(a j))) * (((p - 1 : ℕ) : ℂ))⁻¹) -
      (((p : ℂ) ^ (-(b j))) * (((p - 1 : ℕ) : ℂ))⁻¹) +
      (((p : ℂ) ^ (-(a j + b j))) * (((p - 1 : ℕ) : ℂ))⁻¹)))
  have hpair : (m.primeFactors : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
    rw [hpp.coprime_iff_not_dvd]
    intro hdvd
    exact hpq ((hqp.dvd_iff_eq hpp.ne_one).mp hdvd).symm
  have hpos : ∀ p ∈ m.primeFactors, 0 < p := fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
  have hprod := G_prod_of_pairwise a b m.primeFactors hpos hpair
  rw [Nat.prod_primeFactors_of_squarefree hm] at hprod
  rw [hprod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [G_prime a b (Nat.mem_primeFactors.mp hp).1]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [kern_prime_one (Nat.mem_primeFactors.mp hp).1 (a j) (b j),
    kern_one_prime (Nat.mem_primeFactors.mp hp).1 (a j) (b j),
    kern_prime_prime (Nat.mem_primeFactors.mp hp).1 (a j) (b j)]
  ring

end Commons.NumberTheory.Moebius
