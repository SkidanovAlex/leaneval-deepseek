import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.Moebius.sum_divisors_moebius_lcm_cpow

namespace Commons.NumberTheory.Moebius

open scoped BigOperators

private noncomputable def kernφ (a b : ℂ) (d d' : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((ArithmeticFunction.moebius d' : ℤ) : ℂ) *
    (((Nat.lcm d d').totient : ℂ))⁻¹ * (d : ℂ) ^ (-a) * (d' : ℂ) ^ (-b)

private noncomputable def Fsumφ (a b : ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ m.divisors, ∑ d' ∈ m.divisors, kernφ a b d d'

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

private lemma kernφ_mul {m n u u' v v' : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n)
    (hu : u ∣ m) (hu' : u' ∣ m) (hv : v ∣ n) (hv' : v' ∣ n) (a b : ℂ) :
    kernφ a b (u * v) (u' * v') = kernφ a b u u' * kernφ a b v v' := by
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
  have hA : Nat.lcm u u' ∣ m := Nat.lcm_dvd hu hu'
  have hB : Nat.lcm v v' ∣ n := Nat.lcm_dvd hv hv'
  have hcopAB : Nat.Coprime (Nat.lcm u u') (Nat.lcm v v') :=
    (hmn.coprime_dvd_left hA).coprime_dvd_right hB
  have hφ_split : (((Nat.lcm (u * v) (u' * v')).totient : ℕ) : ℂ)⁻¹ =
      (((Nat.lcm u u').totient : ℕ) : ℂ)⁻¹ * (((Nat.lcm v v').totient : ℕ) : ℂ)⁻¹ := by
    rw [hlc, Nat.totient_mul hcopAB, Nat.cast_mul, mul_inv]
  have hcu : ((u * v : ℕ) : ℂ) ^ (-a) = (u : ℂ) ^ (-a) * (v : ℂ) ^ (-a) := by
    rw [show ((u * v : ℕ) : ℂ) = (u : ℂ) * (v : ℂ) by push_cast; ring]
    exact Complex.natCast_mul_natCast_cpow u v (-a)
  have hcv : ((u' * v' : ℕ) : ℂ) ^ (-b) = (u' : ℂ) ^ (-b) * (v' : ℂ) ^ (-b) := by
    rw [show ((u' * v' : ℕ) : ℂ) = (u' : ℂ) * (v' : ℂ) by push_cast; ring]
    exact Complex.natCast_mul_natCast_cpow u' v' (-b)
  simp only [kernφ]
  rw [hmu1, hmu2, hφ_split, hcu, hcv]
  ring_nf

private lemma sum_divisors_mul_coprime {m n : ℕ} (hmn : m.Coprime n) (f : ℕ → ℂ) :
    ∑ d ∈ (m * n).divisors, f d = ∑ u ∈ m.divisors, ∑ v ∈ n.divisors, f (u * v) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image (hmn.mul_injOn_divisors)]
  rw [Finset.sum_product]

private lemma prod_double_sum_eq (s t : Finset ℕ) (f g : ℕ → ℕ → ℂ) :
    (∑ i ∈ s, ∑ i' ∈ s, f i i') * (∑ j ∈ t, ∑ j' ∈ t, g j j')
      = ∑ i ∈ s, ∑ i' ∈ s, ∑ j ∈ t, ∑ j' ∈ t, f i i' * g j j' := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.sum_mul_sum]

private lemma Fsumφ_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) (a b : ℂ) :
    Fsumφ a b (m * n) = Fsumφ a b m * Fsumφ a b n := by
  have h1 : Fsumφ a b (m * n) =
      ∑ u ∈ m.divisors, ∑ v ∈ n.divisors, ∑ u' ∈ m.divisors, ∑ v' ∈ n.divisors,
        kernφ a b (u * v) (u' * v') := by
    simp only [Fsumφ]
    rw [sum_divisors_mul_coprime hmn]
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    rw [sum_divisors_mul_coprime hmn]
  have h2 : (∑ u ∈ m.divisors, ∑ v ∈ n.divisors, ∑ u' ∈ m.divisors, ∑ v' ∈ n.divisors,
        kernφ a b (u * v) (u' * v'))
      = ∑ u ∈ m.divisors, ∑ u' ∈ m.divisors, ∑ v ∈ n.divisors, ∑ v' ∈ n.divisors,
        kernφ a b u u' * kernφ a b v v' := by
    apply Finset.sum_congr rfl; intro u hu
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u' hu'
    apply Finset.sum_congr rfl; intro v hv
    apply Finset.sum_congr rfl; intro v' hv'
    rw [kernφ_mul hm hn hmn (Nat.mem_divisors.mp hu).1 (Nat.mem_divisors.mp hu').1
        (Nat.mem_divisors.mp hv).1 (Nat.mem_divisors.mp hv').1]
  rw [h1, h2, ← prod_double_sum_eq]
  rfl

private lemma kernφ_one_one (a b : ℂ) : kernφ a b 1 1 = 1 := by
  simp [kernφ]

private lemma kernφ_prime_one {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    kernφ a b p 1 = - (p : ℂ) ^ (-a) * (((p - 1 : ℕ) : ℂ))⁻¹ := by
  have htot : Nat.totient p = p - 1 := Nat.totient_prime hp
  simp only [kernφ, ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
    Nat.lcm_one_right, htot, Nat.cast_one, Int.cast_neg, Int.cast_one, mul_one,
    Complex.one_cpow]
  ring

private lemma kernφ_one_prime {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    kernφ a b 1 p = - (p : ℂ) ^ (-b) * (((p - 1 : ℕ) : ℂ))⁻¹ := by
  have htot : Nat.totient p = p - 1 := Nat.totient_prime hp
  simp only [kernφ, ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
    Nat.lcm_one_left, htot, Nat.cast_one, Int.cast_neg, Int.cast_one, mul_one, one_mul,
    Complex.one_cpow]
  ring

private lemma kernφ_prime_prime {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    kernφ a b p p = (p : ℂ) ^ (-(a + b)) * (((p - 1 : ℕ) : ℂ))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htot : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hmain : (p : ℂ) ^ (-a) * (p : ℂ) ^ (-b) = (p : ℂ) ^ (-(a + b)) := by
    rw [← Complex.cpow_add (-a) (-b) hp0]
    congr 1
    ring
  simp only [kernφ, ArithmeticFunction.moebius_apply_prime hp, Nat.lcm_self, htot,
    Int.cast_neg, Int.cast_one]
  rw [show ((-1 : ℂ) * -1) = 1 by ring, one_mul]
  calc ((↑(p - 1) : ℂ))⁻¹ * (p : ℂ) ^ (-a) * (p : ℂ) ^ (-b)
      = ((↑(p - 1) : ℂ))⁻¹ * ((p : ℂ) ^ (-a) * (p : ℂ) ^ (-b)) := by ring
    _ = ((↑(p - 1) : ℂ))⁻¹ * (p : ℂ) ^ (-(a + b)) := by rw [hmain]
    _ = (p : ℂ) ^ (-(a + b)) * ((↑(p - 1) : ℂ))⁻¹ := by ring

private lemma Fsumφ_one (a b : ℂ) : Fsumφ a b 1 = 1 := by
  simp only [Fsumφ, Nat.divisors_one, Finset.sum_singleton, kernφ_one_one]

private lemma Fsumφ_prime {p : ℕ} (hp : p.Prime) (a b : ℂ) :
    Fsumφ a b p = 1 - ((p : ℂ) ^ (-a) + (p : ℂ) ^ (-b) - (p : ℂ) ^ (-(a + b))) *
      (((p - 1 : ℕ) : ℂ))⁻¹ := by
  have h1p : (1 : ℕ) ≠ p := fun h => hp.ne_one h.symm
  simp only [Fsumφ, Nat.Prime.divisors hp]
  rw [Finset.sum_pair h1p, Finset.sum_pair h1p, Finset.sum_pair h1p,
    kernφ_one_one, kernφ_prime_one hp, kernφ_one_prime hp, kernφ_prime_prime hp]
  ring

private lemma Fsumφ_prod_of_pairwise (a b : ℂ) (s : Finset ℕ) (hpos : ∀ p ∈ s, 0 < p)
    (h : (s : Set ℕ).Pairwise Nat.Coprime) :
    Fsumφ a b (∏ p ∈ s, p) = ∏ p ∈ s, Fsumφ a b p := by
  revert hpos h
  refine Finset.induction_on s ?_ ?_
  · intro hpos h
    simp only [Finset.prod_empty]
    exact Fsumφ_one a b
  · intro p t hpt ih hpos h
    rw [Finset.prod_insert hpt, Finset.prod_insert hpt]
    simp only [Finset.coe_insert, Set.pairwise_insert] at h
    obtain ⟨ht, hpall⟩ := h
    have hpt0 : ∀ q ∈ t, 0 < q := fun q hq => hpos q (Finset.mem_insert_of_mem hq)
    have hp0 : p ≠ 0 := (hpos p (Finset.mem_insert_self p t)).ne'
    have ht0 : (∏ q ∈ t, q) ≠ 0 := (Finset.prod_pos hpt0).ne'
    have hcop : p.Coprime (∏ q ∈ t, q) :=
      Nat.Coprime.prod_right fun q hq => (hpall q hq (fun hpq => hpt (hpq ▸ hq))).1
    rw [Fsumφ_mul hp0 ht0 hcop, ih hpt0 ht]

theorem sum_divisors_moebius_totient_lcm_cpow (m : ℕ) (hm : Squarefree m) (a b : ℂ) :
    (∑ d ∈ m.divisors, ∑ d' ∈ m.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((ArithmeticFunction.moebius d' : ℤ) : ℂ) *
          (((Nat.lcm d d').totient : ℂ))⁻¹ * (d : ℂ) ^ (-a) * (d' : ℂ) ^ (-b))
      = ∏ p ∈ m.primeFactors,
          (1 - ((p : ℂ) ^ (-a) + (p : ℂ) ^ (-b) - (p : ℂ) ^ (-(a + b))) *
            (((p - 1 : ℕ) : ℂ))⁻¹) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hpair : (m.primeFactors : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
    rw [hpp.coprime_iff_not_dvd]
    intro hdvd
    exact hpq ((hqp.dvd_iff_eq hpp.ne_one).mp hdvd).symm
  have hpos : ∀ p ∈ m.primeFactors, 0 < p := fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
  have hprod := Fsumφ_prod_of_pairwise a b m.primeFactors hpos hpair
  rw [Nat.prod_primeFactors_of_squarefree hm] at hprod
  show Fsumφ a b m = ∏ p ∈ m.primeFactors,
    (1 - ((p : ℂ) ^ (-a) + (p : ℂ) ^ (-b) - (p : ℂ) ^ (-(a + b))) * (((p - 1 : ℕ) : ℂ))⁻¹)
  rw [hprod]
  apply Finset.prod_congr rfl
  intro p hp
  exact Fsumφ_prime (Nat.mem_primeFactors.mp hp).1 a b

end Commons.NumberTheory.Moebius