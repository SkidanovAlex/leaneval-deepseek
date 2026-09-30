import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.liouville.recip_twist_re_upper
import Submission.Work.BMF.liouville.prime_recip_mod_one_uniform
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # N11 `liouville_facts`: Liouville is multiplicative, `1`-bounded, uniformly non-pretentious

Route: `𝔻(1, χ₀ n^{imt}) ≤ 2 ord(χ) 𝔻(λ, χ n^{it})` (the `m`-th power trick, `m = 2φ(q)`),
then the twist bound `Work.BMF.liouville.recip_twist_re_upper` for large and middle `|mt|`,
and primes `≡ 1 (mod q)` (`Work.BMF.liouville.prime_recip_mod_one_uniform`) for tiny `|mt|`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.BMF
open Polynomial Finset Real BoundedMultiplicativeFunctions Filter
open scoped ComplexConjugate


/-! ## Part 0: elementary helpers -/

lemma liouville_cp_oneBounded :
    IsOneBounded (ArithmeticFunction.liouville : ArithmeticFunction ℂ) := by
  intro n
  rw [ArithmeticFunction.intCoe_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ArithmeticFunction.liouville]
  · rw [ArithmeticFunction.liouville_apply hn]
    simp

lemma mulChar_norm_le_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ n‖ ≤ 1 := by
  by_cases h : IsUnit (n : ZMod q)
  · obtain ⟨u, hu⟩ := h
    have hval : χ (n : ZMod q) = ↑(χ.toUnitHom u) := by rw [← hu, MulChar.coe_toUnitHom]
    rw [hval]
    haveI : Fintype (ZMod q)ˣ := inferInstance
    haveI : Nonempty (ZMod q)ˣ := ⟨1⟩
    have hN : (0 : ℕ) < Fintype.card (ZMod q)ˣ := Fintype.card_pos_iff.mpr inferInstance
    have hpow : (χ.toUnitHom u : ℂ) ^ (Fintype.card (ZMod q)ˣ) = 1 := by
      have h2 := congrArg (fun ψ : DirichletCharacter ℂ q => (ψ (u : ZMod q) : ℂ))
        (MulChar.pow_card_eq_one χ)
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h2
      exact h2
    have hnorm : ‖(χ.toUnitHom u : ℂ)‖ ^ (Fintype.card (ZMod q)ˣ) = 1 := by
      rw [← norm_pow, hpow, norm_one]
    rcases lt_trichotomy ‖(χ.toUnitHom u : ℂ)‖ 1 with hl | he | hg
    · exfalso
      have hlt := pow_lt_one₀ (norm_nonneg _) hl (Nat.pos_iff_ne_zero.mp hN)
      rw [hnorm] at hlt; exact absurd hlt (lt_irrefl 1)
    · exact le_of_eq he
    · exfalso
      have hgt := one_lt_pow₀ hg (Nat.pos_iff_ne_zero.mp hN)
      rw [hnorm] at hgt; exact absurd hgt (lt_irrefl 1)
  · rw [MulCharClass.map_nonunit χ h]; simp

lemma norm_cpow_I_mul (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖((n : ℂ) ^ (Complex.I * (t : ℂ)))‖ = 1 := by
  have hnC : ((n : ℂ)) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hnC]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, ← Complex.ofReal_log (show (0:ℝ) ≤ n by positivity)]
  rw [hlog]
  have : ((Real.log n : ℝ) : ℂ) * (Complex.I * (t : ℂ)) =
      (((Real.log n * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_cpow_I_mul_le_one (n : ℕ) (t : ℝ) :
    ‖((n : ℂ) ^ (Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero]
    rcases eq_or_ne (Complex.I * (t : ℂ)) 0 with h0 | h0
    · rw [h0, Complex.cpow_zero]; simp
    · rw [Complex.zero_cpow h0]; simp
  · rw [norm_cpow_I_mul n hn t]

lemma isOneBounded_chi_cpow (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    IsOneBounded (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * t)) := by
  intro n
  rw [norm_mul]
  exact mul_le_one₀ (mulChar_norm_le_one q χ n) (norm_nonneg _) (norm_cpow_I_mul_le_one n t)

lemma dist_nonneg (f g : ℕ → ℂ) (X : ℝ) (hf : IsOneBounded f) (hg : IsOneBounded g) :
    0 ≤ 𝔻 f g X := by
  rw [𝔻]
  refine Real.rpow_nonneg (Finset.sum_nonneg ?_) _
  intro p hp
  have hp2 : (0 : ℝ) < (p : ℝ) := by
    have := (Nat.mem_primesLE.mp hp).2.two_le
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two this
  refine div_nonneg ?_ (le_of_lt hp2)
  have h1 : ‖f p‖ ≤ 1 := hf p
  have h2 : ‖conj (g p)‖ ≤ 1 := by rw [Complex.norm_conj]; exact hg p
  have h3 : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (f p), norm_nonneg (conj (g p))]
  have h4 : (f p * conj (g p)).re ≤ 1 := le_trans (Complex.re_le_norm _) h3
  linarith

lemma le_dist_of_sq_le (f g : ℕ → ℂ) (X : ℝ) (B : ℝ) (hf : IsOneBounded f) (hg : IsOneBounded g)
    (h : (B + 1) ^ 2 ≤ (𝔻 f g X) ^ 2) : B + 1 ≤ 𝔻 f g X := by
  have hd : 0 ≤ 𝔻 f g X := dist_nonneg f g X hf hg
  have h1 : Real.sqrt ((B + 1) ^ 2) ≤ Real.sqrt ((𝔻 f g X) ^ 2) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hd] at h1
  exact le_trans (le_abs_self _) h1

lemma re_cpow_I_mul (p : ℕ) (hp : p ≠ 0) (t : ℝ) :
    ((p : ℂ) ^ (Complex.I * (t : ℂ))).re = Real.cos (t * Real.log p) := by
  have hpC : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp
  rw [Complex.cpow_def_of_ne_zero hpC]
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, ← Complex.ofReal_log (show (0:ℝ) ≤ p by positivity)]
  rw [hlog]
  have : ((Real.log p : ℝ) : ℂ) * (Complex.I * (t : ℂ)) = ((t * Real.log p : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma re_cpow_neg_I_mul (p : ℕ) (hp : p ≠ 0) (u : ℝ) :
    ((p : ℂ) ^ (-(Complex.I * (u : ℂ)))).re = Real.cos (u * Real.log p) := by
  have hpC : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp
  rw [Complex.cpow_def_of_ne_zero hpC]
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, ← Complex.ofReal_log (show (0:ℝ) ≤ p by positivity)]
  rw [hlog]
  have : ((Real.log p : ℝ) : ℂ) * (-(Complex.I * (u : ℂ))) =
      (((-(u * Real.log p)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

lemma cpow_I_mul_pow_of_ne_zero (p : ℕ) (hp : p ≠ 0) (m : ℕ) (t : ℝ) :
    (((p : ℂ) ^ (Complex.I * (t : ℂ))) ^ m) =
      (p : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ)) := by
  have hpC : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp
  rw [← Complex.cpow_mul_nat p (Complex.I * (t : ℂ)) m]
  congr 1
  push_cast
  ring


/-! ## Part 1: the `m`-th power pointwise inequality -/

lemma normSq_re_im (z : ℂ) (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  rw [hz, one_pow] at h
  linarith [h]

lemma norm_one_sub_sq (z : ℂ) (hz : ‖z‖ = 1) : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  have h := Complex.sq_norm (1 - z)
  rw [Complex.normSq_apply] at h
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub] at h
  have h2 := normSq_re_im z hz
  linarith [h, h2]

lemma norm_one_sub_pow_le (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    1 - (z ^ (2 * k)).re ≤ 4 * (k : ℝ) ^ 2 * (1 - z.re) := by
  have hw : ‖z ^ k‖ = 1 := by rw [Complex.norm_pow, hz, one_pow]
  have hre : ((z ^ k) ^ 2).re = 2 * (z ^ k).re ^ 2 - 1 := by
    rw [pow_two, Complex.mul_re]
    have h2 := normSq_re_im (z ^ k) hw
    nlinarith [h2]
  have hle1 : (z ^ k).re ≤ 1 := le_trans (Complex.re_le_norm _) (le_of_eq hw)
  have hge1 : -1 ≤ (z ^ k).re := by
    have h := Complex.abs_re_le_norm (z ^ k)
    rw [hw] at h
    have h' : -1 ≤ (z^k).re := by
      have := abs_le.mp h
      linarith [this.1]
    exact h'
  have hsub : 1 - (z ^ k).re = ‖1 - z ^ k‖ ^ 2 / 2 := by
    have h := norm_one_sub_sq (z ^ k) hw
    linarith [h]
  have hnorm : ‖1 - z ^ k‖ ≤ (k : ℝ) * ‖1 - z‖ := by
    have hgs : (∑ i ∈ Finset.range k, z ^ i) * (1 - z) = 1 - z ^ k := geom_sum_mul_neg z k
    rw [← hgs, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖∑ i ∈ Finset.range k, z ^ i‖ ≤ ∑ i ∈ Finset.range k, ‖z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range k, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Complex.norm_pow, hz, one_pow]
      _ = (k : ℝ) := by simp
  have hnorm2 : ‖1 - z ^ k‖ ^ 2 ≤ ((k : ℝ) * ‖1 - z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hz2 : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := norm_one_sub_sq z hz
  rw [show z ^ (2 * k) = (z ^ k) ^ 2 from by rw [mul_comm 2 k, pow_mul], hre]
  nlinarith [hsub, hnorm2, hz2, hle1, hge1, hw]

lemma one_sub_re_pow_even_le (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    1 - (z ^ (k + k)).re ≤ (((k + k : ℕ)) : ℝ) ^ 2 * (1 - z.re) := by
  rw [show k + k = 2 * k from by ring]
  have h := norm_one_sub_pow_le z hz k
  have hcast : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [hcast]
  linarith [h]

lemma one_sub_re_pow_le (z : ℂ) (hz : ‖z‖ = 1) (m : ℕ) (hm : Even m) :
    1 - (z ^ m).re ≤ (m : ℝ) ^ 2 * (1 + z.re) := by
  obtain ⟨k, hk⟩ := hm
  subst hk
  have hknn : (0 : ℝ) ≤ (((k + k : ℕ)) : ℝ) ^ 2 := by positivity
  by_cases h0 : 0 ≤ z.re
  · have h := one_sub_re_pow_even_le z hz k
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hknn
  · push_neg at h0
    have hneg : ‖-z‖ = 1 := by rw [norm_neg, hz]
    have hpoweq : (-z) ^ (k + k) = z ^ (k + k) := Even.neg_pow ⟨k, rfl⟩ z
    have h := one_sub_re_pow_even_le (-z) hneg k
    rw [hpoweq, Complex.neg_re] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hknn

/-! ## Part 2: the per-prime comparison and the summed `m`-th power bound -/

lemma one_sub_cos_le_mul_one_add_re (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℕ) (hmeven : Even m) (hpow : χ ^ m = 1) (p : ℕ) (hp : p.Prime)
    (hpd : ¬ p ∣ q) (t : ℝ) :
    1 - Real.cos (((m : ℝ) * t) * Real.log p) ≤
      (m : ℝ) ^ 2 * (1 + (χ p * (p : ℂ) ^ (Complex.I * (t : ℂ))).re) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hunit : IsUnit ((p : ℕ) : ZMod q) := ZMod.isUnit_prime_of_not_dvd hp hpd
  have hχ1 : (1 : DirichletCharacter ℂ q) p = 1 := MulChar.one_apply hunit
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp
  · have hχpow : (χ p) ^ m = 1 := by
      have h1 : (χ ^ m) p = (χ p) ^ m := MulChar.pow_apply' χ (Nat.pos_iff_ne_zero.mp hmpos) p
      rw [← h1, hpow, MulChar.one_apply hunit]
    have hχnorm : ‖χ p‖ = 1 := by
      have h1 : ‖χ p‖ ^ m = (1 : ℝ) := by
        rw [← norm_pow, hχpow, norm_one]
      have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.pos_iff_ne_zero.mp hmpos)).mp h1
      exact this
    have hcp : ‖(p : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := norm_cpow_I_mul p hp0 t
    have hz : ‖χ p * (p : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
      rw [norm_mul, hχnorm, hcp, one_mul]
    have hzpow : ((χ p * (p : ℂ) ^ (Complex.I * (t : ℂ))) ^ m).re
        = Real.cos (((m : ℝ) * t) * Real.log p) := by
      rw [mul_pow, hχpow, one_mul, cpow_I_mul_pow_of_ne_zero p hp0 m t,
        re_cpow_I_mul p hp0 ((m : ℝ) * t)]
    have h := one_sub_re_pow_le (χ p * (p : ℂ) ^ (Complex.I * (t : ℂ))) hz m hmeven
    rw [hzpow] at h
    exact h

/-! ## Part 2: the squared distance identity, monotonicity, and the `m`-th power bound -/

lemma summand_nonneg (f g : ℕ → ℂ) (hf : IsOneBounded f) (hg : IsOneBounded g) (p : ℕ)
    (hp : p.Prime) : 0 ≤ (1 - (f p * conj (g p)).re) / (p : ℝ) := by
  have hp2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  refine div_nonneg ?_ (le_of_lt hp2)
  have h1 : ‖f p‖ ≤ 1 := hf p
  have h2 : ‖conj (g p)‖ ≤ 1 := by rw [Complex.norm_conj]; exact hg p
  have h3 : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (f p), norm_nonneg (conj (g p))]
  have h4 : (f p * conj (g p)).re ≤ 1 := le_trans (Complex.re_le_norm _) h3
  linarith

lemma dist_sq_eq (f g : ℕ → ℂ) (X : ℝ) (hf : IsOneBounded f) (hg : IsOneBounded g) :
    (𝔻 f g X) ^ 2 = ∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / p := by
  have hsum : 0 ≤ ∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / p := by
    refine Finset.sum_nonneg ?_
    intro p hp
    exact summand_nonneg f g hf hg p (Nat.mem_primesLE.mp hp).2
  rw [𝔻, ← Real.sqrt_eq_rpow, Real.sq_sqrt hsum]

lemma dist_sq_ge_sum (f g : ℕ → ℂ) (X : ℝ) (S : Finset ℕ) (hf : IsOneBounded f)
    (hg : IsOneBounded g) (hS : S ⊆ ⌊X⌋₊.primesLE) :
    (∑ p ∈ S, (1 - (f p * conj (g p)).re) / p) ≤ (𝔻 f g X) ^ 2 := by
  rw [dist_sq_eq f g X hf hg]
  refine Finset.sum_le_sum_of_subset_of_nonneg hS ?_
  intro p hp _
  exact summand_nonneg f g hf hg p (Nat.mem_primesLE.mp hp).2

lemma not_isUnit_of_dvd (q p : ℕ) (hq1 : 1 < q) (hp : p.Prime) (hpd : p ∣ q) :
    ¬ IsUnit ((p : ℕ) : ZMod q) := by
  intro hunit
  have hcop : p.Coprime q := (ZMod.isUnit_iff_coprime p q).mp hunit
  exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_refl p) hpd hcop

lemma dist_one_sq_ge_sum (q : ℕ) [NeZero q] (u N : ℝ) :
    (∑ p ∈ (⌊N⌋₊.primesLE).filter (fun p ↦ ¬ p ∣ q),
        (1 - Real.cos (u * Real.log p)) / (p : ℝ))
      ≤ (𝔻 (fun _ : ℕ ↦ (1 : ℂ))
          (fun n : ℕ ↦ (1 : DirichletCharacter ℂ q) n *
            (n : ℂ) ^ (Complex.I * ((u : ℝ) : ℂ))) N) ^ 2 := by
  have hf : IsOneBounded (fun _ : ℕ ↦ (1 : ℂ)) := fun n => by simp
  have hg : IsOneBounded (fun n : ℕ ↦ (1 : DirichletCharacter ℂ q) n *
      (n : ℂ) ^ (Complex.I * ((u : ℝ) : ℂ))) :=
    isOneBounded_chi_cpow q (1 : DirichletCharacter ℂ q) u
  refine le_trans (Finset.sum_le_sum ?_)
    (dist_sq_ge_sum _ _ N _ hf hg (Finset.filter_subset _ _))
  intro p hp
  have hpp : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_of_mem_filter p hp)).2
  have hpd : ¬ p ∣ q := (Finset.mem_filter.mp hp).2
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hunit : IsUnit ((p : ℕ) : ZMod q) := ZMod.isUnit_prime_of_not_dvd hpp hpd
  have h1 : (1 : DirichletCharacter ℂ q) p = 1 := MulChar.one_apply hunit
  have hz : (1 : ℂ) * conj ((1 : DirichletCharacter ℂ q) p *
      (p : ℂ) ^ (Complex.I * ((u : ℝ) : ℂ)))
      = conj ((p : ℂ) ^ (Complex.I * ((u : ℝ) : ℂ))) := by
    rw [h1, one_mul, one_mul]
  rw [hz, Complex.conj_re, re_cpow_I_mul p hp0 u]

lemma sum_filter_dvd_le (q : ℕ) [NeZero q] (u N : ℝ) :
    (∑ p ∈ (⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q),
        (1 - Real.cos (u * Real.log p)) / (p : ℝ)) ≤ 2 * ((q : ℝ) + 1) := by
  have hcard : ((⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q)).card ≤ q + 1 := by
    have hsub : (⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q) ⊆ Finset.range (q + 1) := by
      intro p hp
      have hpq : p ∣ q := (Finset.mem_filter.mp hp).2
      have hle : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hpq
      simp only [Finset.mem_range]; omega
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact h
  have hcardR : (((⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q)).card : ℝ) ≤ (q : ℝ) + 1 := by
    have h1 : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
    rw [← h1]
    exact_mod_cast hcard
  have hb : (∑ p ∈ (⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q),
      (1 - Real.cos (u * Real.log p)) / (p : ℝ))
      ≤ ((⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q)).card := by
    calc (∑ p ∈ (⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q),
        (1 - Real.cos (u * Real.log p)) / (p : ℝ))
        ≤ ∑ _p ∈ (⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q), (1 : ℝ) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hpp : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_of_mem_filter p hp)).2
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
          have hle : 1 - Real.cos (u * Real.log p) ≤ (p : ℝ) := by
            linarith [Real.neg_one_le_cos (u * Real.log p), hp2]
          exact div_le_one_of_le₀ hle (by linarith)
      _ = (((⌊N⌋₊.primesLE).filter (fun p ↦ p ∣ q)).card : ℝ) := by simp
  linarith [hb, hcardR]

lemma prime_term_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ)
    (hm1 : 1 ≤ m) (hmeven : Even m) (hpow : χ ^ m = 1) (p : ℕ) (hp : p.Prime) (t : ℝ) :
    (1 - ((1 : ℂ) * conj ((1 : DirichletCharacter ℂ q) p *
        (p : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ)))).re) / (p : ℝ)
      ≤ (m : ℝ) ^ 2 * ((1 - ((ArithmeticFunction.liouville : ArithmeticFunction ℂ) p *
          conj (χ p * (p : ℂ) ^ (Complex.I * (t : ℂ)))).re) / (p : ℝ)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hpd : p ∣ q
  · have hq1 : 1 < q := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hpd)
    have hnu : ¬ IsUnit ((p : ℕ) : ZMod q) := not_isUnit_of_dvd q p hq1 hp hpd
    have hχ0 : (1 : DirichletCharacter ℂ q) p = 0 := MulCharClass.map_nonunit 1 hnu
    have hχp : χ p = 0 := MulCharClass.map_nonunit χ hnu
    rw [hχ0, hχp]
    simp only [zero_mul, map_zero, one_mul, mul_zero, Complex.zero_re, sub_zero]
    have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      nlinarith
    simpa using mul_le_mul_of_nonneg_right hm2 (by positivity : (0:ℝ) ≤ (p:ℝ)⁻¹)
  · have hunit : IsUnit ((p : ℕ) : ZMod q) := ZMod.isUnit_prime_of_not_dvd hp hpd
    have hχ0 : (1 : DirichletCharacter ℂ q) p = 1 := MulChar.one_apply hunit
    have hre1 : ((1 : ℂ) * conj ((1 : DirichletCharacter ℂ q) p *
        (p : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ)))).re
        = Real.cos (((m : ℝ) * t) * Real.log p) := by
      rw [hχ0, one_mul, one_mul, Complex.conj_re, re_cpow_I_mul p hp0 ((m : ℝ) * t)]
    have hliou : ((ArithmeticFunction.liouville : ArithmeticFunction ℂ) p) = -1 := by
      rw [ArithmeticFunction.intCoe_apply, ArithmeticFunction.liouville_apply hp0,
        ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr hp]
      norm_num
    have hre2 : ((ArithmeticFunction.liouville : ArithmeticFunction ℂ) p *
        conj (χ p * (p : ℂ) ^ (Complex.I * (t : ℂ)))).re
        = -((χ p * (p : ℂ) ^ (Complex.I * (t : ℂ))).re) := by
      rw [hliou]
      simp only [neg_mul, Complex.neg_re, Complex.conj_re, one_mul]
    rw [hre1, hre2, sub_neg_eq_add]
    have hpt := one_sub_cos_le_mul_one_add_re q χ m hmeven hpow p hp hpd t
    rw [← mul_div_assoc]
    rw [div_le_div_iff_of_pos_right hppos]
    exact hpt

lemma dist_one_sq_le_mul (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ)
    (hm1 : 1 ≤ m) (hmeven : Even m) (hpow : χ ^ m = 1) (t N : ℝ) :
    (𝔻 (fun _ : ℕ ↦ (1 : ℂ))
        (fun n : ℕ ↦ (1 : DirichletCharacter ℂ q) n *
          (n : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) N) ^ 2
      ≤ (m : ℝ) ^ 2 * (𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N) ^ 2 := by
  have hf1 : IsOneBounded (fun _ : ℕ ↦ (1 : ℂ)) := fun n => by simp
  have hg1 : IsOneBounded (fun n : ℕ ↦ (1 : DirichletCharacter ℂ q) n *
      (n : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) :=
    isOneBounded_chi_cpow q (1 : DirichletCharacter ℂ q) ((m : ℝ) * t)
  have hf2 : IsOneBounded (ArithmeticFunction.liouville : ArithmeticFunction ℂ) :=
    liouville_cp_oneBounded
  have hg2 : IsOneBounded (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) :=
    isOneBounded_chi_cpow q χ t
  rw [dist_sq_eq _ _ N hf1 hg1, dist_sq_eq _ _ N hf2 hg2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  exact prime_term_le q χ m hm1 hmeven hpow p (Nat.mem_primesLE.mp hp).2 t


/-! ## Part 3: the `1 - cos` decomposition of the twisted reciprocal sum -/

lemma sum_re_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ) :
    (∑ i ∈ s, z i).re = ∑ i ∈ s, (z i).re := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Complex.add_re, ih]

lemma cos_div_eq {p : ℕ} (hp : p ≠ 0) (u : ℝ) :
    (((p : ℂ) ^ (-(Complex.I * (u : ℂ)))) / (p : ℂ)).re
      = Real.cos (u * Real.log p) / (p : ℝ) := by
  have hz : ((p : ℂ) ^ (-(Complex.I * (u : ℂ)))) / (p : ℂ)
      = (((p : ℝ)⁻¹ : ℝ) : ℂ) * ((p : ℂ) ^ (-(Complex.I * (u : ℂ)))) := by
    rw [div_eq_inv_mul, ← Complex.ofReal_natCast p, ← Complex.ofReal_inv, mul_comm]
  rw [hz, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    re_cpow_neg_I_mul p hp u, zero_mul, sub_zero]
  rw [div_eq_mul_inv]
  ring

lemma sum_one_sub_cos_eq (s : Finset ℕ) (u : ℝ) (hsp : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, (1 - Real.cos (u * Real.log p)) / (p : ℝ))
      = (∑ p ∈ s, (1 : ℝ) / (p : ℝ))
        - (∑ p ∈ s, ((p : ℂ) ^ (-(Complex.I * (u : ℂ)))) / (p : ℂ)).re := by
  have h1 : ∀ p ∈ s, (1 - Real.cos (u * Real.log p)) / (p : ℝ)
      = (1 : ℝ) / (p : ℝ) - Real.cos (u * Real.log p) / (p : ℝ) := by
    intro p hp; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, sum_re_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [cos_div_eq (hsp p hp).ne_zero u]

/-! ## Part 4: the main theorem -/

theorem liouville_facts_aux (k : ℕ) (θ₁ Cc : ℝ) (hθ₀ : 0 < θ₁) (hθ₁ : θ₁ < 1 / 2) (hC : 0 < Cc)
    (Q : ℕ+) (B : ℝ) :
    ∃ Y₀ : ℝ, ∀ Y H : ℝ, Y₀ ≤ Y → Y ^ θ₁ ≤ H → H ≤ Y ^ (1 - θ₁) →
      B < M (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
        (Cc * Y ^ (k + 1) / H ^ (k + 1)) Q := by
  obtain ⟨Cm, hCm_pos, hMert⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  obtain ⟨Cp, hCp_nn, hAP⟩ := Work.BMF.liouville.prime_recip_mod_one_uniform Q
  obtain ⟨⟨Ct, hCt_nn, hTwistL⟩, ⟨Cs, hCs_nn, hTwistS⟩⟩ := liouville.recip_twist_re_upper
  have hCm_nn : 0 ≤ Cm := le_of_lt hCm_pos
  set Qn : ℝ := (Q : ℝ) with hQn
  have hQnpos : 0 < Qn := by rw [hQn]; exact_mod_cast Q.pos
  set K : ℝ := Real.exp ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
      + Real.pi * Qn + 1 with hK
  have hexpK : (2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1 ≤ Real.log K := by
    rw [hK]
    have hp := Real.exp_pos ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
    have hle : Real.exp ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1) ≤
        Real.exp ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
          + Real.pi * Qn + 1 := by
      have hpi : 0 ≤ Real.pi * Qn := by positivity
      linarith
    calc (2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1
        = Real.log (Real.exp ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)) :=
          (Real.log_exp _).symm
      _ ≤ Real.log (Real.exp ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
            + Real.pi * Qn + 1) := Real.log_le_log hp hle
  have hKpos : 0 < K := by
    rw [hK]
    have hp := Real.exp_pos ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
    have hpi : 0 < Real.pi * Qn := by positivity
    linarith
  have hK1 : 1 < K := by
    rw [hK]
    have hp := Real.exp_pos ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
    have hpi : 0 < Real.pi * Qn := by positivity
    linarith
  have hKpi : Real.pi * Qn ≤ K := by
    rw [hK]
    have hp := Real.exp_pos ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + Cs + 2 * (Qn + 1) + 1)
    linarith
  have hpoint : ∀ᶠ N : ℝ in atTop, ∀ (q : ℕ+) (hq : q ≤ Q) (χ : DirichletCharacter ℂ (q : ℕ))
      (t : ℝ), |t| ≤ N → B + 1 ≤ 𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
        (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N := by
    have hN3 : ∀ᶠ N : ℝ in atTop, (3 : ℝ) ≤ N := eventually_ge_atTop 3
    have hN11 : ∀ᶠ N : ℝ in atTop, (11 : ℝ) ≤ N := eventually_ge_atTop 11
    have hlog1 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log N :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
    have hbig1 : ∀ᶠ N : ℝ in atTop,
        Real.log K + Qn * ((B + 1) ^ 2 + Cp) ≤ Real.log (Real.log N) :=
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop _)
    have hbig2 : ∀ᶠ N : ℝ in atTop,
        5 * ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + 2 * (Qn + 1) + 1)
          ≤ Real.log (Real.log N) :=
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop _)
    have hsqu : ∀ᶠ N : ℝ in atTop, 3 + 2 * Qn * N ≤ N ^ 2 := by
      have hNN : ∀ᶠ N : ℝ in atTop, max 3 (2 * Qn + 1) ≤ N := eventually_ge_atTop _
      filter_upwards [hNN] with N hN
      have h3 : (3 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
      have h2 : 2 * Qn + 1 ≤ N := le_trans (le_max_right _ _) hN
      have hNn : (0 : ℝ) ≤ N := by linarith
      nlinarith [hQnpos, h3, h2, hNn]
    have hlog2le : ∀ᶠ N : ℝ in atTop, Real.log 2 ≤ (Real.pi / K) * Real.log N := by
      have hNN : ∀ᶠ N : ℝ in atTop, K * Real.log 2 / Real.pi ≤ Real.log N :=
        Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
      filter_upwards [hNN] with N hN
      rw [div_le_iff₀ Real.pi_pos] at hN
      rw [div_mul_eq_mul_div, le_div_iff₀ hKpos]
      linarith
    have hsmallN : ∀ᶠ N : ℝ in atTop, 2 * Qn * N ≤ Real.exp ((Real.log N) ^ (21 / 20 : ℝ)) := by
      have hNN : ∀ᶠ N : ℝ in atTop, max ((2:ℝ) ^ 20) (Real.log (2 * Qn)) ≤ Real.log N :=
        Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
      filter_upwards [hN3, hNN] with N hN3' hN
      have hNpos : (0 : ℝ) < N := by linarith
      have h16 : ((2:ℝ) ^ 20) ≤ Real.log N := le_trans (le_max_left _ _) hN
      have hL : (0 : ℝ) < Real.log N := by norm_num at h16 ⊢; linarith
      have hlogle : Real.log (2 * Qn) ≤ Real.log N := le_trans (le_max_right _ _) hN
      have hpow : (Real.log N) ^ (21 / 20 : ℝ)
          = Real.log N * (Real.log N) ^ (1 / 20 : ℝ) := by
        rw [show (21 / 20 : ℝ) = 1 + 1 / 20 from by norm_num, Real.rpow_add hL, Real.rpow_one]
      have h14 : (2 : ℝ) ≤ (Real.log N) ^ (1 / 20 : ℝ) := by
        have h4 : ((Real.log N) ^ (1 / 20 : ℝ)) ^ 20 = Real.log N := by
          rw [← Real.rpow_natCast ((Real.log N) ^ (1 / 20 : ℝ)) 20, ← Real.rpow_mul (le_of_lt hL)]
          norm_num
        have h24 : ((2 : ℝ)) ^ 20 ≤ ((Real.log N) ^ (1 / 20 : ℝ)) ^ 20 := by
          rw [h4]; exact h16
        exact le_of_pow_le_pow_left₀ (by norm_num : (20:ℕ) ≠ 0)
          (Real.rpow_nonneg (le_of_lt hL) _) h24
      have h3 : Real.log (2 * Qn * N) ≤ (Real.log N) ^ (21 / 20 : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity), hpow]
        nlinarith [hL, h14, hlogle]
      calc 2 * Qn * N = Real.exp (Real.log (2 * Qn * N)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((Real.log N) ^ (21 / 20 : ℝ)) := Real.exp_le_exp.mpr h3
    have hall : ∀ᶠ N : ℝ in atTop, (3 ≤ N) ∧ (11 ≤ N) ∧ (1 ≤ Real.log N) ∧
        (Real.log K + Qn * ((B + 1) ^ 2 + Cp) ≤ Real.log (Real.log N)) ∧
        (5 * ((2 * Qn) ^ 2 * (B + 1) ^ 2 + Cm + Ct + 2 * (Qn + 1) + 1)
          ≤ Real.log (Real.log N)) ∧
        (3 + 2 * Qn * N ≤ N ^ 2) ∧ (Real.log 2 ≤ (Real.pi / K) * Real.log N) ∧
        (2 * Qn * N ≤ Real.exp ((Real.log N) ^ (21 / 20 : ℝ))) := by
      filter_upwards [hN3, hN11, hlog1, hbig1, hbig2, hsqu, hlog2le, hsmallN] with N h1 h2 h3 h4 h5 h6 h7 h8
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hT : ∀ᶠ N : ℝ in atTop, ∀ (q : ℕ+) (hq : q ≤ Q) (χ : DirichletCharacter ℂ (q : ℕ))
        (t : ℝ), |t| ≤ N → (2 * ((q : ℕ).totient) : ℝ) * |t| * Real.log N ≤ K →
        B + 1 ≤ 𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N := by
      filter_upwards [hall] with N hN
      obtain ⟨hN3, hN11, hlog1, hbig1, hbig2, hsqu, hlog2le, hsmallN⟩ := hN
      intro q hq χ t ht hcase
      haveI : NeZero (q : ℕ) := ⟨q.pos.ne'⟩
      set m : ℕ := 2 * (q : ℕ).totient with hmdef
      have hmcast : (m : ℝ) = 2 * ((q : ℕ).totient : ℝ) := by simp [hmdef]
      have hcase' : (m : ℝ) * |t| * Real.log N ≤ K := by rw [hmcast]; linarith [hcase]
      have hm1 : 1 ≤ m := by
        rw [hmdef]; have := Nat.totient_pos.mpr q.pos; omega
      have hmge2 : (2 : ℝ) ≤ (m : ℝ) := by
        have h1 : (1 : ℕ) ≤ (q : ℕ).totient := Nat.totient_pos.mpr q.pos
        have h2 : (1 : ℝ) ≤ ((q : ℕ).totient : ℝ) := by exact_mod_cast h1
        rw [hmcast]; linarith
      have hmle : (m : ℝ) ≤ 2 * Qn := by
        have h1 : ((q : ℕ).totient : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (q : ℕ)
        have h2 : ((q : ℕ) : ℝ) ≤ Qn := by rw [hQn]; exact_mod_cast hq
        rw [hmcast]; linarith
      have hNpos : 0 < N := by linarith
      have hlogNpos : 0 < Real.log N := by linarith
      set x₁ : ℝ := N ^ (Real.pi * (m : ℝ) / (2 * K)) with hx1def
      have hx1pos : 0 < x₁ := by rw [hx1def]; exact Real.rpow_pos_of_pos hNpos _
      have hlogx1 : Real.log x₁ = Real.pi * (m : ℝ) / (2 * K) * Real.log N := by
        rw [hx1def, Real.log_rpow hNpos]
      have hexp1 : Real.pi * (m : ℝ) / (2 * K) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [hKpi, hmle, Real.pi_pos]
      have hx1le : x₁ ≤ N := by
        rw [hx1def]; exact Real.rpow_le_self_of_one_le (by linarith) hexp1
      have hs : Real.pi / K ≤ Real.pi * (m : ℝ) / (2 * K) := by
        have hK2 : (0 : ℝ) < 2 * K := by positivity
        have h1 : Real.pi / K * (2 * K) = 2 * Real.pi := by field_simp
        rw [le_div_iff₀ hK2, h1]
        nlinarith [hmge2, Real.pi_pos]
      have hx1ge2 : 2 ≤ x₁ := by
        have h3 : Real.log 2 ≤ Real.pi * (m : ℝ) / (2 * K) * Real.log N := by
          have h4 : (Real.pi / K) * Real.log N ≤ (Real.pi * (m : ℝ) / (2 * K)) * Real.log N :=
            mul_le_mul_of_nonneg_right hs (le_of_lt hlogNpos)
          linarith [hlog2le, h4]
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp ((Real.pi * (m : ℝ) / (2 * K)) * Real.log N) := Real.exp_le_exp.mpr h3
          _ = x₁ := by rw [hx1def, Real.rpow_def_of_pos hNpos, mul_comm]
      have hIsB : IsOneBounded (fun n : ℕ ↦ (ArithmeticFunction.liouville : ArithmeticFunction ℂ) n) :=
        liouville_cp_oneBounded
      have hIsBg : IsOneBounded (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) :=
        isOneBounded_chi_cpow (q : ℕ) χ t
      have hSsub : ((⌊x₁⌋₊.primesLE).filter (fun p => p ≡ 1 [MOD (q : ℕ)])) ⊆ ⌊N⌋₊.primesLE := by
        intro p hp
        have hp1 : p ∈ ⌊x₁⌋₊.primesLE := (Finset.mem_filter.mp hp).1
        rw [Nat.mem_primesLE] at hp1 ⊢
        exact ⟨le_trans hp1.1 (Nat.floor_mono hx1le), hp1.2⟩
      have hsub := dist_sq_ge_sum (fun n : ℕ ↦ (ArithmeticFunction.liouville : ArithmeticFunction ℂ) n)
        (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N
        ((⌊x₁⌋₊.primesLE).filter (fun p => p ≡ 1 [MOD (q : ℕ)])) hIsB hIsBg hSsub
      have hterm : (∑ p ∈ (⌊x₁⌋₊.primesLE).filter (fun p => p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ (⌊x₁⌋₊.primesLE).filter (fun p => p ≡ 1 [MOD (q : ℕ)]),
            (1 - (((fun n : ℕ ↦ (ArithmeticFunction.liouville : ArithmeticFunction ℂ) n) p)
              * conj (((fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) p))).re) / (p : ℝ) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp1 := Finset.mem_filter.mp hp
        have hprime : p.Prime := (Nat.mem_primesLE.mp hp1.1).2
        have hp2 : (0 : ℝ) < (p : ℝ) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hprime.two_le
        have hlogp : Real.log p ≤ Real.pi * (m : ℝ) / (2 * K) * Real.log N := by
          have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_le
          have h2 : (p : ℝ) ≤ x₁ := by
            have hpile : p ≤ ⌊x₁⌋₊ := (Nat.mem_primesLE.mp hp1.1).1
            have hcast : (p : ℝ) ≤ (⌊x₁⌋₊ : ℝ) := Nat.cast_le.mpr hpile
            exact le_trans hcast (Nat.floor_le hx1pos.le)
          rw [← hlogx1]
          exact Real.log_le_log (by linarith) h2
        have hlt : |t| * Real.log p ≤ Real.pi / 2 := by
          have h0 : |t| * (Real.pi * (m : ℝ) / (2 * K) * Real.log N)
              = (Real.pi / 2) * ((m : ℝ) * |t| * Real.log N) / K := by
            field_simp
          have h1 : |t| * Real.log p ≤ (Real.pi / 2) * ((m : ℝ) * |t| * Real.log N) / K := by
            calc |t| * Real.log p ≤ |t| * (Real.pi * (m : ℝ) / (2 * K) * Real.log N) :=
                  mul_le_mul_of_nonneg_left hlogp (abs_nonneg t)
              _ = (Real.pi / 2) * ((m : ℝ) * |t| * Real.log N) / K := h0
          have h5 : (Real.pi / 2) * ((m : ℝ) * |t| * Real.log N) / K ≤ Real.pi / 2 := by
            rw [div_le_iff₀ hKpos]
            have hpi2 : (0:ℝ) ≤ Real.pi / 2 := by positivity
            exact mul_le_mul_of_nonneg_left hcase' hpi2
          exact le_trans h1 h5
        have hcos : 0 ≤ Real.cos (t * Real.log p) := by
          have hlogpnn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
          refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
          · have h4 : -|t| ≤ t := neg_abs_le t
            have h5 : -|t| * Real.log p ≤ t * Real.log p := mul_le_mul_of_nonneg_right h4 hlogpnn
            have h6 : -(Real.pi / 2) ≤ -|t| * Real.log p := by linarith
            linarith
          · have h2 : t * Real.log p ≤ |t| * Real.log p :=
              mul_le_mul_of_nonneg_right (le_abs_self t) hlogpnn
            linarith
        have hmodeq : (p : ZMod (q : ℕ)) = 1 := by
          simpa using (ZMod.natCast_eq_natCast_iff p 1 (q : ℕ)).mpr hp1.2
        have hchi : χ p = 1 := by rw [hmodeq]; exact MulChar.map_one χ
        have hliou : ((ArithmeticFunction.liouville : ArithmeticFunction ℂ) p) = -1 := by
          rw [ArithmeticFunction.intCoe_apply, ArithmeticFunction.liouville_apply hprime.ne_zero,
            ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr hprime]
          norm_num
        have hre : ((p : ℂ) ^ (Complex.I * (t : ℂ))).re = Real.cos (t * Real.log p) :=
          re_cpow_I_mul p hprime.ne_zero t
        have hgoal : (((ArithmeticFunction.liouville : ArithmeticFunction ℂ) p)
            * conj (χ p * (p : ℂ) ^ (Complex.I * (t : ℂ)))).re = -Real.cos (t * Real.log p) := by
          rw [hchi, hliou]
          simp only [one_mul, neg_mul, Complex.neg_re, Complex.conj_re, hre]
        rw [hgoal]
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      have hap := hAP q x₁ hq hx1ge2
      have hkey : (B + 1) ^ 2 ≤ (𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N) ^ 2 := by
        have h1 : ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x₁) - Cp ≤
            ∑ p ∈ (⌊x₁⌋₊.primesLE).filter (fun p => p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / (p : ℝ) := hap
        have h2 : Real.log (Real.log x₁) =
            Real.log (Real.pi * (m : ℝ) / (2 * K)) + Real.log (Real.log N) := by
          rw [hlogx1, Real.log_mul (by positivity) hlogNpos.ne']
        have h3 : -Real.log K ≤ Real.log (Real.pi * (m : ℝ) / (2 * K)) := by
          have h4 : 1 ≤ Real.pi * (m : ℝ) / (2 * K) * K := by
            have heq : Real.pi * (m : ℝ) / (2 * K) * K = Real.pi * (m : ℝ) / 2 := by field_simp
            rw [heq]
            nlinarith [hmge2, Real.pi_pos, Real.pi_gt_three]
          have h5 : Real.log (1 : ℝ) ≤ Real.log (Real.pi * (m : ℝ) / (2 * K) * K) :=
            Real.log_le_log (by norm_num) h4
          rw [Real.log_mul (by positivity) hKpos.ne', Real.log_one] at h5
          linarith
        have h8 : (0 : ℝ) ≤ ((q : ℕ).totient : ℝ)⁻¹ := by positivity
        have h9 : ((q : ℕ).totient : ℝ)⁻¹ * (-Real.log K) ≤
            ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.pi * (m : ℝ) / (2 * K)) :=
          mul_le_mul_of_nonneg_left h3 h8
        have hφ1 : (1 : ℝ) ≤ ((q : ℕ).totient : ℝ) := by
          exact_mod_cast (Nat.totient_pos.mpr q.pos : 0 < (q : ℕ).totient)
        have h10 : -Real.log K ≤ ((q : ℕ).totient : ℝ)⁻¹ * (-Real.log K) := by
          have hφinv : ((q : ℕ).totient : ℝ)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ (by linarith)]; exact hφ1
          have hlogK : 0 < Real.log K := Real.log_pos hK1
          nlinarith [hφinv, hlogK]
        have hQle : Qn⁻¹ ≤ ((q : ℕ).totient : ℝ)⁻¹ := by
          rw [inv_le_inv₀ hQnpos (by linarith [hφ1])]
          rw [hQn]
          exact_mod_cast le_trans (Nat.totient_le (q : ℕ)) hq
        have h11 : Real.log K + Qn * ((B + 1) ^ 2 + Cp) ≤ Real.log (Real.log N) := hbig1
        have hQle2 : (B + 1) ^ 2 + Cp ≤
            ((q : ℕ).totient : ℝ)⁻¹ * (Real.log (Real.log N) - Real.log K) := by
          have hSnn : (0 : ℝ) ≤ (B + 1) ^ 2 + Cp := by positivity
          have hA : (B + 1) ^ 2 + Cp ≤ (Real.log (Real.log N) - Real.log K) / Qn := by
            rw [le_div_iff₀ hQnpos]
            nlinarith [h11]
          have hKle : Real.log K ≤ Real.log (Real.log N) := by
            have hQnS : 0 ≤ Qn * ((B + 1) ^ 2 + Cp) := by positivity
            linarith [h11, hQnS]
          have hB : (Real.log (Real.log N) - Real.log K) / Qn ≤
              ((q : ℕ).totient : ℝ)⁻¹ * (Real.log (Real.log N) - Real.log K) := by
            rw [div_eq_inv_mul]
            exact mul_le_mul_of_nonneg_right hQle (by linarith)
          linarith [hA, hB]
        have h13' : (B + 1) ^ 2 + Cp ≤
            ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x₁) := by
          have h8b : (0 : ℝ) ≤ ((q : ℕ).totient : ℝ)⁻¹ := by positivity
          have h9b : ((q : ℕ).totient : ℝ)⁻¹ * (Real.log (Real.log N) - Real.log K)
              ≤ ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x₁) := by
            rw [h2]
            exact mul_le_mul_of_nonneg_left (by linarith [h3]) h8b
          linarith [hQle2, h9b]
        linarith [h1, h13', hsub, hterm]
      exact le_dist_of_sq_le _ _ N B hIsB hIsBg hkey
    have hM : ∀ᶠ N : ℝ in atTop, ∀ (q : ℕ+) (hq : q ≤ Q) (χ : DirichletCharacter ℂ (q : ℕ))
        (t : ℝ), |t| ≤ N → K < (2 * ((q : ℕ).totient) : ℝ) * |t| * Real.log N →
        (2 * ((q : ℕ).totient) : ℝ) * |t| ≤ 1 →
        B + 1 ≤ 𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N := by
      filter_upwards [hall] with N hN
      obtain ⟨hN3, hN11, hlog1, hbig1, hbig2, hsqu, hlog2le, hsmallN⟩ := hN
      intro q hq χ t ht hcase hsmall'
      haveI : NeZero (q : ℕ) := ⟨q.pos.ne'⟩
      set m : ℕ := 2 * (q : ℕ).totient with hmdef
      have hmcast : (m : ℝ) = 2 * ((q : ℕ).totient : ℝ) := by simp [hmdef]
      have hm1 : 1 ≤ m := by rw [hmdef]; have := Nat.totient_pos.mpr q.pos; omega
      have hmeven : Even m := ⟨(q : ℕ).totient, by rw [hmdef]; ring⟩
      have hmle : (m : ℝ) ≤ 2 * Qn := by
        have h1 : ((q : ℕ).totient : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (q : ℕ)
        have h2 : ((q : ℕ) : ℝ) ≤ Qn := by rw [hQn]; exact_mod_cast hq
        rw [hmcast]; linarith
      have hpow : χ ^ m = 1 := by
        rw [hmdef, show 2 * (q : ℕ).totient = (q : ℕ).totient * 2 from by ring, pow_mul]
        have hcard : χ ^ Fintype.card (ZMod (q : ℕ))ˣ = 1 := MulChar.pow_card_eq_one χ
        rw [ZMod.card_units_eq_totient] at hcard
        rw [hcard, one_pow]
      have hmpos : (0 : ℝ) < (m : ℝ) := by
        have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        linarith
      have hcaseM : K < (m : ℝ) * |t| * Real.log N := by rw [hmcast]; linarith [hcase]
      have hsmallM : (m : ℝ) * |t| ≤ 1 := by rw [hmcast]; linarith [hsmall']
      have hNpos : 0 < N := by linarith
      have hlogNpos : 0 < Real.log N := by linarith
      have hu0 : (m : ℝ) * t ≠ 0 := by
        intro h0
        have h1 : (m : ℝ) * |t| = 0 := by
          have h2 : |(m : ℝ) * t| = 0 := by rw [h0, abs_zero]
          rwa [abs_mul, abs_of_nonneg (le_of_lt hmpos)] at h2
        have h2 : (m : ℝ) * |t| * Real.log N = 0 := by rw [h1, zero_mul]
        linarith [hcaseM, h2, hKpos]
      have huabs : |(m : ℝ) * t| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hmpos)]; exact hsmallM
      have hkey1 := dist_one_sq_ge_sum (q : ℕ) ((m : ℝ) * t) N
      have hkey2 := sum_filter_dvd_le (q : ℕ) ((m : ℝ) * t) N
      have hsplit := Finset.sum_filter_add_sum_filter_not (⌊N⌋₊.primesLE) (fun p ↦ p ∣ q)
        (f := fun p ↦ (1 - Real.cos (((m : ℝ) * t) * Real.log p)) / (p : ℝ))
      have hlowSum : Real.log K - Cm - Cs ≤
          ∑ p ∈ ⌊N⌋₊.primesLE, (1 - Real.cos (((m : ℝ) * t) * Real.log p)) / (p : ℝ) := by
        have hmert' : Real.log (Real.log N) - Cm ≤ ∑ p ∈ ⌊N⌋₊.primesLE, (1 : ℝ) / (p : ℝ) := by
          have h := (abs_le.mp (hMert N hN11)).1
          linarith [h]
        have htw := hTwistS N hN3 ((m : ℝ) * t) (abs_pos.mpr hu0) huabs
        have hid := sum_one_sub_cos_eq (⌊N⌋₊.primesLE) ((m : ℝ) * t)
          (fun p hp => (Nat.mem_primesLE.mp hp).2)
        have hlogu : Real.log (1 / |(m : ℝ) * t|) ≤ Real.log (Real.log N) - Real.log K := by
          have h1 : K / Real.log N ≤ |(m : ℝ) * t| := by
            rw [div_le_iff₀ hlogNpos]
            have h2 : |(m : ℝ) * t| = (m : ℝ) * |t| := by
              rw [abs_mul, abs_of_nonneg (le_of_lt hmpos)]
            rw [h2]
            linarith [hcaseM]
          have h2 : Real.log K - Real.log (Real.log N) ≤ Real.log |(m : ℝ) * t| := by
            have h := Real.log_le_log (by positivity : (0 : ℝ) < K / Real.log N) h1
            rwa [Real.log_div (ne_of_gt hKpos) (ne_of_gt hlogNpos)] at h
          have h3 : Real.log (1 / |(m : ℝ) * t|) = - Real.log |(m : ℝ) * t| := by
            rw [one_div, Real.log_inv]
          rw [h3]; linarith [h2]
        linarith [hmert', htw, hid, hlogu]
      have hD1 : Real.log K - Cm - Cs - 2 * ((q : ℝ) + 1) ≤
          (𝔻 (fun _ : ℕ ↦ (1 : ℂ)) (fun n : ℕ ↦ (1 : DirichletCharacter ℂ (q : ℕ)) n *
            (n : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) N) ^ 2 := by
        linarith [hlowSum, hkey1, hkey2, hsplit]
      have hmul := dist_one_sq_le_mul (q : ℕ) χ m hm1 hmeven hpow t N
      have hArith : (m : ℝ) ^ 2 * (B + 1) ^ 2 ≤ Real.log K - Cm - Cs - 2 * ((q : ℝ) + 1) := by
        have hqle : (q : ℝ) + 1 ≤ Qn + 1 := by
          have h1 : ((q : ℕ) : ℝ) ≤ Qn := by rw [hQn]; exact_mod_cast hq
          linarith
        have hm2 : (m : ℝ) ^ 2 ≤ (2 * Qn) ^ 2 := by
          have h1 : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hmpos
          have h2 : (0 : ℝ) ≤ 2 * Qn := by positivity
          nlinarith [hmle, h1, h2]
        have h3 : (m : ℝ) ^ 2 * (B + 1) ^ 2 ≤ (2 * Qn) ^ 2 * (B + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hm2 (by positivity)
        linarith [h3, hexpK, hqle]
      have hkey : (B + 1) ^ 2 ≤ (𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N) ^ 2 := by
        have hm2pos : 0 < (m : ℝ) ^ 2 := by positivity
        have h1 : (m : ℝ) ^ 2 * (B + 1) ^ 2 ≤
            (m : ℝ) ^ 2 * (𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
              (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N) ^ 2 :=
          le_trans hArith (le_trans hD1 hmul)
        exact le_of_mul_le_mul_left h1 hm2pos
      exact le_dist_of_sq_le _ _ N B liouville_cp_oneBounded
        (isOneBounded_chi_cpow (q : ℕ) χ t) hkey
    have hL : ∀ᶠ N : ℝ in atTop, ∀ (q : ℕ+) (hq : q ≤ Q) (χ : DirichletCharacter ℂ (q : ℕ))
        (t : ℝ), |t| ≤ N → 1 < (2 * ((q : ℕ).totient) : ℝ) * |t| →
        B + 1 ≤ 𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N := by
      filter_upwards [hall] with N hN
      obtain ⟨hN3, hN11, hlog1, hbig1, hbig2, hsqu, hlog2le, hsmallN⟩ := hN
      intro q hq χ t ht hbig
      haveI : NeZero (q : ℕ) := ⟨q.pos.ne'⟩
      set m : ℕ := 2 * (q : ℕ).totient with hmdef
      have hmcast : (m : ℝ) = 2 * ((q : ℕ).totient : ℝ) := by simp [hmdef]
      have hm1 : 1 ≤ m := by rw [hmdef]; have := Nat.totient_pos.mpr q.pos; omega
      have hmeven : Even m := ⟨(q : ℕ).totient, by rw [hmdef]; ring⟩
      have hmle : (m : ℝ) ≤ 2 * Qn := by
        have h1 : ((q : ℕ).totient : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (q : ℕ)
        have h2 : ((q : ℕ) : ℝ) ≤ Qn := by rw [hQn]; exact_mod_cast hq
        rw [hmcast]; linarith
      have hpow : χ ^ m = 1 := by
        rw [hmdef, show 2 * (q : ℕ).totient = (q : ℕ).totient * 2 from by ring, pow_mul]
        have hcard : χ ^ Fintype.card (ZMod (q : ℕ))ˣ = 1 := MulChar.pow_card_eq_one χ
        rw [ZMod.card_units_eq_totient] at hcard
        rw [hcard, one_pow]
      have hmpos : (0 : ℝ) < (m : ℝ) := by
        have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        linarith
      have hbigM : 1 < (m : ℝ) * |t| := by rw [hmcast]; linarith [hbig]
      have hNpos : 0 < N := by linarith
      have hlogNpos : 0 < Real.log N := by linarith
      have hu1 : 1 ≤ |(m : ℝ) * t| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hmpos)]
        exact le_of_lt hbigM
      have huN : (m : ℝ) * |t| ≤ 2 * Qn * N := by
        have h1 : |t| ≤ N := ht
        have h2 : (0 : ℝ) ≤ |t| := abs_nonneg t
        nlinarith [hmle, hmpos, h1, h2]
      have hule21 : |(m : ℝ) * t| ≤ Real.exp ((Real.log N) ^ (21 / 20 : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hmpos)]
        linarith [huN, hsmallN]
      have hule : |(m : ℝ) * t| ≤ Real.exp ((Real.log N) ^ (5 / 4 : ℝ)) := by
        refine le_trans hule21 (Real.exp_le_exp.mpr ?_)
        have hlog3 : (1 : ℝ) < Real.log 3 := by
          have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
          rwa [Real.log_exp] at h
        have h1 : (1 : ℝ) < Real.log N :=
          lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hN3)
        rw [Real.rpow_le_rpow_left_iff h1]
        norm_num
      have hkey1 := dist_one_sq_ge_sum (q : ℕ) ((m : ℝ) * t) N
      have hkey2 := sum_filter_dvd_le (q : ℕ) ((m : ℝ) * t) N
      have hsplit := Finset.sum_filter_add_sum_filter_not (⌊N⌋₊.primesLE) (fun p ↦ p ∣ q)
        (f := fun p ↦ (1 - Real.cos (((m : ℝ) * t) * Real.log p)) / (p : ℝ))
      have hlowSum : (1 / 5) * Real.log (Real.log N) - (Cm + Ct + (4 / 5) * Real.log 2) ≤
          ∑ p ∈ ⌊N⌋₊.primesLE, (1 - Real.cos (((m : ℝ) * t) * Real.log p)) / (p : ℝ) := by
        have hmert' : Real.log (Real.log N) - Cm ≤ ∑ p ∈ ⌊N⌋₊.primesLE, (1 : ℝ) / (p : ℝ) := by
          have h := (abs_le.mp (hMert N hN11)).1
          linarith [h]
        have htw := hTwistL N hN3 ((m : ℝ) * t) hu1 hule
        have hid := sum_one_sub_cos_eq (⌊N⌋₊.primesLE) ((m : ℝ) * t)
          (fun p hp => (Nat.mem_primesLE.mp hp).2)
        have hlogu : Real.log (Real.log (3 + |(m : ℝ) * t|))
            ≤ Real.log (Real.log N) + Real.log 2 := by
          have h1 : 3 + |(m : ℝ) * t| ≤ N ^ 2 := by
            have habs : |(m : ℝ) * t| = (m : ℝ) * |t| := by
              rw [abs_mul, abs_of_nonneg (le_of_lt hmpos)]
            rw [habs]
            linarith [hsqu, huN]
          have hpos1 : (0 : ℝ) < 3 + |(m : ℝ) * t| := by positivity
          have hlogle : Real.log (3 + |(m : ℝ) * t|) ≤ 2 * Real.log N := by
            have h := Real.log_le_log hpos1 h1
            rw [Real.log_pow] at h
            exact h
          have hlogpos2 : (0 : ℝ) < Real.log (3 + |(m : ℝ) * t|) := by
            apply Real.log_pos
            have := abs_nonneg ((m : ℝ) * t)
            linarith
          calc Real.log (Real.log (3 + |(m : ℝ) * t|))
              ≤ Real.log (2 * Real.log N) := Real.log_le_log hlogpos2 hlogle
            _ = Real.log (Real.log N) + Real.log 2 := by
                rw [Real.log_mul (by norm_num) (ne_of_gt hlogNpos), add_comm]
        linarith [hmert', htw, hid, hlogu]
      have hD1 : (1 / 5) * Real.log (Real.log N) - (Cm + Ct + (4 / 5) * Real.log 2)
            - 2 * ((q : ℝ) + 1) ≤
          (𝔻 (fun _ : ℕ ↦ (1 : ℂ)) (fun n : ℕ ↦ (1 : DirichletCharacter ℂ (q : ℕ)) n *
            (n : ℂ) ^ (Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) N) ^ 2 := by
        linarith [hlowSum, hkey1, hkey2, hsplit]
      have hmul := dist_one_sq_le_mul (q : ℕ) χ m hm1 hmeven hpow t N
      have hArith : (m : ℝ) ^ 2 * (B + 1) ^ 2 ≤
          (1 / 5) * Real.log (Real.log N) - (Cm + Ct + (4 / 5) * Real.log 2) - 2 * ((q : ℝ) + 1) := by
        have hqle : (q : ℝ) + 1 ≤ Qn + 1 := by
          have h1 : ((q : ℕ) : ℝ) ≤ Qn := by rw [hQn]; exact_mod_cast hq
          linarith
        have hm2 : (m : ℝ) ^ 2 ≤ (2 * Qn) ^ 2 := by
          have h1 : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hmpos
          have h2 : (0 : ℝ) ≤ 2 * Qn := by positivity
          nlinarith [hmle, h1, h2]
        have h3 : (m : ℝ) ^ 2 * (B + 1) ^ 2 ≤ (2 * Qn) ^ 2 * (B + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hm2 (by positivity)
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
          linarith
        have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith [h3, hbig2, hqle, hlog2, hlog2nn]
      have hkey : (B + 1) ^ 2 ≤ (𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
          (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N) ^ 2 := by
        have hm2pos : 0 < (m : ℝ) ^ 2 := by positivity
        have h1 : (m : ℝ) ^ 2 * (B + 1) ^ 2 ≤
            (m : ℝ) ^ 2 * (𝔻 (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
              (fun n : ℕ ↦ χ n * (n : ℂ) ^ (Complex.I * (t : ℂ))) N) ^ 2 :=
          le_trans hArith (le_trans hD1 hmul)
        exact le_of_mul_le_mul_left h1 hm2pos
      exact le_dist_of_sq_le _ _ N B liouville_cp_oneBounded
        (isOneBounded_chi_cpow (q : ℕ) χ t) hkey
    filter_upwards [hT, hM, hL] with N hTN hMN hLN
    intro q hq χ t ht
    rcases lt_or_ge (1 : ℝ) ((2 * ((q : ℕ).totient) : ℝ) * |t|) with hbig | hsmall
    · exact hLN q hq χ t ht hbig
    · rcases le_or_gt ((2 * ((q : ℕ).totient) : ℝ) * |t| * Real.log N) K with htiny | hmid
      · exact hTN q hq χ t ht htiny
      · exact hMN q hq χ t ht hmid hsmall
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hpoint
  refine ⟨max 1 (((max N₀ 0) / Cc) ^ (1 / (θ₁ * ((k : ℝ) + 1))) + 1), ?_⟩
  intro Y H hY hHY hH
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hYstep : ((max N₀ 0) / Cc) ^ (1 / (θ₁ * ((k : ℝ) + 1))) + 1 ≤ Y :=
    le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hθk : (0 : ℝ) < θ₁ * ((k : ℝ) + 1) := by
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    positivity
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hY0 θ₁) hHY
  have hNnonneg : (0 : ℝ) ≤ Cc * Y ^ (k + 1) / H ^ (k + 1) := by positivity
  have hNge : N₀ ≤ Cc * Y ^ (k + 1) / H ^ (k + 1) := by
    have hYpow : (((max N₀ 0) / Cc) ^ (1 / (θ₁ * ((k : ℝ) + 1)))) ^ (θ₁ * ((k : ℝ) + 1))
        = (max N₀ 0) / Cc := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (max N₀ 0) / Cc)]
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hθk), Real.rpow_one]
    have h1 : (max N₀ 0) / Cc ≤ Y ^ (θ₁ * ((k : ℝ) + 1)) := by
      rw [← hYpow]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) (by linarith [hYstep]) (le_of_lt hθk)
    have h2 : Cc * ((max N₀ 0) / Cc) ≤ Cc * Y ^ (θ₁ * ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC)
    have h3 : (max N₀ 0) ≤ Cc * Y ^ (θ₁ * ((k : ℝ) + 1)) := by
      have h4 : Cc * ((max N₀ 0) / Cc) = max N₀ 0 := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hC)]
      linarith [h2, h4.symm.le, h4.le]
    have h5 : H ^ (k + 1) ≤ (Y ^ (1 - θ₁)) ^ (k + 1) :=
      pow_le_pow_left₀ (le_of_lt hHpos) hH (k + 1)
    have h6 : (Y ^ (1 - θ₁)) ^ (k + 1) = Y ^ ((1 - θ₁) * ((k : ℝ) + 1)) := by
      rw [← Real.rpow_mul_natCast (le_of_lt hY0) (1 - θ₁) (k + 1)]
      congr 1
      push_cast
      ring
    have hYk : Y ^ (k + 1) = Y ^ ((k : ℝ) + 1) := by
      rw [← Real.rpow_natCast Y (k + 1)]
      congr 1
      push_cast
      ring
    have h6' : H ^ (k + 1) ≤ Y ^ ((1 - θ₁) * ((k : ℝ) + 1)) := by
      rw [← h6]; exact h5
    have h7 : Cc * Y ^ ((k : ℝ) + 1) / Y ^ ((1 - θ₁) * ((k : ℝ) + 1))
        ≤ Cc * Y ^ (k + 1) / H ^ (k + 1) := by
      rw [hYk, div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact inv_anti₀ (by positivity : (0:ℝ) < H ^ (k + 1)) h6'
    have h8 : Cc * Y ^ ((k : ℝ) + 1) / Y ^ ((1 - θ₁) * ((k : ℝ) + 1))
        = Cc * Y ^ (θ₁ * ((k : ℝ) + 1)) := by
      rw [mul_div_assoc, ← Real.rpow_sub hY0]
      congr 1
      congr 1
      ring
    rw [h8] at h7
    linarith [h3, h7, le_max_left N₀ 0]
  have hpt := hN₀ (Cc * Y ^ (k + 1) / H ^ (k + 1)) hNge
  have hM : B + 1 ≤ M (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
      (Cc * Y ^ (k + 1) / H ^ (k + 1)) Q := by
    haveI hne1 : Nonempty {t : ℝ // |t| ≤ Cc * Y ^ (k + 1) / H ^ (k + 1)} :=
      ⟨⟨0, by simpa using hNnonneg⟩⟩
    haveI hne2 : Nonempty {q : ℕ+ // q ≤ Q} := ⟨⟨1, by exact_mod_cast Q.pos⟩⟩
    refine le_ciInf (fun t => ?_)
    refine le_ciInf (fun q => ?_)
    refine le_ciInf (fun χ => ?_)
    exact hpt q.1 q.2 χ t.1 t.2
  linarith

/-- **N11. The Liouville function is multiplicative, `1`-bounded and uniformly
non-pretentious** at every scale `C Y^{k+1}/H^{k+1}` with `Y^{θ₁} ≤ H ≤ Y^{1-θ₁}`:
`M(λ; C Y^{k+1}/H^{k+1}, Q) > B` for `Y` large. Route: `𝔻(1, χ₀ n^{imt}) ≤ 2 ord(χ) 𝔻(λ, χ n^{it})`,
then N10 for large `|t|`, the PNT for middle `|t|`, and primes `≡ 1 (mod q)`
for tiny `|t|`. -/
theorem liouville_facts (k : ℕ) (θ₁ C : ℝ) (hθ₀ : 0 < θ₁) (hθ₁ : θ₁ < 1 / 2) (hC : 0 < C)
    (Q : ℕ+) (B : ℝ) :
    ((ArithmeticFunction.liouville : ArithmeticFunction ℂ).IsMultiplicative ∧
      IsOneBounded (ArithmeticFunction.liouville : ArithmeticFunction ℂ)) ∧
    ∃ Y₀ : ℝ, ∀ Y H : ℝ, Y₀ ≤ Y → Y ^ θ₁ ≤ H → H ≤ Y ^ (1 - θ₁) →
      B < M (ArithmeticFunction.liouville : ArithmeticFunction ℂ)
        (C * Y ^ (k + 1) / H ^ (k + 1)) Q := by
  refine ⟨⟨?_, liouville_cp_oneBounded⟩, ?_⟩
  · exact ArithmeticFunction.isMultiplicative_liouville.intCast
  · exact liouville_facts_aux k θ₁ C hθ₀ hθ₁ hC Q B

end Work.BMF
