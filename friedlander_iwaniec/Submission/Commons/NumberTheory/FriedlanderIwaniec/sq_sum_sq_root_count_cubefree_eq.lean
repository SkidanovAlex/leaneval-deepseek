import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_eq_gcd_mul
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_eq_prod_factorization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_one_add_chi4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

private lemma gcd_pow_eq_gcd_of_squarefree {a b : ℕ} (hb : Squarefree b) :
    Nat.gcd (a ^ 2) b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · have h1 : Nat.gcd (a ^ 2) b ∣ b := Nat.gcd_dvd_right _ _
    have hsq : Squarefree (Nat.gcd (a ^ 2) b) := hb.squarefree_of_dvd h1
    have h2 : Nat.gcd (a ^ 2) b ∣ a ^ 2 := Nat.gcd_dvd_left _ _
    have h3 : Nat.gcd (a ^ 2) b ∣ a :=
      (hsq.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    exact Nat.dvd_gcd h3 h1
  · exact Nat.dvd_gcd
      (dvd_trans (Nat.gcd_dvd_left a b) (dvd_pow_self a (by norm_num : (2 : ℕ) ≠ 0)))
      (Nat.gcd_dvd_right a b)

private lemma sq_roots_neg_one_ncard_cast_eq_prod {n : ℕ} (hn4 : ¬ 4 ∣ n) (hn : n ≠ 0) :
    (({α : ZMod n | α ^ 2 = -1}.ncard : ℕ) : ℤ) =
      (n.primeFactors).prod (fun p => (1 + ZMod.χ₄ (p : ZMod 4))) := by
  rw [sq_roots_neg_one_eq_prod_factorization (Nat.pos_of_ne_zero hn)]
  push_cast
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have he : 1 ≤ n.factorization p := hp'.factorization_pos_of_dvd hn hpdvd
  have h4 : ¬ 4 ∣ p ^ n.factorization p := fun h => hn4 (h.trans (Nat.ordProj_dvd n p))
  exact sq_roots_neg_one_mod_prime_pow_eq_one_add_chi4 hp' he h4

private lemma sq_roots_neg_one_ncard_eq_of_primeFactors_eq {m n : ℕ} (hm : ¬ 4 ∣ m) (hn : ¬ 4 ∣ n)
    (h : m.primeFactors = n.primeFactors) :
    ({α : ZMod m | α ^ 2 = -1}.ncard) = ({α : ZMod n | α ^ 2 = -1}.ncard) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 4)
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero 4)
  apply Nat.cast_injective (R := ℤ)
  rw [sq_roots_neg_one_ncard_cast_eq_prod hm hm0, sq_roots_neg_one_ncard_cast_eq_prod hn hn0, h]

private lemma prod_primeFactors_half_factorization_eq {d d₁ d₂ : ℕ} (hd0 : 0 < d)
    (hd : d = d₁ * d₂ ^ 2) (hs₁ : Squarefree d₁) (_hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) :
    (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) = d₂ := by
  have hd2 : d₂ ≠ 0 := by rintro h; rw [h] at hd; simp at hd; exact hd0.ne' hd
  have hd1 : d₁ ≠ 0 := by rintro h; rw [h] at hd; simp at hd; exact hd0.ne' hd
  have hle1 : ∀ p, d₁.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hd1).mp hs₁
  have hcop' : Nat.Coprime d₁ (d₂ ^ 2) := hcop.pow_right 2
  have hdfac : ∀ p, d.factorization p = d₁.factorization p + 2 * d₂.factorization p := by
    intro p
    have h1 : d.factorization = d₁.factorization + (d₂ ^ 2).factorization := by
      rw [hd, Nat.factorization_mul_of_coprime hcop']
    rw [h1, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hhalf : ∀ p, d.factorization p / 2 = d₂.factorization p := by
    intro p
    rw [hdfac p]
    have := hle1 p
    omega
  rw [Finset.prod_congr rfl (fun p _ => by rw [hhalf p])]
  have hsub : d₂.primeFactors ⊆ d.primeFactors := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    refine ⟨hp.1, ?_, hd0.ne'⟩
    rw [hd]
    exact dvd_mul_of_dvd_right (dvd_trans hp.2.1 (dvd_pow_self d₂ (by norm_num : (2 : ℕ) ≠ 0))) d₁
  have hf : ∀ x ∈ d.primeFactors, x ∉ d₂.primeFactors → x ^ d₂.factorization x = 1 := by
    intro x hx hxnot
    have hx' : x.Prime := Nat.prime_of_mem_primeFactors hx
    have hnot : ¬ x ∣ d₂ := fun hxd => hxnot (Nat.mem_primeFactors.mpr ⟨hx', hxd, hd2⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnot, pow_zero]
  rw [(Finset.prod_subset hsub hf).symm]
  exact (Nat.prod_primeFactors_pow_factorization hd2).symm

private lemma dvd_iff_factorization_pos {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ∣ n ↔ 0 < n.factorization p := by
  constructor
  · exact Nat.Prime.factorization_pos_of_dvd hp hn
  · intro h
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd] at h
    exact lt_irrefl _ h

private theorem primeFactors_div_gcd_pow_eq {d d₁ d₂ ℓ : ℕ} (hd0 : 0 < d) (hd : d = d₁ * d₂ ^ 2)
    (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂) (hcop : Nat.Coprime d₁ d₂) (_h4 : ¬ 4 ∣ d) :
    (d / Nat.gcd (ℓ ^ 4) d).primeFactors =
      (d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂)).primeFactors := by
  have hd2 : d₂ ≠ 0 := by rintro h; rw [h] at hd; simp at hd; exact hd0.ne' hd
  have hd1 : d₁ ≠ 0 := by rintro h; rw [h] at hd; simp at hd; exact hd0.ne' hd
  have hd12 : d₁ * d₂ ≠ 0 := mul_ne_zero hd1 hd2
  set D := d / Nat.gcd (ℓ ^ 4) d with hDdef
  set E := d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂) with hEdef
  have hD0 : D ≠ 0 := by
    intro h
    rw [hDdef] at h
    have hdv : d / Nat.gcd (ℓ ^ 4) d ∣ d := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    rw [h] at hdv
    exact hd0.ne' (Nat.eq_zero_of_zero_dvd hdv)
  have hE0 : E ≠ 0 := by
    intro h
    rw [hEdef] at h
    have hdv : d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂) ∣ d₁ * d₂ :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    rw [h] at hdv
    exact hd12 (Nat.eq_zero_of_zero_dvd hdv)
  rcases eq_or_ne ℓ 0 with hℓ0 | hℓ0
  · subst hℓ0
    have hD1 : D = 1 := by
      rw [hDdef, zero_pow (by norm_num : (4 : ℕ) ≠ 0), Nat.gcd_zero_left, Nat.div_self hd0]
    have hE1 : E = 1 := by
      rw [hEdef, Nat.gcd_zero_left, Nat.div_self (Nat.pos_of_ne_zero hd12)]
    rw [hD1, hE1]
  · have hℓ4 : ℓ ^ 4 ≠ 0 := pow_ne_zero _ hℓ0
    have hcop' : Nat.Coprime d₁ (d₂ ^ 2) := hcop.pow_right 2
    have hdfac : ∀ q, d.factorization q = d₁.factorization q + 2 * d₂.factorization q := by
      intro q
      have h1 : d.factorization = d₁.factorization + (d₂ ^ 2).factorization := by
        rw [hd, Nat.factorization_mul_of_coprime hcop']
      rw [h1, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hle1 : ∀ q, d₁.factorization q ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hd1).mp hs₁
    have hle2 : ∀ q, d₂.factorization q ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hd2).mp hs₂
    have hdle2 : ∀ q, d.factorization q ≤ 2 := by
      intro q
      rw [hdfac q]
      have h1 := hle1 q
      have h2 := hle2 q
      by_cases hb1 : d₁.factorization q = 1
      · have hb2 : d₂.factorization q = 0 := by
          by_contra hne
          have hb2' : d₂.factorization q = 1 := by omega
          have hqd1 : q ∣ d₁ := by
            by_contra hnd
            rw [Nat.factorization_eq_zero_of_not_dvd hnd] at hb1
            omega
          have hqd2 : q ∣ d₂ := by
            by_contra hnd
            rw [Nat.factorization_eq_zero_of_not_dvd hnd] at hb2'
            omega
          have hq1 : q ∣ 1 := by
            have hh := Nat.dvd_gcd hqd1 hqd2
            rwa [hcop.gcd_eq_one] at hh
          have hqe : q = 1 := Nat.dvd_one.mp hq1
          rw [hqe] at hb1
          have hz : d₁.factorization 1 = 0 :=
            (Nat.factorization_eq_zero_iff d₁ 1).mpr (Or.inl (by norm_num))
          omega
        omega
      · omega
    have hDfac_eq : D.factorization
        = d.factorization - ((ℓ ^ 4).factorization ⊓ d.factorization) := by
      rw [hDdef, Nat.factorization_div (Nat.gcd_dvd_right (ℓ ^ 4) d),
          Nat.factorization_gcd hℓ4 hd0.ne']
    have hDfac : ∀ p, D.factorization p
        = d.factorization p - min (4 * ℓ.factorization p) (d.factorization p) := by
      intro p
      have h := DFunLike.congr_fun hDfac_eq p
      simp only [Nat.factorization_pow] at h
      exact h
    have hEfac_eq : E.factorization
        = (d₁ * d₂).factorization - (ℓ.factorization ⊓ (d₁ * d₂).factorization) := by
      rw [hEdef, Nat.factorization_div (Nat.gcd_dvd_right ℓ (d₁ * d₂)),
          Nat.factorization_gcd hℓ0 hd12]
    have hEfac : ∀ p, E.factorization p
        = (d₁ * d₂).factorization p - min (ℓ.factorization p) ((d₁ * d₂).factorization p) := by
      intro p
      rw [hEfac_eq]
      rfl
    have hsq12 : Squarefree (d₁ * d₂) := Nat.squarefree_mul_iff.mpr ⟨hcop, hs₁, hs₂⟩
    have h12le1 : ∀ q, (d₁ * d₂).factorization q ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hd12).mp hsq12
    have hpd_iff : ∀ p, p.Prime → (p ∣ d ↔ p ∣ d₁ * d₂) := by
      intro p hp
      constructor
      · intro h
        rw [hd] at h
        rcases hp.dvd_mul.mp h with h1 | h2
        · exact dvd_mul_of_dvd_left h1 d₂
        · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h2) d₁
      · intro h
        rw [hd]
        have := dvd_mul_of_dvd_left h d₂
        simpa [pow_two, mul_assoc] using this
    have hDp : ∀ p, p.Prime → (p ∣ D ↔ p ∣ d ∧ ¬ p ∣ ℓ) := by
      intro p hp
      rw [dvd_iff_factorization_pos hp hD0]
      constructor
      · intro hpos
        rw [hDfac p] at hpos
        have hlt : min (4 * ℓ.factorization p) (d.factorization p) < d.factorization p :=
          Nat.sub_pos_iff_lt.mp hpos
        have h4f : 4 * ℓ.factorization p < d.factorization p := by
          by_contra hc
          rw [Nat.min_eq_right (le_of_not_gt hc)] at hlt
          exact absurd hlt (lt_irrefl _)
        have hepos : 0 < d.factorization p := by omega
        refine ⟨(dvd_iff_factorization_pos hp hd0.ne').mpr hepos, ?_⟩
        intro hpl
        have hp1 : 1 ≤ ℓ.factorization p := hp.factorization_pos_of_dvd hℓ0 hpl
        have := hdle2 p
        omega
      · rintro ⟨hpd, hnpl⟩
        rw [hDfac p]
        have hf0 : ℓ.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnpl
        have hdfp : 0 < d.factorization p := (dvd_iff_factorization_pos hp hd0.ne').mp hpd
        rw [hf0, mul_zero, Nat.min_eq_left (Nat.zero_le _), Nat.sub_zero]
        exact hdfp
    have hEp : ∀ p, p.Prime → (p ∣ E ↔ p ∣ d ∧ ¬ p ∣ ℓ) := by
      intro p hp
      rw [dvd_iff_factorization_pos hp hE0]
      constructor
      · intro hpos
        rw [hEfac p] at hpos
        have hlt : min (ℓ.factorization p) ((d₁ * d₂).factorization p) < (d₁ * d₂).factorization p :=
          Nat.sub_pos_iff_lt.mp hpos
        have hfA : ℓ.factorization p < (d₁ * d₂).factorization p := by
          by_contra hc
          rw [Nat.min_eq_right (le_of_not_gt hc)] at hlt
          exact absurd hlt (lt_irrefl _)
        have hApos : 0 < (d₁ * d₂).factorization p := by omega
        refine ⟨?_, ?_⟩
        · exact (hpd_iff p hp).mpr ((dvd_iff_factorization_pos hp hd12).mpr hApos)
        · intro hpl
          have hp1 : 1 ≤ ℓ.factorization p := hp.factorization_pos_of_dvd hℓ0 hpl
          have := h12le1 p
          omega
      · rintro ⟨hpd, hnpl⟩
        rw [hEfac p]
        have hf0 : ℓ.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnpl
        have hApos : 0 < (d₁ * d₂).factorization p :=
          (dvd_iff_factorization_pos hp hd12).mp ((hpd_iff p hp).mp hpd)
        rw [hf0, Nat.min_eq_left (Nat.zero_le _), Nat.sub_zero]
        exact hApos
    ext p
    rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpD, _⟩
      exact ⟨hp, (hEp p hp).mpr ((hDp p hp).mp hpD), hE0⟩
    · rintro ⟨hp, hpE, _⟩
      exact ⟨hp, (hDp p hp).mpr ((hEp p hp).mp hpE), hD0⟩

theorem sq_sum_sq_root_count_cubefree_eq
    {d d₁ d₂ ℓ : ℕ} (hd0 : 0 < d) (hd : d = d₁ * d₂ ^ 2)
    (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂) (hcop : Nat.Coprime d₁ d₂)
    (h4 : ¬ 4 ∣ d) :
    ({α : ZMod d | α ^ 2 + (((ℓ ^ 4 : ℕ) : ZMod d)) = 0}).ncard =
      Nat.gcd ℓ d₂ *
        ({α : ZMod (d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂)) | α ^ 2 = -1}.ncard) := by
  have hcast : ((ℓ ^ 4 : ℕ) : ZMod d) = (((ℓ ^ 2 : ℕ) : ZMod d)) ^ 2 := by
    push_cast
    ring
  rw [hcast]
  rw [sq_sum_sq_root_count_eq_gcd_mul (d := d) (b := ℓ ^ 2) hd0]
  have hpow : (ℓ ^ 2) ^ 2 = ℓ ^ 4 := by ring
  rw [hpow]
  have hP : (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) = d₂ :=
    prod_primeFactors_half_factorization_eq hd0 hd hs₁ hs₂ hcop
  have hg : Nat.gcd (ℓ ^ 2) ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)))
      = Nat.gcd ℓ d₂ := by
    rw [hP, gcd_pow_eq_gcd_of_squarefree hs₂]
  have hD4 : ¬ 4 ∣ d / Nat.gcd (ℓ ^ 4) d := by
    intro h
    exact h4 (h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  have hE4 : ¬ 4 ∣ d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂) := by
    intro h
    have h1 : d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂) ∣ d₁ * d₂ :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    have h2 : d₁ * d₂ ∣ d := by
      rw [hd]
      exact ⟨d₂, by ring⟩
    exact h4 (h.trans (dvd_trans h1 h2))
  have hpf := primeFactors_div_gcd_pow_eq (ℓ := ℓ) hd0 hd hs₁ hs₂ hcop h4
  have hM : ({α : ZMod (d / Nat.gcd (ℓ ^ 4) d) | α ^ 2 = -1}.ncard)
      = ({α : ZMod (d₁ * d₂ / Nat.gcd ℓ (d₁ * d₂)) | α ^ 2 = -1}.ncard) :=
    sq_roots_neg_one_ncard_eq_of_primeFactors_eq hD4 hE4 hpf
  rw [hg, hM]

end Commons.NumberTheory.FriedlanderIwaniec
