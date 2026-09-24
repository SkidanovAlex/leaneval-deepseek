import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.upper_moebius
import Submission.Work.ChenPlan.LinearSieve.RI.support_lt
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_error_le
import Submission.Work.ChenPlan.LinearSieve.Assembly.rem_bound_plus
import Submission.Work.ChenPlan.LinearSieve.FrameworkR

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators
open Work.ChenPlan.LinearSieve.RI

set_option maxHeartbeats 1600000

noncomputable section

/-! ## Auxiliary lemmas for the `Q`-trick -/

/-- `Σ_{d ∣ m} μ(d) = [m = 1]`. -/
private lemma moebius_sum_divisors (m : ℕ) :
    (∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if m = 1 then 1 else 0 := by
  have h : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) m)
      = (1 : ArithmeticFunction ℤ) m := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  exact_mod_cast h

/-- `|λ⁺(d)| ≤ 3^{ω(d)}`. -/
private lemma abs_lamPlus_le_card (P : ℕ) (D : ℝ) (d : ℕ) :
    |lamPlus P D d| ≤ (3 : ℝ) ^ d.primeFactors.card := by
  by_cases h : d ∣ P ∧ rdPlus D d
  · have hlm : lamPlus P D d = ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
      unfold lamPlus; rw [if_pos h]
    rw [hlm]
    have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
    linarith
  · have hlm : lamPlus P D d = 0 := by unfold lamPlus; rw [if_neg h]
    rw [hlm, abs_zero]
    positivity

/-- `(q,d) ↦ q·d` is injective on `q ∣ Q`, `d ∣ R` when `Q` and `R` are coprime. -/
private lemma mul_inj_coprime {Q R q d q' d' : ℕ} (hQ0 : Q ≠ 0) (hQR : Nat.Coprime Q R)
    (hq : q ∣ Q) (hd : d ∣ R) (hq' : q' ∣ Q) (hd' : d' ∣ R) (h : q * d = q' * d') :
    q = q' ∧ d = d' := by
  have hqd' : Nat.Coprime q d' := (hQR.coprime_dvd_left hq).coprime_dvd_right hd'
  have hq'd : Nat.Coprime q' d := (hQR.coprime_dvd_left hq').coprime_dvd_right hd
  have h1 : q ∣ q' := hqd'.dvd_of_dvd_mul_right (h ▸ dvd_mul_right q d)
  have h2 : q' ∣ q := hq'd.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right q' d')
  have hqq : q = q' := Nat.dvd_antisymm h1 h2
  have hq0 : q ≠ 0 := fun hz => hQ0 (zero_dvd_iff.mp (hz ▸ hq))
  exact ⟨hqq, mul_left_cancel₀ hq0 (by rw [← hqq] at h; exact h)⟩

/-- **The pointwise `Q`-trick inequality.**  The Möbius inversion `1_{(n,Q)=1} =
Σ_{q ∣ Q, q ∣ n} μ(q)` together with the upper Möbius property of `λ⁺` for the `P/Q`-problem
dominates the sifting indicator. -/
private theorem qtInd_le_double (A : BoundingSieve) (Q R : ℕ) (Z D' : ℝ)
    (hQ0 : Q ≠ 0) (hR0 : R ≠ 0) (hQdvd : Q ∣ A.prodPrimes) (hR_dvd : R ∣ A.prodPrimes / Q)
    (hQR : Nat.Coprime Q R) (hD' : 1 < D')
    (hQsub : ∀ p ∈ Q.primeFactors, p ∈ A.prodPrimes.primeFactors ∧ (p:ℝ) < Z)
    (hRsub : ∀ p ∈ R.primeFactors, p ∈ A.prodPrimes.primeFactors ∧ (p:ℝ) < Z)
    (n : ℕ) :
    (if ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < Z → ¬ p ∣ n then (1:ℝ) else 0)
      ≤ ∑ q ∈ Q.divisors, ∑ d ∈ R.divisors,
          ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Q) D' d
            * (if q * d ∣ n then (1:ℝ) else 0) := by
  classical
  have hQsq : Squarefree Q := Squarefree.squarefree_of_dvd hQdvd A.prodPrimes_squarefree
  have hdivsq : Squarefree (A.prodPrimes / Q) := by
    have hmul : Q * (A.prodPrimes / Q) = A.prodPrimes := Nat.mul_div_cancel' hQdvd
    have hsf : Squarefree (Q * (A.prodPrimes / Q)) := by rw [hmul]; exact A.prodPrimes_squarefree
    exact (Nat.squarefree_mul_iff.mp hsf).2.2
  have hAAeq : (∑ q ∈ Q.divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
      = if Nat.gcd n Q = 1 then (1:ℝ) else 0 := by
    have h1 : (∑ q ∈ Q.divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
        = ∑ q ∈ Q.divisors, (if q ∣ n then ((ArithmeticFunction.moebius q : ℤ):ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun q _ => ?_)
      by_cases h : q ∣ n <;> simp [h]
    rw [h1, ← Finset.sum_filter]
    have hset : Q.divisors.filter (fun q => q ∣ n) = (Nat.gcd n Q).divisors := by
      ext d
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdQ, -⟩, hdn⟩
        exact ⟨Nat.dvd_gcd hdn hdQ, fun h => hQ0 (Nat.gcd_eq_zero_iff.mp h).2⟩
      · rintro ⟨hdg, -⟩
        exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_right n Q), hQ0⟩, dvd_trans hdg (Nat.gcd_dvd_left n Q)⟩
    rw [hset]
    exact moebius_sum_divisors (Nat.gcd n Q)
  have hBBeq : (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0))
      = Wp (Nat.gcd n R) D' := by
    have h1 : (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0))
        = ∑ d ∈ R.divisors, (if d ∣ n then lamPlus (A.prodPrimes / Q) D' d else 0) := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      by_cases h : d ∣ n <;> simp [h]
    rw [h1, ← Finset.sum_filter]
    have hset : R.divisors.filter (fun d => d ∣ n) = (Nat.gcd n R).divisors := by
      ext d
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdR, -⟩, hdn⟩
        exact ⟨Nat.dvd_gcd hdn hdR, fun h => hR0 (Nat.gcd_eq_zero_iff.mp h).2⟩
      · rintro ⟨hdg, -⟩
        exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_right n R), hR0⟩, dvd_trans hdg (Nat.gcd_dvd_left n R)⟩
    rw [hset, Wp]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdR : d ∣ R := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right n R)
    have hdP : d ∣ A.prodPrimes / Q := dvd_trans hdR hR_dvd
    unfold lamPlus
    by_cases h : rdPlus D' d
    · rw [if_pos ⟨hdP, h⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.2), if_neg h]
  have hfac : (∑ q ∈ Q.divisors, ∑ d ∈ R.divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ)
        * lamPlus (A.prodPrimes / Q) D' d * (if q * d ∣ n then (1:ℝ) else 0))
      = (∑ q ∈ Q.divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
        * (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0)) := by
    have hinner : ∀ q ∈ Q.divisors, ∀ d ∈ R.divisors,
        ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Q) D' d
            * (if q * d ∣ n then (1:ℝ) else 0)
        = (((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
          * (lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0)) := by
      intro q hq d hd
      have hqQ : q ∣ Q := (Nat.mem_divisors.mp hq).1
      have hdR : d ∣ R := (Nat.mem_divisors.mp hd).1
      have hqd : Nat.Coprime q d := (hQR.coprime_dvd_left hqQ).coprime_dvd_right hdR
      have hiff : (if q * d ∣ n then (1:ℝ) else 0)
          = (if q ∣ n then (1:ℝ) else 0) * (if d ∣ n then (1:ℝ) else 0) := by
        by_cases hqn : q ∣ n
        · by_cases hdn : d ∣ n
          · rw [if_pos (hqd.mul_dvd_of_dvd_of_dvd hqn hdn), if_pos hqn, if_pos hdn]; norm_num
          · rw [if_neg (fun h => hdn (dvd_trans (dvd_mul_left d q) h)), if_pos hqn, if_neg hdn]; ring
        · rw [if_neg (fun h => hqn (dvd_trans (dvd_mul_right q d) h)), if_neg hqn]; ring
      rw [hiff]; ring
    calc (∑ q ∈ Q.divisors, ∑ d ∈ R.divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ)
            * lamPlus (A.prodPrimes / Q) D' d * (if q * d ∣ n then (1:ℝ) else 0))
        = ∑ q ∈ Q.divisors, ∑ d ∈ R.divisors,
            (((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
            * (lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0)) :=
          Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun d hd => hinner q hq d hd))
      _ = ∑ q ∈ Q.divisors, (((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
            * (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0)) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.mul_sum]
      _ = (∑ q ∈ Q.divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ) * (if q ∣ n then (1:ℝ) else 0))
            * (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Q) D' d * (if d ∣ n then (1:ℝ) else 0)) := by
          rw [Finset.sum_mul]
  rw [hfac, hAAeq, hBBeq]
  by_cases hcond : ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < Z → ¬ p ∣ n
  · rw [if_pos hcond]
    have hgQ : Nat.gcd n Q = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      rw [← Nat.prod_primeFactors_of_squarefree hQsq, Nat.coprime_prod_right_iff]
      intro p hp
      exact Nat.coprime_comm.mp ((Nat.mem_primeFactors.mp hp).1.coprime_iff_not_dvd.mpr
        (hcond p (hQsub p hp).1 (hQsub p hp).2))
    have hgR : Nat.gcd n R = 1 := by
      have hRsq : Squarefree R := Squarefree.squarefree_of_dvd hR_dvd hdivsq
      rw [← Nat.coprime_iff_gcd_eq_one]
      rw [← Nat.prod_primeFactors_of_squarefree hRsq, Nat.coprime_prod_right_iff]
      intro p hp
      exact Nat.coprime_comm.mp ((Nat.mem_primeFactors.mp hp).1.coprime_iff_not_dvd.mpr
        (hcond p (hRsub p hp).1 (hRsub p hp).2))
    rw [if_pos hgQ, hgR]
    have h1 := (Wm_Wp_bounds 1 squarefree_one).2 D' (show (0:ℝ) ≤ D' by linarith)
    simp only [if_true] at h1
    linarith
  · rw [if_neg hcond]
    have h1 : (0:ℝ) ≤ (if Nat.gcd n Q = 1 then (1:ℝ) else 0) := by split <;> norm_num
    have h2 : (0:ℝ) ≤ Wp (Nat.gcd n R) D' := by
      have hRsq : Squarefree R := Squarefree.squarefree_of_dvd hR_dvd hdivsq
      have hgsq : Squarefree (Nat.gcd n R) :=
        Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right n R) hRsq
      have h3 := (Wm_Wp_bounds (Nat.gcd n R) hgsq).2 D' (show (0:ℝ) ≤ D' by linarith)
      have hnn : (0:ℝ) ≤ (if Nat.gcd n R = 1 then (1:ℝ) else 0) := by split <;> norm_num
      linarith
    exact mul_nonneg h1 h2

/-- **The `3^{ω}`-weighted remainder bound for the `Q`-trick.**  Since `(q,d) ↦ q·d` is injective
on `q ∣ Q`, `d ∣ R` and every upper-admissible `d` satisfies `d < D'`, the double remainder sum is
dominated by the single `remSum`-shaped sum over the divisors of `P(Z)` below `Q·D'`. -/
private theorem double_rem_le (A : BoundingSieve) (Q R : ℕ) (Z D' : ℝ)
    (hQ0 : Q ≠ 0) (hQR : Nat.Coprime Q R) (hD' : 1 < D')
    (hQdvdPz : Q ∣ Pz A Z) (hRdvdPz : R ∣ Pz A Z) :
    (∑ q ∈ Q.divisors, ∑ d ∈ R.divisors,
        |((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Q) D' d| * |A.rem (q * d)|)
      ≤ ∑ m ∈ (Pz A Z).divisors.filter (fun m : ℕ => (m : ℝ) < (Q : ℝ) * D'),
          (3 : ℝ) ^ m.primeFactors.card * |A.rem m| := by
  classical
  have hRsq : Squarefree R := Squarefree.squarefree_of_dvd hRdvdPz (RI.Pz_squarefree A Z)
  have hpt : ∀ q ∈ Q.divisors, ∀ d ∈ R.divisors,
      |((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Q) D' d| * |A.rem (q * d)|
        ≤ (if ((q * d : ℕ) : ℝ) < (Q : ℝ) * D' then
              (3 : ℝ) ^ (q * d).primeFactors.card * |A.rem (q * d)| else 0) := by
    intro q hq d hd
    have hqQ : q ∣ Q := (Nat.mem_divisors.mp hq).1
    have hdR : d ∣ R := (Nat.mem_divisors.mp hd).1
    have hq0 : q ≠ 0 := fun h => hQ0 (zero_dvd_iff.mp (h ▸ hqQ))
    have hd0 : d ≠ 0 := by
      intro h
      have hR0 : R = 0 := zero_dvd_iff.mp (h ▸ hdR)
      exact RI.Pz_ne_zero A Z (zero_dvd_iff.mp (hR0 ▸ hRdvdPz))
    by_cases hlt : ((q * d : ℕ) : ℝ) < (Q : ℝ) * D'
    · rw [if_pos hlt]
      have hmu1 : |((ArithmeticFunction.moebius q : ℤ):ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hlamL : |lamPlus (A.prodPrimes / Q) D' d| ≤ (3 : ℝ) ^ d.primeFactors.card :=
        abs_lamPlus_le_card _ _ _
      have hcard : d.primeFactors.card ≤ (q * d).primeFactors.card :=
        Finset.card_le_card (Nat.primeFactors_mono (dvd_mul_left d q) (mul_ne_zero hq0 hd0))
      have hpow : (3 : ℝ) ^ d.primeFactors.card ≤ (3 : ℝ) ^ (q * d).primeFactors.card :=
        pow_le_pow_right₀ (by norm_num) hcard
      have h5 : |((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Q) D' d|
          ≤ (3 : ℝ) ^ (q * d).primeFactors.card := by
        rw [abs_mul]
        calc |((ArithmeticFunction.moebius q : ℤ):ℝ)| * |lamPlus (A.prodPrimes / Q) D' d|
            ≤ 1 * (3 : ℝ) ^ d.primeFactors.card :=
              mul_le_mul hmu1 hlamL (abs_nonneg _) (by norm_num)
          _ ≤ (3 : ℝ) ^ (q * d).primeFactors.card := by rw [one_mul]; exact hpow
      exact mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
    · rw [if_neg hlt]
      have hlam : lamPlus (A.prodPrimes / Q) D' d = 0 := by
        by_cases hc : d ∣ A.prodPrimes / Q ∧ rdPlus D' d
        · exfalso
          have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdR hRsq
          have hdlt : (d:ℝ) < D' := rdPlus_lt hD' hdsq hc.2
          have hqle : (q:ℝ) ≤ (Q:ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0) hqQ
          have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQ0
          have hdnn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
          have hle : ((q * d : ℕ) : ℝ) ≤ (Q:ℝ) * (d:ℝ) := by
            rw [Nat.cast_mul]
            exact mul_le_mul_of_nonneg_right hqle hdnn
          have hlt2 : (Q:ℝ) * (d:ℝ) < (Q:ℝ) * D' := mul_lt_mul_of_pos_left hdlt hQpos
          exact absurd (lt_of_le_of_lt hle hlt2) hlt
        · unfold lamPlus; rw [if_neg hc]
      rw [hlam]
      simp
  calc (∑ q ∈ Q.divisors, ∑ d ∈ R.divisors,
          |((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Q) D' d| * |A.rem (q * d)|)
      ≤ ∑ q ∈ Q.divisors, ∑ d ∈ R.divisors,
          (if ((q * d : ℕ) : ℝ) < (Q : ℝ) * D' then
              (3 : ℝ) ^ (q * d).primeFactors.card * |A.rem (q * d)| else 0) :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun d hd => hpt q hq d hd))
    _ = ∑ p ∈ (Q.divisors ×ˢ R.divisors).filter
            (fun p : ℕ × ℕ => ((p.1 * p.2 : ℕ) : ℝ) < (Q : ℝ) * D'),
          (3 : ℝ) ^ (p.1 * p.2).primeFactors.card * |A.rem (p.1 * p.2)| := by
        rw [← Finset.sum_product', ← Finset.sum_filter]
    _ = ∑ m ∈ ((Q.divisors ×ˢ R.divisors).filter
            (fun p : ℕ × ℕ => ((p.1 * p.2 : ℕ) : ℝ) < (Q : ℝ) * D')).image
              (fun p : ℕ × ℕ => p.1 * p.2),
          (3 : ℝ) ^ m.primeFactors.card * |A.rem m| := by
        rw [Finset.sum_image]
        intro p hp p' hp' h
        obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp1', -⟩ := Finset.mem_filter.mp hp'
        obtain ⟨hq, hd⟩ := Finset.mem_product.mp hp1
        obtain ⟨hq', hd'⟩ := Finset.mem_product.mp hp1'
        obtain ⟨h1, h2⟩ := mul_inj_coprime hQ0 hQR (Nat.mem_divisors.mp hq).1
          (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hq').1 (Nat.mem_divisors.mp hd').1 h
        exact Prod.ext h1 h2
    _ ≤ ∑ m ∈ (Pz A Z).divisors.filter (fun m : ℕ => (m : ℝ) < (Q : ℝ) * D'),
          (3 : ℝ) ^ m.primeFactors.card * |A.rem m| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
        intro m hm
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        obtain ⟨hq, hd⟩ := Finset.mem_product.mp hp1
        have hqQ : p.1 ∣ Q := (Nat.mem_divisors.mp hq).1
        have hdR : p.2 ∣ R := (Nat.mem_divisors.mp hd).1
        have hqd : Nat.Coprime p.1 p.2 := (hQR.coprime_dvd_left hqQ).coprime_dvd_right hdR
        have hdvd : p.1 * p.2 ∣ Pz A Z :=
          hqd.mul_dvd_of_dvd_of_dvd (dvd_trans hqQ hQdvdPz) (dvd_trans hdR hRdvdPz)
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, RI.Pz_ne_zero A Z⟩, hp2⟩

/-- The **`Q`-trick core** (upper form): splitting off the Möbius sum over the small primes
`Q = Qmod A u₀` (the product of the primes of `P` below `u₀`) turns the sifted sum into a
`λ⁺`-weighted double sum over `q ∣ Q`, `d ∣ (P/Q)(Z)`, whose main term factorises as
`∏_{p ∣ Q}(1-ν_p) × Σ_d λ⁺(d)ν_d` and whose remainder is dominated by the `3^ω`-weighted remainder
sum.  The key point is that `(q,d) ↦ q·d` is *injective* on `q ∣ Q`, `d ∣ P/Q` (the two are
coprime), so the remainder does not blow up by `2^{ω(Q)}`.  `u₀ ≤ Z` ensures `Q ∣ Pz A Z`, i.e.
every prime removed by the Möbius factor is actually being sifted.

Vocabulary in `JR2/Defs.lean`: `Qmod A u₀ = ∏_{p ∣ P, p < u₀} p`, `Qmod_dvd`,
`subSieve A Q hQ` (same support/weights/`totalMass`/`ν`, `prodPrimes = P/Q`), and
`Work.ChenPlan.LinearSieve.Pz`, `lamPlus`, `VfR`, `siftedSumR`, `remSum`.
Ingredients: `RI/basic.lean` (`lamPlus`), `RI/upper_moebius.lean`, `BoundingSieve.multSum`,
`BoundingSieve.multSum_eq_main_err`, `Nat.divisors`, `Finset.prod_dvd_prod_of_subset`, and the
multiplicativity `A.nu_mult`. -/
theorem q_trick_upper_core (A : BoundingSieve) (u₀ Z D' : ℝ) (hu₀ : 2 ≤ u₀) (hu₀Z : u₀ ≤ Z)
    (hZ : 2 ≤ Z) (hD' : 1 < D') :
    ( Work.ChenPlan.LinearSieve.siftedSumR A Z
        ≤ ∑ q ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).divisors,
            ∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
              ((ArithmeticFunction.moebius q : ℤ) : ℝ)
                * (Work.ChenPlan.LinearSieve.lamPlus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)
                * A.multSum (q * d) )
    ∧ ( (∑ q ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).divisors,
            ∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
              ((ArithmeticFunction.moebius q : ℤ) : ℝ)
                * (Work.ChenPlan.LinearSieve.lamPlus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)
                * A.nu (q * d))
          = (∏ p ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).primeFactors, (1 - A.nu p))
              * (∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
                  (Work.ChenPlan.LinearSieve.lamPlus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)
                    * A.nu d) )
    ∧ ( (∑ q ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).divisors,
            ∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
              |((ArithmeticFunction.moebius q : ℤ) : ℝ)
                * (Work.ChenPlan.LinearSieve.lamPlus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)|
                * |A.rem (q * d)|)
          ≤ ∑ m ∈ (Work.ChenPlan.LinearSieve.Pz A Z).divisors.filter
                  (fun m : ℕ => (m : ℝ) < (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ) * D'),
              (3 : ℝ) ^ m.primeFactors.card * |A.rem m| ) := by
  classical
  set R : ℕ := Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) Z with hRdef
  have hQdvd : Qmod A u₀ ∣ A.prodPrimes := Qmod_dvd A u₀
  have hQ0 : Qmod A u₀ ≠ 0 := ne_zero_of_dvd_ne_zero A.prodPrimes_ne_zero hQdvd
  have hR0 : R ≠ 0 := by rw [hRdef]; exact RI.Pz_ne_zero _ Z
  have hQdvdPz : Qmod A u₀ ∣ Pz A Z := by
    rw [Qmod]
    rw [show Pz A Z = ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < Z), p from rfl]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, lt_of_lt_of_le hp.2 hu₀Z⟩
  have hRdvdPz : R ∣ Pz A Z := by
    rw [hRdef, Pz, Pz]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    have hp1 : p ∈ A.prodPrimes.primeFactors :=
      Nat.primeFactors_mono (Nat.div_dvd_of_dvd (Qmod_dvd A u₀)) A.prodPrimes_ne_zero hp.1
    exact ⟨hp1, hp.2⟩
  have hQcop : Nat.Coprime (Qmod A u₀) (A.prodPrimes / Qmod A u₀) := by
    have hmul : Qmod A u₀ * (A.prodPrimes / Qmod A u₀) = A.prodPrimes :=
      Nat.mul_div_cancel' hQdvd
    have hsf : Squarefree (Qmod A u₀ * (A.prodPrimes / Qmod A u₀)) := by
      rw [hmul]; exact A.prodPrimes_squarefree
    exact (Nat.squarefree_mul_iff.mp hsf).1
  have hR_dvd : R ∣ A.prodPrimes / Qmod A u₀ := by
    rw [hRdef]; exact RI.Pz_dvd_prodPrimes _ Z
  have hQR : Nat.Coprime (Qmod A u₀) R := Nat.Coprime.coprime_dvd_right hR_dvd hQcop
  have hQsq : Squarefree (Qmod A u₀) := Squarefree.squarefree_of_dvd hQdvd A.prodPrimes_squarefree
  have hQsub : ∀ p ∈ (Qmod A u₀).primeFactors,
      p ∈ A.prodPrimes.primeFactors ∧ (p:ℝ) < Z := by
    have hpf : (Qmod A u₀).primeFactors
        = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < u₀) := RI.Pz_primeFactors A u₀
    intro p hp
    rw [hpf] at hp
    exact ⟨(Finset.mem_filter.mp hp).1, lt_of_lt_of_le (Finset.mem_filter.mp hp).2 hu₀Z⟩
  have hRsub : ∀ p ∈ R.primeFactors, p ∈ A.prodPrimes.primeFactors ∧ (p:ℝ) < Z := by
    have hpf : R.primeFactors
        = (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)).prodPrimes.primeFactors.filter
            (fun p : ℕ => (p:ℝ) < Z) := by
      rw [hRdef]; exact RI.Pz_primeFactors _ Z
    intro p hp
    rw [hpf] at hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.primeFactors_mono (Nat.div_dvd_of_dvd (Qmod_dvd A u₀)) A.prodPrimes_ne_zero hp1, hp2⟩
  refine ⟨?c1, ?c2, ?c3⟩
  · -- conjunct 1
    have hsift : siftedSumR A Z = ∑ n ∈ A.support,
        (if ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < Z → ¬ p ∣ n then A.weights n else 0) := by
      rw [siftedSumR]
    rw [hsift]
    have hdbl : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
          ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
            * A.multSum (q * d))
        = ∑ n ∈ A.support, A.weights n *
            (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
              ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
                * (if q * d ∣ n then (1:ℝ) else 0)) := by
      have h1 : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
            ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
              * A.multSum (q * d))
          = ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors, ∑ n ∈ A.support,
              A.weights n * (((ArithmeticFunction.moebius q : ℤ):ℝ)
                * lamPlus (A.prodPrimes / Qmod A u₀) D' d * (if q * d ∣ n then (1:ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun d _ => ?_))
        rw [BoundingSieve.multSum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases h : q * d ∣ n <;> simp [h] <;> ring
      rw [h1]
      calc ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors, ∑ n ∈ A.support,
              A.weights n * (((ArithmeticFunction.moebius q : ℤ):ℝ)
                * lamPlus (A.prodPrimes / Qmod A u₀) D' d * (if q * d ∣ n then (1:ℝ) else 0))
          = ∑ q ∈ (Qmod A u₀).divisors, ∑ n ∈ A.support, ∑ d ∈ R.divisors,
              A.weights n * (((ArithmeticFunction.moebius q : ℤ):ℝ)
                * lamPlus (A.prodPrimes / Qmod A u₀) D' d * (if q * d ∣ n then (1:ℝ) else 0)) :=
            Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
        _ = ∑ n ∈ A.support, ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
              A.weights n * (((ArithmeticFunction.moebius q : ℤ):ℝ)
                * lamPlus (A.prodPrimes / Qmod A u₀) D' d * (if q * d ∣ n then (1:ℝ) else 0)) :=
            Finset.sum_comm
        _ = ∑ n ∈ A.support, A.weights n *
              (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
                ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
                  * (if q * d ∣ n then (1:ℝ) else 0)) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Finset.mul_sum]
    rw [hdbl]
    refine Finset.sum_le_sum (fun n _ => ?_)
    have hpt := qtInd_le_double A (Qmod A u₀) R Z D' hQ0 hR0 hQdvd hR_dvd hQR hD'
      hQsub hRsub n
    by_cases hcond : ∀ p ∈ A.prodPrimes.primeFactors, (p:ℝ) < Z → ¬ p ∣ n
    · rw [if_pos hcond]
      rw [if_pos hcond] at hpt
      have hw := mul_le_mul_of_nonneg_left hpt (A.weights_nonneg n)
      simpa using hw
    · rw [if_neg hcond]
      rw [if_neg hcond] at hpt
      exact mul_nonneg (A.weights_nonneg n) hpt
  · -- conjunct 2
    have hnu : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
          ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
            * A.nu (q * d))
        = (∑ q ∈ (Qmod A u₀).divisors,
              ((ArithmeticFunction.moebius q : ℤ):ℝ) * A.nu q)
          * (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Qmod A u₀) D' d * A.nu d) := by
      have hinner : ∀ q ∈ (Qmod A u₀).divisors, ∀ d ∈ R.divisors,
          ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
              * A.nu (q * d)
          = (((ArithmeticFunction.moebius q : ℤ):ℝ) * A.nu q)
            * (lamPlus (A.prodPrimes / Qmod A u₀) D' d * A.nu d) := by
        intro q hq d hd
        have hqQ : q ∣ Qmod A u₀ := (Nat.mem_divisors.mp hq).1
        have hdR : d ∣ R := (Nat.mem_divisors.mp hd).1
        have hqd : Nat.Coprime q d := (hQR.coprime_dvd_left hqQ).coprime_dvd_right hdR
        rw [A.nu_mult.map_mul_of_coprime hqd]; ring
      calc (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
              ((ArithmeticFunction.moebius q : ℤ):ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) D' d
                * A.nu (q * d))
          = ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ R.divisors,
              (((ArithmeticFunction.moebius q : ℤ):ℝ) * A.nu q)
                * (lamPlus (A.prodPrimes / Qmod A u₀) D' d * A.nu d) :=
            Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun d hd => hinner q hq d hd))
        _ = ∑ q ∈ (Qmod A u₀).divisors, (((ArithmeticFunction.moebius q : ℤ):ℝ) * A.nu q)
              * (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Qmod A u₀) D' d * A.nu d) := by
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Finset.mul_sum]
        _ = (∑ q ∈ (Qmod A u₀).divisors, ((ArithmeticFunction.moebius q : ℤ):ℝ) * A.nu q)
              * (∑ d ∈ R.divisors, lamPlus (A.prodPrimes / Qmod A u₀) D' d * A.nu d) := by
            rw [Finset.sum_mul]
    rw [hnu, (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      A.nu A.nu_mult hQsq).symm]
  · -- conjunct 3
    exact double_rem_le A (Qmod A u₀) R Z D' hQ0 hQR hD' hQdvdPz hRdvdPz

end

end Work.ChenPlan.LinearSieve.JR2
