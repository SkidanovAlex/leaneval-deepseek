import Mathlib
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Commons.Analysis.Asymptotics.tail_rpow_nat_le
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div
import Submission.Commons.NumberTheory.DirichletSeries.omega_euler_product
import Submission.Commons.NumberTheory.Moebius.tsum_moebius_div_sq
import Submission.Commons.NumberTheory.Totient.smooth_inv_sum_le_totient_ratio
import Submission.Work.LinnikAreas.Density4.coprime_indicator_moebius
import Submission.Work.LinnikAreas.Density4.divisors_sqrtrecip_mul_coprime
import Submission.Work.LinnikAreas.Density4.selTheta_asymptotic
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Work.LinnikAreas.Density4.sum_tail_inv_sq_le
import Submission.Work.LinnikAreas.Density4.tau_rpow_sum_bound

/-!
# The `κ`-weighted log-weighted coprime Möbius sum (`mu_kappa_log_sum`)

For `Q ≥ 2`, `t ≥ 1`,
`Σ_{(n,t)=1, n ≤ Q} μ(n)·(∏_{p | n} p/(p+1))·log(Q/n)/n = (π²/6)·∏_{p | t}(p+1)/p + O(σ_{-1/2}(t)/log²Q)`.

Three ingredients:

* `kappa_log_sum_reduction`: expanding `∏_{p|n} p/(p+1) = Σ_{d | n} β(d)` and exchanging the
  summation gives
  `Σ_{(n,t)=1, n ≤ Q} μ(n)·W(n)·log(Q/n)/n = Σ_{d ≤ Q, d sqfree, (d,t)=1} Π(d)·selTheta(Q/d, dt)`
  with `Π(d) = ∏_{p|d} 1/(p(p+1))`;
* `sqfree_coprime_recip_pm1_finite_self` (Euler product): the main term equals
  `(π²/6)·∏_{p|t}(p+1)/p` up to `O(1/√Q)`;
* `kappa_error_sum_self`: the summed `Θ`-error is `O(σ_{-1/2}(t)/log²Q)`.
-/

namespace Work.LinnikAreas.Density4

open Finset BigOperators
open scoped BigOperators

noncomputable section

open Finset BigOperators
open scoped BigOperators



def betaFun (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, (-(1 : ℝ)) / ((p : ℝ) + 1) else 0

def prodKappa (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) + 1))

def kappaW (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

lemma not_squarefree_zero' : ¬ Squarefree (0:ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨2, by norm_num, by norm_num⟩

lemma betaFun_one : betaFun 1 = 1 := by
  rw [betaFun, if_pos squarefree_one, Nat.primeFactors_one, Finset.prod_empty]

lemma betaFun_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    betaFun (a * b) = betaFun a * betaFun b := by
  unfold betaFun
  by_cases ha : Squarefree a
  · by_cases hb : Squarefree b
    · have ha0 : a ≠ 0 := fun h => not_squarefree_zero' (h ▸ ha)
      have hb0 : b ≠ 0 := fun h => not_squarefree_zero' (h ▸ hb)
      have hab' : Squarefree (a * b) := (Nat.squarefree_mul hab).mpr ⟨ha, hb⟩
      rw [if_pos hab', if_pos ha, if_pos hb, Nat.primeFactors_mul ha0 hb0,
        Finset.prod_union hab.disjoint_primeFactors]
    · have hab' : ¬ Squarefree (a * b) := fun h => hb ((Nat.squarefree_mul hab).mp h).2
      rw [if_neg hab', if_pos ha, if_neg hb, mul_zero]
  · have hab' : ¬ Squarefree (a * b) := fun h => ha ((Nat.squarefree_mul hab).mp h).1
    rw [if_neg hab', if_neg ha, zero_mul]

lemma betaFun_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : betaFun (p ^ k) = 0 := by
  rw [betaFun, if_neg]
  intro hsq
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by simpa [pow_two] using pow_dvd_pow p hk)

/-- `Σ_{d | n} β(d) = ∏_{p | n} p/(p+1)` for `n ≥ 1`. -/
lemma sum_betaFun_eq_kappaW (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, betaFun d = kappaW n := by
  have hn0 : n ≠ 0 := by omega
  have hkey := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
    betaFun n hn0 betaFun_one (fun a b hab => betaFun_mul hab)
    (fun p k hp hk => betaFun_prime_pow hp hk)
  rw [← hkey, kappaW]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  unfold betaFun
  rw [if_pos (Nat.prime_iff.mp hpp).squarefree, hpp.primeFactors, Finset.prod_singleton]
  field_simp
  ring

lemma betaFun_mul_moebius (d : ℕ) (hd : Squarefree d) :
    betaFun d * (ArithmeticFunction.moebius d : ℝ) = ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)+1) := by
  set g : ℕ → ℝ := fun n => betaFun n * (ArithmeticFunction.moebius n : ℝ) with hg
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd
  have hgm : ∀ a b : ℕ, Nat.Coprime a b → g (a*b) = g a * g b := by
    intro a b hab
    have hm : (ArithmeticFunction.moebius (a*b) : ℝ)
        = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.coprime_iff_gcd_eq_one.mp hab)]
      push_cast; ring
    simp only [hg, hm, betaFun_mul hab]; ring
  have hg1 : g 1 = 1 := by
    simp only [hg, betaFun_one, ArithmeticFunction.moebius_apply_one]
    norm_num
  have hkey := Commons.Algebra.BigOperators.f_prod_prime g hg1 hgm d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hL : betaFun d * (ArithmeticFunction.moebius d : ℝ) = g (∏ p ∈ d.primeFactors, p) := by
    conv_lhs => rw [← hprod]
  rw [hL, hkey]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  simp only [hg]
  unfold betaFun
  rw [if_pos (Nat.prime_iff.mp hpp).squarefree, hpp.primeFactors, Finset.prod_singleton,
    ArithmeticFunction.moebius_apply_prime hpp]
  ring_nf

lemma prodKappa_eq (d : ℕ) (hd : Squarefree d) :
    betaFun d * (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) = prodKappa d := by
  have hb := betaFun_mul_moebius d hd
  have h1 : ((d : ℕ) : ℝ) = ∏ p ∈ d.primeFactors, (p:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [hb, prodKappa, h1, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have hp1 : ((p:ℝ)+1) ≠ 0 := by linarith
  field_simp

/-- `μ (a*b) = μ a * μ b` whenever `(a,b) = 1`, as a real number. -/
lemma moebius_mul_of_coprime (a b : ℕ) (hab : Nat.Coprime a b) :
    (ArithmeticFunction.moebius (a*b) : ℝ)
      = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (Nat.coprime_iff_gcd_eq_one.mp hab)]
  push_cast; ring

/-- `μ (a*b)` vanishes unless `(a,b) = 1`. -/
lemma moebius_mul_eq (a b : ℕ) :
    (ArithmeticFunction.moebius (a*b) : ℝ) =
      (if Nat.Coprime a b then
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) else 0) := by
  by_cases hab : Nat.Coprime a b
  · rw [if_pos hab, moebius_mul_of_coprime a b hab]
  · have hns : ¬ Squarefree (a * b) := by
      intro hsq
      have hg1 : a.gcd b ≠ 1 := fun h => hab (Nat.coprime_iff_gcd_eq_one.mpr h)
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
      have hpa : p ∣ a := (Nat.dvd_gcd_iff.mp hpg).1
      have hpb : p ∣ b := (Nat.dvd_gcd_iff.mp hpg).2
      have hp2 : p * p ∣ a * b := by
        obtain ⟨x, rfl⟩ := hpa
        obtain ⟨y, rfl⟩ := hpb
        exact ⟨x*y, by ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hp2
    have hzero : ArithmeticFunction.moebius (a*b) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
    rw [if_neg hab, hzero]
    simp

/-- Swapping the order of summation: `Σ_{n ≤ N} Σ_{d | n} F d n = Σ_{d ≤ N} Σ_{m ≤ N/d} F d (d*m)`. -/
lemma sum_Icc_swap_divisors (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d n)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N/d), F d (d*m) := by
  classical
  have h := sum_Icc_div_reindex N (fun _ : ℕ => True) (fun d m => F d (d*m))
  simp only [Finset.filter_true] at h
  have h2 : (∑ x ∈ Finset.Icc 1 N, ∑ d ∈ x.divisors, F d (d*(x/d)))
      = ∑ x ∈ Finset.Icc 1 N, ∑ d ∈ x.divisors, F d x := by
    refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun d hd => ?_))
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [← h2, ← h]

/-- The inner sum over `m ≤ Q/d`, evaluated against `selTheta`: for `1 ≤ d ≤ Q`,
`Σ_{m ≤ Q/d, (dm,t)=1} μ(dm)·β(d)·(log Q - log(dm))/(dm)`
`   = [d squarefree, (d,t)=1]·Π(d)·selTheta(Q/d, d·t)`. -/
lemma inner_selTheta (Q d t : ℕ) (hd : 1 ≤ d) (hdQ : d ≤ Q) :
    (∑ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime (d*m) t),
        (ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
          (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ))
    = (if Squarefree d ∧ Nat.Coprime d t then (1:ℝ) else 0) *
        (prodKappa d * selTheta ((Q:ℝ)/(d:ℝ)) (d*t)) := by
  classical
  have hd0 : (d:ℝ) ≠ 0 := by positivity
  have hQd : ⌊(Q:ℝ)/(d:ℝ)⌋₊ = Q/d := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hsel : selTheta ((Q:ℝ)/(d:ℝ)) (d*t)
      = ∑ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m (d*t)),
          (ArithmeticFunction.moebius m : ℝ) * Real.log (((Q:ℝ)/(d:ℝ))/(m:ℝ)) / (m:ℝ) := by
    simp only [selTheta]
    rw [hQd]
  let C : ℝ := betaFun d * (ArithmeticFunction.moebius d : ℝ) / (d:ℝ)
  by_cases hdt : Nat.Coprime d t
  · by_cases hds : Squarefree d
    · rw [if_pos ⟨hds, hdt⟩, one_mul]
      have hfil : (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime (d*m) t)
          = (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m t) := by
        refine Finset.filter_congr (fun m _ => ?_)
        rw [Nat.coprime_mul_iff_left]
        exact ⟨fun h => h.2, fun h => ⟨hdt, h⟩⟩
      rw [hfil]
      have hpt : ∀ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m t),
          (ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
            (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ)
          = (if Nat.Coprime d m then (1:ℝ) else 0) *
            (C * ((ArithmeticFunction.moebius m : ℝ) *
                (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / (m:ℝ))) := by
        intro m hm
        obtain ⟨hmIcc, -⟩ := Finset.mem_filter.mp hm
        rw [moebius_mul_eq d m]
        by_cases hcm : Nat.Coprime d m
        · rw [if_pos hcm, if_pos hcm, Nat.cast_mul]
          have hm0 : (m:ℝ) ≠ 0 := by
            have : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
            positivity
          simp only [C]
          field_simp
        · rw [if_neg hcm, if_neg hcm, zero_mul]
          simp
      rw [Finset.sum_congr rfl hpt]
      have hpt2 : ∀ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m t),
          (if Nat.Coprime d m then (1:ℝ) else 0) *
            (C * ((ArithmeticFunction.moebius m : ℝ) *
                (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / (m:ℝ)))
          = (if Nat.Coprime m (d*t) then
              C * ((ArithmeticFunction.moebius m : ℝ) *
                (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / (m:ℝ)) else 0) := by
        intro m hm
        have hmt : Nat.Coprime m t := (Finset.mem_filter.mp hm).2
        have hiff : Nat.Coprime d m ↔ Nat.Coprime m (d*t) := by
          rw [Nat.coprime_mul_iff_right]
          exact ⟨fun h => ⟨h.symm, hmt⟩, fun h => h.1.symm⟩
        by_cases h : Nat.Coprime d m
        · rw [if_pos h, if_pos (hiff.mp h), one_mul]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), zero_mul]
      rw [Finset.sum_congr rfl hpt2, ← Finset.sum_filter, Finset.filter_filter]
      have hfil2 : (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m t ∧ Nat.Coprime m (d*t))
          = (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m (d*t)) := by
        refine Finset.filter_congr (fun m _ => ?_)
        rw [Nat.coprime_mul_iff_right]
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨h.2, h⟩
      rw [hfil2]
      calc (∑ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m (d*t)),
              C * ((ArithmeticFunction.moebius m : ℝ) *
                (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / (m:ℝ)))
          = C * ∑ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m (d*t)),
              ((ArithmeticFunction.moebius m : ℝ) *
                (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / (m:ℝ)) := by
            rw [Finset.mul_sum]
        _ = prodKappa d * ∑ m ∈ (Finset.Icc 1 (Q/d)).filter (fun m => Nat.Coprime m (d*t)),
              ((ArithmeticFunction.moebius m : ℝ) *
                (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / (m:ℝ)) := by
            rw [show C = prodKappa d from prodKappa_eq d hds]
        _ = prodKappa d * selTheta ((Q:ℝ)/(d:ℝ)) (d*t) := by
            rw [hsel]
            congr 1
            refine Finset.sum_congr rfl (fun m hm => ?_)
            obtain ⟨hmIcc, -⟩ := Finset.mem_filter.mp hm
            have hm0 : (m:ℝ) ≠ 0 := by
              have : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
              positivity
            have hlog : Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)
                = Real.log ((Q:ℝ)/(d:ℝ)/(m:ℝ)) := by
              have hdm0 : ((d:ℝ)*(m:ℝ)) ≠ 0 := mul_ne_zero hd0 hm0
              have hQ0 : (Q:ℝ) ≠ 0 := by
                have : 1 ≤ Q := le_trans hd hdQ
                positivity
              rw [Nat.cast_mul, Real.log_mul hd0 hm0,
                show ((Q:ℝ)/(d:ℝ)/(m:ℝ)) = (Q:ℝ)/((d:ℝ)*(m:ℝ)) by ring,
                Real.log_div hQ0 hdm0,
                Real.log_mul hd0 hm0]
            rw [hlog]
    · rw [if_neg (fun h => hds h.1), zero_mul]
      refine Finset.sum_eq_zero (fun m hm => ?_)
      simp [betaFun, hds]
  · rw [if_neg (fun h => hdt h.2), zero_mul]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    obtain ⟨-, hcm⟩ := Finset.mem_filter.mp hm
    exact absurd (hcm.coprime_dvd_left (Nat.dvd_mul_right d m)) hdt

/-- **Reduction.** The `κ`-weighted coprime log-weighted Möbius sum is a `d`-sum of
`selTheta`-values: for `Q ≥ 1`,
`Σ_{(n,t)=1, n ≤ Q} μ(n)·(n/κ(n))·log(Q/n)/n`
`   = Σ_{d ≤ Q, d squarefree, (d,t)=1} Π(d)·selTheta(Q/d, d·t)` with `Π(d) = ∏_{p|d} 1/(p(p+1))`. -/
theorem kappa_log_sum_reduction (Q t : ℕ) (hQ : 1 ≤ Q) :
    (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n t),
        (ArithmeticFunction.moebius n : ℝ) * kappaW n *
          (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ))
      = ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          prodKappa d * selTheta ((Q:ℝ)/(d:ℝ)) (d*t) := by
  classical
  -- Step 1: expand `kappaW n = Σ_{d | n} betaFun d` and swap the order of summation.
  have h1 : (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n t),
        (ArithmeticFunction.moebius n : ℝ) * kappaW n *
          (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ))
      = ∑ n ∈ Finset.Icc 1 Q, ∑ d ∈ n.divisors,
          (if Nat.Coprime n t then (1:ℝ) else 0) *
            ((ArithmeticFunction.moebius n : ℝ) * betaFun d *
              (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hnt : Nat.Coprime n t
    · rw [if_pos hnt, if_pos hnt, ← sum_betaFun_eq_kappaW n hn1]
      have hstep : (ArithmeticFunction.moebius n : ℝ) * (∑ d ∈ n.divisors, betaFun d) *
            (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ)
          = ∑ d ∈ n.divisors, (1:ℝ) * ((ArithmeticFunction.moebius n : ℝ) * betaFun d *
              (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ)) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl (fun d hd => ?_)
        ring
      rw [hstep]
    · rw [if_neg hnt, if_neg hnt]
      simp
  rw [h1, sum_Icc_swap_divisors Q
    (fun d n => (if Nat.Coprime n t then (1:ℝ) else 0) *
      ((ArithmeticFunction.moebius n : ℝ) * betaFun d *
        (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ)))]
  -- Step 2: evaluate each inner sum with `inner_selTheta`.
  have h2 : ∀ d ∈ Finset.Icc 1 Q,
      (∑ m ∈ Finset.Icc 1 (Q/d),
          (if Nat.Coprime (d*m) t then (1:ℝ) else 0) *
            ((ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
              (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ)))
        = (if Squarefree d ∧ Nat.Coprime d t then
            (prodKappa d * selTheta ((Q:ℝ)/(d:ℝ)) (d*t)) else 0) := by
    intro d hd
    obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hd
    have hite : ∀ m : ℕ, (if Nat.Coprime (d*m) t then (1:ℝ) else 0) *
          ((ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
            (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ))
        = (if Nat.Coprime (d*m) t then
          ((ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
            (Real.log (Q:ℝ) - Real.log ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ)) else 0) := by
      intro m; rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_congr rfl (fun m _ => hite m), ← Finset.sum_filter,
      inner_selTheta Q d t hd1 hdQ]
    by_cases h : Squarefree d ∧ Nat.Coprime d t
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]

lemma prodKappa_nonneg (d : ℕ) : 0 ≤ prodKappa d := by
  rw [prodKappa]; positivity

/-- The `d`-th main term of the reduction: for `d` squarefree and coprime to `t`,
`Π(d)·(dt)/φ(dt) = (∏_{p | d} 1/(p²-1))·(t/φ(t))`. -/
lemma main_term_d (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) (hcop : Nat.Coprime d t)
    (hds : Squarefree d) :
    prodKappa d * (((d*t : ℕ)):ℝ)/(Nat.totient (d*t):ℝ)
      = (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1)) * ((t:ℝ)/(Nat.totient t:ℝ)) := by
  have hdtt : (((d*t : ℕ)):ℝ) = (d:ℝ)*(t:ℝ) := Nat.cast_mul d t
  have htotR : ((Nat.totient (d*t):ℕ):ℝ) = (Nat.totient d:ℝ)*(Nat.totient t:ℝ) := by
    rw [Nat.totient_mul hcop, Nat.cast_mul]
  rw [hdtt, htotR, mul_div_assoc, ← div_mul_div_comm, ← mul_assoc]
  have h1 : prodKappa d * ((d:ℝ)/(Nat.totient d:ℝ))
      = ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1) := by
    rw [prodKappa, Commons.NumberTheory.Totient.totient_div_eq_prod_primeFactors_div_pred d hd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (p:ℝ) ≠ 0 := by linarith
    have hp1 : ((p:ℝ) - 1) ≠ 0 := by linarith
    have hpp1 : ((p:ℝ) + 1) ≠ 0 := by linarith
    have hp21 : (-1 + (p:ℝ)^2) ≠ 0 := by nlinarith
    have hp21' : (p:ℝ)^2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [h1]

/-- `t/φ(t) ≤ 2·σ_{-1/2}(t)`. -/
lemma totient_ratio_le_two_sHalf (t : ℕ) (ht : 1 ≤ t) :
    ((t:ℝ)/(Nat.totient t:ℝ)) ≤ 2 * sHalf t := by
  rw [Commons.NumberTheory.Totient.totient_div_eq_prod_primeFactors_div_pred t ht]
  have hfac : ∀ p ∈ t.primeFactors, (p:ℝ)/((p:ℝ)-1)
      ≤ (if p = 2 then (2:ℝ) else 1) * (1 + 1/Real.sqrt ((p:ℕ):ℝ)) := by
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hspos : 0 < Real.sqrt ((p:ℕ):ℝ) := by
      apply Real.sqrt_pos.mpr
      linarith
    have hppos : 0 < (p:ℝ) - 1 := by linarith
    rcases eq_or_lt_of_le hp2 with h | h
    · subst h
      rw [if_pos rfl]
      have hval : (((2:ℕ):ℝ))/(((2:ℕ):ℝ)-1) = 2 := by norm_num
      rw [hval]
      have hnn : (0:ℝ) ≤ 1/Real.sqrt ((2:ℕ):ℝ) := by positivity
      linarith
    · have hp3 : 3 ≤ p := h
      have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      rw [if_neg (by omega : p ≠ 2), one_mul]
      have hsqrtle : Real.sqrt ((p:ℕ):ℝ) ≤ (p:ℝ) - 1 := by
        rw [Real.sqrt_le_left (le_of_lt hppos)]
        nlinarith
      have hle : 1/((p:ℝ)-1) ≤ 1/Real.sqrt ((p:ℕ):ℝ) :=
        one_div_le_one_div_of_le hspos hsqrtle
      have hsplit : (p:ℝ)/((p:ℝ)-1) = 1 + 1/((p:ℝ)-1) := by
        field_simp
        ring
      rw [hsplit]
      linarith
  have hnonneg : ∀ p ∈ t.primeFactors, (0:ℝ) ≤ (p:ℝ)/((p:ℝ)-1) := by
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
    exact div_nonneg (by linarith) (by linarith)
  have hprod := Finset.prod_le_prod₀ hnonneg hfac
  rw [Finset.prod_mul_distrib] at hprod
  have htwo : (∏ p ∈ t.primeFactors, (if p = 2 then (2:ℝ) else 1)) ≤ 2 := by
    by_cases h2 : 2 ∈ t.primeFactors
    · rw [Finset.prod_eq_single (2:ℕ) (fun b hb hb2 => by simp [hb2]) (fun hc => absurd h2 hc)]
      simp
    · rw [Finset.prod_eq_one (fun b hb => by
        by_cases hb2 : b = 2
        · exact absurd (hb2 ▸ hb) h2
        · simp [hb2])]
      norm_num
  have h9' : (∏ p ∈ t.primeFactors, (1 + 1/Real.sqrt ((p:ℕ):ℝ))) ≤ sHalf t :=
    (sHalf_facts t ht).1
  calc (∏ p ∈ t.primeFactors, (p:ℝ)/((p:ℝ)-1))
      ≤ (∏ p ∈ t.primeFactors, (if p = 2 then (2:ℝ) else 1))
          * ∏ p ∈ t.primeFactors, (1 + 1/Real.sqrt ((p:ℕ):ℝ)) := hprod
    _ ≤ 2 * sHalf t := by
        apply mul_le_mul htwo h9' (by positivity) (by norm_num)

/-- `(log Q)² ≤ 16·√Q` for `Q ≥ 1`. -/
lemma log_sq_le_sixteen_sqrt (Q : ℕ) (hQ : 1 ≤ Q) :
    (Real.log (Q:ℝ))^2 ≤ 16 * Real.sqrt (Q:ℝ) := by
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hlog : Real.log (Q:ℝ) ≤ (Q:ℝ)^((1:ℝ)/4) / (1/4) :=
    Commons.Analysis.ExpLog.log_le_rpow_div hQ1 (by norm_num)
  have hlog0 : 0 ≤ Real.log (Q:ℝ) := Real.log_nonneg hQ1
  have hpow : ((Q:ℝ)^((1:ℝ)/4))^2 = Real.sqrt (Q:ℝ) := by
    rw [← Real.rpow_natCast ((Q:ℝ)^((1:ℝ)/4)) 2, ← Real.rpow_mul (Nat.cast_nonneg Q)]
    norm_num
    rw [Real.sqrt_eq_rpow]
  calc (Real.log (Q:ℝ))^2 ≤ ((Q:ℝ)^((1:ℝ)/4)/(1/4))^2 := pow_le_pow_left₀ hlog0 hlog 2
    _ = 16 * Real.sqrt (Q:ℝ) := by rw [div_eq_mul_inv, mul_pow, hpow]; ring

/-- The main term in closed form: `(t/φ(t))·(π²/6)·∏_{p | t}(1 - 1/p²) = (π²/6)·∏_{p | t}(p+1)/p`. -/
lemma main_const (t : ℕ) (ht : 1 ≤ t) :
    ((t:ℝ)/(Nat.totient t:ℝ)) * ((Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2))
      = (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ) := by
  rw [Commons.NumberTheory.Totient.totient_div_eq_prod_primeFactors_div_pred t ht]
  have hprod : (∏ p ∈ t.primeFactors, (p:ℝ)/((p:ℝ)-1))
      * (∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2))
      = ∏ p ∈ t.primeFactors, (((p:ℝ)+1)/(p:ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (p:ℝ) ≠ 0 := by linarith
    have hp1 : ((p:ℝ) - 1) ≠ 0 := by linarith
    field_simp
    ring
  calc (∏ p ∈ t.primeFactors, (p:ℝ)/((p:ℝ)-1))
        * ((Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2))
      = (Real.pi^2/6) * ((∏ p ∈ t.primeFactors, (p:ℝ)/((p:ℝ)-1))
          * (∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2))) := by ring
    _ = (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ) := by rw [hprod]

/-- `Π(d) ≤ 1/d²` for squarefree `d`. -/
lemma prodKappa_le_inv_sq (d : ℕ) (hd : Squarefree d) : prodKappa d ≤ 1/((d:ℝ)^2) := by
  have hprod := Nat.prod_primeFactors_of_squarefree hd
  rw [prodKappa]
  calc ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))
      ≤ ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2) := by
        refine Finset.prod_le_prod₀ (fun p hp => by positivity) (fun p hp => ?_)
        have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = 1/((d:ℝ)^2) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow,
          ← Nat.cast_prod, hprod]

/-- `σ_{-1/2}(d) ≤ τ(d)`. -/
lemma sHalf_le_card (d : ℕ) : sHalf d ≤ ((Nat.divisors d).card : ℝ) := by
  rw [sHalf]
  calc ∑ e ∈ d.divisors, (1:ℝ)/Real.sqrt (e:ℝ) ≤ ∑ e ∈ d.divisors, (1:ℝ) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
        have heR : (1:ℝ) ≤ (e:ℝ) := by exact_mod_cast he1
        rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
        exact Real.one_le_sqrt.mpr heR
    _ = ((Nat.divisors d).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `Π(d)·σ_{-1/2}(d) ≤ τ(d)/d²` for squarefree `d`. -/
lemma prodKappa_mul_sHalf_le_sq (d : ℕ) (hd : Squarefree d) :
    prodKappa d * sHalf d ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 := by
  calc prodKappa d * sHalf d
      ≤ (1/(d:ℝ)^2) * ((Nat.divisors d).card : ℝ) :=
        mul_le_mul (prodKappa_le_inv_sq d hd) (sHalf_le_card d) (sHalf_nonneg d) (by positivity)
    _ = ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 := by ring

/-- `Π(d)·σ_{-1/2}(d) ≤ τ(d)·d^{-3/2}` for squarefree `d`. -/
lemma prodKappa_mul_sHalf_le (d : ℕ) (hd : Squarefree d) :
    prodKappa d * sHalf d ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
  have hd0 : d ≠ 0 := fun h => not_squarefree_zero' (h ▸ hd)
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
  have hpow : (d:ℝ)^(3/2 : ℝ) ≤ (d:ℝ)^2 := by
    rw [← Real.rpow_natCast ((d:ℝ)) 2]
    exact Real.rpow_le_rpow_of_exponent_le hdR1 (by norm_num)
  calc prodKappa d * sHalf d
      ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 := prodKappa_mul_sHalf_le_sq d hd
    _ ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos (by linarith) _) hpow

/-- For `1 ≤ d` with `d² ≤ Q` and `Q ≥ 2`: `(log(2+Q/d))^{-3} ≤ 8·(log Q)^{-3}`. -/
lemma log_factor_le_halves {Q d : ℕ} (hQ : 2 ≤ Q) (hd1 : 1 ≤ d) (hd2 : d*d ≤ Q) :
    (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ) ≤ 8 * (Real.log (Q:ℝ))^(-3:ℤ) := by
  have hQR : (0:ℝ) < (Q:ℝ) := by
    have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
    linarith
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd2R : ((d:ℝ))^2 ≤ (Q:ℝ) := by
    have : ((d*d : ℕ):ℝ) ≤ (Q:ℝ) := by exact_mod_cast hd2
    simpa [Nat.cast_mul, pow_two] using this
  have hsqrt : Real.sqrt (Q:ℝ) ≤ (Q:ℝ)/(d:ℝ) := by
    rw [Real.sqrt_le_left (le_of_lt (div_pos hQR hdR))]
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [hd2R]
  have hQlog : 0 < Real.log (Q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  have hlogmono : Real.log (Real.sqrt (Q:ℝ)) ≤ Real.log (2 + (Q:ℝ)/(d:ℝ)) :=
    Real.log_le_log (Real.sqrt_pos.mpr hQR) (by linarith)
  have hval : Real.log (Real.sqrt (Q:ℝ)) = (1/2) * Real.log (Q:ℝ) := by
    rw [Real.log_sqrt hQR.le]; ring
  have h3 : (1/2) * Real.log (Q:ℝ) ≤ Real.log (2 + (Q:ℝ)/(d:ℝ)) := by
    rw [← hval]; exact hlogmono
  have h2 : (0:ℝ) < (1/2) * Real.log (Q:ℝ) := by linarith
  have h4 : ((1/2) * Real.log (Q:ℝ))^3 ≤ (Real.log (2 + (Q:ℝ)/(d:ℝ)))^3 :=
    pow_le_pow_left₀ (le_of_lt h2) h3 3
  have h5 : (0:ℝ) < ((1/2) * Real.log (Q:ℝ))^3 := by positivity
  have h6 : (0:ℝ) < Real.log (2 + (Q:ℝ)/(d:ℝ)) := by linarith [h2, h3]
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  calc ((Real.log (2 + (Q:ℝ)/(d:ℝ)))^3)⁻¹ ≤ (((1/2) * Real.log (Q:ℝ))^3)⁻¹ :=
        (inv_le_inv₀ (pow_pos h6 3) h5).mpr h4
    _ = 8 * ((Real.log (Q:ℝ))^3)⁻¹ := by
        rw [mul_pow, show ((1/2:ℝ))^3 = 1/8 by norm_num, mul_inv]
        norm_num

/-- For `1 ≤ d ≤ Q`, `Q ≥ 2`: `(log(2+Q/d))^{-3} ≤ 1`. -/
lemma log_factor_le_one {Q d : ℕ} (hQ : 2 ≤ Q) (hd1 : 1 ≤ d) (hdQ : d ≤ Q) :
    (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ) ≤ 1 := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hge : (3:ℝ) ≤ 2 + (Q:ℝ)/(d:ℝ) := by
    have h1 : (1:ℝ) ≤ (Q:ℝ)/(d:ℝ) := by
      rw [one_le_div hdR]
      exact_mod_cast hdQ
    linarith
  have hlog : (1:ℝ) ≤ Real.log (2 + (Q:ℝ)/(d:ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hge
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_of_lt Real.exp_one_lt_three
    linarith
  rw [zpow_neg, zpow_ofNat]
  rw [inv_le_one₀ (by positivity)]
  exact one_le_pow₀ hlog

/-- `log 2 ≥ 1/2`. -/
lemma log_two_ge_half : (1/2:ℝ) ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
  have h : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h3 : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_three
  have h4 : Real.exp (1/2:ℝ) < 2 := by
    nlinarith [Real.exp_pos (1/2:ℝ), h, h3]
  linarith

/-- `(log Q)^{-3} ≤ 2·(log Q)^{-2}` for `Q ≥ 2`. -/
lemma zpow_neg_three_le (Q : ℕ) (hQ : 2 ≤ Q) :
    (Real.log (Q:ℝ))^(-3:ℤ) ≤ 2 * (Real.log (Q:ℝ))^(-2:ℤ) := by
  have hlogQ : 0 < Real.log (Q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  have hle : Real.log 2 ≤ Real.log (Q:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have h2 : (1:ℝ)/Real.log (Q:ℝ) ≤ 2 := by
    rw [div_le_iff₀ hlogQ]
    linarith [log_two_ge_half, hle]
  have hhalf : (1:ℝ)/2 ≤ Real.log (Q:ℝ) := by
    have := (div_le_iff₀ hlogQ).mp h2
    linarith
  have h3 : (Real.log (Q:ℝ))^2 / 2 ≤ (Real.log (Q:ℝ))^3 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [hhalf, hlogQ]
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  calc ((Real.log (Q:ℝ))^3)⁻¹ ≤ ((Real.log (Q:ℝ))^2 / 2)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).mpr h3
    _ = 2 * ((Real.log (Q:ℝ))^2)⁻¹ := by
        rw [div_eq_mul_inv, mul_inv]
        ring

/-- `1/Q^{1/4} ≤ 64·(log Q)^{-2}` for `Q ≥ 2`. -/
lemma inv_quarter_le (Q : ℕ) (hQ : 2 ≤ Q) :
    (1:ℝ)/(Q:ℝ)^((1:ℝ)/4) ≤ 64 * (Real.log (Q:ℝ))^(-2:ℤ) := by
  have hQpos : (0:ℝ) < (Q:ℝ) := by
    have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
    linarith
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hlogQ : 0 < Real.log (Q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  have hlog : Real.log (Q:ℝ) ≤ (Q:ℝ)^((1:ℝ)/8) / (1/8) :=
    Commons.Analysis.ExpLog.log_le_rpow_div hQ1 (by norm_num)
  have hsq : (Real.log (Q:ℝ))^2 ≤ 64 * (Q:ℝ)^((1:ℝ)/4) := by
    have h1 : (Real.log (Q:ℝ))^2 ≤ ((Q:ℝ)^((1:ℝ)/8) / (1/8))^2 :=
      pow_le_pow_left₀ hlogQ.le hlog 2
    have h2 : ((Q:ℝ)^((1:ℝ)/8) / (1/8))^2 = 64 * (Q:ℝ)^((1:ℝ)/4) := by
      rw [div_eq_mul_inv, mul_pow, ← Real.rpow_natCast ((Q:ℝ)^((1:ℝ)/8)) 2,
        ← Real.rpow_mul hQpos.le]
      norm_num
      ring
    linarith [h1, h2]
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hlogQ 2)]
  rw [div_mul_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hQpos _)]
  simpa using hsq

/-- **The `Θ`-error sum bound** (proved here directly, using `tau_rpow_sum_bound`). -/
theorem kappa_error_sum_self (Q t : ℕ) (hQ : 2 ≤ Q) (ht : 1 ≤ t) :
    (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
        (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))) * sHalf (d*t) *
          (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      ≤ 4096 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ) := by
  classical
  have hQ1 : 1 ≤ Q := by omega
  have hlogQ : 0 < Real.log (Q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  set D : Finset ℕ := (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t) with hD
  have hfac : ∀ d ∈ D, prodKappa d * sHalf (d*t) * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)
      = sHalf t * (prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) := by
    intro d hd
    obtain ⟨hdIcc, hdsq, hdcop⟩ := Finset.mem_filter.mp hd
    have h : sHalf (d*t) = sHalf d * sHalf t := divisors_sqrtrecip_mul_coprime hdcop
    rw [h]; ring
  have hDL : (∑ d ∈ D, prodKappa d * sHalf (d*t) * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      = (∑ d ∈ D, (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))) * sHalf (d*t) *
          (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [prodKappa]
  rw [← hDL]
  have hexp : (∑ d ∈ D, prodKappa d * sHalf (d*t) * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      = sHalf t * ∑ d ∈ D, prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ) := by
    rw [Finset.sum_congr rfl hfac, Finset.mul_sum]
  rw [hexp]
  have hsplit : (∑ d ∈ D, prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      = (∑ d ∈ D.filter (fun d => d*d ≤ Q),
            prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
        + (∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
            prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not D (fun d => d*d ≤ Q)
      (fun d => prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))]
  rw [hsplit]
  have hpart1 : (∑ d ∈ D.filter (fun d => d*d ≤ Q),
        prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      ≤ 128 * (Real.log (Q:ℝ))^(-3:ℤ) := by
    have hstep : (∑ d ∈ D.filter (fun d => d*d ≤ Q),
          prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
        ≤ ∑ d ∈ D.filter (fun d => d*d ≤ Q),
            prodKappa d * sHalf d * (8 * (Real.log (Q:ℝ))^(-3:ℤ)) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hdD, hd2⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdIcc, -⟩ := Finset.mem_filter.mp hdD
      obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hdIcc
      exact mul_le_mul_of_nonneg_left (log_factor_le_halves hQ hd1 hd2)
        (mul_nonneg (prodKappa_nonneg d) (sHalf_nonneg d))
    refine hstep.trans ?_
    have hsum : (∑ d ∈ D.filter (fun d => d*d ≤ Q), prodKappa d * sHalf d) ≤ 16 := by
      calc (∑ d ∈ D.filter (fun d => d*d ≤ Q), prodKappa d * sHalf d)
          ≤ ∑ d ∈ D.filter (fun d => d*d ≤ Q),
              ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
            refine Finset.sum_le_sum (fun d hd => ?_)
            obtain ⟨hdD, -⟩ := Finset.mem_filter.mp hd
            obtain ⟨-, hdsq, -⟩ := Finset.mem_filter.mp hdD
            exact prodKappa_mul_sHalf_le d hdsq
        _ ≤ ∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d),
              ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
            rw [hD]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro d hd
              simp only [Finset.mem_filter] at hd ⊢
              exact ⟨hd.1.1, hd.1.2.1⟩
            · intro d hd _
              exact div_nonneg (by positivity) (by positivity)
        _ ≤ ∑ d ∈ Finset.Icc 1 Q, ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun d => ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ))
              (Finset.filter_subset _ _) ?_
            intro d hd _
            exact div_nonneg (by positivity) (by positivity)
        _ ≤ 16 := tau_rpow_sum_bound Q
    have hgoal2 : (∑ d ∈ D.filter (fun d => d*d ≤ Q),
          prodKappa d * sHalf d * (8 * (Real.log (Q:ℝ))^(-3:ℤ)))
        = 8 * (Real.log (Q:ℝ))^(-3:ℤ) * (∑ d ∈ D.filter (fun d => d*d ≤ Q),
            prodKappa d * sHalf d) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      ring
    rw [hgoal2]
    have hnn : (0:ℝ) ≤ 8 * (Real.log (Q:ℝ))^(-3:ℤ) := by positivity
    calc 8 * (Real.log (Q:ℝ))^(-3:ℤ) * (∑ d ∈ D.filter (fun d => d*d ≤ Q), prodKappa d * sHalf d)
        ≤ 8 * (Real.log (Q:ℝ))^(-3:ℤ) * 16 := mul_le_mul_of_nonneg_left hsum hnn
      _ = 128 * (Real.log (Q:ℝ))^(-3:ℤ) := by ring
  have hpart2 : (∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
        prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      ≤ 16/(Q:ℝ)^((1:ℝ)/4) := by
    have hstep : (∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
          prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
        ≤ ∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
            ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hdD, hd2⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdIcc, hdsq, -⟩ := Finset.mem_filter.mp hdD
      obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hdIcc
      have h1 : prodKappa d * sHalf d ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 :=
        prodKappa_mul_sHalf_le_sq d hdsq
      have hLnn : (0:ℝ) ≤ (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ) := by
        apply zpow_nonneg
        apply Real.log_nonneg
        have h0 : (0:ℝ) ≤ (Q:ℝ)/(d:ℝ) := by positivity
        linarith
      calc prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)
          ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ) :=
            mul_le_mul_of_nonneg_right h1 hLnn
        _ ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * 1 :=
            mul_le_mul_of_nonneg_left (log_factor_le_one hQ hd1 hdQ)
              (div_nonneg (by positivity) (by positivity))
        _ = ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 := by ring
    refine hstep.trans ?_
    have hsub : D.filter (fun d => ¬ d*d ≤ Q) ⊆ Finset.Icc 1 Q := by
      intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
    have hper : ∀ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
        ((Nat.divisors d).card : ℝ)/(d:ℝ)^2
          ≤ (1/(Q:ℝ)^((1:ℝ)/4)) * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := by
      intro d hd
      obtain ⟨hdD, hd2⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdIcc, -, -⟩ := Finset.mem_filter.mp hdD
      obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hdIcc
      have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hd2R : (Q:ℝ) < (d:ℝ)^2 := by
        have hcon : ¬ ((d*d : ℕ):ℝ) ≤ (Q:ℝ) := by
          intro hcc; exact hd2 (by exact_mod_cast hcc)
        push_cast at hcon
        linarith
      have hsqrt : Real.sqrt (Q:ℝ) < (d:ℝ) := by
        rw [Real.sqrt_lt' (by positivity)]
        exact hd2R
      have hquarter : (1:ℝ)/Real.sqrt (d:ℝ) ≤ 1/(Q:ℝ)^((1:ℝ)/4) := by
        have hQpos : (0:ℝ) < (Q:ℝ) := by
          have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
          linarith
        have hqle : (Q:ℝ)^((1:ℝ)/4) ≤ Real.sqrt (d:ℝ) := by
          have heq : (Q:ℝ)^((1:ℝ)/4) = Real.sqrt (Real.sqrt (Q:ℝ)) := by
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hQpos.le]
            norm_num
          rw [heq]
          exact Real.sqrt_le_sqrt (le_of_lt hsqrt)
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hQpos _) hqle
      have heq : ((Nat.divisors d).card : ℝ)/(d:ℝ)^2
          = ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) * (1/Real.sqrt (d:ℝ)) := by
        have hd2eq : (d:ℝ)^2 = (d:ℝ)^(3/2 : ℝ) * Real.sqrt (d:ℝ) := by
          rw [← Real.rpow_natCast ((d:ℝ)) 2, Real.sqrt_eq_rpow, ← Real.rpow_add hdR]
          norm_num
        have hne1 : ((d:ℝ)^(3/2 : ℝ)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hdR _)
        have hne2 : (Real.sqrt (d:ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdR)
        rw [hd2eq]
        field_simp
      calc ((Nat.divisors d).card : ℝ)/(d:ℝ)^2
          = ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) * (1/Real.sqrt (d:ℝ)) := heq
        _ ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) * (1/(Q:ℝ)^((1:ℝ)/4)) :=
            mul_le_mul_of_nonneg_left hquarter (by positivity)
        _ = (1/(Q:ℝ)^((1:ℝ)/4)) * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := by ring
    calc (∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q), ((Nat.divisors d).card : ℝ)/(d:ℝ)^2)
        ≤ ∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
            (1/(Q:ℝ)^((1:ℝ)/4)) * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) :=
          Finset.sum_le_sum hper
        _ = (1/(Q:ℝ)^((1:ℝ)/4)) * (∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
            ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := by
          rw [Finset.mul_sum]
        _ ≤ (1/(Q:ℝ)^((1:ℝ)/4)) * 16 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun d => ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) hsub
            (fun d hd _ => div_nonneg (by positivity) (by positivity))).trans
            (tau_rpow_sum_bound Q)
        _ = 16/(Q:ℝ)^((1:ℝ)/4) := by ring
  have hA : (∑ d ∈ D.filter (fun d => d*d ≤ Q),
        prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      + (∑ d ∈ D.filter (fun d => ¬ d*d ≤ Q),
        prodKappa d * sHalf d * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
      ≤ 128 * (Real.log (Q:ℝ))^(-3:ℤ) + 16/(Q:ℝ)^((1:ℝ)/4) :=
    add_le_add hpart1 hpart2
  have hbound : 128 * (Real.log (Q:ℝ))^(-3:ℤ) + 16/(Q:ℝ)^((1:ℝ)/4)
      ≤ 4096 * (Real.log (Q:ℝ))^(-2:ℤ) := by
    have h1 : 128 * (Real.log (Q:ℝ))^(-3:ℤ) ≤ 256 * (Real.log (Q:ℝ))^(-2:ℤ) := by
      calc 128 * (Real.log (Q:ℝ))^(-3:ℤ)
          ≤ 128 * (2 * (Real.log (Q:ℝ))^(-2:ℤ)) :=
            mul_le_mul_of_nonneg_left (zpow_neg_three_le Q hQ) (by norm_num)
        _ = 256 * (Real.log (Q:ℝ))^(-2:ℤ) := by ring
    have h2 : 16/(Q:ℝ)^((1:ℝ)/4) ≤ 1024 * (Real.log (Q:ℝ))^(-2:ℤ) := by
      calc 16/(Q:ℝ)^((1:ℝ)/4) = 16 * ((1:ℝ)/(Q:ℝ)^((1:ℝ)/4)) := by ring
        _ ≤ 16 * (64 * (Real.log (Q:ℝ))^(-2:ℤ)) :=
            mul_le_mul_of_nonneg_left (inv_quarter_le Q hQ) (by norm_num)
        _ = 1024 * (Real.log (Q:ℝ))^(-2:ℤ) := by ring
    have hx : (0:ℝ) ≤ (Real.log (Q:ℝ))^(-2:ℤ) := zpow_nonneg hlogQ.le _
    linarith [h1, h2, hx]
  refine (mul_le_mul_of_nonneg_left hA (sHalf_nonneg t)).trans ?_
  exact (mul_le_mul_of_nonneg_left hbound (sHalf_nonneg t)).trans (le_of_eq (by ring))

/-- **Assembly**: the reduction, `selTheta_asymptotic` and the two arithmetic estimates
(`herr` for the `Θ`-error, `hmain` for the main term) give the target estimate. -/
theorem kappa_assembly (C1 C2 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (herr : ∀ Q t : ℕ, 2 ≤ Q → 1 ≤ t →
      (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
        (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))) * sHalf (d*t) *
          (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) ≤ C1 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ))
    (hmain : ∀ Q t : ℕ, 1 ≤ Q → 1 ≤ t →
      |(∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
        ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
      - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)|
        ≤ C2 / Real.sqrt (Q:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q t : ℕ, 2 ≤ Q → 1 ≤ t →
      |(∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n t),
          (ArithmeticFunction.moebius n : ℝ) * kappaW n *
            (Real.log (Q:ℝ) - Real.log (n:ℝ)) / (n:ℝ))
        - (Real.pi^2/6) * (∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ))|
        ≤ C * sHalf t / (Real.log (Q:ℝ))^2 := by
  obtain ⟨C0, hC0pos, hsel⟩ := selTheta_asymptotic
  refine ⟨C0*C1 + 2*C2*16 + 1, by positivity, ?_⟩
  intro Q t hQ ht
  have hQ1 : 1 ≤ Q := by omega
  have hQpos : (0:ℝ) < (Q:ℝ) := by
    have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ1
    linarith
  have hlogQ : 0 < Real.log (Q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  rw [kappa_log_sum_reduction Q t hQ1]
  set D : Finset ℕ := (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t) with hD
  set M : ℝ := ∑ d ∈ D, prodKappa d * (((d*t : ℕ)):ℝ)/(Nat.totient (d*t):ℝ) with hM
  set E : ℝ := ∑ d ∈ D, prodKappa d *
    (selTheta ((Q:ℝ)/(d:ℝ)) (d*t) - (((d*t : ℕ)):ℝ)/(Nat.totient (d*t):ℝ)) with hE
  have hsplit : (∑ d ∈ D, prodKappa d * selTheta ((Q:ℝ)/(d:ℝ)) (d*t)) = M + E := by
    rw [hM, hE, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    ring
  rw [hsplit]
  -- ### the error part
  have hEbound : |E| ≤ C0 * C1 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ) := by
    rw [hE]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : (∑ d ∈ D,
          |prodKappa d * (selTheta ((Q:ℝ)/(d:ℝ)) (d*t)
            - (((d*t : ℕ)):ℝ)/(Nat.totient (d*t):ℝ))|)
        ≤ ∑ d ∈ D, C0 * (prodKappa d * sHalf (d*t)
            * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      obtain ⟨hdIcc, hds, hdc⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hdIcc
      have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hy : 1 ≤ (Q:ℝ)/(d:ℝ) := by
        rw [one_le_div hdpos]
        exact_mod_cast hdQ
      have hr : 1 ≤ d*t := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have hb := hsel ((Q:ℝ)/(d:ℝ)) hy (d*t) hr
      rw [abs_mul, abs_of_nonneg (prodKappa_nonneg d)]
      calc prodKappa d * |selTheta ((Q:ℝ)/(d:ℝ)) (d*t)
              - (((d*t : ℕ)):ℝ)/(Nat.totient (d*t):ℝ)|
          ≤ prodKappa d * (C0 * sHalf (d*t)
              * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) :=
            mul_le_mul_of_nonneg_left hb (prodKappa_nonneg d)
        _ = C0 * (prodKappa d * sHalf (d*t)
              * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) := by ring
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    have hherr := herr Q t hQ ht
    have hsum_eq : (∑ d ∈ D, prodKappa d * sHalf (d*t)
          * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
        = (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
            (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))) * sHalf (d*t)
              * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ)) := by
      rw [hD]; simp only [prodKappa]
    rw [hsum_eq]
    calc C0 * (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
            (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))) * sHalf (d*t)
              * (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
        ≤ C0 * (C1 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ)) :=
          mul_le_mul_of_nonneg_left hherr hC0pos.le
      _ = C0 * C1 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ) := by ring
  -- ### the main part
  have hMeq : M = ((t:ℝ)/(Nat.totient t:ℝ)) *
      (∑ d ∈ D, ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1)) := by
    rw [hM, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hdIcc, hds, hdc⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hdIcc
    rw [main_term_d d t hd1 ht hdc hds]
    ring
  have hkey : M - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ)
      = ((t:ℝ)/(Nat.totient t:ℝ)) *
          ((∑ d ∈ D, ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
            - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)) := by
    rw [hMeq, mul_sub, main_const t ht]
  have hMt : |M - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ)|
      ≤ 2 * C2 * 16 * sHalf t / (Real.log (Q:ℝ))^2 := by
    rw [hkey, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (t:ℝ)/(Nat.totient t:ℝ))]
    have h1 : ((t:ℝ)/(Nat.totient t:ℝ)) ≤ 2 * sHalf t := totient_ratio_le_two_sHalf t ht
    have h2 : C2 / Real.sqrt ((Q:ℝ)) ≤ C2 * 16 / (Real.log (Q:ℝ))^2 := by
      have hlog2 : (Real.log (Q:ℝ))^2 ≤ 16 * Real.sqrt ((Q:ℝ)) := log_sq_le_sixteen_sqrt Q hQ1
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hQpos) (pow_pos hlogQ 2)]
      nlinarith [hlog2, hC2]
    have hSD := hmain Q t hQ1 ht
    have hSD' : |(∑ d ∈ D, ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
        - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)| ≤ C2/Real.sqrt (Q:ℝ) := by
      rw [hD]; exact hSD
    have h2' : C2 / Real.sqrt ((Q:ℝ)) ≤ C2 * 16 / (Real.log (Q:ℝ))^2 := h2
    calc ((t:ℝ)/(Nat.totient t:ℝ)) * |(∑ d ∈ D, ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
            - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)|
        ≤ (2 * sHalf t) * (C2 / Real.sqrt ((Q:ℝ))) :=
          mul_le_mul h1 hSD' (abs_nonneg _) (by have := sHalf_nonneg t; linarith)
      _ ≤ (2 * sHalf t) * (C2 * 16 / (Real.log (Q:ℝ))^2) :=
          mul_le_mul_of_nonneg_left h2' (by have := sHalf_nonneg t; linarith)
      _ = 2 * C2 * 16 * sHalf t / (Real.log (Q:ℝ))^2 := by ring
  -- ### combination
  have hfin : |M + E - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ)|
      ≤ (C0*C1 + 2*C2*16) * sHalf t / (Real.log (Q:ℝ))^2 := by
    have h1 : M + E - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ)
        = (M - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, ((p:ℝ)+1)/(p:ℝ)) + E := by ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    have h3 : C0 * C1 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ)
        = C0 * C1 * sHalf t / (Real.log (Q:ℝ))^2 := by
      rw [zpow_neg, zpow_ofNat, div_eq_mul_inv]
    rw [h3] at hEbound
    refine (add_le_add hMt hEbound).trans (le_of_eq ?_)
    ring
  refine hfin.trans ?_
  apply div_le_div_of_nonneg_right _ (pow_pos hlogQ 2).le
  exact mul_le_mul_of_nonneg_right (by linarith) (sHalf_nonneg t)

open Finset BigOperators
open scoped BigOperators



/-- `f_t(n) = [n squarefree, (n,t)=1]·∏_{p | n} 1/(p²-1)`. -/
def sqfreeProd (t : ℕ) : ℕ → ℝ :=
  fun n => if Squarefree n ∧ Nat.Coprime n t then ∏ p ∈ n.primeFactors, (1:ℝ)/((p:ℝ)^2 - 1) else 0

/-- `ρ_t(n) = [n ⊥ t]/n²`. -/
def coprSq (t : ℕ) : ℕ → ℝ :=
  fun n => if Nat.Coprime n t then (1:ℝ)/((n:ℝ)^2) else 0

lemma not_squarefree_zero'' : ¬ Squarefree (0:ℕ) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨2, by norm_num, by norm_num⟩

lemma sqfreeProd_zero (t : ℕ) : sqfreeProd t 0 = 0 := by
  rw [sqfreeProd, if_neg]
  rintro ⟨hs, -⟩
  exact not_squarefree_zero'' hs

lemma sqfreeProd_one (t : ℕ) : sqfreeProd t 1 = 1 := by
  rw [sqfreeProd, if_pos ⟨squarefree_one, Nat.coprime_one_left t⟩, Nat.primeFactors_one,
    Finset.prod_empty]

lemma sqfreeProd_mul (t : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    sqfreeProd t (a*b) = sqfreeProd t a * sqfreeProd t b := by
  rw [sqfreeProd, sqfreeProd, sqfreeProd]
  by_cases ha : Squarefree a ∧ Nat.Coprime a t
  · by_cases hb : Squarefree b ∧ Nat.Coprime b t
    · have hab' : Squarefree (a*b) ∧ Nat.Coprime (a*b) t :=
        ⟨(Nat.squarefree_mul hab).mpr ⟨ha.1, hb.1⟩, ha.2.mul_left hb.2⟩
      rw [if_pos ha, if_pos hb, if_pos hab']
      have ha0 : a ≠ 0 := fun h => not_squarefree_zero'' (h ▸ ha.1)
      have hb0 : b ≠ 0 := fun h => not_squarefree_zero'' (h ▸ hb.1)
      rw [Nat.primeFactors_mul ha0 hb0, Finset.prod_union hab.disjoint_primeFactors]
    · have hab' : ¬ (Squarefree (a*b) ∧ Nat.Coprime (a*b) t) := by
        rintro ⟨hs, hc⟩
        exact hb ⟨((Nat.squarefree_mul hab).mp hs).2, ((Nat.coprime_mul_iff_left).mp hc).2⟩
      rw [if_pos ha, if_neg hb, if_neg hab', mul_zero]
  · have hab' : ¬ (Squarefree (a*b) ∧ Nat.Coprime (a*b) t) := by
      rintro ⟨hs, hc⟩
      exact ha ⟨((Nat.squarefree_mul hab).mp hs).1, ((Nat.coprime_mul_iff_left).mp hc).1⟩
    rw [if_neg ha, if_neg hab', zero_mul]

lemma coprSq_zero (t : ℕ) : coprSq t 0 = 0 := by
  rw [coprSq]; simp

lemma coprSq_one (t : ℕ) : coprSq t 1 = 1 := by
  rw [coprSq, if_pos (Nat.coprime_one_left t)]; norm_num

lemma coprSq_mul (t : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    coprSq t (a*b) = coprSq t a * coprSq t b := by
  rw [coprSq, coprSq, coprSq]
  by_cases ha : Nat.Coprime a t
  · by_cases hb : Nat.Coprime b t
    · rw [if_pos ha, if_pos hb, if_pos (ha.mul_left hb), Nat.cast_mul, mul_pow,
        div_mul_div_comm, one_mul]
    · have h : ¬ Nat.Coprime (a*b) t := fun hc => hb ((Nat.coprime_mul_iff_left.mp hc).2)
      rw [if_pos ha, if_neg hb, if_neg h, mul_zero]
  · have h : ¬ Nat.Coprime (a*b) t := fun hc => ha ((Nat.coprime_mul_iff_left.mp hc).1)
    rw [if_neg ha, if_neg h, zero_mul]

lemma one_div_sq_sub_one_nonneg {p : ℕ} (hp : p.Prime) :
    (0:ℝ) ≤ (1:ℝ)/((p:ℝ)^2 - 1) := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  exact div_nonneg zero_le_one (by nlinarith)

lemma summable_inv_sq : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)^2)) := by
  have hbase : Summable (fun n : ℕ => (n:ℝ)^(-(2:ℝ))) := by
    have h := (Real.summable_nat_rpow_inv (p := (2:ℝ))).mpr (by norm_num)
    exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
  exact hbase.congr (fun n => by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, one_div])

/-- Pointwise bound for the summand `f_t`. -/
lemma norm_sqfreeProd_le {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ n : ℕ, 1 ≤ n → (2:ℝ) ^ n.primeFactors.card ≤ C * (n:ℝ)^((1:ℝ)/2))
    (t : ℕ) (n : ℕ) : ‖sqfreeProd t n‖ ≤ C * (n:ℝ)^(-(3/2:ℝ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [sqfreeProd_zero, norm_zero]
    exact mul_nonneg (le_of_lt hCpos)
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ ((0:ℕ):ℝ)) (-(3/2:ℝ)))
  · rw [sqfreeProd]
    by_cases h : Squarefree n ∧ Nat.Coprime n t
    · rw [if_pos h, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun p hp =>
          one_div_sq_sub_one_nonneg (Nat.prime_of_mem_primeFactors hp)))]
      have hprod : ∏ p ∈ n.primeFactors, (1:ℝ)/((p:ℝ)^2 - 1)
          ≤ ∏ p ∈ n.primeFactors, 2/(p:ℝ)^2 := by
        refine Finset.prod_le_prod₀ (fun p hp =>
          one_div_sq_sub_one_nonneg (Nat.prime_of_mem_primeFactors hp)) (fun p hp => ?_)
        have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have h1 : (0:ℝ) < (p:ℝ)^2 - 1 := by nlinarith
        have h2 : (0:ℝ) < (p:ℝ)^2 := by positivity
        rw [div_le_div_iff₀ h1 h2]
        nlinarith
      have hval : ∏ p ∈ n.primeFactors, 2/(p:ℝ)^2
          = (2:ℝ)^(n.primeFactors.card)/ (∏ p ∈ n.primeFactors, (p:ℝ))^2 := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.prod_pow]
      have hrad : ∏ p ∈ n.primeFactors, (p:ℝ) = (n:ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree h.1]
      rw [hval, hrad] at hprod
      have hroot : (2:ℝ)^(n.primeFactors.card) ≤ C * (n:ℝ)^((1:ℝ)/2) := hC n hn
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      rw [Real.rpow_neg hnR.le, ← div_eq_mul_inv]
      rw [le_div_iff₀ (by positivity)]
      calc (∏ p ∈ n.primeFactors, (1:ℝ)/((p:ℝ)^2 - 1)) * (n:ℝ)^((3:ℝ)/2)
          ≤ ((2:ℝ)^(n.primeFactors.card)/(n:ℝ)^2) * (n:ℝ)^((3:ℝ)/2) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hnR.le _)
        _ = (2:ℝ)^(n.primeFactors.card) * ((n:ℝ)^((3:ℝ)/2)/(n:ℝ)^2) := by ring
        _ = (2:ℝ)^(n.primeFactors.card) * (n:ℝ)^(-(1:ℝ)/2) := by
            congr 1
            rw [← Real.rpow_natCast ((n:ℝ)) 2, div_eq_mul_inv, ← Real.rpow_neg hnR.le,
              ← Real.rpow_add hnR]
            norm_num
        _ ≤ (C * (n:ℝ)^((1:ℝ)/2)) * (n:ℝ)^(-(1:ℝ)/2) :=
            mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hnR.le _)
        _ = C := by
            rw [mul_assoc, ← Real.rpow_add hnR, show ((1:ℝ)/2 + -(1:ℝ)/2) = 0 by norm_num,
              Real.rpow_zero, mul_one]
    · rw [if_neg h, norm_zero]
      exact mul_nonneg (le_of_lt hCpos) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma summable_norm_sqfreeProd (t : ℕ) : Summable (fun n : ℕ => ‖sqfreeProd t n‖) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletSeries.pow_card_primeFactors_le_const_mul_rpow
      2 (1/2) (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => C * (n:ℝ)^(-(3/2:ℝ)))
    (fun n => norm_nonneg _) (fun n => norm_sqfreeProd_le hCpos hC t n) ?_
  have hbase : Summable (fun n : ℕ => (n:ℝ)^(-(3/2:ℝ))) := by
    have h := (Real.summable_nat_rpow_inv (p := (3/2:ℝ))).mpr (by norm_num)
    exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
  exact hbase.mul_left C

lemma one_div_sq_le_one (n : ℕ) : (1:ℝ)/((n:ℝ)^2) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    rw [div_le_one (by positivity)]
    nlinarith

lemma summable_norm_coprSq (t : ℕ) : Summable (fun n : ℕ => ‖coprSq t n‖) := by
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^2))
    (fun n => norm_nonneg _) (fun n => ?_) summable_inv_sq
  rw [coprSq]
  by_cases h : Nat.Coprime n t
  · rw [if_pos h, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ)/((n:ℝ)^2))]
  · rw [if_neg h, norm_zero]
    exact div_nonneg zero_le_one (by positivity)

/-- `Σ_{d | t} μ(d)/d² = ∏_{p | t}(1 - 1/p²)`. -/
lemma sum_divisors_moebius_div_sq_eq_prod (t : ℕ) (ht : 1 ≤ t) :
    (∑ d ∈ t.divisors, (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2)
      = ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2) := by
  have hf1 : (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) 1 = 1 := by
    simp
  have hfm : ∀ a b : ℕ, Nat.Coprime a b →
      (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) (a*b)
        = (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) a
          * (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) b := by
    intro a b hab
    have hmul : (ArithmeticFunction.moebius (a*b) : ℝ)
        = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.coprime_iff_gcd_eq_one.mp hab)]
      push_cast; ring
    by_cases ha : a = 0
    · subst ha
      have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
      subst hb; simp
    by_cases hb : b = 0
    · subst hb
      have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
      subst ha1; simp
    have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha
    have hbR : (b:ℝ) ≠ 0 := by exact_mod_cast hb
    simp only [hmul]
    rw [Nat.cast_mul, mul_pow]
    field_simp
  have hfs : ∀ p k : ℕ, p.Prime → 2 ≤ k →
      (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) (p^k) = 0 := by
    intro p k hp hk
    show (ArithmeticFunction.moebius (p^k) : ℝ)/(((p^k : ℕ)):ℝ)^2 = 0
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0)]
    simp [show k ≠ 1 by omega]
  have h := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
    (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) t (by omega) hf1 hfm hfs
  rw [← h]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.moebius_apply_prime hpp]
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
  have hp0 : (p:ℝ) ≠ 0 := by linarith
  have hpne : (p:ℝ)^2 ≠ 0 := pow_ne_zero _ hp0
  field_simp
  ring

lemma tsum_moebius_div_sq_eq (t : ℕ) (ht : 1 ≤ t) :
    (∑' m : ℕ, coprSq t m) = (Real.pi^2/6) *
      ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2) := by
  have hpt : ∀ m : ℕ, coprSq t m
      = ∑ d ∈ t.divisors, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(m:ℝ)^2) else 0 := by
    intro m
    rw [coprSq]
    exact coprime_indicator_moebius m t ht ((1:ℝ)/(m:ℝ)^2)
  rw [tsum_congr hpt]
  have hsum : ∀ d ∈ t.divisors, Summable
      (fun m : ℕ => if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(m:ℝ)^2) else 0) := by
    intro d hd
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (f := fun m : ℕ => (1:ℝ)/((m:ℝ)^2))
      (fun m => norm_nonneg _) (fun m => ?_) summable_inv_sq
    by_cases h : d ∣ m
    · rw [if_pos h, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ)/((m:ℝ)^2))]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        simpa using Commons.NumberTheory.Moebius.moebius_abs_le_one d
      calc |(ArithmeticFunction.moebius d : ℝ)| * ((1:ℝ)/(m:ℝ)^2) ≤ 1 * ((1:ℝ)/(m:ℝ)^2) :=
            mul_le_mul_of_nonneg_right hmu (by positivity)
        _ = (1:ℝ)/(m:ℝ)^2 := by ring
    · rw [if_neg h, norm_zero]
      exact div_nonneg zero_le_one (by positivity)
  rw [Summable.tsum_finsetSum hsum]
  have hinner : ∀ d ∈ t.divisors,
      (∑' m : ℕ, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(m:ℝ)^2) else 0)
        = ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) * (Real.pi^2/6) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hd0 : 0 < d := by omega
    have hreindex : (∑' m : ℕ, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(m:ℝ)^2) else 0)
        = ∑' k : ℕ, (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(((d*k:ℕ)):ℝ)^2) := by
      rw [← Function.Injective.tsum_eq (f := fun m : ℕ => if d ∣ m then
            (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(m:ℝ)^2) else 0)
          (g := fun k : ℕ => d*k) (fun a b hab => Nat.mul_left_cancel hd0 hab) ?_]
      · refine tsum_congr (fun k => ?_)
        simp
      · intro m hm
        rw [Function.mem_support] at hm
        rw [Set.mem_range]
        by_cases h : d ∣ m
        · obtain ⟨k, hk⟩ := h
          exact ⟨k, hk.symm⟩
        · simp [h] at hm
    rw [hreindex]
    have hterm : ∀ k : ℕ, (ArithmeticFunction.moebius d : ℝ) * ((1:ℝ)/(((d*k:ℕ)):ℝ)^2)
        = ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^2) * ((1:ℝ)/((k:ℝ)^2)) := by
      intro k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
        have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
        rw [Nat.cast_mul, mul_pow]
        field_simp
    rw [tsum_congr hterm, tsum_mul_left, hasSum_zeta_two.tsum_eq]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, sum_divisors_moebius_div_sq_eq_prod t ht,
    mul_comm]

lemma local_sqfreeProd {t p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, sqfreeProd t (p^e)) = if p ∣ t then 1 else (p:ℝ)^2/((p:ℝ)^2 - 1) := by
  have hfin : ∀ e : ℕ, e ∉ ({0,1} : Finset ℕ) → sqfreeProd t (p^e) = 0 := by
    intro e he
    have he2 : 2 ≤ e := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
      omega
    rw [sqfreeProd, if_neg]
    rintro ⟨hsq, -⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp)
      (by simpa [pow_two] using pow_dvd_pow p he2)
  rw [tsum_eq_sum hfin]
  have h0 : sqfreeProd t (p^0) = 1 := by
    rw [sqfreeProd, if_pos ⟨squarefree_one, Nat.coprime_one_left t⟩]
    simp
  have h1 : sqfreeProd t (p^1) = if p ∣ t then 0 else (1:ℝ)/((p:ℝ)^2 - 1) := by
    rw [sqfreeProd]
    by_cases hpt : p ∣ t
    · rw [if_neg, if_pos hpt]
      rintro ⟨-, hc⟩
      rw [pow_one] at hc
      exact (hp.coprime_iff_not_dvd.mp hc) hpt
    · rw [if_pos, if_neg hpt]
      · rw [pow_one, hp.primeFactors, Finset.prod_singleton]
      · exact ⟨by simpa using hp.squarefree, by simpa using (hp.coprime_iff_not_dvd).mpr hpt⟩
  rw [show ({0,1} : Finset ℕ) = insert 0 {1} by rfl, Finset.sum_insert (by simp),
    Finset.sum_singleton, h0, h1]
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  by_cases hpt : p ∣ t
  · rw [if_pos hpt, if_pos hpt]; norm_num
  · rw [if_neg hpt, if_neg hpt]
    have hne : ((p:ℝ)^2 - 1) ≠ 0 := by nlinarith
    field_simp
    ring

lemma local_coprSq {t p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, coprSq t (p^e)) = if p ∣ t then 1 else (1 - (1:ℝ)/(p:ℝ)^2)⁻¹ := by
  by_cases hpt : p ∣ t
  · rw [if_pos hpt]
    rw [tsum_eq_single 0]
    · simp [coprSq]
    · intro e he
      rw [coprSq, if_neg]
      intro hc
      have hpe : p ∣ p^e := dvd_pow_self p he
      exact (hp.coprime_iff_not_dvd.mp (hc.coprime_dvd_left hpe)) hpt
  · rw [if_neg hpt]
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    have hnorm : ‖(1:ℝ)/((p:ℝ)^2)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one (by positivity)]
      nlinarith
    have hgeosum : (∑' e : ℕ, ((1:ℝ)/((p:ℝ)^2))^e) = (1 - (1:ℝ)/(p:ℝ)^2)⁻¹ :=
      tsum_geometric_of_norm_lt_one hnorm
    rw [← hgeosum]
    refine tsum_congr (fun e => ?_)
    rw [coprSq, if_pos ((hp.coprime_iff_not_dvd.mpr hpt).pow_left e)]
    have hpow : (1:ℝ)/(((p:ℝ)^e)^2) = ((1:ℝ)/((p:ℝ)^2))^e := by
      rw [div_pow, one_pow, show (((p:ℝ)^2)^e) = ((p:ℝ)^e)^2 by ring_nf]
    rw [← hpow, Nat.cast_pow]

lemma tsum_sqfreeProd_eq (t : ℕ) :
    (∑' n : ℕ, sqfreeProd t n) = ∑' n : ℕ, coprSq t n := by
  have h1 := EulerProduct.eulerProduct_tprod (f := sqfreeProd t) (sqfreeProd_one t)
    (fun {a b} hab => sqfreeProd_mul t hab) (summable_norm_sqfreeProd t) (sqfreeProd_zero t)
  have h2 := EulerProduct.eulerProduct_tprod (f := coprSq t) (coprSq_one t)
    (fun {a b} hab => coprSq_mul t hab) (summable_norm_coprSq t) (coprSq_zero t)
  rw [← h1, ← h2]
  refine tprod_congr (fun p => ?_)
  rw [local_sqfreeProd p.2, local_coprSq p.2]
  by_cases hpt : (p:ℕ) ∣ t
  · rw [if_pos hpt, if_pos hpt]
  · rw [if_neg hpt, if_neg hpt]
    have hp2 : (2:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (((p:ℕ)):ℝ) ≠ 0 := by positivity
    have hne : (1:ℝ) - 1/(((p:ℕ)):ℝ)^2 ≠ 0 := by
      rw [sub_ne_zero]
      have hlt : (1:ℝ)/(((p:ℕ)):ℝ)^2 < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith
      exact (ne_of_lt hlt).symm
    have hne2 : (((p:ℕ)):ℝ)^2 - 1 ≠ 0 := by nlinarith
    field_simp


/-- **Finite form of the squarefree Euler product** (proved here directly). -/
theorem sqfree_coprime_recip_pm1_finite_self :
    ∃ C : ℝ, 0 < C ∧ ∀ Q t : ℕ, 1 ≤ Q → 1 ≤ t →
      |(∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
        - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)|
        ≤ C / Real.sqrt (Q:ℝ) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletSeries.pow_card_primeFactors_le_const_mul_rpow
      2 (1/2) (by norm_num) (by norm_num)
  refine ⟨32 * C, by positivity, ?_⟩
  intro Q t hQ ht
  have hQpos : (0:ℝ) < (Q:ℝ) := by
    have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
    linarith
  have hsqrtpos : 0 < Real.sqrt (Q:ℝ) := Real.sqrt_pos.mpr hQpos
  have hmain : (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)
      = ∑' n : ℕ, sqfreeProd t n := by
    rw [tsum_sqfreeProd_eq t, tsum_moebius_div_sq_eq t ht]
  have hsum_eq : (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
      = ∑ d ∈ Finset.Icc 1 Q, sqfreeProd t d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    by_cases h : Squarefree d ∧ Nat.Coprime d t <;> simp [sqfreeProd, h]
  rw [hsum_eq, hmain]
  have hsummable : Summable (sqfreeProd t) := (summable_norm_sqfreeProd t).of_norm
  have hsplit := Summable.sum_add_tsum_nat_add (f := sqfreeProd t) (Q+1) hsummable
  have hrange : (∑ i ∈ Finset.range (Q+1), sqfreeProd t i)
      = ∑ i ∈ Finset.Icc 1 Q, sqfreeProd t i := by
    rw [show Finset.range (Q+1) = insert 0 (Finset.Icc 1 Q) by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
    rw [Finset.sum_insert (by simp), sqfreeProd_zero, zero_add]
  have hkey : (∑' n : ℕ, sqfreeProd t n) - (∑ d ∈ Finset.Icc 1 Q, sqfreeProd t d)
      = ∑' i : ℕ, sqfreeProd t (i + (Q+1)) := by
    rw [← hsplit, hrange]; ring
  rw [abs_sub_comm, hkey]
  have htail : ‖∑' i : ℕ, sqfreeProd t (i + (Q+1))‖ ≤ 8 * C / Real.sqrt (Q:ℝ) := by
    have h1 : ‖∑' i : ℕ, sqfreeProd t (i + (Q+1))‖
        ≤ ∑' i : ℕ, ‖sqfreeProd t (i + (Q+1))‖ :=
      norm_tsum_le_tsum_norm ((summable_norm_sqfreeProd t).comp_injective
        (fun a b h => Nat.add_right_cancel h))
    have hbasesummable : Summable (fun n : ℕ => (n:ℝ)^(-(3/2:ℝ))) := by
      have h := (Real.summable_nat_rpow_inv (p := (3/2:ℝ))).mpr (by norm_num)
      exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
    have h2 : (∑' i : ℕ, ‖sqfreeProd t (i + (Q+1))‖)
        ≤ ∑' i : ℕ, C * (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ)) := by
      refine Summable.tsum_le_tsum (fun i => norm_sqfreeProd_le hCpos hC t _) ?_ ?_
      · exact (summable_norm_sqfreeProd t).comp_injective
          (fun a b h => Nat.add_right_cancel h)
      · have hshift : Summable (((fun n : ℕ => (n:ℝ)^(-(3/2:ℝ))) ∘ fun i : ℕ => i + (Q+1))) :=
          hbasesummable.comp_injective (fun a b h => Nat.add_right_cancel h)
        simpa only [Function.comp_apply] using hshift.mul_left C
    have h3 : (∑' i : ℕ, C * (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ)))
        = C * (∑' i : ℕ, (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ))) := tsum_mul_left
    have h4 : (∑' i : ℕ, (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ)))
        ≤ 2 * Real.sqrt 2 / Real.sqrt (Q:ℝ) := by
      have h := Commons.Analysis.Asymptotics.tail_rpow_nat_le (r := (3/2:ℝ))
        (by norm_num) (X₀ := Q+1) (by omega)
      have hQ1 : (0:ℝ) < ((Q+1 : ℕ):ℝ) := by
        have : (1:ℕ) ≤ Q+1 := by omega
        exact_mod_cast (by omega : 0 < Q+1)
      have hsqrt1 : 0 < Real.sqrt (((Q+1 : ℕ)):ℝ) := Real.sqrt_pos.mpr hQ1
      have hle : 1/Real.sqrt (((Q+1 : ℕ)):ℝ) ≤ 1/Real.sqrt (Q:ℝ) := by
        apply one_div_le_one_div_of_le hsqrtpos
        exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : Q ≤ Q+1))
      calc (∑' i : ℕ, (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ)))
          = ∑' m : ℕ, (((Q+1 + m : ℕ)):ℝ)^(-(3/2:ℝ)) :=
            tsum_congr (fun i => by rw [Nat.add_comm])
        _ ≤ ((2:ℝ)^((3:ℝ)/2 - 1)/((3:ℝ)/2 - 1)) * (((Q+1 : ℕ)):ℝ)^(1 - (3:ℝ)/2) := h
        _ = 2 * Real.sqrt 2 * (1/Real.sqrt (((Q+1 : ℕ)):ℝ)) := by
            rw [show ((3:ℝ)/2 - 1) = 1/2 by norm_num,
              show (1 - (3:ℝ)/2) = -(1/2) by norm_num,
              Real.rpow_neg (le_of_lt hQ1), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
            field_simp
        _ ≤ 2 * Real.sqrt 2 * (1/Real.sqrt (Q:ℝ)) := by
            refine mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 2 * Real.sqrt 2 / Real.sqrt (Q:ℝ) := by ring
    calc ‖∑' i : ℕ, sqfreeProd t (i + (Q+1))‖
        ≤ ∑' i : ℕ, ‖sqfreeProd t (i + (Q+1))‖ := h1
      _ ≤ ∑' i : ℕ, C * (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ)) := h2
      _ = C * (∑' i : ℕ, (((i + (Q+1) : ℕ)):ℝ)^(-(3/2:ℝ))) := h3
      _ ≤ C * (2 * Real.sqrt 2 / Real.sqrt (Q:ℝ)) :=
          mul_le_mul_of_nonneg_left h4 hCpos.le
      _ ≤ 8 * C / Real.sqrt (Q:ℝ) := by
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hsqrtpos.le
          have h2 : (2 * Real.sqrt 2) ≤ 8 := by
            have h4 : Real.sqrt 2 < 4 := (Real.sqrt_lt' (by norm_num : (0:ℝ) < 4)).mpr (by norm_num)
            linarith
          nlinarith [hCpos]
  rw [Real.norm_eq_abs] at htail
  exact htail.trans (by
    apply div_le_div_of_nonneg_right _ hsqrtpos.le
    nlinarith [hCpos])

/-- **Linnik's theorem, density-4 `κ`-sum.** -/
theorem mu_kappa_log_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ Q t : ℕ, 2 ≤ Q → 1 ≤ t →
      |(∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n t),
          (ArithmeticFunction.moebius n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
            * (Real.log (Q : ℝ) - Real.log (n : ℝ)) / (n : ℝ))
        - (Real.pi ^ 2 / 6) * (∏ p ∈ t.primeFactors, ((p : ℝ) + 1) / (p : ℝ))|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt d) / (Real.log (Q : ℝ)) ^ 2 := by
  obtain ⟨C2, hC2, hmain⟩ := sqfree_coprime_recip_pm1_finite_self
  have herr' : ∀ Q t : ℕ, 2 ≤ Q → 1 ≤ t →
      (∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
        (∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)*((p:ℝ)+1))) * sHalf (d*t) *
          (Real.log (2 + (Q:ℝ)/(d:ℝ)))^(-3:ℤ))
        ≤ 4096 * sHalf t * (Real.log (Q:ℝ))^(-2:ℤ) := by
    intro Q t hQ ht
    simpa only [sHalf] using kappa_error_sum_self Q t hQ ht
  have hmain' : ∀ Q t : ℕ, 1 ≤ Q → 1 ≤ t →
      |(∑ d ∈ (Finset.Icc 1 Q).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
        ∏ p ∈ d.primeFactors, (1:ℝ)/((p:ℝ)^2-1))
      - (Real.pi^2/6) * ∏ p ∈ t.primeFactors, (1 - (1:ℝ)/(p:ℝ)^2)|
        ≤ C2 / Real.sqrt (Q:ℝ) := fun Q t hQ ht => hmain Q t hQ ht
  obtain ⟨C, hC, hfin⟩ := kappa_assembly 4096 C2 (by norm_num) hC2 herr' hmain'
  exact ⟨C, hC, fun Q t hQ ht => by simpa only [kappaW, sHalf] using hfin Q t hQ ht⟩

end

end Work.LinnikAreas.Density4
