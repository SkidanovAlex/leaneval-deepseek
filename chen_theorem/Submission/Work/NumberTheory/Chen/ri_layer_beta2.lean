import Mathlib
import Submission.Commons.NumberTheory.Chen.rough_theta_lower_of_bv

/-!
# The β = 2 (cube) Rosser–Iwaniec chain layers

For the cube (`β = 2`) chain sets `Gp 2`/`Gm 2` of `rough_theta_lower_of_bv` this file
develops the classical Buchstab layer decomposition
`MpSum2 D Y = Vsieve Y + Σ_{n odd} T_n(D,Y)`
and the triangular recursion `T_{n+1}(D,Y) = Σ_{q admissible} a_q T_n(D/q,q)`
(the basis of the profile induction `T_n(D,Y) ≤ Vsieve Y · delayFn (n-1) (log D/log Y)`).
-/

namespace Commons.NumberTheory.Chen

open Finset
open scoped BigOperators

noncomputable section

/-- the cube-convention (`β = 2`) upper-bound main term -/
def MpSum2 (D : ℝ) (Y : ℕ) : ℝ :=
  (Gp 2 D Y).sum (fun c => (-1:ℝ)^c.length / (Nat.totient (lprod c) : ℝ))

/-- the cube-convention (`β = 2`) lower-bound main term -/
def MeSum2 (D : ℝ) (Y : ℕ) : ℝ :=
  (Gm 2 D Y).sum (fun c => (-1:ℝ)^c.length / (Nat.totient (lprod c) : ℝ))

lemma prime_not_dvd_prod_lt {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hl : ∀ x ∈ l, x.Prime ∧ x < p) : ¬ p ∣ l.prod := by
  induction l with
  | nil => intro hd; exact hp.ne_one (Nat.dvd_one.mp hd)
  | cons a t ih =>
    rw [List.prod_cons]; intro hd
    rcases hp.dvd_mul.mp hd with h | h
    · have ha := hl a (by simp)
      have hpa : p = a := (Nat.prime_dvd_prime_iff_eq hp ha.1).mp h
      omega
    · exact ih (fun x hx => hl x (by simp [hx])) h

/-- one-step recursion of the cube upper-bound main term -/
lemma MpSum2_rec (D : ℝ) (Y : ℕ) :
    MpSum2 D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum2 (D/q) q else 0) := by
  rw [MpSum2, sum_Gp_decomp]
  have hnil : (-1:ℝ)^(([] : List ℕ).length) / (Nat.totient (lprod ([] : List ℕ)) : ℕ) = 1 := by
    simp [lprod]
  rw [hnil]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqprime : q.Prime := (sievePrime_iff_mem Y q).mp hq |>.1
  have hqne2 : q ≠ 2 := (sievePrime_iff_mem Y q).mp hq |>.2.1
  have hpow : (2:ℝ) + 1 = 3 := by norm_num
  have hterm : (Gm 2 (D/q) q).sum
        (fun l => (-1:ℝ)^(q :: l).length / (Nat.totient (lprod (q :: l)) : ℝ))
      = -((1/((q:ℝ)-1)) * MeSum2 (D/q) q) := by
    rw [MeSum2, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hlt : ∀ x ∈ l, x.Prime ∧ x < q := by
      intro x hx
      have hx' := (chain_primes 2 q (D/q)).2 l hl x hx
      exact ⟨hx'.1, hx'.2.2⟩
    have hcop : q.Coprime l.prod :=
      hqprime.coprime_iff_not_dvd.mpr (prime_not_dvd_prod_lt hqprime l hlt)
    have hcop' : q.Coprime (lprod l) := hcop
    rw [List.length_cons, lprod_cons, Nat.totient_mul hcop', Nat.totient_prime hqprime]
    push_cast
    rw [pow_succ]
    have hqm : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      rw [Nat.cast_sub hqprime.one_le]; norm_num
    rw [hqm]
    field_simp
  by_cases hqD : (q:ℝ)^((2:ℝ)+1) ≤ D
  · rw [if_pos hqD, if_pos hqD]; exact hterm
  · rw [if_neg hqD, if_neg hqD]; simp

/-- one-step recursion of the cube lower-bound main term -/
lemma MeSum2_rec (D : ℝ) (Y : ℕ) :
    MeSum2 D Y = 1 - ∑ q ∈ oddPrimesLt Y,
      (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum2 (D/q) q else 0) := by
  rw [MeSum2, sum_Gm_decomp]
  have hnil : (-1:ℝ)^(([] : List ℕ).length) / (Nat.totient (lprod ([] : List ℕ)) : ℕ) = 1 := by
    simp [lprod]
  rw [hnil]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hqprime : q.Prime := (sievePrime_iff_mem Y q).mp hq |>.1
  have hqne2 : q ≠ 2 := (sievePrime_iff_mem Y q).mp hq |>.2.1
  have hterm : (Gp 2 (D/q) q).sum
        (fun l => (-1:ℝ)^(q :: l).length / (Nat.totient (lprod (q :: l)) : ℝ))
      = -((1/((q:ℝ)-1)) * MpSum2 (D/q) q) := by
    rw [MpSum2, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hlt : ∀ x ∈ l, x.Prime ∧ x < q := by
      intro x hx
      have hx' := (chain_primes 2 q (D/q)).1 l hl x hx
      exact ⟨hx'.1, hx'.2.2⟩
    have hcop : q.Coprime l.prod :=
      hqprime.coprime_iff_not_dvd.mpr (prime_not_dvd_prod_lt hqprime l hlt)
    have hcop' : q.Coprime (lprod l) := hcop
    rw [List.length_cons, lprod_cons, Nat.totient_mul hcop', Nat.totient_prime hqprime]
    push_cast
    rw [pow_succ]
    have hqm : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      rw [Nat.cast_sub hqprime.one_le]; norm_num
    rw [hqm]
    field_simp
  by_cases hqD : (q:ℝ) ≤ D
  · rw [if_pos hqD, if_pos hqD]
    exact hterm
  · rw [if_neg hqD, if_neg hqD]; simp

/-- the terminating first layer: the chains `[q]` of the cube set that cannot be extended -/
def Tone (D : ℝ) (Y : ℕ) : ℝ :=
  ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => ¬ ((q:ℝ)^((2:ℝ)+1) ≤ D)),
    (1/((q:ℝ)-1)) * Vsieve q

/-- the admissibility condition at position 1 of a chain of length `n` (cube for odd `n`,
linear for even `n`) -/
def condT (n : ℕ) (q : ℕ) (D : ℝ) : Prop :=
  if n % 2 = 1 then (q:ℝ)^((2:ℝ)+1) ≤ D else (q:ℝ) ≤ D

instance (n : ℕ) (q : ℕ) (D : ℝ) : Decidable (condT n q D) := by
  unfold condT; split <;> infer_instance

/-- the Buchstab layer sums of the cube sieve: `T_n` = the chains of length `n` whose
admissibility conditions hold at positions `1..n-1` and fail at position `n`. -/
def Tsieve2 : ℕ → ℝ → ℕ → ℝ
  | 0, D, Y => Vsieve Y
  | (n+1), D, Y => if n = 0 then Tone D Y else
      ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => condT (n+1) q D),
        (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q

lemma Tsieve2_zero (D : ℝ) (Y : ℕ) : Tsieve2 0 D Y = Vsieve Y := rfl

lemma Tsieve2_one (D : ℝ) (Y : ℕ) : Tsieve2 1 D Y = Tone D Y := by
  rw [Tsieve2]; simp

lemma Tsieve2_succ_succ (n : ℕ) (D : ℝ) (Y : ℕ) :
    Tsieve2 (n+2) D Y =
      ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => condT (n+2) q D),
        (1/((q:ℝ)-1)) * Tsieve2 (n+1) (D/q) q := by
  rw [Tsieve2]; simp


private lemma three_pow_succ (n : ℕ) : (3:ℝ)^(n+1) = 3 * (3:ℝ)^n := by
  rw [pow_succ]; ring

/-- for `n ≥ 2` the layers vanish once the level is below `3^{n-1}` -/
lemma Tsieve2_eq_zero : ∀ n : ℕ, 2 ≤ n → ∀ (D : ℝ) (Y : ℕ),
    D < (3:ℝ)^(n-1) → Tsieve2 n D Y = 0 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hn D Y hD
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m ≤ 1 := by omega
      have hm1' : 1 ≤ m := by omega
      obtain rfl : m = 1 := by omega
      rw [show (1:ℕ) + 1 = (0:ℕ) + 2 from rfl, Tsieve2_succ_succ 0 D Y]
      refine Finset.sum_eq_zero (fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      obtain ⟨hqY, hqc⟩ := hq
      have hq3 : 3 ≤ q := prime_three_le ((sievePrime_iff_mem Y q).mp hqY).1
        (by have := (sievePrime_iff_mem Y q).mp hqY; exact this.2.1)
      have hqR : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
      unfold condT at hqc
      rw [if_neg (by norm_num : ¬ (((0:ℕ)+2) % 2 = 1))] at hqc
      norm_num at hD
      exfalso
      linarith
    · -- m ≥ 2
      rw [show m + 1 = (m - 1) + 2 from by omega, Tsieve2_succ_succ (m - 1)]
      refine Finset.sum_eq_zero (fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      obtain ⟨hqY, hqc⟩ := hq
      have hq3 : 3 ≤ q := prime_three_le ((sievePrime_iff_mem Y q).mp hqY).1
        (by have := (sievePrime_iff_mem Y q).mp hqY; exact this.2.1)
      have hqR : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
      have hqpos : (0:ℝ) < (q:ℝ) := by linarith
      have hDm : D < (3:ℝ)^m := by
        have hsub : m + 1 - 1 = m := by omega
        rwa [hsub] at hD
      have hlt : D/q < (3:ℝ)^(m-1) := by
        rw [div_lt_iff₀ hqpos]
        have h3pow : (3:ℝ)^m = (3:ℝ)^(m-1) * 3 := by
          conv_lhs => rw [show m = (m-1) + 1 from by omega]
          rw [pow_succ]
        have hnn : (0:ℝ) ≤ (3:ℝ)^(m-1) := pow_nonneg (by norm_num) _
        nlinarith [hDm, hqR, h3pow, hnn]
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1, ih (by omega) (D/q) q hlt]
      ring

lemma linComp_eq_zero {D : ℝ} {q : ℕ} (hcube : (q:ℝ)^3 ≤ D) :
    (∑ q' ∈ (oddPrimesLt q).filter (fun q' : ℕ => D/q < (q':ℝ)),
        (1/((q':ℝ)-1)) * Vsieve q') = 0 := by
  refine Finset.sum_eq_zero (fun q' hq' => ?_)
  rw [Finset.mem_filter] at hq'
  obtain ⟨hq'lt, hq'gt⟩ := hq'
  have hq'prime : q'.Prime := (sievePrime_iff_mem q q').mp hq'lt |>.1
  have hq'3 : 3 ≤ q' := prime_three_le hq'prime
    (by have := (sievePrime_iff_mem q q').mp hq'lt; exact this.2.1)
  have hqlt : q' < q := (sievePrime_iff_mem q q').mp hq'lt |>.2.2
  have hqRlt : (q':ℝ) < (q:ℝ) := by exact_mod_cast hqlt
  have hqpos : (0:ℝ) < (q:ℝ) := by
    have : (3:ℕ) ≤ q := by omega
    exact_mod_cast (by omega : 0 < q)
  have hq4 : (4:ℝ) ≤ (q:ℝ) := by
    have : (4:ℕ) ≤ q := by omega
    exact_mod_cast this
  have hDq : (q:ℝ)^2 ≤ D/q := by
    rw [le_div_iff₀ hqpos]
    nlinarith [hcube]
  exfalso
  nlinarith [hq'gt, hDq, hqRlt, hq4]

/-- **The Buchstab layer identity.**  If all layers above `N` vanish (uniformly in the level and
the sift limit), then the cube majorant/minorant main terms are, exactly, the Euler product plus
(minus) their odd (even) layers. -/
theorem MpSum2_layer_identity (N : ℕ)
    (hvan : ∀ (D' : ℝ) (Y' : ℕ) (n : ℕ), N < n → Tsieve2 n D' Y' = 0) :
    ∀ Y : ℕ, ∀ D : ℝ,
      (MpSum2 D Y = Vsieve Y
        + ∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1), Tsieve2 n D Y)
      ∧ (MeSum2 D Y = Vsieve Y
          + (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => D < (q:ℝ)), (1/((q:ℝ)-1)) * Vsieve q)
          - ∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n), Tsieve2 n D Y) := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | h Y ih =>
    intro D
    -- recursion, filter form
    have hrecP : MpSum2 D Y = 1 - ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((2:ℝ)+1) ≤ D),
        (1/((q:ℝ)-1)) * MeSum2 (D/q) q := by
      rw [MpSum2_rec, Finset.sum_filter]
    have hrecM : MeSum2 D Y = 1 - ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D),
        (1/((q:ℝ)-1)) * MpSum2 (D/q) q := by
      rw [MeSum2_rec, Finset.sum_filter]
    -- Tone in filter form (definition)
    have hTone : Tone D Y = ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => ¬ ((q:ℝ)^((2:ℝ)+1) ≤ D)),
        (1/((q:ℝ)-1)) * Vsieve q := rfl
    -- the telescoping of the Euler product, split by the cube condition
    have hsplitV : (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((2:ℝ)+1) ≤ D),
          (1/((q:ℝ)-1)) * Vsieve q)
        + (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => ¬ ((q:ℝ)^((2:ℝ)+1) ≤ D)),
          (1/((q:ℝ)-1)) * Vsieve q)
        = ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun q _ => by by_cases hc : (q:ℝ)^((2:ℝ)+1) ≤ D <;> simp [hc])
    have htel : 1 - ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q = Vsieve Y := by
      rw [Vsieve_rec]
    constructor
    · rw [MpSum2_rec]
      have hA : ∀ q ∈ oddPrimesLt Y,
          (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * MeSum2 (D/q) q else 0)
          = (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * (Vsieve q
              - ∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
                  Tsieve2 n (D/q) q) else 0) := by
        intro q hq
        have hqY : q < Y := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
        by_cases hc : (q:ℝ)^((2:ℝ)+1) ≤ D
        · rw [if_pos hc, if_pos hc, (ih q hqY (D/q)).2,
              linComp_eq_zero (D := D) (q := q) (by
                simpa [show (q:ℝ)^((2:ℝ)+1) = (q:ℝ)^3 from by
                  rw [show (2:ℝ)+1 = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]] using hc)]
          ring
        · rw [if_neg hc, if_neg hc]
      rw [Finset.sum_congr rfl hA]
      have hB : ∀ q ∈ oddPrimesLt Y,
          (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * (Vsieve q
              - ∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
                  Tsieve2 n (D/q) q) else 0)
          = (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * Vsieve q else 0)
            - (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) *
                (∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
                  Tsieve2 n (D/q) q) else 0) := by
        intro q hq
        by_cases hc : (q:ℝ)^((2:ℝ)+1) ≤ D
        · rw [if_pos hc, if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc, if_neg hc]; ring
      rw [Finset.sum_congr rfl hB, Finset.sum_sub_distrib]
      -- main term
      have hmain : 1 - (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * Vsieve q else 0))
          = Vsieve Y + Tone D Y := by
        have h1 : (∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) * Vsieve q else 0))
            = (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((2:ℝ)+1) ≤ D),
                (1/((q:ℝ)-1)) * Vsieve q) := by
          rw [Finset.sum_filter]
        rw [h1]
        linarith [hsplitV, htel, hTone]
      -- layer part
      have hlay : (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ)^((2:ℝ)+1) ≤ D then (1/((q:ℝ)-1)) *
                (∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
                  Tsieve2 n (D/q) q) else 0))
          = ∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1), Tsieve2 n D Y
            - Tone D Y := by
        have hstep : ∀ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
            (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((2:ℝ)+1) ≤ D),
                (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q) = Tsieve2 (n+1) D Y := by
          intro n hn
          rw [Finset.mem_filter] at hn
          obtain ⟨hnN, hne, hn2⟩ := hn
          have hpar : (n+1) % 2 = 1 := by omega
          rw [show Tsieve2 (n+1) D Y
                = ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => condT (n+1) q D),
                    (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q from by
            have h := Tsieve2_succ_succ (n-1) D Y
            rwa [show n - 1 + 2 = n + 1 from by omega,
                 show n - 1 + 1 = n from by omega] at h]
          congr 1
          apply Finset.filter_congr
          intro q _
          simp only [condT, hpar, if_true]
        rw [← Finset.sum_filter]
        have hdist : (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((2:ℝ)+1) ≤ D),
              (1/((q:ℝ)-1)) * (∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
                Tsieve2 n (D/q) q))
            = ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ)^((2:ℝ)+1) ≤ D),
              ∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
                (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.mul_sum]
        rw [hdist, Finset.sum_comm]
        rw [Finset.sum_congr rfl (fun n hn => hstep n hn)]
        have hbij : (∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
              Tsieve2 (n+1) D Y)
            = ∑ m ∈ ((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter (fun m => 3 ≤ m),
                Tsieve2 m D Y := by
          refine Finset.sum_bij (fun n _ => n+1) ?_ ?_ ?_ ?_
          · intro n hn
            simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
            omega
          · intro a ha b hb hab
            omega
          · intro b hb
            simp only [Finset.mem_filter, Finset.mem_range] at hb
            exact ⟨b-1, by simp only [Finset.mem_filter, Finset.mem_range]; omega, by omega⟩
          · intro n hn
            rfl
        rw [hbij]
        have hset : (Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)
            = insert 1 (((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter
                (fun m => 3 ≤ m)) := by
          ext m
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
          omega
        have hnot : 1 ∉ (((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter
            (fun m => 3 ≤ m)) := by
          simp only [Finset.mem_filter, Finset.mem_range]; omega
        rw [hset, Finset.sum_insert hnot, Tsieve2_one]
        have hfin3 : (insert 1 (((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter
              (fun m => 3 ≤ m))).filter (fun x => 3 ≤ x)
            = ((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter (fun m => 3 ≤ m) := by
          rw [Finset.filter_insert]
          simp
        have hfin2 : (((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter
              (fun m => 3 ≤ m)).filter (fun x => 3 ≤ x)
            = ((Finset.range (N+2)).filter (fun m : ℕ => m % 2 = 1)).filter (fun m => 3 ≤ m) :=
          Finset.filter_true_of_mem (fun x hx => (Finset.mem_filter.mp hx).2)
        rw [add_sub_cancel_left, hfin3]
      linarith [hmain, hlay]
    · -- MeSum2 (the mirror)
      rw [MeSum2_rec]
      have hA2 : ∀ q ∈ oddPrimesLt Y,
          (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * MpSum2 (D/q) q else 0)
          = (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * (Vsieve q
              + ∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
                  Tsieve2 n (D/q) q) else 0) := by
        intro q hq
        have hqY : q < Y := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
        by_cases hc : (q:ℝ) ≤ D
        · rw [if_pos hc, if_pos hc, (ih q hqY (D/q)).1]
        · rw [if_neg hc, if_neg hc]
      rw [Finset.sum_congr rfl hA2]
      have hB2 : ∀ q ∈ oddPrimesLt Y,
          (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * (Vsieve q
              + ∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
                  Tsieve2 n (D/q) q) else 0)
          = (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * Vsieve q else 0)
            + (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) *
                (∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
                  Tsieve2 n (D/q) q) else 0) := by
        intro q hq
        by_cases hc : (q:ℝ) ≤ D
        · rw [if_pos hc, if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc, if_neg hc]; ring
      rw [Finset.sum_congr rfl hB2, Finset.sum_add_distrib]
      have htel2 : 1 - ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q = Vsieve Y := by
        rw [Vsieve_rec]
      have hmain2 : 1 - (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * Vsieve q else 0))
          = Vsieve Y + (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => D < (q:ℝ)),
              (1/((q:ℝ)-1)) * Vsieve q) := by
        have h1 : (∑ q ∈ oddPrimesLt Y,
              (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) * Vsieve q else 0))
            = (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D),
                (1/((q:ℝ)-1)) * Vsieve q) := by
          rw [Finset.sum_filter]
        have hsplit2 : (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D),
              (1/((q:ℝ)-1)) * Vsieve q)
            + (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => ¬ ((q:ℝ) ≤ D)),
                (1/((q:ℝ)-1)) * Vsieve q)
            = ∑ q ∈ oddPrimesLt Y, (1/((q:ℝ)-1)) * Vsieve q := by
          rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun q _ => by by_cases hc : (q:ℝ) ≤ D <;> simp [hc])
        have hcompl : (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => ¬ ((q:ℝ) ≤ D)),
              (1/((q:ℝ)-1)) * Vsieve q)
            = (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => D < (q:ℝ)),
                (1/((q:ℝ)-1)) * Vsieve q) := by
          apply Finset.sum_congr
          · exact Finset.filter_congr (fun q _ => not_le)
          · intro q _; rfl
        rw [h1]
        linarith [hsplit2, htel2, hcompl]
      have hlay2 : (∑ q ∈ oddPrimesLt Y,
            (if (q:ℝ) ≤ D then (1/((q:ℝ)-1)) *
                (∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
                  Tsieve2 n (D/q) q) else 0))
          = ∑ n ∈ (Finset.range (N+1)).filter (fun n : ℕ => n % 2 = 0 ∧ 2 ≤ n),
              Tsieve2 n D Y := by
        have hv1 : Tsieve2 (N+1) D Y = 0 := hvan D Y (N+1) (by omega)
        have hv2 : Tsieve2 (N+2) D Y = 0 := hvan D Y (N+2) (by omega)
        have hstep : ∀ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
            (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D),
                (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q) = Tsieve2 (n+1) D Y := by
          intro n hn
          rw [Finset.mem_filter] at hn
          obtain ⟨hnN, hno⟩ := hn
          have hpar : ¬ ((n+1) % 2 = 1) := by omega
          rw [show Tsieve2 (n+1) D Y
                = ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => condT (n+1) q D),
                    (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q from by
            have h := Tsieve2_succ_succ (n-1) D Y
            rwa [show n - 1 + 2 = n + 1 from by omega,
                 show n - 1 + 1 = n from by omega] at h]
          congr 1
          apply Finset.filter_congr
          intro q _
          simp only [condT, hpar, if_false]
        rw [← Finset.sum_filter]
        have hdist : (∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D),
              (1/((q:ℝ)-1)) * (∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
                Tsieve2 n (D/q) q))
            = ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => (q:ℝ) ≤ D),
              ∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
                (1/((q:ℝ)-1)) * Tsieve2 n (D/q) q := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.mul_sum]
        rw [hdist, Finset.sum_comm]
        rw [Finset.sum_congr rfl (fun n hn => hstep n hn)]
        have hbij : (∑ n ∈ (Finset.range (N+2)).filter (fun n : ℕ => n % 2 = 1),
              Tsieve2 (n+1) D Y)
            = ∑ m ∈ (Finset.range (N+3)).filter (fun m : ℕ => m % 2 = 0 ∧ 2 ≤ m),
                Tsieve2 m D Y := by
          refine Finset.sum_bij (fun n _ => n+1) ?_ ?_ ?_ ?_
          · intro n hn
            simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
            omega
          · intro a ha b hb hab
            omega
          · intro b hb
            simp only [Finset.mem_filter, Finset.mem_range] at hb
            exact ⟨b-1, by simp only [Finset.mem_filter, Finset.mem_range]; omega, by omega⟩
          · intro n hn
            rfl
        rw [hbij]
        have hshrink : (∑ m ∈ (Finset.range (N+3)).filter (fun m : ℕ => m % 2 = 0 ∧ 2 ≤ m),
              Tsieve2 m D Y)
            = ∑ m ∈ (Finset.range (N+1)).filter (fun m : ℕ => m % 2 = 0 ∧ 2 ≤ m),
                Tsieve2 m D Y :=
          (Finset.sum_subset
            (by
              intro m hm
              simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
              omega)
            (by
              intro m hm hmnot
              simp only [Finset.mem_filter, Finset.mem_range] at hm hmnot
              have hm' : m = N+1 ∨ m = N+2 := by omega
              rcases hm' with rfl | rfl
              · exact hv1
              · exact hv2)).symm
        rw [hshrink]
      linarith [hmain2, hlay2]

end

end Commons.NumberTheory.Chen
