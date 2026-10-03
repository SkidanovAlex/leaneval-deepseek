import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_eq_sum_c
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Aseq_ge_const_mul_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega_mul_of_cubefree
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_filter_dvd_sq_add_pow_four_le
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos
import Submission.Commons.NumberTheory.Divisors.prod_factorization_div_two_eq_sqPart
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_eight_cubefree
import Submission.Commons.NumberTheory.FriedlanderIwaniec.ncard_sq_add_pow_four_ge
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_residues_le_two_pow_omega_gcd
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gcd_sq_eq_gcd_of_squarefree
import Submission.Commons.NumberTheory.FriedlanderIwaniec.squarefree_sqKernel_of_cubefree
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd
import Submission.Commons.NumberTheory.FriedlanderIwaniec.primeFactors_sqKernel_subset
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.Int.ncard_int_fiber_le
import Submission.Commons.NumberTheory.Int.card_multiples_pow_four_le
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_totient_div_divisors_le_two_pow_omega

open Finset

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- `((a.natAbs : ℤ)) ^ 4 = a ^ 4`. -/
private lemma int_natAbs_pow_four (a : ℤ) : ((a.natAbs : ℤ)) ^ 4 = a ^ 4 := by
  have h1 : ((a.natAbs : ℤ)) ^ 4 = ((a.natAbs ^ 4 : ℕ) : ℤ) := by rw [Nat.cast_pow]
  rw [h1, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity)]

private lemma gcd_sum_totient_of_ne_zero {c m : ℕ} (hm : m ≠ 0) :
    Nat.gcd c m = ∑ k ∈ m.divisors.filter (fun k => k ∣ c), Nat.totient k := by
  have hgne : Nat.gcd c m ≠ 0 :=
    fun h => hm (Nat.eq_zero_of_zero_dvd (h ▸ Nat.gcd_dvd_right c m))
  have hset : m.divisors.filter (fun k => k ∣ c) = (Nat.gcd c m).divisors := by
    ext k
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hkm, _⟩, hkc⟩
      exact ⟨Nat.dvd_gcd hkc hkm, hgne⟩
    · rintro ⟨hkg, _⟩
      exact ⟨⟨dvd_trans hkg (Nat.gcd_dvd_right c m), hm⟩, dvd_trans hkg (Nat.gcd_dvd_left c m)⟩
  rw [hset, Nat.sum_totient]

private lemma reindex_gcd_sum_totient (m : ℕ) (hm : m ≠ 0) (S : Finset ℤ) (w : ℤ → ℝ) :
    (∑ b ∈ S, (Nat.gcd b.natAbs m : ℝ) * w b) =
      ∑ k ∈ m.divisors, (Nat.totient k : ℝ) * (∑ b ∈ S.filter (fun b => (k : ℤ) ∣ b), w b) := by
  have hpt : ∀ b : ℤ, (Nat.gcd b.natAbs m : ℝ)
      = ∑ k ∈ m.divisors, (if k ∣ b.natAbs then (Nat.totient k : ℝ) else 0) := by
    intro b
    rw [gcd_sum_totient_of_ne_zero hm]
    push_cast
    rw [← Finset.sum_filter]
  calc (∑ b ∈ S, (Nat.gcd b.natAbs m : ℝ) * w b)
      = ∑ b ∈ S, (∑ k ∈ m.divisors,
            (if k ∣ b.natAbs then (Nat.totient k : ℝ) else 0)) * w b := by
        apply Finset.sum_congr rfl; intro b _; rw [hpt b]
    _ = ∑ b ∈ S, ∑ k ∈ m.divisors,
            (if k ∣ b.natAbs then (Nat.totient k : ℝ) else 0) * w b := by
        apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul]
    _ = ∑ k ∈ m.divisors, ∑ b ∈ S,
            (if k ∣ b.natAbs then (Nat.totient k : ℝ) else 0) * w b :=
        Finset.sum_comm
    _ = ∑ k ∈ m.divisors, ∑ b ∈ S,
            (if k ∣ b.natAbs then (Nat.totient k : ℝ) * w b else 0) := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro b _
        by_cases h : k ∣ b.natAbs <;> simp [h]
    _ = ∑ k ∈ m.divisors,
            ∑ b ∈ S.filter (fun b => k ∣ b.natAbs), (Nat.totient k : ℝ) * w b := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_filter]
    _ = ∑ k ∈ m.divisors,
            (Nat.totient k : ℝ) * (∑ b ∈ S.filter (fun b => k ∣ b.natAbs), w b) := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
    _ = ∑ k ∈ m.divisors,
            (Nat.totient k : ℝ) * (∑ b ∈ S.filter (fun b => (k : ℤ) ∣ b), w b) := by
        apply Finset.sum_congr rfl; intro k _
        rw [show S.filter (fun b => k ∣ b.natAbs) = S.filter (fun b => (k : ℤ) ∣ b) from by
              apply Finset.filter_congr
              intro b _
              exact (by rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs])]

/-- Companion-sieve bound for the Friedlander–Iwaniec sequence with the **sharp**
`d⁻¹ τ(d)² A(x)` right-hand side (for cubefree `d ≤ x^{1/2}`); stated for the lattice-point
counts `A_d(x)` and `A(x)`. -/
theorem Ad_ncard_le_tau_sq_of_cubefree :
    ∃ C : ℝ, 0 < C ∧ ∀ d x : ℕ, 1 ≤ d → d ^ 2 ≤ x →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) →
      (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (p.1 ^ 2 + p.2 ^ 4)}.ncard : ℕ) : ℝ)
        ≤ C * (((Nat.divisors d).card : ℕ) : ℝ) ^ 2 / (d : ℝ)
            * (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard : ℕ) : ℝ) := by
  refine ⟨18, by norm_num, ?_⟩
  intro d x hd hdx hcube
  have hx : 1 ≤ x := by
    have h1 : 1 ≤ d ^ 2 := by nlinarith [hd]
    omega
  classical
  set Sd : Set (ℤ × ℤ) := {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (p.1 ^ 2 + p.2 ^ 4)} with hSd
  set S : Set (ℤ × ℤ) := {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)} with hS
  set s : ℝ := Real.sqrt (Real.sqrt (x : ℝ)) with hsdef
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxR0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hxR1)
  have hs2 : s ^ 2 = Real.sqrt (x : ℝ) := by
    rw [hsdef, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hs4 : s ^ 4 = (x : ℝ) := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hxR0]
  have hsnn : 0 ≤ s := le_trans zero_le_one hs1
  -- d ≤ s²
  have hdle_s2 : (d : ℝ) ≤ s ^ 2 := by
    rw [hs2]
    exact (Real.le_sqrt (by positivity) hxR0).mpr (by exact_mod_cast hdx)
  -- t2 = d₂ = ∏ p^(v_p/2)
  set t2 : ℕ := (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) with ht2def
  have ht2sf : Squarefree t2 := squarefree_sqKernel_of_cubefree hcube
  have ht2dvd : t2 ^ 2 ∣ d := sqKernel_sq_dvd d
  have ht2pf : t2.primeFactors ⊆ d.primeFactors := primeFactors_sqKernel_subset d
  have hdpos : 0 < d := hd
  have ht2pos : 0 < t2 := by
    rw [ht2def]
    exact Finset.prod_pos (fun p hp => pow_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)) _)
  have ht2sq_le_d : t2 ^ 2 ≤ d := Nat.le_of_dvd hdpos ht2dvd
  have ht2_le_s : (t2 : ℝ) ≤ s := by
    have h1 : ((t2 : ℝ)) ^ 2 ≤ s ^ 2 := by
      have h2 : ((t2 : ℝ)) ^ 2 ≤ (d : ℝ) := by exact_mod_cast ht2sq_le_d
      exact le_trans h2 hdle_s2
    nlinarith [hsnn, (show (0 : ℝ) ≤ (t2 : ℝ) by positivity), sq_nonneg ((t2 : ℝ) - s), h1, hs1]
  -- ω, τ
  set om : ℕ := (Nat.primeFactors d).card with homdef
  set tau : ℕ := (Nat.divisors d).card with htaudef
  have h2om_tau : 2 ^ om ≤ tau := two_pow_card_primeFactors_le_card_divisors hdpos
  have htau1 : 1 ≤ tau := by
    rw [htaudef]
    have hmem : d ∈ Nat.divisors d := Nat.mem_divisors.mpr ⟨dvd_rfl, hdpos.ne'⟩
    have := Finset.card_pos.mpr ⟨d, hmem⟩
    omega
  have h4om : (4 : ℝ) ^ om ≤ (tau : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ^ om ≤ (tau : ℝ) := by exact_mod_cast h2om_tau
    have h4 : (4 : ℝ) ^ om = ((2 : ℝ) ^ om) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 om, pow_mul]
    rw [h4]
    exact pow_le_pow_left₀ (by positivity) h2 2
  -- Bfin
  set Bfin : Finset ℤ := (Finset.Icc (-(x : ℤ)) x).filter (fun b => b ^ 4 ≤ (x : ℤ)) with hBfin
  set T1 : ℝ := ∑ b ∈ Bfin, (Nat.gcd b.natAbs t2 : ℝ) * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) with hT1
  set T0 : ℝ := ∑ b ∈ Bfin, (Nat.gcd b.natAbs t2 : ℝ) with hT0
  rcases Sd.finite_or_infinite with hfin | hinf
  · -- main case
    have hB : ∀ p ∈ Sd, p.2 ∈ Bfin := by
      intro p hp
      rw [hSd] at hp
      obtain ⟨hle, _⟩ := hp
      have h1 : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
      have h2 : (0 : ℤ) ≤ p.2 ^ 4 := by positivity
      have hp24 : p.2 ^ 4 ≤ (x : ℤ) := by linarith
      rw [hBfin, Finset.mem_filter, Finset.mem_Icc]
      have hb : ((p.2.natAbs : ℤ)) ^ 4 ≤ (x : ℤ) := by rw [int_natAbs_pow_four]; exact hp24
      have hb' : p.2.natAbs ^ 4 ≤ x := by exact_mod_cast hb
      have hb'' : p.2.natAbs ≤ x := le_trans (Nat.le_self_pow (n := 4) (by norm_num) _) hb'
      have hle' : |p.2| ≤ (x : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb''
      exact ⟨abs_le.mp hle', hp24⟩
    have hfiber := ncard_fiber_sum Sd Bfin hfin hB
    -- per-fiber bound
    have hper : ∀ b ∈ Bfin,
        (({a : ℤ | (a, b) ∈ Sd}).ncard : ℝ) ≤
          ((2 : ℝ) ^ om) * (Nat.gcd b.natAbs t2 : ℝ)
            * (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1) := by
      intro b hb
      have hLHS : ({a : ℤ | (a, b) ∈ Sd} : Set ℤ)
          = {a : ℤ | a ^ 2 + b ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (a ^ 2 + b ^ 4)} := by
        ext a; rw [hSd]; simp only [Set.mem_ofPred_eq]
      have hfib := Commons.NumberTheory.Int.ncard_int_fiber_le (d := d) (x := x) hd b
      rw [hLHS]
      have hg : (((Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ ((r : ℤ) ^ 2 + b ^ 4))).card : ℝ)
          ≤ (2 : ℝ) ^ om * (Nat.gcd b.natAbs t2 : ℝ) := by
        have hcr := card_residues_le_two_pow_omega_gcd hdpos b
        have hgcd : Nat.gcd (b.natAbs ^ 2) t2 = Nat.gcd b.natAbs t2 :=
          gcd_sq_eq_gcd_of_squarefree ht2sf
        rw [hgcd] at hcr
        have : (2 : ℝ) ^ om = (2 : ℝ) ^ (Nat.primeFactors d).card := by rw [homdef]
        rw [this]
        exact_mod_cast hcr
      have hfac : 0 ≤ (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1) := by positivity
      calc (({a : ℤ | a ^ 2 + b ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (a ^ 2 + b ^ 4)}).ncard : ℝ)
          ≤ (((Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ ((r : ℤ) ^ 2 + b ^ 4))).card : ℝ)
              * (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1) := hfib
        _ ≤ ((2 : ℝ) ^ om * (Nat.gcd b.natAbs t2 : ℝ))
              * (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hg hfac
        _ = ((2 : ℝ) ^ om) * (Nat.gcd b.natAbs t2 : ℝ)
              * (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1) := by ring
    have hstep1 : ((Sd.ncard : ℕ) : ℝ)
        ≤ (2 / (d : ℝ)) * ((2 : ℝ) ^ om) * T1 + ((2 : ℝ) ^ om) * T0 := by
      rw [hfiber]
      push_cast
      rw [hT1, hT0]
      calc (∑ b ∈ Bfin, ↑({a : ℤ | (a, b) ∈ Sd}.ncard))
          ≤ ∑ b ∈ Bfin, ((2 : ℝ) ^ om * (Nat.gcd b.natAbs t2 : ℝ)
              * (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) / (d : ℝ) + 1)) :=
              Finset.sum_le_sum hper
        _ = (2 / (d : ℝ)) * ((2 : ℝ) ^ om)
              * (∑ b ∈ Bfin, (Nat.gcd b.natAbs t2 : ℝ) * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4))
            + ((2 : ℝ) ^ om) * (∑ b ∈ Bfin, (Nat.gcd b.natAbs t2 : ℝ)) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro b hb
              ring
    -- reindex T1, T0
    have hT1re : T1 = ∑ k ∈ t2.divisors, (Nat.totient k : ℝ)
        * (∑ b ∈ Bfin.filter (fun b => (k : ℤ) ∣ b), Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4)) := by
      rw [hT1]
      exact reindex_gcd_sum_totient t2 ht2pos.ne' Bfin _
    have hT0re : T0 = ∑ k ∈ t2.divisors, (Nat.totient k : ℝ)
        * ((Bfin.filter (fun b => (k : ℤ) ∣ b)).card : ℝ) := by
      rw [hT0]
      have h := reindex_gcd_sum_totient t2 ht2pos.ne' Bfin (fun _ => (1 : ℝ))
      simp only [mul_one] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    -- inner bounds
    have hinner1 : ∀ k ∈ t2.divisors,
        (∑ b ∈ Bfin.filter (fun b => (k : ℤ) ∣ b), Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4))
          ≤ (2 * s / (k : ℝ) + 1) * s ^ 2 := by
      intro k hk
      have hkpos : 1 ≤ k := Nat.pos_of_mem_divisors hk
      have hcard : ((Bfin.filter (fun b => (k : ℤ) ∣ b)).card : ℝ) ≤ 2 * s / (k : ℝ) + 1 := by
        have hcm := Commons.NumberTheory.Int.card_multiples_pow_four_le x k hkpos
        have : Bfin.filter (fun b => (k : ℤ) ∣ b)
            = ((Finset.Icc (-(x : ℤ)) x).filter (fun b => b ^ 4 ≤ (x : ℤ))).filter
                (fun b => (k : ℤ) ∣ b) := by rw [hBfin]
        rw [this, hsdef]
        exact hcm
      calc (∑ b ∈ Bfin.filter (fun b => (k : ℤ) ∣ b), Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4))
          ≤ ∑ b ∈ Bfin.filter (fun b => (k : ℤ) ∣ b), s ^ 2 := by
            apply Finset.sum_le_sum
            intro b hb
            rw [Finset.mem_filter] at hb
            have hb4 : (b : ℝ) ^ 4 ≤ (x : ℝ) := by
              rw [hBfin, Finset.mem_filter] at hb
              exact_mod_cast hb.1.2
            have hle : Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4) ≤ Real.sqrt (x : ℝ) :=
              Real.sqrt_le_sqrt (by linarith [(show (0:ℝ) ≤ (b:ℝ)^4 by positivity)])
            rw [hs2]; exact hle
        _ = (Bfin.filter (fun b => (k : ℤ) ∣ b)).card * s ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * s / (k : ℝ) + 1) * s ^ 2 :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
    have hinner0 : ∀ k ∈ t2.divisors,
        ((Bfin.filter (fun b => (k : ℤ) ∣ b)).card : ℝ) ≤ 2 * s / (k : ℝ) + 1 := by
      intro k hk
      have hkpos : 1 ≤ k := Nat.pos_of_mem_divisors hk
      have hcm := Commons.NumberTheory.Int.card_multiples_pow_four_le x k hkpos
      have : Bfin.filter (fun b => (k : ℤ) ∣ b)
          = ((Finset.Icc (-(x : ℤ)) x).filter (fun b => b ^ 4 ≤ (x : ℤ))).filter
              (fun b => (k : ℤ) ∣ b) := by rw [hBfin]
      rw [this, hsdef]
      exact hcm
    -- divisor sums
    have hphidiv : (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ)) ≤ (2 : ℝ) ^ om := by
      have h := Commons.NumberTheory.ArithmeticFunction.sum_totient_div_divisors_le_two_pow_omega ht2sf
      have hc : (t2.primeFactors).card ≤ om := by
        rw [homdef]
        exact Finset.card_le_card ht2pf
      calc (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ))
          ≤ (2 : ℝ) ^ (t2.primeFactors).card := h
        _ ≤ (2 : ℝ) ^ om := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hc)
    have hphisum : (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)) = (t2 : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast Nat.sum_totient t2
    -- T1 bound
    have hT1le : T1 ≤ 3 * (2 : ℝ) ^ om * s ^ 3 := by
      rw [hT1re]
      have hmid : (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)
            * (∑ b ∈ Bfin.filter (fun b => (k : ℤ) ∣ b), Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4)))
          ≤ 2 * s ^ 3 * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ))
            + s ^ 2 * (t2 : ℝ) := by
        calc (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)
              * (∑ b ∈ Bfin.filter (fun b => (k : ℤ) ∣ b), Real.sqrt ((x : ℝ) - (b : ℝ) ^ 4)))
            ≤ ∑ k ∈ t2.divisors, (Nat.totient k : ℝ) * ((2 * s / (k : ℝ) + 1) * s ^ 2) := by
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_left (hinner1 k hk) (by positivity)
          _ = 2 * s ^ 3 * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ))
                + s ^ 2 * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              have hkpos : (0 : ℝ) < (k : ℝ) := by
                have := Nat.pos_of_mem_divisors hk; exact_mod_cast this
              field_simp
          _ = 2 * s ^ 3 * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ))
                + s ^ 2 * (t2 : ℝ) := by rw [hphisum]
      calc _ ≤ 2 * s ^ 3 * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ)) + s ^ 2 * (t2 : ℝ) := hmid
        _ ≤ 2 * s ^ 3 * ((2 : ℝ) ^ om) + s ^ 2 * s := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hphidiv (by positivity)
              · exact mul_le_mul_of_nonneg_left ht2_le_s (by positivity)
        _ ≤ 3 * (2 : ℝ) ^ om * s ^ 3 := by
              have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ om := one_le_pow₀ (by norm_num)
              nlinarith [hsnn, hs1, hp1, sq_nonneg s, mul_nonneg hsnn hsnn]
    -- T0 bound
    have hT0le : T0 ≤ 3 * (2 : ℝ) ^ om * s := by
      rw [hT0re]
      have hmid : (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)
            * ((Bfin.filter (fun b => (k : ℤ) ∣ b)).card : ℝ))
          ≤ 2 * s * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ))
            + (t2 : ℝ) := by
        calc (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)
              * ((Bfin.filter (fun b => (k : ℤ) ∣ b)).card : ℝ))
            ≤ ∑ k ∈ t2.divisors, (Nat.totient k : ℝ) * (2 * s / (k : ℝ) + 1) := by
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_left (hinner0 k hk) (by positivity)
          _ = 2 * s * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ))
                + (∑ k ∈ t2.divisors, (Nat.totient k : ℝ)) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              have hkpos : (0 : ℝ) < (k : ℝ) := by
                have := Nat.pos_of_mem_divisors hk; exact_mod_cast this
              field_simp
          _ = 2 * s * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ)) + (t2 : ℝ) := by
              rw [hphisum]
      calc _ ≤ 2 * s * (∑ k ∈ t2.divisors, (Nat.totient k : ℝ) / (k : ℝ)) + (t2 : ℝ) := hmid
        _ ≤ 2 * s * ((2 : ℝ) ^ om) + s := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hphidiv (by positivity)
              · exact ht2_le_s
        _ ≤ 3 * (2 : ℝ) ^ om * s := by
              have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ om := one_le_pow₀ (by norm_num)
              nlinarith [hsnn, hs1, hp1]
    -- lower bound on S
    have hSl : s ^ 3 / 2 ≤ ((S.ncard : ℕ) : ℝ) := by
      rw [hS]; exact ncard_sq_add_pow_four_ge x hx
    -- final assembly
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hAnum : s ^ 3 ≤ 2 * ((S.ncard : ℕ) : ℝ) := by linarith [hSl]
    have hsD : s * (d : ℝ) ≤ 2 * ((S.ncard : ℕ) : ℝ) := by
      have h1 : s * (d : ℝ) ≤ s * s ^ 2 := mul_le_mul_of_nonneg_left hdle_s2 hsnn
      have h2 : s * s ^ 2 = s ^ 3 := by ring
      linarith [h1, h2.le, h2.ge, hAnum]
    have hnum : 6 * (4 : ℝ) ^ om * s ^ 3 + 3 * (4 : ℝ) ^ om * s * (d : ℝ)
        ≤ 18 * (tau : ℝ) ^ 2 * ((S.ncard : ℕ) : ℝ) := by
      have hP1 : (0 : ℝ) ≤ (tau : ℝ) ^ 2 := by positivity
      have h1 : 6 * (4 : ℝ) ^ om * s ^ 3 ≤ 12 * (tau : ℝ) ^ 2 * ((S.ncard : ℕ) : ℝ) := by
        calc 6 * (4 : ℝ) ^ om * s ^ 3 ≤ 6 * (tau : ℝ) ^ 2 * s ^ 3 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h4om (by norm_num)) (by positivity)
          _ ≤ 6 * (tau : ℝ) ^ 2 * (2 * ((S.ncard : ℕ) : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hAnum (by positivity)
          _ = 12 * (tau : ℝ) ^ 2 * ((S.ncard : ℕ) : ℝ) := by ring
      have h2 : 3 * (4 : ℝ) ^ om * s * (d : ℝ) ≤ 6 * (tau : ℝ) ^ 2 * ((S.ncard : ℕ) : ℝ) := by
        calc 3 * (4 : ℝ) ^ om * s * (d : ℝ)
            = 3 * (4 : ℝ) ^ om * (s * (d : ℝ)) := by ring
          _ ≤ 3 * (tau : ℝ) ^ 2 * (s * (d : ℝ)) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h4om (by norm_num : (0:ℝ) ≤ 3)) (by positivity)
          _ ≤ 3 * (tau : ℝ) ^ 2 * (2 * ((S.ncard : ℕ) : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hsD (by positivity)
          _ = 6 * (tau : ℝ) ^ 2 * ((S.ncard : ℕ) : ℝ) := by ring
      linarith [h1, h2]
    have hfin : 6 * (4 : ℝ) ^ om * s ^ 3 / (d : ℝ) + 3 * (4 : ℝ) ^ om * s
        ≤ 18 * (tau : ℝ) ^ 2 / (d : ℝ) * ((S.ncard : ℕ) : ℝ) := by
      rw [show 6 * (4 : ℝ) ^ om * s ^ 3 / (d : ℝ) + 3 * (4 : ℝ) ^ om * s
            = (6 * (4 : ℝ) ^ om * s ^ 3 + 3 * (4 : ℝ) ^ om * s * (d : ℝ)) / (d : ℝ) by
            field_simp]
      rw [show 18 * (tau : ℝ) ^ 2 / (d : ℝ) * ((S.ncard : ℕ) : ℝ)
            = (18 * (tau : ℝ) ^ 2 * ((S.ncard : ℕ) : ℝ)) / (d : ℝ) by
            field_simp]
      exact (div_le_div_iff_of_pos_right hdR).mpr hnum
    calc ((Sd.ncard : ℕ) : ℝ)
        ≤ (2 / (d : ℝ)) * ((2 : ℝ) ^ om) * T1 + ((2 : ℝ) ^ om) * T0 := hstep1
      _ ≤ (2 / (d : ℝ)) * ((2 : ℝ) ^ om) * (3 * (2 : ℝ) ^ om * s ^ 3)
            + ((2 : ℝ) ^ om) * (3 * (2 : ℝ) ^ om * s) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hT1le (by positivity)
            · exact mul_le_mul_of_nonneg_left hT0le (by positivity)
      _ = 6 * (4 : ℝ) ^ om * s ^ 3 / (d : ℝ) + 3 * (4 : ℝ) ^ om * s := by
            rw [show (4 : ℝ) ^ om = ((2 : ℝ) ^ om) ^ 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 om, pow_mul]]
            field_simp
            ring
      _ ≤ 18 * (tau : ℝ) ^ 2 / (d : ℝ) * ((S.ncard : ℕ) : ℝ) := hfin
      _ = 18 * (((Nat.divisors d).card : ℕ) : ℝ) ^ 2 / (d : ℝ)
            * ((S.ncard : ℕ) : ℝ) := by rw [htaudef]
  · -- infinite case (impossible, but ncard = 0 then)
    rw [hinf.ncard]
    push_cast
    positivity

/-- `A_d(x) ≤ C τ(d)²/d · A(x)` for cubefree `d` with `d² ≤ x`. -/
theorem Ad_le_tau_sq_div_of_cubefree : ∃ C : ℝ, 0 < C ∧ ∀ d x : ℕ, 1 ≤ d →
    (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) → d ^ 2 ≤ x →
    (Submission.Ad d x : ℝ)
      ≤ C * (((Nat.divisors d).card : ℝ) ^ 2 / (d : ℝ))
          * (Submission.Aseq x : ℝ) := by
  obtain ⟨C, hC, h⟩ := Ad_ncard_le_tau_sq_of_cubefree
  refine ⟨C, hC, fun d x hd hcb hdx => ?_⟩
  have hAd : Submission.Ad d x
      = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (p.1 ^ 2 + p.2 ^ 4)}).ncard := by
    rw [Submission.Ad]
    simp only [Submission.an]
    exact (Submission.ncard_eq_Ad_sum d x).symm
  have hA : Submission.Aseq x = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard :=
    Submission.Aseq_eq_ncard x
  rw [show (Submission.Ad d x : ℝ)
        = (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ (p.1 ^ 2 + p.2 ^ 4)}.ncard : ℕ) : ℝ)
      from by rw [hAd],
    show (Submission.Aseq x : ℝ)
        = (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard : ℕ) : ℝ) from by rw [hA]]
  simpa only [mul_div_assoc] using h d x hd hdx hcb

end Commons.NumberTheory.FriedlanderIwaniec
