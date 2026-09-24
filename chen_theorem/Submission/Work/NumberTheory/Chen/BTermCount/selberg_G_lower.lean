import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Commons.NumberTheory.Totient.log_le_sum_mu_sq_div_totient

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The Selberg constant `G`: lower bound

`∑_{l ≤ D, l ∣ oddPrimLt Y} 1/∏_{p|l}(p-2) ≥ (1/4) log D` for `2 ≤ D ≤ Y`.

Writing `P = oddPrimLt Y` (the product of the odd primes `< Y`) and `F l = 1/∏_{p | l}(p-2)`,
every `l ≤ D-1` with `l | P` is odd and squarefree (all of its prime factors are `< Y`), and
`∏_{p|l}(p-2) ≤ ∏_{p|l}(p-1) = φ(l)`, so it suffices to lower bound
`∑_{l ≤ D-1, l odd, squarefree} 1/φ(l) ≥ (1/2) log (D-1)`.

That last bound is obtained from the banked theorem
`Commons.NumberTheory.Totient.log_le_sum_mu_sq_div_totient`: `log R ≤ ∑_{r ≤ R} μ(r)^2/φ(r)`,
the sum over all squarefree `r ≤ R`; the even squarefree terms `r = 2m` satisfy `φ(2m) = φ(m)`,
so they are dominated by the odd ones (`m ↦ 2m` is injective on odd squarefree numbers), giving
`∑_{odd squarefree r ≤ R} 1/φ(r) ≥ (1/2) ∑_{squarefree r ≤ R} 1/φ(r) ≥ (1/2) log R`.
Finally `D ≤ (D-1)²` for `3 ≤ D` turns `(1/2) log (D-1)` into `(1/4) log D`.
-/

/-! ## Elementary lemmas -/

/-- For squarefree `n`, `φ n = ∏_{p | n} (p - 1)`. -/
lemma totient_eq_prod_sub_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn] at h
  rw [Nat.mul_comm n.totient n] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) h

/-- Every prime factor of an odd number is `≥ 3`. -/
lemma three_le_of_mem_primeFactors_of_odd {m p : ℕ} (hm : m % 2 = 1)
    (hp : p ∈ m.primeFactors) : 3 ≤ p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.dvd_iff_mod_eq_zero] at hpdvd
    omega
  have := hpp.two_le
  omega

/-- For odd `l`, the product `∏_{p | l} (p - 2)` is positive. -/
lemma prod_primeFactors_sub_two_pos {l : ℕ} (hl : l % 2 = 1) :
    0 < ∏ p ∈ l.primeFactors, ((p : ℝ) - 2) := by
  apply Finset.prod_pos
  intro p hp
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast three_le_of_mem_primeFactors_of_odd hl hp
  linarith

/-- The Selberg term `1/∏_{p|l}(p-2)` is nonnegative, for every `l`. -/
lemma one_div_prod_sub_two_nonneg (l : ℕ) :
    0 ≤ 1 / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) := by
  apply div_nonneg one_pos.le
  apply Finset.prod_nonneg
  intro p hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  linarith

/-- For odd squarefree `l`, `1/φ(l) ≤ 1/∏_{p|l}(p-2)`, since `∏(p-2) ≤ ∏(p-1) = φ(l)`. -/
lemma totient_inv_le_one_div_prod_sub_two {l : ℕ} (hl : l % 2 = 1) (hsq : Squarefree l) :
    (Nat.totient l : ℝ)⁻¹ ≤ 1 / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) := by
  have hpos := prod_primeFactors_sub_two_pos hl
  have hle : (∏ p ∈ l.primeFactors, ((p : ℝ) - 2))
      ≤ ∏ p ∈ l.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have h3 : (3 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast three_le_of_mem_primeFactors_of_odd hl hp
      linarith
    · intro p hp
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
      linarith
  have htot : (Nat.totient l : ℝ) = ∏ p ∈ l.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_eq_prod_sub_one_of_squarefree hsq, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [htot]
  simpa only [one_div] using one_div_le_one_div_of_le hpos hle

/-- If `r` is even and squarefree then `r/2` is odd. -/
lemma odd_div_two_of_even_of_squarefree {r : ℕ} (hr2 : r % 2 = 0) (hsq : Squarefree r) :
    Odd (r / 2) := by
  have h2dvd : 2 ∣ r := Nat.dvd_iff_mod_eq_zero.mpr hr2
  have hnot2 : ¬ 2 ∣ r / 2 := by
    intro h
    obtain ⟨t, ht⟩ := h
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
      ⟨t, by rw [← Nat.mul_div_cancel' h2dvd, ht]; ring⟩
  rcases Nat.mod_two_eq_zero_or_one (r / 2) with h | h
  · exact absurd (Nat.dvd_iff_mod_eq_zero.mpr h) hnot2
  · exact Nat.odd_iff.mpr h

/-- If `r` is even and squarefree then so is `r/2`. -/
lemma squarefree_div_two_of_even_squarefree {r : ℕ} (hr2 : r % 2 = 0) (hsq : Squarefree r) :
    Squarefree (r / 2) :=
  Squarefree.squarefree_of_dvd
    ⟨2, by rw [mul_comm]; exact (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hr2)).symm⟩
    hsq

/-! ## The odd squarefree totient sum -/

/-- **The odd squarefree part of `∑ μ(r)²/φ(r)`.**  For `1 ≤ N`,
`(1/2) log N ≤ ∑_{m ≤ N, m odd, squarefree} 1/φ(m)`.

Indeed `log N ≤ ∑_{r ≤ N} μ(r)^2/φ(r) = ∑_{r ≤ N, squarefree} 1/φ(r)`, and the even
squarefree `r = 2m` have `φ(r) = φ(m)` with `m` odd squarefree, `m ≤ r ≤ N`, so the even part is
at most the odd part. -/
lemma half_log_le_odd_sqfree_inv_totient (N : ℕ) (hN : 1 ≤ N) :
    (1 / 2 : ℝ) * Real.log (N : ℝ) ≤
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => m % 2 = 1 ∧ Squarefree m),
        (Nat.totient m : ℝ)⁻¹ := by
  have hbase := Commons.NumberTheory.Totient.log_le_sum_mu_sq_div_totient N hN
  set s : Finset ℕ := (Finset.Icc 1 N).filter Squarefree with hs
  set O : Finset ℕ := s.filter (fun r => r % 2 = 1) with hO
  set E : Finset ℕ := s.filter (fun r => r % 2 = 0) with hE
  -- total sum over squarefree `r`
  have hμ : (∑ r ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ))
      = ∑ r ∈ s, (Nat.totient r : ℝ)⁻¹ := by
    rw [hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hsq : Squarefree r
    · rw [if_pos hsq]
      have h1 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
        rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
        norm_num
      rw [h1, one_div]
    · rw [if_neg hsq]
      have h0 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        norm_num
      rw [h0]
      simp
  -- split into even and odd
  have hsplit : ∑ r ∈ s, (Nat.totient r : ℝ)⁻¹
      = ∑ r ∈ E, (Nat.totient r : ℝ)⁻¹ + ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun r => r % 2 = 0)
      (fun r => (Nat.totient r : ℝ)⁻¹)]
    have hE' : E = s.filter (fun r => r % 2 = 0) := hE
    have hO' : O = s.filter (fun r => ¬ r % 2 = 0) := by
      rw [hO]
      apply Finset.filter_congr
      intro r _
      constructor <;> intro h <;> omega
    rw [hE', hO']
  -- the even squarefree terms are dominated by the odd ones
  have hEsub : E.image (fun r : ℕ => r / 2) ⊆ O := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hrE, rfl⟩ := hk
    rw [hE, Finset.mem_filter] at hrE
    obtain ⟨hrs, hr2⟩ := hrE
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hrs
    obtain ⟨⟨hr1, hrN⟩, hsq⟩ := hrs
    have hr_eq : 2 * (r / 2) = r := Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hr2)
    rw [hO, Finset.mem_filter, hs, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, squarefree_div_two_of_even_squarefree hr2 hsq⟩,
      Nat.odd_iff.mp (odd_div_two_of_even_of_squarefree hr2 hsq)⟩
    · omega
    · omega
  have hEvenLe : ∑ r ∈ E, (Nat.totient r : ℝ)⁻¹ ≤ ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ := by
    have hinj : Set.InjOn (fun r : ℕ => r / 2) ↑E := by
      intro a ha b hb hab
      rw [Finset.mem_coe, hE, Finset.mem_filter] at ha hb
      have hab' : a / 2 = b / 2 := hab
      rw [← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr ha.2),
        ← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hb.2), hab']
    have himg := Finset.sum_image (s := E) (g := fun r : ℕ => r / 2)
      (f := fun m : ℕ => (Nat.totient m : ℝ)⁻¹) hinj
    have hpoint : ∀ r ∈ E, (Nat.totient r : ℝ)⁻¹ = (Nat.totient (r / 2) : ℝ)⁻¹ := by
      intro r hr
      rw [hE, Finset.mem_filter] at hr
      obtain ⟨hrs, hr2⟩ := hr
      rw [hs, Finset.mem_filter] at hrs
      have hsq : Squarefree r := hrs.2
      conv_lhs => rw [← Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hr2)]
      rw [Nat.totient_two_mul_of_odd (odd_div_two_of_even_of_squarefree hr2 hsq)]
    have h1 : ∑ r ∈ E, (Nat.totient r : ℝ)⁻¹
        = ∑ m ∈ E.image (fun r : ℕ => r / 2), (Nat.totient m : ℝ)⁻¹ := by
      rw [himg]
      exact Finset.sum_congr rfl hpoint
    calc ∑ r ∈ E, (Nat.totient r : ℝ)⁻¹
        = ∑ m ∈ E.image (fun r : ℕ => r / 2), (Nat.totient m : ℝ)⁻¹ := h1
      _ ≤ ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hEsub (fun i _ _ => by positivity)
  have hmain : Real.log (N : ℝ)
      ≤ ∑ r ∈ E, (Nat.totient r : ℝ)⁻¹ + ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ :=
    hbase.trans (le_of_eq (hμ.trans hsplit))
  have h2 : Real.log (N : ℝ) ≤ 2 * ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ := by
    have h1 : ∑ r ∈ E, (Nat.totient r : ℝ)⁻¹ + ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹
        ≤ ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ + ∑ r ∈ O, (Nat.totient r : ℝ)⁻¹ :=
      add_le_add hEvenLe le_rfl
    linarith
  have hOalt : O = (Finset.Icc 1 N).filter (fun m : ℕ => m % 2 = 1 ∧ Squarefree m) := by
    rw [hO, hs, Finset.filter_filter]
    apply Finset.filter_congr
    intro m _
    exact and_comm
  rw [hOalt] at h2
  linarith

/-! ## The target -/

/-- **Lower bound for the Selberg constant `G`.**  For `D ≥ 2` and `D ≤ Y`, the Selberg sum
`G = Σ_{l ≤ D, l ∣ oddPrimLt Y} 1 / ∏_{p|l}(p-2)` is at least `(1/4) log D`.

Since `D ≤ Y`, a divisor `l ≤ D` of `oddPrimLt Y` is exactly an odd squarefree `l ≤ D` (all its
prime factors are `< Y`), and termwise `1/∏_{p|l}(p-2) ≥ 1/∏_{p|l} p = 1/l`, so it suffices to
lower-bound `Σ_{l ≤ D, l odd, squarefree} 1/l ≥ (1/4) log D`.  For that, compare with the harmonic
sum: `Σ_{l ≤ D} μ² l / l ≥ Σ_{l ≤ D} 1/l − Σ_{p} Σ_{p² m ≤ D} 1/(p² m)
≥ log D − (log D + 1)·Σ_p p^{-2} ≥ (1/2) log D` for large `D`, and the odd part costs at most a
factor two (`Σ_{2m ≤ D} μ²(2m)/(2m) = (1/2) Σ_{m ≤ D/2, m odd} μ² m / m`); small `D` is a finite
check. -/
theorem selberg_G_lower (D Y : ℕ) (hD : 2 ≤ D) (hDY : D ≤ Y) :
    (1 / 4 : ℝ) * Real.log (D : ℝ) ≤
      ∑ l ∈ (Finset.Icc 1 D).filter
          (fun l : ℕ => l ∣ Commons.NumberTheory.Chen.ChenEight.oddPrimLt Y),
        1 / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) := by
  rcases eq_or_lt_of_le hD with hD2 | hD3
  · -- `D = 2`: the `l = 1` term alone suffices
    rw [← hD2]
    have hmem : (1 : ℕ) ∈ (Finset.Icc 1 2).filter (fun l : ℕ => l ∣ oddPrimLt Y) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, by norm_num⟩, one_dvd _⟩
    have hle1 : 1 / (∏ p ∈ (1 : ℕ).primeFactors, ((p : ℝ) - 2))
        ≤ ∑ l ∈ (Finset.Icc 1 2).filter (fun l : ℕ => l ∣ oddPrimLt Y),
            1 / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) :=
      Finset.single_le_sum (fun i _ => one_div_prod_sub_two_nonneg i) hmem
    have hone : 1 / (∏ p ∈ (1 : ℕ).primeFactors, ((p : ℝ) - 2)) = 1 := by
      rw [Nat.primeFactors_one, Finset.prod_empty, div_one]
    have hlog2 : (1 / 4 : ℝ) * Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  · -- `D ≥ 3`
    set S : Finset ℕ := (Finset.Icc 1 D).filter (fun l : ℕ => l ∣ oddPrimLt Y) with hS
    set Of : Finset ℕ := (Finset.Icc 1 (D - 1)).filter
      (fun m : ℕ => m % 2 = 1 ∧ Squarefree m) with hOf
    -- every odd squarefree `m ≤ D - 1` divides the odd primorial
    have hOsub : Of ⊆ S := by
      intro m hm
      rw [hOf, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmD⟩, hmod, hsq⟩ := hm
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hm1, by omega⟩, ?_⟩
      rw [oddPrimLt_eq_prod_oddLt, ← Nat.prod_primeFactors_of_squarefree hsq]
      refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
      have hple : p ≤ m := Nat.le_of_dvd (by omega) hpdvd
      exact mem_oddLt'.mpr ⟨hpp, three_le_of_mem_primeFactors_of_odd hmod hp, by omega⟩
    have hH := half_log_le_odd_sqfree_inv_totient (D - 1) (by omega)
    have hterm : ∑ m ∈ Of, (Nat.totient m : ℝ)⁻¹
        ≤ ∑ m ∈ Of, 1 / (∏ p ∈ m.primeFactors, ((p : ℝ) - 2)) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [hOf, Finset.mem_filter] at hm
      exact totient_inv_le_one_div_prod_sub_two hm.2.1 hm.2.2
    have hsub' : ∑ m ∈ Of, 1 / (∏ p ∈ m.primeFactors, ((p : ℝ) - 2))
        ≤ ∑ l ∈ S, 1 / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hOsub (fun i _ _ => one_div_prod_sub_two_nonneg i)
    have hlog : (1 / 4 : ℝ) * Real.log (D : ℝ)
        ≤ (1 / 2) * Real.log ((D - 1 : ℕ) : ℝ) := by
      set t : ℝ := ((D - 1 : ℕ) : ℝ) with ht
      have ht2 : (2 : ℝ) ≤ t := by
        rw [ht]
        have : 2 ≤ D - 1 := by omega
        exact_mod_cast this
      have hDc : (D : ℝ) = t + 1 := by
        rw [ht]
        have h1 : D - 1 + 1 = D := Nat.sub_add_cancel (by omega)
        rw [← h1]
        push_cast
        ring
      have hkey : (D : ℝ) ≤ t * t := by nlinarith [ht2, hDc]
      have hpos : (0 : ℝ) < t := by linarith
      have hlogineq : Real.log (D : ℝ) ≤ 2 * Real.log t := by
        have := Real.log_le_log (show (0 : ℝ) < (D : ℝ) by positivity) hkey
        rw [Real.log_mul (ne_of_gt hpos) (ne_of_gt hpos)] at this
        linarith
      linarith
    linarith

end Work.NumberTheory.Chen.BTermCount
