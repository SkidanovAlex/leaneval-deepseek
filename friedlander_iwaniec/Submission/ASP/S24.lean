/-
  **The `τ^{20/3}`-weighted sum of the congruence sums `A_d(t)` over an ARBITRARY modulus range.**

  Two elementary ingredients for the `(2.1)`-type aggregates of X² + Y⁴:

  * `∑_{d ∣ n} τ(d)^{20/3} ≤ τ(n)^8` (`sum_divisors_tau_pow_le`), and
  * the resulting crude aggregate
    `∑_{d ≤ D} τ(d)^{20/3} A_d(t) ≤ C ( ∑_{d ≤ D} τ(d)^{20/3} + t^{1/100} A(t) )`
    (`sum_tau_pow_Ad_le_crude`), where the first term is the contribution of the pair
    `(a,c) = (0,0)` (which is counted by *every* modulus) and the second is the contribution of the
    pairs with `a² + c⁴ ≥ 1`.

  ⚠ EXPONENT BOOKKEEPING (important for the next session): this crude form carries a power of `D`
  (namely `∑_{d ≤ D} τ(d)^{20/3} ≍ D(log D)^{2^{20/3}−1}`).  Plugged into the (R′)-Hölder step with
  the *global* normalisation `A(x)` it is therefore NOT enough when `D ≫ t^{3/4}` **and** the target
  has a *negative* power of `log x`.  The correct route for the **unweighted? no — for the
  τ^{20/3}-weighted (2.3)** is instead the paper's `τ^8`-reduction (see `S2b` step 1+3):
  `∑_{d ≤ t} τ(d)^{20/3} A_d(t) ≤ ∑_{n ≤ t} a_n τ(n)^8 ≤ ∑_{d³ ≤ t} (2τ(d))^{40} A_d(t)`,
  whose right-hand side lives in the *cube* range `d ≤ t^{1/3} ≤ t^{3/4}`, where the (3.3)-route plus
  the pointwise `τ(d)^{40} ≪ t^{40ε/3}` costs only `x^{40ε/3}` against
  `t^{1/12+9/16+1/100} ≤ x^{0.646}` — well inside `A(x) ≍ x^{3/4}`.
-/
import Mathlib
import Submission.ASP.S23
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.DivisorSum.sum_mul_tau_pow_eight_le_cube

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset

noncomputable section

/-- For `d ∣ n` and `n ≠ 0`, `τ(d) ≤ τ(n)`. -/
lemma card_divisors_le_of_dvd {d n : ℕ} (h : d ∣ n) (hn : n ≠ 0) :
    d.divisors.card ≤ n.divisors.card := by
  refine Finset.card_le_card fun x hx => ?_
  rw [Nat.mem_divisors] at hx ⊢
  exact ⟨hx.1.trans h, hn⟩

/-- The divisor sum bound behind the `(2.1)` aggregate: `∑_{d ∣ n} τ(d)^{20/3} ≤ τ(n)^8`. -/
lemma sum_divisors_tau_pow_le (n : ℕ) :
    (∑ d ∈ n.divisors, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
      ≤ ((n.divisors.card : ℝ)) ^ (8:ℕ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnd : n.divisors.Nonempty := ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
    have h1 : ∀ d ∈ n.divisors, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
        ≤ ((n.divisors.card : ℝ)) ^ ((20:ℝ)/3) := by
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hcard : (d.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_le_of_dvd hdvd hn
      exact Real.rpow_le_rpow (by positivity) hcard (by norm_num)
    calc (∑ d ∈ n.divisors, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        ≤ ∑ _d ∈ n.divisors, ((n.divisors.card : ℝ)) ^ ((20:ℝ)/3) := Finset.sum_le_sum h1
      _ = (n.divisors.card : ℝ) * ((n.divisors.card : ℝ)) ^ ((20:ℝ)/3) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n.divisors.card : ℝ)) ^ (8:ℕ) := by
            have hcard1 : (1:ℝ) ≤ (n.divisors.card : ℝ) := by
              exact_mod_cast Finset.card_pos.mpr hnd
            have hEq : (n.divisors.card : ℝ) * ((n.divisors.card : ℝ)) ^ ((20:ℝ)/3)
                = ((n.divisors.card : ℝ)) ^ ((23:ℝ)/3) := by
              have h1 : ((n.divisors.card : ℝ)) ^ ((1:ℝ)) * ((n.divisors.card : ℝ)) ^ ((20:ℝ)/3)
                  = ((n.divisors.card : ℝ)) ^ ((23:ℝ)/3) := by
                rw [← Real.rpow_add (by positivity)]
                norm_num
              simpa only [Real.rpow_one] using h1
            rw [hEq, ← Real.rpow_natCast (n.divisors.card : ℝ) 8]
            exact Real.rpow_le_rpow_of_exponent_le hcard1 (by norm_num)

/-- **The crude `τ^{20/3}`-weighted aggregate over an arbitrary modulus range.** -/
theorem sum_tau_pow_Ad_le_crude :
    ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ,
      (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
        ≤ C * ((∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
            + (t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/800 : ℝ) (by norm_num)
  refine ⟨(Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1, by positivity, fun D t => ?_⟩
  have hswap : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
      = ∑ n ∈ Finset.range (t + 1), (Submission.an n : ℝ)
          * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
              ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
        = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (t + 1),
            (if d ∣ n then ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
              * (Submission.an n : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      have hAd : (Submission.Ad d t : ℝ)
          = ∑ n ∈ Finset.range (t + 1), (if d ∣ n then (Submission.an n : ℝ) else 0) := by
        unfold Submission.Ad
        rw [Finset.sum_filter, Nat.cast_sum]
        exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
      rw [hAd, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
  rw [hswap]
  -- split off `n = 0` (whose `d`-sum is the full range, since `d ∣ 0` always)
  have hrange : Finset.range (t + 1) = insert 0 (Finset.Icc 1 t) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hinner0 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ 0),
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
      = ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) := by
    rw [Finset.filter_true_of_mem (fun d _ => dvd_zero d)]
  have hterm1 : (Submission.an 0 : ℝ) * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ 0),
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
      ≤ (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))) := by
    rw [hinner0]
  have hterm2 : (∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ)
        * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))))
      ≤ ∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ) * (C ^ (8:ℕ) * (t:ℝ)^((1:ℝ)/100)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnt : n ≤ t := (Finset.mem_Icc.mp hn).2
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ n.divisors := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
    refine le_trans (sum_divisors_tau_pow_le n) ?_
    have h1 : (n.divisors.card : ℝ) ≤ C * (n:ℝ)^((1:ℝ)/800) := hb n
    have h2 : ((n.divisors.card : ℝ)) ^ (8:ℕ) ≤ (C * (n:ℝ)^((1:ℝ)/800)) ^ (8:ℕ) :=
      pow_le_pow_left₀ (by positivity) h1 8
    have h3 : (C * (n:ℝ)^((1:ℝ)/800)) ^ (8:ℕ)
        ≤ (C * (t:ℝ)^((1:ℝ)/800)) ^ (8:ℕ) := by
      refine pow_le_pow_left₀ (by positivity) ?_ 8
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnt) (by norm_num)) hC.le
    refine le_trans (le_trans h2 h3) ?_
    rw [mul_pow, ← Real.rpow_natCast ((t:ℝ)^((1:ℝ)/800)) 8, ← Real.rpow_mul (Nat.cast_nonneg t)]
    norm_num
  calc (∑ n ∈ Finset.range (t + 1), (Submission.an n : ℝ)
        * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))))
      = (Submission.an 0 : ℝ) * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ 0),
            ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        + ∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ)
            * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
                ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))) := by
        rw [hrange, Finset.sum_insert (by simp : (0:ℕ) ∉ Finset.Icc 1 t)]
    _ ≤ (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        + C ^ (8:ℕ) * ((t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ)) := by
        refine add_le_add hterm1 ?_
        refine le_trans hterm2 ?_
        rw [← Finset.sum_mul]
        have hsub : Finset.Icc 1 t ⊆ Finset.range (t + 1) := by
          intro m hm
          simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
          omega
        have hsum : (∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ)) ≤ (Submission.Aseq t : ℝ) := by
          rw [Submission.Aseq]
          exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
        have hK : (0:ℝ) ≤ C ^ (8:ℕ) * (t:ℝ)^((1:ℝ)/100) := by positivity
        calc (∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ)) * (C ^ (8:ℕ) * (t:ℝ)^((1:ℝ)/100))
            ≤ (Submission.Aseq t : ℝ) * (C ^ (8:ℕ) * (t:ℝ)^((1:ℝ)/100)) :=
              mul_le_mul_of_nonneg_right hsum hK
          _ = C ^ (8:ℕ) * ((t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ)) := by ring
    _ ≤ ((Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1)
        * ((∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        + (t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ)) := by
        have h0 : (0:ℝ) ≤ (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))) :=
          Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h1 : (0:ℝ) ≤ (t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ) := by positivity
        have h2 : C ^ (8:ℕ) ≤ max (C ^ (8:ℕ)) 1 := le_max_left _ _
        have ha : (Submission.an 0 : ℝ) ≤ (Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1 := by
          linarith [le_max_left (C ^ (8:ℕ)) 1, le_max_right (C ^ (8:ℕ)) 1]
        have hb : C ^ (8:ℕ) ≤ (Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1 := by
          linarith [le_max_left (C ^ (8:ℕ)) 1]
        calc (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
              + C ^ (8:ℕ) * ((t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ))
            ≤ ((Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1)
                * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
              + ((Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1)
                * ((t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ)) :=
              add_le_add (mul_le_mul_of_nonneg_right ha h0) (mul_le_mul_of_nonneg_right hb h1)
          _ = ((Submission.an 0 : ℝ) + max (C ^ (8:ℕ)) 1 + 1)
                * ((∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
                  + (t:ℝ)^((1:ℝ)/100) * (Submission.Aseq t : ℝ)) := by ring
/-! ## The `τ^8`-reduction: the moduli are brought into the CUBE range -/

/-- **The `τ^8`-reduction of the `τ^{20/3}`-weighted congruence sums.**  For every modulus cut-off
`D`, the `τ^{20/3}`-weighted sum of `A_d(t)` is bounded by the pair `(a,c) = (0,0)` contribution plus
a `(2τ)^{40}`-weighted sum over the *cube* range `d³ ≤ t` (the range where the main paper's Lemma 3.1
applies without loss). -/
theorem sum_tau_pow_Ad_le_cube (D t : ℕ) :
    (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
      ≤ (Submission.an 0 : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        + ∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)
              * (∑ n ∈ (Finset.Icc 1 t).filter (fun n => d ∣ n), (Submission.an n : ℝ)) := by
  have hswap : (∑ d ∈ Finset.Icc 1 D,
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
      = ∑ n ∈ Finset.range (t + 1), (Submission.an n : ℝ)
          * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
              ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D,
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) * (Submission.Ad d t : ℝ))
        = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (t + 1),
            (if d ∣ n then ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))
              * (Submission.an n : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      have hAd : (Submission.Ad d t : ℝ)
          = ∑ n ∈ Finset.range (t + 1), (if d ∣ n then (Submission.an n : ℝ) else 0) := by
        unfold Submission.Ad
        rw [Finset.sum_filter, Nat.cast_sum]
        exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
      rw [hAd, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> ring
  rw [hswap]
  have hrange : Finset.range (t + 1) = insert 0 (Finset.Icc 1 t) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp : (0:ℕ) ∉ Finset.Icc 1 t)]
  have hinner0 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ 0),
        ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
      = ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)) := by
    rw [Finset.filter_true_of_mem (fun d _ => dvd_zero d)]
  rw [hinner0]
  refine add_le_add le_rfl ?_
  have hpt : ∀ n ∈ Finset.Icc 1 t,
      (Submission.an n : ℝ) * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n),
          ((d.divisors.card : ℝ) ^ ((20:ℝ)/3)))
        ≤ (Submission.an n : ℝ) * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ n.divisors := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
    refine le_trans (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sum_divisors_tau_pow_le n)) ?_
    exact le_of_eq (Real.rpow_natCast (n.divisors.card : ℝ) 8).symm
  calc (∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ)
        * (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ∣ n), ((d.divisors.card : ℝ) ^ ((20:ℝ)/3))))
      ≤ ∑ n ∈ Finset.Icc 1 t, (Submission.an n : ℝ) * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)) :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ d ∈ (Finset.Icc 1 t).filter (fun d => d ^ 3 ≤ t),
          (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)
            * (∑ n ∈ (Finset.Icc 1 t).filter (fun n => d ∣ n), (Submission.an n : ℝ)) :=
        Commons.NumberTheory.DivisorSum.sum_mul_tau_pow_eight_le_cube
          (fun n => (Submission.an n : ℝ)) (fun n => by positivity) t

end

end Submission.ASP
