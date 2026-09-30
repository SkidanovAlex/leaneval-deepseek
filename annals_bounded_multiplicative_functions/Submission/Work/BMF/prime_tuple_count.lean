import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tuple_setup
import Submission.Work.BMF.n4_defs
import Submission.Work.BMF.n4_case_large_q_alt
import Submission.Work.BMF.n4_case_small_q

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# N4 `prime_tuple_count`: the analytic case `q ≤ (log P)^{O(1)}`

MRT Lemma 2.6 / MRTTZ (3.12).  The counting problem is turned into an integral over the
Fourier variable (`n4_count_le_integral`), bounded with the character expansion and the
Vinogradov–Korobov prime-sum bound.  The complementary elementary case
`q ≥ C (log P)^{ℓ+3}` is `Submission.Work.BMF.n4_case_large_q`.
-/

namespace Work.BMF

open Polynomial Finset Real
open scoped BigOperators ComplexConjugate

/-! ## Bounds for the character sum -/

/-- `(M+E)^{2ℓ} ≤ 2^{2ℓ-1}(M^{2ℓ} + E^{2ℓ})` for nonnegative `M, E`. -/
lemma add_pow_two_mul_le {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E) (ℓ : ℕ) :
    (M + E) ^ (2 * ℓ) ≤ 2 ^ (2 * ℓ - 1) * (M ^ (2 * ℓ) + E ^ (2 * ℓ)) :=
  add_pow_le hM hE (2 * ℓ)

/-- The norm of the pair correlation is bounded by the average of `‖psum‖^{2ℓ}`. -/
lemma norm_n4corr_le {ℓ m : ℕ} {P : ℝ} {q : ℕ} (hP : 0 ≤ P) (hq : 1 ≤ q) (t : ℝ) :
    ‖n4corr ℓ m P q t‖ ≤ ((q.totient : ℝ))⁻¹ *
      ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hφpos : (0:ℝ) < (q.totient : ℝ) := by
    have h1 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h1
  rw [n4corr_eq hP hq t, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∑ ψ : DirichletCharacter ℂ q,
        (psum P q (ψ ^ m) t) ^ ℓ * conj ((psum P q (ψ ^ m) t) ^ ℓ)‖
      ≤ ∑ ψ : DirichletCharacter ℂ q,
          ‖(psum P q (ψ ^ m) t) ^ ℓ * conj ((psum P q (ψ ^ m) t) ^ ℓ)‖ := norm_sum_le _ _
    _ = ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) := by
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        simp only [norm_mul, norm_pow, Complex.norm_conj]
        rw [← pow_add]
        congr 1
        ring

/-- The sum over the characters, split into the characters whose `m`-th power is trivial
and the rest. -/
lemma psi_sum_le {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) {P : ℝ} {q : ℕ} [NeZero q]
    {Cp Ce : ℝ} (hCp : 0 ≤ Cp) (hCe : 0 ≤ Ce) (t : ℝ)
    (hbound : ∀ χ : DirichletCharacter ℂ q,
      ‖psum P q χ t‖ ≤ Cp / (1 + |t|) * (if χ = 1 then (1:ℝ) else 0) + Ce) :
    ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) ≤
      ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ q ↦ ψ ^ m = 1)).card : ℝ)
          * (2 ^ (2 * ℓ - 1) * ((Cp / (1 + |t|)) ^ (2 * ℓ) + Ce ^ (2 * ℓ)))
        + (Fintype.card (DirichletCharacter ℂ q) : ℝ) * (2 ^ (2 * ℓ - 1) * Ce ^ (2 * ℓ)) := by
  classical
  have h2l : 2 * ℓ ≠ 0 := by omega
  have hkey : ∀ χ : DirichletCharacter ℂ q, ‖psum P q χ t‖ ^ (2 * ℓ) ≤
      2 ^ (2 * ℓ - 1) * ((Cp / (1 + |t|)) ^ (2 * ℓ) * (if χ = 1 then (1:ℝ) else 0)
        + Ce ^ (2 * ℓ)) := by
    intro χ
    have h1 := hbound χ
    have h3 := add_pow_two_mul_le
      (M := Cp / (1 + |t|) * (if χ = 1 then (1:ℝ) else 0)) (E := Ce) (by positivity) hCe ℓ
    calc ‖psum P q χ t‖ ^ (2 * ℓ)
        ≤ (Cp / (1 + |t|) * (if χ = 1 then (1:ℝ) else 0) + Ce) ^ (2 * ℓ) :=
          pow_le_pow_left₀ (norm_nonneg _) h1 _
      _ ≤ 2 ^ (2 * ℓ - 1) * ((Cp / (1 + |t|) * (if χ = 1 then (1:ℝ) else 0)) ^ (2 * ℓ)
            + Ce ^ (2 * ℓ)) := h3
      _ = 2 ^ (2 * ℓ - 1) * ((Cp / (1 + |t|)) ^ (2 * ℓ) * (if χ = 1 then (1:ℝ) else 0)
            + Ce ^ (2 * ℓ)) := by
          rcases eq_or_ne χ 1 with h | h
          · subst h; simp
          · rw [if_neg h, mul_zero, zero_pow h2l, mul_zero, zero_add]
  have hsplit : ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)
      = ∑ ψ : DirichletCharacter ℂ q,
          (if ψ ^ m = 1 then ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) else 0)
        + ∑ ψ : DirichletCharacter ℂ q,
          (if ψ ^ m = 1 then 0 else ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    by_cases h : ψ ^ m = 1 <;> simp [h]
  have h1 : ∑ ψ : DirichletCharacter ℂ q,
        (if ψ ^ m = 1 then ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) else 0)
      ≤ ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ q ↦ ψ ^ m = 1)).card : ℝ)
          * (2 ^ (2 * ℓ - 1) * ((Cp / (1 + |t|)) ^ (2 * ℓ) + Ce ^ (2 * ℓ))) := by
    rw [← Finset.sum_filter]
    calc ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ q ↦ ψ ^ m = 1),
            ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)
        ≤ ∑ _ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ q ↦ ψ ^ m = 1),
            (2 ^ (2 * ℓ - 1) * ((Cp / (1 + |t|)) ^ (2 * ℓ) + Ce ^ (2 * ℓ))) := by
          refine Finset.sum_le_sum (fun ψ hψ => ?_)
          rw [Finset.mem_filter] at hψ
          have h := hkey (ψ ^ m)
          rw [if_pos hψ.2, mul_one] at h
          exact h
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ ψ : DirichletCharacter ℂ q,
        (if ψ ^ m = 1 then 0 else ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ))
      ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) * (2 ^ (2 * ℓ - 1) * Ce ^ (2 * ℓ)) := by
    calc ∑ ψ : DirichletCharacter ℂ q,
            (if ψ ^ m = 1 then 0 else ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ))
        ≤ ∑ _ψ : DirichletCharacter ℂ q, (2 ^ (2 * ℓ - 1) * Ce ^ (2 * ℓ)) := by
          refine Finset.sum_le_sum (fun ψ _ => ?_)
          by_cases h : ψ ^ m = 1
          · rw [if_pos h]; positivity
          · rw [if_neg h]
            have h' := hkey (ψ ^ m)
            rw [if_neg h, mul_zero, zero_add] at h'
            exact h'
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hsplit]
  linarith


/-! ## The final assembly -/

/-- **N4. Counting nearby products of primes, with a power congruence**
(MRT §2 (2.6), MRTTZ (3.12)). With `d = π₀(P)²`: the number of pairs of `ℓ`-tuples of primes
in `[P, 2P]` not dividing `q`, whose products differ by at most `C₀ P^ℓ / N` and whose `m`-th
powers are congruent mod `q`, is `≪_{ℓ,m} C₀ (d^ℓ/N) ((2m)^{ω(q)}/φ(q) + 1/log N)`. -/
theorem prime_tuple_count (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P N C₀ : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ → 1 ≤ q →
      ((((Fintype.piFinset fun _ : Fin ℓ ↦ (primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q)) ×ˢ
          (Fintype.piFinset fun _ : Fin ℓ ↦ (primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q))).filter
        (fun v ↦ |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
          (∏ i, v.2 i) ^ m ≡ (∏ i, v.1 i) ^ m [MOD q])).card : ℝ)
        ≤ C * C₀ * pi0 P ^ (2 * ℓ) / N *
          (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ) + 1 / Real.log N) := by
  classical
  obtain ⟨C₁, P₁, hC₁, hcaseA⟩ := n4_case_large_q_alt ℓ m hℓ hm
  obtain ⟨C₂, P₂, hC₂, hcaseB⟩ := n4_case_small_q ℓ m hℓ hm
  refine ⟨2 * max C₁ C₂ + 1, max (max P₁ P₂) (Real.exp (max C₁ 1) + 2), by positivity, ?_⟩
  intro P N C₀ q hP hN hNle hC₀ hq
  have hP₁ : P₁ ≤ P := le_trans (le_trans (le_max_left P₁ P₂) (le_max_left _ _)) hP
  have hP₂ : P₂ ≤ P := le_trans (le_trans (le_max_right P₁ P₂) (le_max_left _ _)) hP
  have hexp : Real.exp (max C₁ 1) + 2 ≤ P := le_trans (le_max_right _ _) hP
  have hPbig : (1:ℝ) < P := by
    have hpos : (0:ℝ) < Real.exp (max C₁ 1) := Real.exp_pos _
    linarith
  have hlogPpos : (0:ℝ) < Real.log P := Real.log_pos hPbig
  have hlogP : max C₁ 1 ≤ Real.log P := by
    have h1 : Real.exp (max C₁ 1) ≤ P := by linarith
    calc max C₁ 1 = Real.log (Real.exp (max C₁ 1)) := (Real.log_exp _).symm
      _ ≤ Real.log P := Real.log_le_log (Real.exp_pos _) h1
  have hcard : ((n4set ℓ m P N C₀ q).card : ℝ)
      = ((((Fintype.piFinset fun _ : Fin ℓ ↦ (primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q)) ×ˢ
          (Fintype.piFinset fun _ : Fin ℓ ↦ (primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q))).filter
        (fun v ↦ |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
          (∏ i, v.2 i) ^ m ≡ (∏ i, v.1 i) ^ m [MOD q])).card : ℝ) := rfl
  rw [← hcard]
  have hCpos : (0:ℝ) < C₀ := by
    have h : 0 < 1 / Real.log P := one_div_pos.mpr hlogPpos
    linarith
  have hNpos : (0:ℝ) < N := by linarith
  have hlogNpos : (0:ℝ) < Real.log N :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1:ℝ) < 3))
      (Real.log_le_log (by norm_num) hN)
  have hφpos : (0:ℝ) < (q.totient : ℝ) := by
    have := Nat.totient_pos.mpr (by omega : 0 < q)
    exact_mod_cast this
  have hpi0 : (0:ℝ) ≤ pi0 P := by
    rw [pi0]
    exact div_nonneg (by linarith) hlogPpos.le
  have hbracket : (0:ℝ) ≤ (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)
      + 1 / Real.log N) := by
    have h1 : (0:ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ) :=
      div_nonneg (by positivity) hφpos.le
    have h2 : (0:ℝ) ≤ 1 / Real.log N := div_nonneg (by norm_num) hlogNpos.le
    linarith
  by_cases hqle : q ≤ (Real.log P) ^ (ℓ + 4)
  · refine le_trans (hcaseB P N C₀ q hP₂ hN hNle hC₀ hq hqle) ?_
    have h1 : C₂ ≤ 2 * max C₁ C₂ + 1 := by
      have := le_max_right C₁ C₂; linarith
    refine mul_le_mul_of_nonneg_right ?_ hbracket
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCpos.le)
      (pow_nonneg hpi0 _)
  · have hqle' : (Real.log P) ^ (ℓ + 4) < (q : ℝ) := not_le.mp hqle
    have hlog0 : (0:ℝ) ≤ Real.log P := le_trans (le_trans (by norm_num : (0:ℝ) ≤ 1)
      (le_max_right C₁ 1)) hlogP
    have hthr : C₁ * Real.log P ^ (ℓ + 3) ≤ (q : ℝ) := by
      have h0 : (0:ℝ) ≤ Real.log P ^ (ℓ + 3) := pow_nonneg hlog0 _
      have h1 : C₁ * Real.log P ^ (ℓ + 3) ≤ Real.log P * Real.log P ^ (ℓ + 3) :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_left C₁ 1) hlogP) h0
      have h2 : Real.log P * Real.log P ^ (ℓ + 3) = Real.log P ^ (ℓ + 4) := by
        rw [show ℓ + 4 = ℓ + 3 + 1 from by omega, pow_succ]; ring
      linarith [le_of_lt hqle']
    refine le_trans (hcaseA P N C₀ q hP₁ hN hNle hC₀ hq hthr) ?_
    have h1 : C₁ ≤ 2 * max C₁ C₂ + 1 := by
      have := le_max_left C₁ C₂; linarith
    have h3 : 1 / Real.log N ≤ (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ))
        + 1 / Real.log N := by
      have h4 : (0:ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ) :=
        div_nonneg (by positivity) hφpos.le
      linarith
    have h5 : C₁ * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N)
        ≤ (2 * max C₁ C₂ + 1) * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine div_le_div_of_nonneg_right ?_ hNpos.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCpos.le)
        (pow_nonneg hpi0 _)
    refine le_trans h5 ?_
    refine mul_le_mul_of_nonneg_left h3 ?_
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hCpos.le)
      (pow_nonneg hpi0 _)) hNpos.le

end Work.BMF
