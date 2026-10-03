import Mathlib
import Submission.Work.FIArea4.polya_vinogradov
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.jacobi_denom_pv
import Submission.Work.FIArea4.card_pairs_mul_sq_le

namespace Work.FIArea4.L14

open scoped BigOperators
open Finset
open Work.FIPlan

attribute [local instance] Classical.propDecidable

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-! ### 0. Elementary arithmetic helpers -/

/-- For odd `q` the `2`-adic part of `oddPart` is trivial. -/
lemma oddPart_eq_self_of_odd {q : ℕ} (hq : Odd q) : oddPart q = q := by
  have h2 : ¬ 2 ∣ q := by
    intro h
    obtain ⟨k, hk⟩ := h
    obtain ⟨m, hm⟩ := hq
    omega
  rw [Work.FIPlan.oddPart, Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one]

/-- The decidable predicate `Nat.sqrt n ^ 2 ≠ n` is "`n` is not a perfect square". -/
lemma not_isSquare_of_sqrt_ne {n : ℕ} (h : Nat.sqrt n ^ 2 ≠ n) :
    ∀ k : ℕ, n ≠ k ^ 2 := by
  intro k hk
  exact h (by rw [hk, Nat.sqrt_eq'])

/-- `J(4n | m) = J(n | m)` for odd `m`, and `0` for even `m`. -/
lemma jacobiSym_four_mul_eq (n m : ℕ) (hm : 1 ≤ m) :
    (jacobiSym (4 * n : ℤ) m : ℝ) = if Odd m then (jacobiSym (n : ℤ) m : ℝ) else 0 := by
  by_cases ho : Odd m
  · rw [if_pos ho]
    have hcast : (4 * n : ℤ) = (4 : ℤ) * (n : ℤ) := by ring
    rw [hcast, jacobiSym.mul_left, jacobiSym.at_four ho, one_mul]
  · rw [if_neg ho]
    have hz : jacobiSym (4 * n : ℤ) m = 0 := by
      rw [jacobiSym.eq_zero_iff]
      refine ⟨by omega, ?_⟩
      have hcast : (4 * n : ℤ) = ((4 * n : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, Int.gcd_natCast_natCast]
      intro hg
      have h2m : 2 ∣ m := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
      have h2 : 2 ∣ Nat.gcd (4 * n) m := Nat.dvd_gcd ⟨2 * n, by ring⟩ h2m
      rw [hg] at h2; omega
    rw [hz]; norm_num

/-! ### 1. Denominator-variable Pólya–Vinogradov over the odd integers -/

/-- The sum over *odd* `q ≤ Q` of the Jacobi symbol `(n | q)`, for `n ≥ 1` not a perfect square,
is `O(√n · log n · log Q)`.  This is `Work.FIArea4.jacobi_denom_pv` (the Pólya–Vinogradov
estimate for the character `a ↦ J(4n | a)` of level `16n`) together with the identity
`Σ_{q odd ≤ Q} J(n|q) = Σ_{m ≤ Q} J(4n|m)`. -/
lemma denom_pv_odd' :
    ∃ C : ℝ, 0 < C ∧ ∀ (n Q : ℕ), 1 ≤ n → (∀ k : ℕ, n ≠ k ^ 2) →
      |∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q), (jacobiSym (n : ℤ) q : ℝ)|
        ≤ C * (Real.log Q + 1) * Real.sqrt n * (Real.log n + 2) := by
  obtain ⟨C, hCpos, hC⟩ := jacobi_denom_pv
  refine ⟨C, hCpos, ?_⟩
  intro n Q hn hnsq
  have hsum : (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q), (jacobiSym (n : ℤ) q : ℝ))
      = ∑ m ∈ Finset.Icc 1 Q, (jacobiSym (4 * n : ℤ) m : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact (jacobiSym_four_mul_eq n m hm1).symm
  rw [hsum]
  refine le_trans (hC n Q hn hnsq) ?_
  have hQ : 1 ≤ Real.log (Q : ℝ) + 1 := by
    have := Real.log_natCast_nonneg Q; linarith
  have hna : 0 ≤ C * Real.sqrt n * (Real.log n + 2) := by
    have h1 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    positivity
  have h := mul_le_mul_of_nonneg_right hQ hna
  calc C * Real.sqrt n * (Real.log n + 2)
      = 1 * (C * Real.sqrt n * (Real.log n + 2)) := by ring
    _ ≤ (Real.log Q + 1) * (C * Real.sqrt n * (Real.log n + 2)) := h
    _ = C * (Real.log Q + 1) * Real.sqrt n * (Real.log n + 2) := by ring

/-! ### 2. The second moment and its two bounds -/

/-- `F(Q) = Σ_{q ≤ Q, q odd, q not a square} |Σ_{r ≤ R} (r | q)|²`. -/
def Fmom (Q R : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
    (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2

/-- The inner sum `Σ_{q ≤ Q, q odd} (n | q)`. -/
def Uodd (Q n : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q), (jacobiSym (n : ℤ) q : ℝ)

/-- The Pólya–Vinogradov per-term bound: `F(Q) ≪ Q² log²Q`. -/
theorem F_bound_i :
    ∃ C : ℝ, 0 < C ∧ ∀ Q R : ℕ, 1 ≤ R →
      Fmom Q R ≤ C * (Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := polya_vinogradov
  refine ⟨C1 ^ 2, by positivity, ?_⟩
  intro Q R hR
  by_cases hQ : Q = 0
  · subst hQ
    have h0 : Fmom 0 R = 0 := by simp [Fmom]
    rw [h0]; positivity
  · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ
    have hqsum : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
          (q : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have hsub : (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q)
          ⊆ Finset.Icc 1 Q := Finset.filter_subset _ _
      have h1 : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), (q : ℝ)
          ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
      have h2 : ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ≤ (Q : ℝ) ^ 2 := by
        have h := Finset.sum_le_card_nsmul (Finset.Icc 1 Q) (fun q => (q : ℝ)) (Q : ℝ)
          (fun q hq => by exact_mod_cast (Finset.mem_Icc.mp hq).2)
        rw [Nat.card_Icc] at h
        simpa [nsmul_eq_mul, pow_two] using h
      linarith
    calc Fmom Q R
        ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
            C1 ^ 2 * (q : ℝ) * (Real.log Q + 1) ^ 2 := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨hqI, hqodd, hqnsq⟩ := hq
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqI).1
          have hqQ : q ≤ Q := (Finset.mem_Icc.mp hqI).2
          have hnsq' : ∀ k : ℕ, oddPart q ≠ k ^ 2 := by
            have hodd : oddPart q = q := oddPart_eq_self_of_odd hqodd
            intro k hk
            rw [hodd] at hk
            exact hqnsq (by rw [hk, Nat.sqrt_eq'])
          have hb := hC1 q R hq1 hnsq'
          set S := ∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ) with hS
          have hlogq : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hqQ)
          have hsq : S ^ 2 ≤ (C1 * Real.sqrt q * (Real.log q + 1)) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hb 2
          have hstep : (C1 * Real.sqrt q * (Real.log q + 1)) ^ 2
              ≤ C1 ^ 2 * (q : ℝ) * (Real.log Q + 1) ^ 2 := by
            have h1 : C1 * Real.sqrt q * (Real.log q + 1)
                ≤ C1 * Real.sqrt q * (Real.log Q + 1) := by
              have : (Real.log q + 1) ≤ (Real.log Q + 1) := by linarith
              exact mul_le_mul_of_nonneg_left this (by positivity)
            have h2 : 0 ≤ C1 * Real.sqrt q * (Real.log q + 1) := by
              have : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
              positivity
            have hpow := pow_le_pow_left₀ h2 h1 2
            calc (C1 * Real.sqrt q * (Real.log q + 1)) ^ 2
                ≤ (C1 * Real.sqrt q * (Real.log Q + 1)) ^ 2 := hpow
              _ = C1 ^ 2 * (q : ℝ) * (Real.log Q + 1) ^ 2 := by
                  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          linarith [hsq, hstep]
      _ = C1 ^ 2 * (Real.log Q + 1) ^ 2
            * ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), (q : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
      _ ≤ C1 ^ 2 * (Real.log Q + 1) ^ 2 * (Q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hqsum (by positivity)
      _ = C1 ^ 2 * (Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2 := by ring

/-- The "square-out" bound: `F(Q) ≪ (QR + R³) log²(QR)`. -/
theorem F_bound_ii :
    ∃ C : ℝ, 0 < C ∧ ∀ Q R : ℕ, 1 ≤ R →
      Fmom Q R ≤ C * ((Q : ℝ) * R + (R : ℝ) ^ 3) * (Real.log (Q * R + 2) + 1) ^ 2 := by
  obtain ⟨C2, hC2pos, hC2⟩ := denom_pv_odd'
  obtain ⟨Cd, hCdpos, hCd⟩ := card_pairs_mul_sq_le
  refine ⟨2 + Cd + 2 * C2, by positivity, ?_⟩
  intro Q R hR
  by_cases hQ0 : Q = 0
  · subst hQ0
    have h0 : Fmom 0 R = 0 := by simp [Fmom]
    rw [h0]
    have : (0 : ℝ) ≤ (Real.log (0 * R + 2) + 1) ^ 2 := sq_nonneg _
    positivity
  · have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero hQ0
    have hQ1r : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    have hR1r : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    set P : Finset (ℕ × ℕ) := (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R) with hP
    set Psq : Finset (ℕ × ℕ) :=
      P.filter (fun p : ℕ × ℕ => Nat.sqrt (p.1 * p.2) ^ 2 = p.1 * p.2) with hPsq
    set Pnsq : Finset (ℕ × ℕ) :=
      P.filter (fun p : ℕ × ℕ => ¬ (Nat.sqrt (p.1 * p.2) ^ 2 = p.1 * p.2)) with hPnsq
    set M : ℝ := (Q : ℝ) * R + (R : ℝ) ^ 3 with hM
    set L : ℝ := Real.log (Q * R + 2) + 1 with hL
    have hstep1 : Fmom Q R
        ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
            (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rw [Finset.mem_filter] at hq ⊢
        exact ⟨hq.1, hq.2.1⟩
      · intro q _ _
        exact sq_nonneg _
    have hstep2 : (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
          (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2)
        = ∑ p ∈ P, Uodd Q (p.1 * p.2) := by
      have e1 : ∀ q : ℕ, (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2
          = ∑ r₁ ∈ Finset.Icc 1 R, ∑ r₂ ∈ Finset.Icc 1 R,
              (jacobiSym (r₁ : ℤ) q : ℝ) * (jacobiSym (r₂ : ℤ) q : ℝ) := by
        intro q
        rw [sq, Finset.sum_mul_sum]
      have e2 : ∀ (r₁ r₂ : ℕ), (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
              (jacobiSym (r₁ : ℤ) q : ℝ) * (jacobiSym (r₂ : ℤ) q : ℝ)) = Uodd Q (r₁ * r₂) := by
        intro r₁ r₂
        rw [Uodd]
        apply Finset.sum_congr rfl
        intro q hq
        rw [jacobiSym_mul_nat]
        push_cast
        ring
      calc (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
              (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2)
          = ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q), ∑ r₁ ∈ Finset.Icc 1 R,
              ∑ r₂ ∈ Finset.Icc 1 R,
              (jacobiSym (r₁ : ℤ) q : ℝ) * (jacobiSym (r₂ : ℤ) q : ℝ) := by
            apply Finset.sum_congr rfl; intro q _; exact e1 q
        _ = ∑ r₁ ∈ Finset.Icc 1 R, ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
              ∑ r₂ ∈ Finset.Icc 1 R,
              (jacobiSym (r₁ : ℤ) q : ℝ) * (jacobiSym (r₂ : ℤ) q : ℝ) :=
            Finset.sum_comm
        _ = ∑ r₁ ∈ Finset.Icc 1 R, ∑ r₂ ∈ Finset.Icc 1 R,
              ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
              (jacobiSym (r₁ : ℤ) q : ℝ) * (jacobiSym (r₂ : ℤ) q : ℝ) := by
            apply Finset.sum_congr rfl; intro r₁ _
            exact Finset.sum_comm
        _ = ∑ r₁ ∈ Finset.Icc 1 R, ∑ r₂ ∈ Finset.Icc 1 R, Uodd Q (r₁ * r₂) := by
            apply Finset.sum_congr rfl; intro r₁ _
            apply Finset.sum_congr rfl; intro r₂ _
            exact e2 r₁ r₂
        _ = ∑ p ∈ P, Uodd Q (p.1 * p.2) := by
            rw [hP]
            exact (Finset.sum_product (Finset.Icc 1 R) (Finset.Icc 1 R)
              (fun p : ℕ × ℕ => Uodd Q (p.1 * p.2))).symm
    have hF : Fmom Q R ≤ ∑ p ∈ P, Uodd Q (p.1 * p.2) := hstep1.trans hstep2.le
    have hsplit : (∑ p ∈ Psq, Uodd Q (p.1 * p.2)) + (∑ p ∈ Pnsq, Uodd Q (p.1 * p.2))
        = ∑ p ∈ P, Uodd Q (p.1 * p.2) := by
      rw [hPsq, hPnsq, Finset.sum_filter_add_sum_filter_not]
    have habsU : ∀ n : ℕ, |Uodd Q n| ≤ (Q : ℝ) := by
      intro n
      rw [Uodd]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h2 : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q),
            |(jacobiSym (n : ℤ) q : ℝ)|
          ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> rw [h] <;> norm_num
      refine le_trans h2 ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard : ((Finset.Icc 1 Q).filter (fun q => Odd q)).card ≤ Q := by
        have hc : ((Finset.Icc 1 Q).filter (fun q => Odd q)).card ≤ (Finset.Icc 1 Q).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        rw [Nat.card_Icc] at hc; omega
      exact_mod_cast hcard
    have hcardP : (Psq.card : ℝ) ≤ Cd * (R : ℝ) * (Real.log R + 1) := by
      have h := hCd R R hR hR
      have hsqrt : Real.sqrt ((R : ℝ) * (R : ℝ)) = (R : ℝ) := Real.sqrt_mul_self (by positivity)
      have hmin : min (R : ℝ) (R : ℝ) = (R : ℝ) := min_self _
      rw [hsqrt, hmin] at h
      have h' : ((((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter
            (fun p : ℕ × ℕ => Nat.sqrt (p.1 * p.2) ^ 2 = p.1 * p.2)).card : ℝ)
          ≤ Cd * (R : ℝ) * (Real.log R + 1) := by exact_mod_cast h
      simpa only [hPsq, hP] using h'
    have hA : ∑ p ∈ Psq, Uodd Q (p.1 * p.2) ≤ Cd * M * L ^ 2 := by
      have h1 : ∑ p ∈ Psq, Uodd Q (p.1 * p.2) ≤ Cd * (R : ℝ) * (Real.log R + 1) * (Q : ℝ) := by
        calc ∑ p ∈ Psq, Uodd Q (p.1 * p.2)
            ≤ ∑ p ∈ Psq, (Q : ℝ) := by
              apply Finset.sum_le_sum
              intro p _
              exact le_trans (le_abs_self _) (habsU _)
          _ = (Psq.card : ℝ) * (Q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Cd * (R : ℝ) * (Real.log R + 1)) * (Q : ℝ) :=
              mul_le_mul_of_nonneg_right hcardP (by positivity)
          _ = Cd * (R : ℝ) * (Real.log R + 1) * (Q : ℝ) := by ring
      refine h1.trans ?_
      have hQR2 : Real.log (R : ℝ) + 1 ≤ L ^ 2 := by
        have hRle : Real.log (R : ℝ) ≤ Real.log (Q * R + 2) := by
          apply Real.log_le_log (by positivity)
          nlinarith [hQ1r, hR1r]
        have hLge1 : (1 : ℝ) ≤ L := by
          rw [hL]
          have : (0 : ℝ) ≤ Real.log (Q * R + 2) := by
            apply Real.log_nonneg
            nlinarith [hQ1r, hR1r]
          linarith
        have h1' : Real.log (R : ℝ) + 1 ≤ L := by rw [hL]; linarith
        calc Real.log (R : ℝ) + 1 ≤ L := h1'
          _ ≤ L ^ 2 := by nlinarith [hLge1]
      have hQRleM : (Q : ℝ) * R ≤ M := by
        rw [hM]; nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ R) 3]
      have hlogRnn : 0 ≤ Real.log (R : ℝ) + 1 := by
        have := Real.log_natCast_nonneg R; linarith
      have hMnn : 0 ≤ M := by rw [hM]; positivity
      calc Cd * (R : ℝ) * (Real.log R + 1) * (Q : ℝ)
          = Cd * ((Q : ℝ) * R * (Real.log R + 1)) := by ring
        _ ≤ Cd * (M * L ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hCdpos)
            calc (Q : ℝ) * R * (Real.log R + 1)
                ≤ M * (Real.log R + 1) := mul_le_mul_of_nonneg_right hQRleM hlogRnn
              _ ≤ M * L ^ 2 := mul_le_mul_of_nonneg_left hQR2 hMnn
        _ = Cd * M * L ^ 2 := by ring
    have hB : ∑ p ∈ Pnsq, Uodd Q (p.1 * p.2) ≤ 2 * C2 * M * L ^ 2 := by
      have hTb : ∀ p ∈ Pnsq, Uodd Q (p.1 * p.2)
          ≤ C2 * (Real.log Q + 1) * Real.sqrt (p.1 * p.2) * (Real.log (p.1 * p.2) + 2) := by
        intro p hp
        rw [hPnsq, Finset.mem_filter] at hp
        obtain ⟨hpP, hpnsq⟩ := hp
        rw [hP, Finset.mem_product] at hpP
        obtain ⟨hp1, hp2⟩ := hpP
        have hp1' : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
        have hp2' : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
        have hn1 : 1 ≤ p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
        have hnnsq : ∀ k : ℕ, p.1 * p.2 ≠ k ^ 2 := not_isSquare_of_sqrt_ne hpnsq
        have hb := hC2 (p.1 * p.2) Q hn1 hnnsq
        have hb' : |Uodd Q (p.1 * p.2)|
            ≤ C2 * (Real.log Q + 1) * Real.sqrt (p.1 * p.2) * (Real.log (p.1 * p.2) + 2) := by
          simpa only [Uodd, Nat.cast_mul] using hb
        exact le_trans (le_abs_self _) hb'
      have hprod : ∀ p ∈ Pnsq, Uodd Q (p.1 * p.2)
          ≤ C2 * (Real.log Q + 1) * (R : ℝ) * (2 * Real.log R + 2) := by
        intro p hp
        refine le_trans (hTb p hp) ?_
        rw [hPnsq, Finset.mem_filter] at hp
        obtain ⟨hpP, _⟩ := hp
        rw [hP, Finset.mem_product] at hpP
        obtain ⟨hp1, hp2⟩ := hpP
        have hp1' : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
        have hp2' : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
        have hp1R : p.1 ≤ R := (Finset.mem_Icc.mp hp1).2
        have hp2R : p.2 ≤ R := (Finset.mem_Icc.mp hp2).2
        have hprodR : p.1 * p.2 ≤ R * R := Nat.mul_le_mul hp1R hp2R
        have hp1pos : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast (show 0 < p.1 by omega)
        have hp2pos : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast (show 0 < p.2 by omega)
        have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
        have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
        have hsqrt : Real.sqrt (p.1 * p.2) ≤ (R : ℝ) := by
          rw [show (R : ℝ) = Real.sqrt ((R : ℝ) * (R : ℝ)) from
                (Real.sqrt_mul_self (by positivity)).symm]
          apply Real.sqrt_le_sqrt
          exact_mod_cast hprodR
        have hRlog : Real.log (p.1 * p.2) ≤ 2 * Real.log R := by
          have h1 : Real.log (p.1 * p.2) ≤ Real.log (R * R) := by
            apply Real.log_le_log (by positivity)
            exact_mod_cast hprodR
          have h2 : Real.log (R * R) = 2 * Real.log R := by
            rw [Real.log_mul (by positivity) (by positivity)]
            ring
          linarith [h1, h2]
        have hlog : Real.log (p.1 * p.2) + 2 ≤ 2 * Real.log R + 2 := by linarith
        have hnn1 : 0 ≤ Real.log (p.1 * p.2) + 2 := by
          have h : 0 ≤ Real.log (p.1 * p.2) := by
            apply Real.log_nonneg
            have h1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp1'
            have h2 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp2'
            nlinarith
          linarith
        calc C2 * (Real.log Q + 1) * Real.sqrt (p.1 * p.2) * (Real.log (p.1 * p.2) + 2)
            ≤ C2 * (Real.log Q + 1) * (R : ℝ) * (Real.log (p.1 * p.2) + 2) := by
              apply mul_le_mul_of_nonneg_right _ hnn1
              exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
          _ ≤ C2 * (Real.log Q + 1) * (R : ℝ) * (2 * Real.log R + 2) := by
              apply mul_le_mul_of_nonneg_left hlog
              positivity
      calc ∑ p ∈ Pnsq, Uodd Q (p.1 * p.2)
          ≤ ∑ p ∈ Pnsq, C2 * (Real.log Q + 1) * (R : ℝ) * (2 * Real.log R + 2) :=
            Finset.sum_le_sum hprod
        _ = (Pnsq.card : ℝ) * (C2 * (Real.log Q + 1) * (R : ℝ) * (2 * Real.log R + 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((R : ℝ) * (R : ℝ)) * (C2 * (Real.log Q + 1) * (R : ℝ) * (2 * Real.log R + 2)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hcard : Pnsq.card ≤ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).card := by
              rw [hPnsq, hP]; exact Finset.card_le_card (Finset.filter_subset _ _)
            rw [Finset.card_product] at hcard
            have hc1 : (Finset.Icc 1 R).card = R := by rw [Nat.card_Icc]; omega
            rw [hc1] at hcard
            exact_mod_cast hcard
        _ = C2 * (Real.log Q + 1) * (2 * Real.log R + 2) * (R : ℝ) ^ 3 := by ring
        _ ≤ 2 * C2 * L ^ 2 * (R : ℝ) ^ 3 := by
            have hlogQ : Real.log (Q : ℝ) ≤ Real.log (Q * R + 2) := by
              apply Real.log_le_log (by positivity)
              nlinarith [hR1r, hQ1r]
            have hlogR : Real.log (R : ℝ) ≤ Real.log (Q * R + 2) := by
              apply Real.log_le_log (by positivity)
              nlinarith [hR1r, hQ1r]
            have hQ1' : Real.log (Q : ℝ) + 1 ≤ L := by rw [hL]; linarith
            have hR1' : Real.log (R : ℝ) + 1 ≤ L := by rw [hL]; linarith
            have hQnn : 0 ≤ Real.log (Q : ℝ) + 1 := by
              have := Real.log_natCast_nonneg Q; linarith
            have hRnn : 0 ≤ Real.log (R : ℝ) + 1 := by
              have := Real.log_natCast_nonneg R; linarith
            have hprod2 : (Real.log (Q : ℝ) + 1) * (Real.log (R : ℝ) + 1) ≤ L ^ 2 := by
              calc (Real.log (Q : ℝ) + 1) * (Real.log (R : ℝ) + 1)
                  ≤ L * L := mul_le_mul hQ1' hR1' hRnn (le_trans hQnn hQ1')
                _ = L ^ 2 := by ring
            rw [show (2 : ℝ) * Real.log R + 2 = 2 * (Real.log R + 1) by ring]
            have hkey : C2 * (Real.log Q + 1) * (2 * (Real.log R + 1)) * (R : ℝ) ^ 3
                = 2 * C2 * (R : ℝ) ^ 3 * ((Real.log Q + 1) * (Real.log R + 1)) := by ring
            rw [hkey]
            have hfin := mul_le_mul_of_nonneg_left hprod2
              (by positivity : (0 : ℝ) ≤ 2 * C2 * (R : ℝ) ^ 3)
            linarith [hfin]
        _ = 2 * C2 * (R : ℝ) ^ 3 * L ^ 2 := by ring
        _ ≤ 2 * C2 * M * L ^ 2 := by
            have hR3leM : (R : ℝ) ^ 3 ≤ M := by
              rw [hM]; nlinarith [show (0 : ℝ) ≤ (Q : ℝ) * R by positivity]
            have hC2nn : 0 ≤ 2 * C2 := by positivity
            have hL2 : 0 ≤ L ^ 2 := sq_nonneg _
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR3leM hC2nn) hL2
    have hsum2 : (∑ p ∈ Psq, Uodd Q (p.1 * p.2)) + (∑ p ∈ Pnsq, Uodd Q (p.1 * p.2))
        ≤ (2 + Cd + 2 * C2) * M * L ^ 2 := by
      have hMnn : 0 ≤ M := by rw [hM]; positivity
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg _
      have h := add_le_add hA hB
      have h2 : Cd * M * L ^ 2 + 2 * C2 * M * L ^ 2 ≤ (2 + Cd + 2 * C2) * M * L ^ 2 := by
        nlinarith [hMnn, hL2]
      linarith [h, h2]
    calc Fmom Q R
        ≤ ∑ p ∈ P, Uodd Q (p.1 * p.2) := hF
      _ = (∑ p ∈ Psq, Uodd Q (p.1 * p.2)) + (∑ p ∈ Pnsq, Uodd Q (p.1 * p.2)) := hsplit.symm
      _ ≤ (2 + Cd + 2 * C2) * M * L ^ 2 := hsum2
      _ = (2 + Cd + 2 * C2) * ((Q : ℝ) * R + (R : ℝ) ^ 3)
            * (Real.log (Q * R + 2) + 1) ^ 2 := by rw [hM, hL]

/-- The two elementary bounds for the second moment. -/
theorem F_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q R : ℕ), 1 ≤ R →
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
          (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2)
        ≤ C * (Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2 ∧
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
          (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2)
        ≤ C * ((Q : ℝ) * R + (R : ℝ) ^ 3) * (Real.log (Q * R + 2) + 1) ^ 2 := by
  obtain ⟨Ci, hCipos, hi⟩ := F_bound_i
  obtain ⟨Cii, hCiipos, hii⟩ := F_bound_ii
  refine ⟨max Ci Cii, lt_max_iff.mpr (Or.inl hCipos), ?_⟩
  intro Q R hR
  refine ⟨?_, ?_⟩
  · calc Fmom Q R ≤ Ci * (Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2 := hi Q R hR
      _ = Ci * ((Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2) := by ring
      _ ≤ max Ci Cii * ((Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max Ci Cii * (Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2 := by ring
  · calc Fmom Q R
        ≤ Cii * ((Q : ℝ) * R + (R : ℝ) ^ 3) * (Real.log (Q * R + 2) + 1) ^ 2 := hii Q R hR
      _ = Cii * (((Q : ℝ) * R + (R : ℝ) ^ 3) * (Real.log (Q * R + 2) + 1) ^ 2) := by ring
      _ ≤ max Ci Cii * (((Q : ℝ) * R + (R : ℝ) ^ 3) * (Real.log (Q * R + 2) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = max Ci Cii * ((Q : ℝ) * R + (R : ℝ) ^ 3)
            * (Real.log (Q * R + 2) + 1) ^ 2 := by ring

end

end Work.FIArea4.L14
