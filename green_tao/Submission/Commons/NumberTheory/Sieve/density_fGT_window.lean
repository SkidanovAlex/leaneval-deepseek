import Mathlib
import Submission.Commons.NumberTheory.PrimesInAP.prime_in_short_interval_AP
import Submission.Commons.NumberTheory.PrimeNumberTheorem.sum_vonMangoldt_sub_primeLog_le
import Submission.Commons.NumberTheory.ZMod.zmod_window_eq_Ioc
import Submission.Commons.NumberTheory.Sieve.window_AP_error_eventually

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Sieve

/-- Lower bound for the prime-log sum in a band `(A,B]` restricted to a residue class
`1 mod W`, in terms of the values of `psiAPNat` at the two endpoints. -/
lemma band_AP_primeLog_lower (W A B : ℕ) (hAB : A ≤ B) :
    ((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ)
      - |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)|
      - |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ)|
      - 2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ)
    ≤ ∑ n ∈ Finset.Ioc A B, (if n % W = 1 % W ∧ Nat.Prime n then Real.log (n : ℝ) else 0) := by
  have hsplit : (Finset.Icc 1 B).filter (fun n => n % W = 1 % W)
      = (Finset.Icc 1 A).filter (fun n => n % W = 1 % W)
        ∪ (Finset.Ioc A B).filter (fun n => n % W = 1 % W) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmod⟩
      by_cases hA : n ≤ A
      · exact Or.inl ⟨⟨h1, hA⟩, hmod⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hmod⟩
    · rintro (⟨⟨h1, h2⟩, hmod⟩ | ⟨⟨h1, h2⟩, hmod⟩)
      · exact ⟨⟨h1, le_trans h2 hAB⟩, hmod⟩
      · exact ⟨⟨by omega, h2⟩, hmod⟩
  have hdisj : Disjoint ((Finset.Icc 1 A).filter (fun n => n % W = 1 % W))
      ((Finset.Ioc A B).filter (fun n => n % W = 1 % W)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn1
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn2
    omega
  have hband : Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B
      - Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A
      = ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W), ArithmeticFunction.vonMangoldt n := by
    unfold Commons.NumberTheory.PrimesInAP.psiAPNat
    rw [hsplit, Finset.sum_union hdisj]
    ring
  have hLam : ((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ)
      - |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)|
      - |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ)|
      ≤ ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W), ArithmeticFunction.vonMangoldt n := by
    rw [← hband]
    have h1 : Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)
        ≤ |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)| :=
      le_abs_self _
    have h2 : -|Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ)|
        ≤ Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ) :=
      neg_abs_le _
    have hdiv : ((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ)
        = (B : ℝ) / (Nat.totient W : ℝ) - (A : ℝ) / (Nat.totient W : ℝ) := by ring
    linarith
  have hpp := Commons.NumberTheory.PrimeNumberTheorem.sum_vonMangoldt_sub_primeLog_le B
    ((Finset.Ioc A B).filter (fun n => n % W = 1 % W))
    (fun n hn => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2)
  have hcorr : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W),
        (ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0))
      ≤ 2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) := hpp
  have hconv : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W),
        (if n.Prime then Real.log (n : ℝ) else 0)
      = ∑ n ∈ Finset.Ioc A B, (if n % W = 1 % W ∧ n.Prime then Real.log (n : ℝ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : n % W = 1 % W
    · simp [h]
    · simp [h]
  rw [← hconv]
  have hSprime_eq : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W),
        (if n.Prime then Real.log (n : ℝ) else 0)
      = (∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W), ArithmeticFunction.vonMangoldt n)
        - ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W),
            (ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log (n : ℝ) else 0)) := by
    rw [Finset.sum_sub_distrib]; ring
  have hkey : (∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W), ArithmeticFunction.vonMangoldt n)
      - 2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ)
      ≤ ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = 1 % W),
          (if n.Prime then Real.log (n : ℝ) else 0) := by
    rw [hSprime_eq]; linarith
  linarith [hkey, hLam]

set_option maxHeartbeats 0 in
/-- The total mass of the `W`-tricked von Mangoldt in the window `[ε p, 2 ε p]` is `≥ δ p`. -/
theorem density_fGT_window (ε : ℝ) (hε : 0 < ε) (hε4 : 4 * ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ W : ℕ, 1 ≤ W → ∃ P : ℕ, ∀ p : ℕ, [NeZero p] → P ≤ p → Nat.Prime p →
      δ * (p : ℝ) ≤ ∑ x : ZMod p,
        (if ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ) ∧
            Nat.Prime (W * x.val + 1)
          then ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log ((W * x.val + 1 : ℕ) : ℝ) else 0) := by
  have h2ε : 2 * ε < 1 := by linarith
  refine ⟨ε / 4, by linarith, ?_⟩
  intro W hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    have h1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    linarith
  have hWle1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  -- PNT in AP (Siegel-Walfisz) with `A = 2`
  obtain ⟨c, C, hc, hC, x₀, hpsi⟩ :=
    Commons.NumberTheory.PrimesInAP.psi_in_AP_smallModulus 2 (by norm_num)
  -- eventual error absorption with the half constant `c / 2`
  obtain ⟨P₁, hP₁⟩ :=
    Commons.NumberTheory.Sieve.window_AP_error_eventually ε (c / 2) C hε (by linarith) hC W hW
  -- structural threshold
  obtain ⟨P₂, hP₂⟩ :=
    exists_nat_ge (max (max x₀ (Real.exp (Real.sqrt (W : ℝ))))
      (max (16 / 5 : ℝ) (max 3 (3 * (W : ℝ)))) / ε)
  refine ⟨max P₁ P₂, ?_⟩
  intro p _ hPp hpPrime
  have hpP₁ : P₁ ≤ p := le_trans (le_max_left _ _) hPp
  have hpP₂ : P₂ ≤ p := le_trans (le_max_right _ _) hPp
  -- threshold condition `K ≤ ε p`
  have hPK : max (max x₀ (Real.exp (Real.sqrt (W : ℝ))))
      (max (16 / 5 : ℝ) (max 3 (3 * (W : ℝ)))) ≤ ε * (p : ℝ) := by
    have h1 : max (max x₀ (Real.exp (Real.sqrt (W : ℝ))))
        (max (16 / 5 : ℝ) (max 3 (3 * (W : ℝ)))) / ε ≤ (P₂ : ℝ) := hP₂
    rw [div_le_iff₀ hε] at h1
    have h2 : (P₂ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP₂
    nlinarith [h1, h2, hε]
  have hx₀ : x₀ ≤ ε * (p : ℝ) :=
    le_trans (le_trans (le_max_left x₀ _) (le_max_left _ _)) hPK
  have hExp : Real.exp (Real.sqrt (W : ℝ)) ≤ ε * (p : ℝ) :=
    le_trans (le_trans (le_max_right x₀ _) (le_max_left _ _)) hPK
  have h165 : (16 / 5 : ℝ) ≤ ε * (p : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hPK
  have h3W : 3 * (W : ℝ) ≤ ε * (p : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right 3 (3 * (W : ℝ)))
      (le_max_right (16 / 5 : ℝ) (max 3 (3 * (W : ℝ)))))
      (le_max_right (max x₀ (Real.exp (Real.sqrt (W : ℝ))))
        (max (16 / 5 : ℝ) (max 3 (3 * (W : ℝ)))))) hPK
  have hεp1 : (1 : ℝ) ≤ ε * (p : ℝ) := by linarith
  have hεp2 : (2 : ℝ) ≤ ε * (p : ℝ) := by linarith
  -- basic facts about ceil / floor
  have hceil_le : (⌈ε * (p : ℝ)⌉₊ : ℝ) ≤ ε * (p : ℝ) + 1 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ε * (p : ℝ) by positivity)
    linarith
  have hfloor_ge : 2 * ε * (p : ℝ) - 1 ≤ (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * ε * (p : ℝ))
    linarith
  have hceilfloor : ⌈ε * (p : ℝ)⌉₊ ≤ ⌊2 * ε * (p : ℝ)⌋₊ :=
    Nat.le_floor (by linarith [hceil_le, hεp2])
  -- reindex the `ZMod p` sum
  have hzmod := Commons.NumberTheory.ZMod.zmod_window_eq_Ioc W p ε
    (fun n : ℕ => ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log ((n : ℕ) : ℝ)) hW hε h2ε
  rw [hzmod]
  set A : ℕ := W * ⌈ε * (p : ℝ)⌉₊ with hA
  set B : ℕ := W * ⌊2 * ε * (p : ℝ)⌋₊ + 1 with hB
  -- structural facts
  have hAB : A ≤ B := by
    rw [hA, hB]
    have := Nat.mul_le_mul_left W hceilfloor
    omega
  have hAle : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hA_ge : (W : ℝ) * (ε * (p : ℝ)) ≤ (A : ℝ) := by
    rw [hA]
    have hcl : ε * (p : ℝ) ≤ (⌈ε * (p : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    calc (W : ℝ) * (ε * (p : ℝ)) ≤ (W : ℝ) * (⌈ε * (p : ℝ)⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg W)
      _ = ((W * ⌈ε * (p : ℝ)⌉₊ : ℕ) : ℝ) := by push_cast; ring
  have hB_le : (B : ℝ) ≤ 3 * (W : ℝ) * (ε * (p : ℝ)) := by
    rw [hB]; push_cast
    have hfl : (⌊2 * ε * (p : ℝ)⌋₊ : ℝ) ≤ 2 * ε * (p : ℝ) := Nat.floor_le (by positivity)
    have hWeps : 1 ≤ (W : ℝ) * (ε * (p : ℝ)) := by nlinarith [hWle1, hεp1]
    nlinarith [hfl, hWeps, hWpos]
  have hA3 : (3 : ℝ) ≤ (A : ℝ) := by
    have : (3 : ℝ) ≤ (W : ℝ) * (ε * (p : ℝ)) := by nlinarith [hWle1, h3W, hWpos]
    linarith [hA_ge, this]
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by linarith [hA1, hAle]
  have hApos : (0 : ℝ) < (A : ℝ) := by linarith
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  -- the exponential factor beats the threshold
  have hexp_le_A : Real.exp (Real.sqrt (W : ℝ)) ≤ (A : ℝ) := by
    have h2 : ε * (p : ℝ) ≤ (W : ℝ) * (ε * (p : ℝ)) := by nlinarith [hWle1, hεp1]
    linarith [hExp, h2, hA_ge]
  have hexp_le_B : Real.exp (Real.sqrt (W : ℝ)) ≤ (B : ℝ) := le_trans hexp_le_A hAle
  have hx₀A : x₀ ≤ (A : ℝ) := by
    have h2 : ε * (p : ℝ) ≤ (W : ℝ) * (ε * (p : ℝ)) := by nlinarith [hWle1, hεp1]
    linarith [hx₀, h2, hA_ge]
  have hx₀B : x₀ ≤ (B : ℝ) := le_trans hx₀A hAle
  -- logarithmic growth conditions
  have hWA : (W : ℝ) ≤ (Real.log (A : ℝ)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    have h1 : Real.sqrt (W : ℝ) ≤ Real.log (A : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) hexp_le_A
      rwa [Real.log_exp] at h
    have h2' : Real.sqrt (W : ℝ) * Real.sqrt (W : ℝ) ≤ Real.log (A : ℝ) * Real.log (A : ℝ) :=
      mul_self_le_mul_self (Real.sqrt_nonneg _) h1
    nlinarith [h2', Real.sq_sqrt (show (0 : ℝ) ≤ (W : ℝ) by positivity)]
  have hWB : (W : ℝ) ≤ (Real.log (B : ℝ)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    have h1 : Real.sqrt (W : ℝ) ≤ Real.log (B : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) hexp_le_B
      rwa [Real.log_exp] at h
    have h2' : Real.sqrt (W : ℝ) * Real.sqrt (W : ℝ) ≤ Real.log (B : ℝ) * Real.log (B : ℝ) :=
      mul_self_le_mul_self (Real.sqrt_nonneg _) h1
    nlinarith [h2', Real.sq_sqrt (show (0 : ℝ) ≤ (W : ℝ) by positivity)]
  -- band bound from the PNT in AP
  have hbA_raw := hpsi (A : ℝ) hx₀A W 1 hW hWA (Nat.coprime_one_left W)
  have hbB_raw := hpsi (B : ℝ) hx₀B W 1 hW hWB (Nat.coprime_one_left W)
  have hbA : |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)|
      ≤ C * (A : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2)))) := by
    simpa only [Nat.floor_natCast, Commons.NumberTheory.PrimesInAP.psiAPNat] using hbA_raw
  have hbB : |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ)|
      ≤ C * (B : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)))) := by
    simpa only [Nat.floor_natCast, Commons.NumberTheory.PrimesInAP.psiAPNat] using hbB_raw
  -- log growth comparison
  have hLpos : 0 < Real.log ((W : ℝ) + 2) := Real.log_pos (by linarith)
  have hlogA_nn : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg hA1
  have hlogB_le : Real.log (B : ℝ) ≤ 4 * Real.log (A : ℝ) := by
    have hB_le_3A : (B : ℝ) ≤ 3 * (A : ℝ) := by
      have h := hB_le
      have hWeps1 : 1 ≤ (W : ℝ) * (ε * (p : ℝ)) := by nlinarith [hWle1, hεp1]
      have hA_ge' : (W : ℝ) * (ε * (p : ℝ)) ≤ (A : ℝ) := hA_ge
      nlinarith [h, hA_ge', hWeps1]
    have hlog3 : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA3
    have h1 : Real.log (B : ℝ) ≤ Real.log (3 * (A : ℝ)) := Real.log_le_log hBpos hB_le_3A
    rw [Real.log_mul (by norm_num) (ne_of_gt hApos)] at h1
    linarith
  have hexp_le : Real.exp (-(c * Real.sqrt (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2))))
      ≤ Real.exp (-(c / 2 * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)))) := by
    apply Real.exp_le_exp.mpr
    have hdiv : Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)
        ≤ 4 * (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2)) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hlogB_le hLpos.le
    have hs : Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2))
        ≤ 2 * Real.sqrt (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2)) := by
      have hu : 0 ≤ Real.log (A : ℝ) / Real.log ((W : ℝ) + 2) := div_nonneg hlogA_nn hLpos.le
      have h2u : (2 * Real.sqrt (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2))) ^ 2
          = 4 * (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2)) := by
        rw [mul_pow, Real.sq_sqrt hu]; ring
      have h := Real.sqrt_le_sqrt (show Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)
          ≤ (2 * Real.sqrt (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2))) ^ 2 by rw [h2u]; linarith)
      rwa [Real.sqrt_sq (by positivity)] at h
    nlinarith [hs, hc, Real.sqrt_nonneg (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2))]
  -- bound the two error terms by the single `B` term with the halved constant
  have hErr : |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)|
        + |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ)|
      ≤ 2 * C * (B : ℝ) * Real.exp (-(c / 2 * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)))) := by
    have hE1 : C * (A : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (A : ℝ) / Real.log ((W : ℝ) + 2))))
        ≤ C * (B : ℝ) * Real.exp (-(c / 2 * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)))) := by
      refine mul_le_mul ?_ hexp_le (Real.exp_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hAle hC.le
    have hE2 : C * (B : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2))))
        ≤ C * (B : ℝ) * Real.exp (-(c / 2 * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply Real.exp_le_exp.mpr
      have hsnn : 0 ≤ Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2)) := Real.sqrt_nonneg _
      nlinarith [hsnn, hc]
    linarith [hE1, hE2, hbA, hbB]
  -- the prime-power correction together with the errors is `≤ ε p / 8`
  have herr : |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 A - (A : ℝ) / (Nat.totient W : ℝ)|
        + |Commons.NumberTheory.PrimesInAP.psiAPNat W 1 B - (B : ℝ) / (Nat.totient W : ℝ)|
        + 2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) ≤ ε * (p : ℝ) / 8 := by
    have hP₁p := hP₁ p hpP₁
    have hP₁p' : 2 * C * (B : ℝ) * Real.exp (-(c / 2 * Real.sqrt (Real.log (B : ℝ) / Real.log ((W : ℝ) + 2))))
        + 2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) ≤ ε * (p : ℝ) / 8 := by
      simpa only [← hB] using hP₁p
    linarith [hErr, hP₁p']
  -- the band lower bound
  have hT := band_AP_primeLog_lower W A B hAB
  have hTfinal : ((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ) - ε * (p : ℝ) / 8
      ≤ ∑ n ∈ Finset.Ioc A B, (if n % W = 1 % W ∧ Nat.Prime n then Real.log (n : ℝ) else 0) := by
    linarith [hT, herr]
  -- the `B - A` lower bound
  have hBA : (W : ℝ) * (ε * (p : ℝ)) - 2 * (W : ℝ) ≤ (B : ℝ) - (A : ℝ) := by
    rw [hA, hB]; push_cast
    nlinarith [hceil_le, hfloor_ge, hWpos]
  -- separate the constant factor
  rw [show (∑ n ∈ Finset.Ioc A B,
        (if n % W = 1 % W ∧ Nat.Prime n then
          (Nat.totient W : ℝ) / (W : ℝ) * Real.log (n : ℝ) else 0))
      = ((Nat.totient W : ℝ) / (W : ℝ)) * (∑ n ∈ Finset.Ioc A B,
          (if n % W = 1 % W ∧ Nat.Prime n then Real.log (n : ℝ) else 0)) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : n % W = 1 % W ∧ Nat.Prime n
    · simp [h]
    · simp [h]]
  -- final arithmetic
  have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) := by
    have h := Nat.totient_pos.mpr (by omega : 0 < W)
    exact_mod_cast h
  have hφle : (Nat.totient W : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.totient_le W
  have hφW_le_one : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 := by
    rw [div_le_one hWpos]; exact hφle
  have hφW_nn : 0 ≤ (Nat.totient W : ℝ) / (W : ℝ) := div_nonneg (Nat.cast_nonneg _) (le_of_lt hWpos)
  have hφW_mul : ((Nat.totient W : ℝ) / (W : ℝ)) * (((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ))
      = ((B : ℝ) - (A : ℝ)) / (W : ℝ) := by
    field_simp
  have hstep1 : ((Nat.totient W : ℝ) / (W : ℝ)) * (((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ) - ε * (p : ℝ) / 8)
      ≤ ((Nat.totient W : ℝ) / (W : ℝ))
        * (∑ n ∈ Finset.Ioc A B, (if n % W = 1 % W ∧ Nat.Prime n then Real.log (n : ℝ) else 0)) :=
    mul_le_mul_of_nonneg_left hTfinal hφW_nn
  have hstep2 : ((Nat.totient W : ℝ) / (W : ℝ)) * (((B : ℝ) - (A : ℝ)) / (Nat.totient W : ℝ) - ε * (p : ℝ) / 8)
      = ((B : ℝ) - (A : ℝ)) / (W : ℝ)
        - ((Nat.totient W : ℝ) / (W : ℝ)) * (ε * (p : ℝ) / 8) := by
    rw [mul_sub, hφW_mul]
  have hstep3 : ((Nat.totient W : ℝ) / (W : ℝ)) * (ε * (p : ℝ) / 8) ≤ ε * (p : ℝ) / 8 :=
    mul_le_of_le_one_left (by positivity) hφW_le_one
  have hstep4 : ε * (p : ℝ) - 2 ≤ ((B : ℝ) - (A : ℝ)) / (W : ℝ) := by
    rw [le_div_iff₀ hWpos]
    nlinarith [hBA]
  nlinarith [hstep1, hstep2, hstep3, hstep4, h165]

end Commons.NumberTheory.Sieve
