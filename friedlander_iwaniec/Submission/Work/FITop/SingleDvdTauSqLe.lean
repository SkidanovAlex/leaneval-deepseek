import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.ASP.S30
import Submission.Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_sq_div_of_cubefree
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

namespace Work.FITop

open Finset

attribute [local instance] Classical.propDecidable

/-! ### Elementary facts about the sequence `ã = atilFIa` -/

lemma atilFIa_nonneg' (n : ℕ) : 0 ≤ atilFIa n := by
  rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  positivity

lemma atilFIa_le_an (n : ℕ) : atilFIa n ≤ (Submission.an n : ℝ) := by
  rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  have h1 : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 ≤ 1 := by
    rw [Submission.ASP.moebius_sq_cast n]; split_ifs <;> norm_num
  have h2 : (0 : ℝ) ≤ (Submission.an n : ℝ) := Nat.cast_nonneg _
  calc ((ArithmeticFunction.moebius n : ℝ)) ^ 2 * (Submission.an n : ℝ)
      ≤ 1 * (Submission.an n : ℝ) := mul_le_mul_of_nonneg_right h1 h2
    _ = (Submission.an n : ℝ) := one_mul _

lemma atilFIa_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) : atilFIa n = 0 := by
  rw [atilFIa]
  exact Submission.ASP.atil_zero_of_not_squarefree hn

lemma AcountAtil_nonneg' (x : ℕ) : 0 ≤ AcountAtil x := by
  rw [AcountAtil, Submission.ASP.Acount]
  exact Finset.sum_nonneg (fun n _ => atilFIa_nonneg' n)

lemma one_le_AcountAtil {x : ℕ} (hx : 1 ≤ x) : 1 ≤ AcountAtil x := by
  rw [AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx⟩
  have hle : atilFIa 1 ≤ ∑ n ∈ Finset.Icc 1 x, atilFIa n :=
    Finset.single_le_sum (fun i _ => atilFIa_nonneg' i) hmem
  have h1 : (1 : ℝ) ≤ atilFIa 1 := by
    rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
    rw [Submission.ASP.moebius_sq_cast 1, if_pos squarefree_one, one_mul]
    exact_mod_cast Submission.ASP.an_one_pos'
  linarith

/-- `A(x) ≤ (2/G + 1)·Ã(x)` for large `x`. -/
lemma Aseq_le_const_mul_AcountAtil :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      (Submission.Aseq x : ℝ)
        ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * AcountAtil x := by
  obtain ⟨XA, hA⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  refine ⟨max XA 1, fun x hx => ?_⟩
  have hxXA : XA ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hGpos : 0 < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  have h1 : Submission.ASP.Acount Submission.ASP.FIa (x : ℝ)
      ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * AcountAtil x := hA x hxXA
  have h2 : Submission.ASP.Acount Submission.ASP.FIa (x : ℝ) = (Submission.Aseq x : ℝ) - 1 :=
    Submission.ASP.FI_Acount_eq x
  have h3 : 1 ≤ AcountAtil x := one_le_AcountAtil hx1
  have h4 : (0 : ℝ) < 2 / Submission.ASP.Gprod Submission.ASP.FIg := by positivity
  nlinarith [h1, h2, h3, h4]

/-- If `α < 0` then `B x^α ≤ (log x)^{-3}` for all large `x`. -/
lemma rpow_exp_le_log_zpow_neg_three {B α : ℝ} (hB : 0 ≤ B) (hα : α < 0) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → B * (x : ℝ) ^ α ≤ (Real.log (x : ℝ)) ^ (-(3 : ℤ)) := by
  obtain ⟨X0, hX01, hX0⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := B) hB (n := 3) (r := -α)
      (by linarith)
  refine ⟨max 2 (⌈X0⌉₊ + 1), fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := by omega
  have hxX0 : X0 ≤ (x : ℝ) := by
    have h1 : (⌈X0⌉₊ + 1 : ℕ) ≤ x := le_trans (le_max_right _ _) hx
    have h2 : X0 ≤ ((⌈X0⌉₊ : ℕ) : ℝ) := Nat.le_ceil X0
    have h3 : ((⌈X0⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hxRpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have h1 : B * (Real.log (x : ℝ)) ^ 3 ≤ (x : ℝ) ^ (-α) := hX0 x hxX0
  have hxαpos : 0 < (x : ℝ) ^ α := Real.rpow_pos_of_pos hxRpos α
  have h2 : B * (Real.log (x : ℝ)) ^ 3 * (x : ℝ) ^ α ≤ 1 := by
    calc B * (Real.log (x : ℝ)) ^ 3 * (x : ℝ) ^ α
        = (B * (Real.log (x : ℝ)) ^ 3) * (x : ℝ) ^ α := by ring
      _ ≤ (x : ℝ) ^ (-α) * (x : ℝ) ^ α := mul_le_mul_of_nonneg_right h1 (le_of_lt hxαpos)
      _ = (x : ℝ) ^ ((-α) + α) := (Real.rpow_add hxRpos (-α) α).symm
      _ = 1 := by rw [neg_add_cancel, Real.rpow_zero]
  have h3 : (B * (x : ℝ) ^ α) * (Real.log (x : ℝ)) ^ 3 ≤ 1 := by
    rw [show (B * (x : ℝ) ^ α) * (Real.log (x : ℝ)) ^ 3
        = B * (Real.log (x : ℝ)) ^ 3 * (x : ℝ) ^ α by ring]
    exact h2
  have hlog3pos : 0 < (Real.log (x : ℝ)) ^ 3 := by positivity
  have h4 : B * (x : ℝ) ^ α ≤ 1 / (Real.log (x : ℝ)) ^ 3 := (le_div_iff₀ hlog3pos).mpr h3
  have h5 : 1 / (Real.log (x : ℝ)) ^ 3 = (Real.log (x : ℝ)) ^ (-(3 : ℤ)) := by
    rw [show (-(3 : ℤ)) = -(((3 : ℕ) : ℤ)) by norm_num, zpow_neg, zpow_natCast, one_div]
  exact h4.trans_eq h5


/-- A single-modulus (`b`) slice of the `τ²`-weighted sum of `ã`, small by a *power* of `x`
when `x^{1/4+η} ≤ b ≤ √x`.  NOTE: add `import Submission.ASP.S30` to the imports (for
`Submission.ASP.FI_Aseq_le_const_mul_Atil`); it is compatible with `Windows`.

Proof route:
* `τ(n)² ≤ C_ε n^{2ε}` (`Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow`), so the
  LHS is `≤ C_ε x^{2ε} ∑_{n : b ∣ n, n ≤ x} ã n ≤ C_ε x^{2ε} (Submission.Ad b x : ℝ)`
  (as `ã ≤ an` pointwise).
* If `b` is not squarefree every term vanishes: `ã n ≠ 0` forces `Squarefree n`, and `b ∣ n` with
  `n` squarefree forces `Squarefree b`.
* If `b` is squarefree it is cubefree, and `b ≤ √x` gives `b² ≤ x`, so
  `Submission.ASP.Ad_le_tau_sq_mul_rpow b x` gives `(Submission.Ad b x : ℝ) ≤ 12 τ(b)² x^{3/4}/b`;
  with `τ(b)² ≤ C_ε b^{2ε}` and `b ≥ x^{1/4+η}` this is
  `≤ C x^{3/4} x^{-1/4-η+3ε}`, and `x^{-1/4-η+3ε} ≤ (log x)^{-3}` for all large `x`
  (with `ε ≤ η/12`).
* Finally `x^{3/4} ≤ C' · Ã(x)` for large `x`: `X2Y4_Aseq_ge_const_mul_rpow` (`c x^{3/4} ≤ Aseq x`),
  `FI_Acount_eq` (`Acount FIa m = Aseq m - 1`) and `FI_Aseq_le_const_mul_Atil`
  (`Acount FIa x ≤ (2/Gprod FIg)·Ã(x)`) give
  `Ã(x) ≥ (Gprod/2)(Aseq x - 1) ≥ (Gprod c/4) x^{3/4}` eventually.
The constant `C` therefore depends on `η`.  (The hypothesis `(b:ℝ) ≤ Real.sqrt x` is the range in
which the pointwise congruence bound is available; the statement is *not* asserted for `b > √x`.) -/
theorem SingleDvdTauSqLe (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ b : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) ≤ (b : ℝ) → (b : ℝ) ≤ Real.sqrt (x : ℝ) →
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n),
          ((n.divisors.card : ℝ)) ^ 2 * atilFIa n
        ≤ C * AcountAtil x * (Real.log (x : ℝ)) ^ (-(3 : ℤ)) := by
  classical
  -- the small exponent `ε` and the resulting exponent `α < 0`
  set ε : ℝ := (1 / 4 + η) / (10 + 8 * η) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε_lt : 2 * ε < 1 := by
    rw [hεdef]
    have hpos : (0 : ℝ) < 10 + 8 * η := by positivity
    have heq : 2 * ((1 / 4 + η) / (10 + 8 * η)) = (2 * (1 / 4 + η)) / (10 + 8 * η) := by ring
    rw [heq, div_lt_one hpos]
    nlinarith [hη]
  set α : ℝ := 2 * ε + (2 * ε - 1) * (1 / 4 + η) with hαdef
  have hαeq : α = -(3 / 4) * (1 / 4 + η) := by
    rw [hαdef, hεdef]
    have hne : (10 : ℝ) + 8 * η ≠ 0 := by positivity
    field_simp
    ring
  have hαneg : α < 0 := by rw [hαeq]; nlinarith [hη]
  -- the divisor bound and the congruence-sum bound
  obtain ⟨Cε, hCεpos, hCε⟩ :=
    Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow ε hεpos
  obtain ⟨Ca, hCapos, hAdle⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.Ad_le_tau_sq_div_of_cubefree
  obtain ⟨XK, hAseqK⟩ := Aseq_le_const_mul_AcountAtil
  set K : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have hG := Submission.ASP.Gprod_FIg_pos
    positivity
  set B : ℝ := Cε ^ 2 * Ca * Cε ^ 2 * K with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hBnn : 0 ≤ B := le_of_lt hBpos
  obtain ⟨Xlog, hXlog⟩ := rpow_exp_le_log_zpow_neg_three hBnn hαneg
  refine ⟨1, one_pos, max 2 (max XK Xlog), ?_⟩
  intro x hx b hb_lo hb_hi
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := by omega
  have hxK : XK ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hxlog : Xlog ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hxRpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hÃnn : 0 ≤ AcountAtil x := AcountAtil_nonneg' x
  have hlog_nn : 0 ≤ (Real.log (x : ℝ)) ^ (-(3 : ℤ)) :=
    le_of_lt (zpow_pos hlogpos (-(3 : ℤ)))
  set S₁ : ℝ := ∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n),
      ((n.divisors.card : ℝ)) ^ 2 * atilFIa n with hS₁
  set S₂ : ℝ := ∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), atilFIa n with hS₂
  -- Step 1: the pointwise `τ²` bound
  have hstep1 : S₁ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε) * S₂ := by
    rw [hS₁, hS₂, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, _⟩ := hn
    have hnR0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnRle : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnx
    have hcard := hCε n hn1
    have hsq : ((n.divisors.card : ℝ)) ^ 2 ≤ (Cε * (n : ℝ) ^ ε) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    have hexp : (Cε * (n : ℝ) ^ ε) ^ 2 = Cε ^ 2 * (n : ℝ) ^ (2 * ε) := by
      have h1 : ((n : ℝ) ^ ε) ^ 2 = (n : ℝ) ^ (2 * ε) := by
        rw [pow_two, ← Real.rpow_add hnRpos, show ε + ε = 2 * ε by ring]
      rw [mul_pow, h1]
    have hxε : (n : ℝ) ^ (2 * ε) ≤ (x : ℝ) ^ (2 * ε) :=
      Real.rpow_le_rpow hnR0 hnRle (by positivity)
    have hτ : ((n.divisors.card : ℝ)) ^ 2 ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε) := by
      calc ((n.divisors.card : ℝ)) ^ 2 ≤ (Cε * (n : ℝ) ^ ε) ^ 2 := hsq
        _ = Cε ^ 2 * (n : ℝ) ^ (2 * ε) := hexp
        _ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε) := mul_le_mul_of_nonneg_left hxε (by positivity)
    exact mul_le_mul_of_nonneg_right hτ (atilFIa_nonneg' n)
  -- Step 2: `∑_{b ∣ n ≤ x} ã n ≤ A_b(x)`
  have hstep2 : S₂ ≤ (Submission.Ad b x : ℝ) := by
    rw [hS₂]
    have hsub : (Finset.Icc 1 x).filter (fun n => b ∣ n)
        ⊆ (Finset.range (x + 1)).filter (fun n => b ∣ n) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hn.2⟩
    have h1 : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), atilFIa n)
        ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => b ∣ n), (Submission.an n : ℝ) := by
      calc (∑ n ∈ (Finset.Icc 1 x).filter (fun n => b ∣ n), atilFIa n)
          ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => b ∣ n), atilFIa n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => atilFIa_nonneg' i)
        _ ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => b ∣ n), (Submission.an n : ℝ) :=
            Finset.sum_le_sum (fun n _ => atilFIa_le_an n)
    rw [Submission.Ad, Nat.cast_sum]
    exact h1
  by_cases hsf : Squarefree b
  · -- squarefree case
    have hb1 : 1 ≤ b := by
      have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 + η) := Real.one_le_rpow hxR1 (by positivity)
      have h2 : (1 : ℝ) ≤ (b : ℝ) := le_trans h1 hb_lo
      exact_mod_cast h2
    have hbRpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have hbR0 : (0 : ℝ) ≤ (b : ℝ) := le_of_lt hbRpos
    have hbsq : b ^ 2 ≤ x := by
      have h1 : (b : ℝ) ^ 2 ≤ (Real.sqrt (x : ℝ)) ^ 2 := by
        nlinarith [hb_hi, Real.sqrt_nonneg (x : ℝ), hbR0]
      rw [Real.sq_sqrt (le_of_lt hxRpos)] at h1
      exact_mod_cast h1
    have hcb : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ b := by
      intro p hp hp3
      have hpp : p * p ∣ b := dvd_trans (show p * p ∣ p ^ 3 from ⟨p, by ring⟩) hp3
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp hpp
    have hAdb : (Submission.Ad b x : ℝ)
        ≤ Ca * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * (Submission.Aseq x : ℝ) :=
      hAdle b x hb1 hcb hbsq
    have hAseqb : (Submission.Aseq x : ℝ) ≤ K * AcountAtil x := by
      rw [hKdef]
      exact hAseqK x hxK
    have htaub : ((b.divisors.card : ℝ)) ^ 2 / (b : ℝ) ≤ Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1) := by
      have hcard := hCε b hb1
      have hsq : ((b.divisors.card : ℝ)) ^ 2 ≤ (Cε * (b : ℝ) ^ ε) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      have hexp : (Cε * (b : ℝ) ^ ε) ^ 2 = Cε ^ 2 * (b : ℝ) ^ (2 * ε) := by
        have h1 : ((b : ℝ) ^ ε) ^ 2 = (b : ℝ) ^ (2 * ε) := by
          rw [pow_two, ← Real.rpow_add hbRpos, show ε + ε = 2 * ε by ring]
        rw [mul_pow, h1]
      calc ((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)
          ≤ (Cε ^ 2 * (b : ℝ) ^ (2 * ε)) / (b : ℝ) := by
            rw [← hexp]
            exact div_le_div_of_nonneg_right hsq hbR0
        _ = Cε ^ 2 * ((b : ℝ) ^ (2 * ε) / (b : ℝ)) := by ring
        _ = Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1) := by
            rw [Real.rpow_sub hbRpos (2 * ε) 1, Real.rpow_one]
    have hbp : (b : ℝ) ^ (2 * ε - 1) ≤ (x : ℝ) ^ ((2 * ε - 1) * (1 / 4 + η)) := by
      have h1 : (b : ℝ) ^ (2 * ε - 1)
          ≤ ((x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ (2 * ε - 1) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hxRpos _) hb_lo (by linarith)
      have h2 : ((x : ℝ) ^ ((1 : ℝ) / 4 + η)) ^ (2 * ε - 1)
          = (x : ℝ) ^ (((1 : ℝ) / 4 + η) * (2 * ε - 1)) :=
        (Real.rpow_mul (le_of_lt hxRpos) ((1 : ℝ) / 4 + η) (2 * ε - 1)).symm
      rw [h2] at h1
      rwa [mul_comm ((1 : ℝ) / 4 + η) (2 * ε - 1)] at h1
    have hTnn : (0 : ℝ) ≤ (b : ℝ) ^ (2 * ε - 1) := Real.rpow_nonneg hbR0 _
    have hTnn' : (0 : ℝ) ≤ (x : ℝ) ^ ((2 * ε - 1) * (1 / 4 + η)) :=
      Real.rpow_nonneg (le_of_lt hxRpos) _
    have hnn1 : (0 : ℝ) ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε) := by positivity
    have hKnn : (0 : ℝ) ≤ K * AcountAtil x := mul_nonneg (le_of_lt hKpos) hÃnn
    have hmain : S₁ ≤ B * (x : ℝ) ^ α * AcountAtil x := by
      calc S₁ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε) * S₂ := hstep1
        _ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε) * (Submission.Ad b x : ℝ) :=
            mul_le_mul_of_nonneg_left hstep2 hnn1
        _ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε)
              * (Ca * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ)) * (Submission.Aseq x : ℝ)) :=
            mul_le_mul_of_nonneg_left hAdb hnn1
        _ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε)
              * (Ca * (Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1)) * (K * AcountAtil x)) := by
            have h1 : Ca * (((b.divisors.card : ℝ)) ^ 2 / (b : ℝ))
                ≤ Ca * (Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1)) :=
              mul_le_mul_of_nonneg_left htaub (le_of_lt hCapos)
            have h2 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
            have h3 : (0 : ℝ) ≤ Ca * (Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1)) :=
              mul_nonneg (le_of_lt hCapos) (mul_nonneg (by positivity) hTnn)
            exact mul_le_mul_of_nonneg_left (mul_le_mul h1 hAseqb h2 h3) hnn1
        _ ≤ Cε ^ 2 * (x : ℝ) ^ (2 * ε)
              * (Ca * (Cε ^ 2 * (x : ℝ) ^ ((2 * ε - 1) * (1 / 4 + η)))
                  * (K * AcountAtil x)) := by
            have h1 : Ca * (Cε ^ 2 * (b : ℝ) ^ (2 * ε - 1))
                ≤ Ca * (Cε ^ 2 * (x : ℝ) ^ ((2 * ε - 1) * (1 / 4 + η))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbp (by positivity))
                (le_of_lt hCapos)
            have h3 : (0 : ℝ) ≤ Ca * (Cε ^ 2 * (x : ℝ) ^ ((2 * ε - 1) * (1 / 4 + η))) :=
              mul_nonneg (le_of_lt hCapos) (mul_nonneg (by positivity) hTnn')
            exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (le_refl _) hKnn h3) hnn1
        _ = B * (x : ℝ) ^ α * AcountAtil x := by
            rw [hBdef, hαdef,
              Real.rpow_add hxRpos (2 * ε) ((2 * ε - 1) * (1 / 4 + η))]
            ring
    calc S₁ ≤ B * (x : ℝ) ^ α * AcountAtil x := hmain
      _ ≤ (Real.log (x : ℝ)) ^ (-(3 : ℤ)) * AcountAtil x :=
          mul_le_mul_of_nonneg_right (hXlog x hxlog) hÃnn
      _ = 1 * AcountAtil x * (Real.log (x : ℝ)) ^ (-(3 : ℤ)) := by ring
  · -- non-squarefree case: every term vanishes
    have hzero : S₁ = 0 := by
      rw [hS₁]
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_filter] at hn
      have hnsf : ¬ Squarefree n := fun hsn => hsf (Squarefree.squarefree_of_dvd hn.2 hsn)
      rw [atilFIa_eq_zero_of_not_squarefree hnsf]
      ring
    rw [hzero]
    have hnn : (0 : ℝ) ≤ 1 * AcountAtil x * (Real.log (x : ℝ)) ^ (-(3 : ℤ)) :=
      mul_nonneg (mul_nonneg zero_le_one hÃnn) hlog_nn
    exact hnn


end Work.FITop
