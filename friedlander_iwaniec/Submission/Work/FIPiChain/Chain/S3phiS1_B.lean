import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIPiChain.Chain.S3phiBDefs
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.LocalS6c
import Submission.Work.FIChain.LocalS5c
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.FIgtil_prod_sub_le
import Submission.Work.FIChain.assemblyC
import Submission.Work.FIPiChain.Chain.chainRangeWideB

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary lemmas for the `S₁`-summand -/

/-- `cseg` is **monotone in reverse in its lower endpoint**: raising the truncation `sz` shrinks
the range `(sz, N/sy]`. -/
private lemma cseg_anti_lo {N : ℕ} {sz sz' sy : ℝ} (h : sz ≤ sz') :
    Submission.ASP.cseg N sz' sy ⊆ Submission.ASP.cseg N sz sy := by
  intro c hc
  simp only [Submission.ASP.cseg, Submission.ASP.seg, Finset.mem_filter] at hc ⊢
  exact ⟨⟨hc.1.1, lt_of_le_of_lt h hc.1.2⟩, hc.2⟩

/-- `L6` is **antitone in its lower endpoint**: enlarging the lower truncation `sz` shrinks the
`c`-range `(sz, N/sy]`, and the summands `Λ(c)·g(c)` are nonnegative. -/
private lemma L6_lo_le {g : ℕ → ℝ} (hg : ∀ n : ℕ, 0 ≤ g n) (N : ℕ) {sz sz' sy : ℝ}
    (h : sz ≤ sz') :
    Submission.ASP.L6 g N sz' sy ≤ Submission.ASP.L6 g N sz sy := by
  rw [Submission.ASP.L6, Submission.ASP.L6]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨cseg_anti_lo h hc.1, hc.2⟩
  · intro c hc _
    rw [Finset.mem_filter] at hc
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hg c)

/-- The threshold at which `100·(2B+6)·loglog x ≤ log x`: an elementary estimate for the
`loglog`-rate (`assemblyC.lean`, step `hevLLN`). -/
private lemma ev_LLN_le (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      100 * (2 * B + 6) * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
  have _ : (0 : ℝ) < B := hB
  have hc : (0 : ℝ) < 100 * (2 * B + 6) := by linarith
  filter_upwards [Work.FITop.FI_ev_log_ge_nat (4 * (100 * (2 * B + 6)) ^ 2),
    Filter.eventually_ge_atTop 3] with M hM h3
  have hM3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h3
  have hL1 : (1 : ℝ) ≤ Real.log (M : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hM3])
  have hLp : 0 < Real.log (M : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hLLN : Real.log (Real.log (M : ℝ)) ≤ 2 * Real.sqrt (Real.log (M : ℝ)) := by
    have h1 : Real.log (Real.log (M : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (M : ℝ))) := by
      rw [Real.log_sqrt hLp.le]; ring
    rw [h1]
    have h2 : Real.log (Real.sqrt (Real.log (M : ℝ))) ≤ Real.sqrt (Real.log (M : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLp)
      linarith
    linarith
  have hsqrt : Real.sqrt (Real.log (M : ℝ)) ≤ Real.log (M : ℝ) / (2 * (100 * (2 * B + 6))) := by
    rw [le_div_iff₀ (by positivity)]
    have h2 : (2 * (100 * (2 * B + 6))) ^ 2 ≤ Real.log (M : ℝ) := by nlinarith [hM]
    have h3 : (2 * (100 * (2 * B + 6))) ≤ Real.sqrt (Real.log (M : ℝ)) :=
      (Real.le_sqrt (by positivity) (by positivity)).mpr h2
    nlinarith [h3, Real.sqrt_nonneg (Real.log (M : ℝ)), Real.sq_sqrt hLp.le]
  have h4 : 2 * Real.sqrt (Real.log (M : ℝ)) ≤ Real.log (M : ℝ) / (100 * (2 * B + 6)) := by
    have h5 := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h6 : (2 : ℝ) * (Real.log (M : ℝ) / (2 * (100 * (2 * B + 6))))
        = Real.log (M : ℝ) / (100 * (2 * B + 6)) := by field_simp
    rwa [h6] at h5
  have h5 : 100 * (2 * B + 6) * (Real.log (M : ℝ) / (100 * (2 * B + 6))) = Real.log (M : ℝ) := by
    have h6 : (100 : ℝ) * (2 * B + 6) ≠ 0 := ne_of_gt hc
    field_simp
  have h6 : 100 * (2 * B + 6) * Real.log (Real.log (M : ℝ))
      ≤ 100 * (2 * B + 6) * (Real.log (M : ℝ) / (100 * (2 * B + 6))) :=
    mul_le_mul_of_nonneg_left (by linarith [hLLN, h4]) hc.le
  linarith [h6, h5]

/-- `(d2c x B)^{1/log Δ} ≤ exp 2`: the `ε`-power of the `§6` cutoff `δ₂ = ⌈2·(log x)^{2B+4}⌉₊`
(`assemblyC.lean`, step `hδ2eps`). -/
private lemma d2c_rpow_eps_le {x : ℕ} (hB : (0 : ℝ) < HasBc.val)
    (hLN1 : 1 ≤ Real.log (x : ℝ))
    (hΔlow : Real.log (x : ℝ) / 100 ≤ Real.log (Deltac x : ℝ))
    (hthresh : 100 * (Real.log 3 + (2 * HasBc.val + 4) * Real.log (Real.log (x : ℝ)))
      ≤ Real.log (x : ℝ)) :
    ((d2c x HasBc.val : ℕ) : ℝ) ^ (1 / Real.log (Deltac x : ℝ)) ≤ Real.exp 2 := by
  have hLNp : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hLN1
  have hLΔpos : 0 < Real.log (Deltac x : ℝ) := by linarith [hΔlow, hLNp]
  have hδ2pos : (0 : ℝ) < ((d2c x HasBc.val : ℕ) : ℝ) := by
    rw [d2c]
    exact_mod_cast Nat.ceil_pos.mpr (by positivity)
  have hδ2ge1 : (1 : ℝ) ≤ ((d2c x HasBc.val : ℕ) : ℝ) := by
    rw [d2c]
    exact_mod_cast Nat.ceil_pos.mpr (by positivity)
  have hδ2le : ((d2c x HasBc.val : ℕ) : ℝ) ≤ 3 * (Real.log (x : ℝ)) ^ (2 * HasBc.val + 4) := by
    rw [d2c]
    have h1 : ((⌈2 * (Real.log (x : ℝ)) ^ (2 * HasBc.val + 4)⌉₊ : ℕ) : ℝ)
        < 2 * (Real.log (x : ℝ)) ^ (2 * HasBc.val + 4) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ (2 * HasBc.val + 4) :=
      Real.one_le_rpow hLN1 (by linarith)
    linarith
  have hlogδ2 : Real.log (((d2c x HasBc.val : ℕ) : ℝ))
      ≤ Real.log 3 + (2 * HasBc.val + 4) * Real.log (Real.log (x : ℝ)) := by
    have h1 := Real.log_le_log hδ2pos hδ2le
    rw [Real.log_mul (by norm_num)
      (ne_of_gt (Real.rpow_pos_of_pos hLNp _)), Real.log_rpow hLNp] at h1
    linarith [h1]
  have hεL : 1 / Real.log (Deltac x : ℝ) ≤ 100 / Real.log (x : ℝ) := by
    rw [div_le_div_iff₀ hLΔpos hLNp]
    linarith [hΔlow]
  have h1 : (1 / Real.log (Deltac x : ℝ)) * Real.log (((d2c x HasBc.val : ℕ) : ℝ)) ≤ 1 := by
    have h2 : (1 / Real.log (Deltac x : ℝ)) * Real.log (((d2c x HasBc.val : ℕ) : ℝ))
        ≤ (100 / Real.log (x : ℝ))
          * (Real.log 3 + (2 * HasBc.val + 4) * Real.log (Real.log (x : ℝ))) :=
      mul_le_mul hεL hlogδ2 (Real.log_nonneg hδ2ge1) (by positivity)
    have h3 : (100 / Real.log (x : ℝ))
        * (Real.log 3 + (2 * HasBc.val + 4) * Real.log (Real.log (x : ℝ))) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hLNp]
      linarith [hthresh]
    linarith [h2, h3]
  rw [Real.rpow_def_of_pos hδ2pos]
  calc Real.exp (Real.log (((d2c x HasBc.val : ℕ) : ℝ)) * (1 / Real.log (Deltac x : ℝ)))
      = Real.exp ((1 / Real.log (Deltac x : ℝ)) * Real.log (((d2c x HasBc.val : ℕ) : ℝ))) := by
        rw [mul_comm]
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)

/-- The `E₃`-rate arithmetic of `assemblyC.lean` (lines 1073–1161, `hE3le`), with the sieve
constant bounded by `K₀` instead of by `Ksie`: the `S₁`-estimate at
`C₅ = C6·(1+loglog x)`, `δ₂` cut off at `LΔ = log Δ`, `C₀` and `C₁ = C1p` is
`≪ (200·C6·e²·K₀·e^{32C₀}·C1p + 1)·Ã·loglog x/log x`. -/
private theorem S1_rate_le {Abar LN LLN LΔ C6 K₀ C0 C1p Cs X Mδ : ℝ}
    (hA : 0 ≤ Abar) (hLN : 1 ≤ LN) (hLLN1 : 1 ≤ LLN)
    (hLΔ0 : 0 < LΔ) (hLΔ : LN / 100 ≤ LΔ)
    (hC6 : 0 < C6) (hK₀ : 0 ≤ K₀) (hC0 : 0 ≤ C0) (hC1p : 0 < C1p)
    (hCs0 : 0 ≤ Cs) (hCsK : Cs ≤ K₀) (hX : X ≤ Real.exp 2) (hMδ : Mδ ≤ LN) :
    Abar * (C6 * (1 + LLN)) * (X * Cs * Real.exp (32 * C0) * C1p / LΔ)
      + Mδ * (Abar * LN ^ (-(3 : ℤ)))
      ≤ (200 * C6 * Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p + 1) * (Abar * (LLN / LN)) := by
  have hLN0 : (0 : ℝ) < LN := lt_of_lt_of_le zero_lt_one hLN
  have hLLN0 : 0 ≤ LLN := le_trans zero_le_one hLLN1
  have hE2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hE32 : (0 : ℝ) < Real.exp (32 * C0) := Real.exp_pos _
  have hLLdiv : 0 ≤ LLN / LN := div_nonneg hLLN0 hLN0.le
  have hAn : 0 ≤ Abar * (LLN / LN) := mul_nonneg hA hLLdiv
  have hC6nn : 0 ≤ C6 := le_of_lt hC6
  -- ### the first term
  have hfirst : Abar * (C6 * (1 + LLN)) * (X * Cs * Real.exp (32 * C0) * C1p / LΔ)
      ≤ 200 * C6 * Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p * (Abar * (LLN / LN)) := by
    have hXC : X * Cs ≤ Real.exp 2 * K₀ := mul_le_mul hX hCsK hCs0 hE2.le
    have hnum : X * Cs * Real.exp (32 * C0) * C1p
        ≤ Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p := by
      refine mul_le_mul_of_nonneg_right ?_ hC1p.le
      exact mul_le_mul_of_nonneg_right hXC hE32.le
    have hεL : 1 / LΔ ≤ 100 / LN := by
      rw [div_le_div_iff₀ hLΔ0 hLN0]
      linarith
    have hq : X * Cs * Real.exp (32 * C0) * C1p / LΔ
        ≤ Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p * (100 / LN) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum hεL (by positivity) (by positivity)
    have hnn1 : 0 ≤ Abar * (C6 * (1 + LLN)) :=
      mul_nonneg hA (mul_nonneg hC6nn (by linarith))
    have hstep : Abar * (C6 * (1 + LLN)) * (X * Cs * Real.exp (32 * C0) * C1p / LΔ)
        ≤ Abar * (C6 * (1 + LLN))
            * (Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p * (100 / LN)) :=
      mul_le_mul_of_nonneg_left hq hnn1
    have hkey : (1 + LLN) * (100 / LN) ≤ 200 * (LLN / LN) := by
      have h := mul_le_mul_of_nonneg_right (show 1 + LLN ≤ 2 * LLN by linarith)
        (by norm_num : (0 : ℝ) ≤ 100)
      have h2 : ((1 + LLN) * 100) / LN ≤ ((2 * LLN) * 100) / LN :=
        div_le_div_of_nonneg_right h hLN0.le
      have e2 : ((2 * LLN) * 100) / LN = 200 * (LLN / LN) := by ring
      rw [e2] at h2
      have e1 : (1 + LLN) * (100 / LN) = ((1 + LLN) * 100) / LN := by ring
      rwa [e1]
    have hAnC6 : 0 ≤ Abar * C6 := mul_nonneg hA hC6nn
    have hE' : 0 ≤ Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p := by positivity
    refine le_trans hstep ?_
    calc Abar * (C6 * (1 + LLN)) * (Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p * (100 / LN))
        = (Abar * C6) * ((1 + LLN) * (100 / LN))
            * (Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p) := by ring
      _ ≤ (Abar * C6) * (200 * (LLN / LN))
            * (Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hAnC6) hE'
      _ = 200 * C6 * Real.exp 2 * K₀ * Real.exp (32 * C0) * C1p * (Abar * (LLN / LN)) := by ring
  -- ### the second term
  have hsecond : Mδ * (Abar * LN ^ (-(3 : ℤ))) ≤ Abar * (LLN / LN) := by
    have hLN3 : LN ^ (-(3 : ℤ)) = (LN ^ 3)⁻¹ := by simp [zpow_neg]
    have h3nn : 0 ≤ Abar * LN ^ (-(3 : ℤ)) := by
      rw [hLN3]
      exact mul_nonneg hA (inv_nonneg.mpr (pow_nonneg hLN0.le 3))
    have h1 : Mδ * (Abar * LN ^ (-(3 : ℤ))) ≤ LN * (Abar * LN ^ (-(3 : ℤ))) :=
      mul_le_mul_of_nonneg_right hMδ h3nn
    refine le_trans h1 ?_
    have hkey2 : LN * (LN ^ 3)⁻¹ = (LN ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      rw [show LN * (1 / LN ^ 3) = 1 / LN ^ 2 by
        rw [mul_one_div, div_eq_div_iff (pow_ne_zero 3 (ne_of_gt hLN0))
          (pow_ne_zero 2 (ne_of_gt hLN0))]
        ring]
    have hkey : LN * (Abar * LN ^ (-(3 : ℤ))) = Abar * (LN ^ 2)⁻¹ := by
      rw [hLN3]
      rw [show LN * (Abar * (LN ^ 3)⁻¹) = Abar * (LN * (LN ^ 3)⁻¹) by ring, hkey2]
    rw [hkey]
    refine mul_le_mul_of_nonneg_left ?_ hA
    have h3 : (LN ^ 2)⁻¹ ≤ LLN / LN := by
      rw [inv_eq_one_div, div_le_div_iff₀ (pow_pos hLN0 2) hLN0]
      nlinarith only [hLN, hLLN1]
    exact h3
  -- ### assembly
  refine le_trans (add_le_add hfirst hsecond) (le_of_eq ?_)
  ring

/-- **The `S₁`-summand of the `§4–§7` estimate `Work.FIChain.S3phi_Bstar_v2`, uniformly over the
`z`-window, with the sieve constant `C_sieve` bounded by the parameter `K₀`.**

`|S₁ ã λ (x) (sc x HasBc.val·y) (sc x HasBc.val·z)| ≪ Ã(x)·loglog x/log x` for every `λ` satisfying
`SieveInput` at `Δ = Deltac x` **with `C_sieve ≤ K₀`**, every `y ∈ [Yc x HasBc.val, e·Yc x HasBc.val]` and
every `z ∈ [zc x HasBc.val, e·zc x HasBc.val]`.

The hypothesis `C_sieve ≤ K₀` is **essential**: the only `§6` estimate available
(`Submission.ASP.S1_bound_of_sieve`, local copy `Work.FIChain.LocalS6c.S1_bound_of_sieve`) reads
`|S₁| ≤ Ã·C₅·((δ₂)^ε·C_sieve·e^{32C₀}·C₁/log Δ) + log(M·δ₂)·RemainderSum`, i.e. is *proportional to*
`C_sieve`; and `SieveInput` alone bounds `C_sieve` only from below
(`Work.FIChain.exists_SieveInput_lamδ_large`).

Route: `S1_bound_of_sieve` at `sy := sc x HasBc.val·y`, `sz := sc x HasBc.val·z`,
`δ2 := d2c x HasBc.val`, `Δ := Deltac x`, `M := Mc x HasBc.val`, `D := Submission.Rcut x`,
`ε := 1/log (Deltac x)`, `C₅ := C₆·(1 + loglog x)` with `C₆` from `Work.FIChain.L6_param_le` at
`B := HasBc.val` (`Commons.NumberTheory.Chebyshev.sum_prime_log_mul_g_Ioc_le` supplies the input),
`C₁ := C1p` from `Work.FIChain.FIgtil_prod_sub_le`, `C₀ := max Chb 1` from
`Submission.ASP.FIgtil_bound`, `C_sieve := C_sieve`.  The three `z`-dependent hypotheses are
monotone in `z ≥ zc x HasBc.val`:
* `(Δ:ℝ) < sc x HasBc.val·z` because `sc x HasBc.val·zc x HasBc.val > Δ` (`scale_factsC`) and `sc ≥ 1`;
* the `δ₂`-condition `x/(b c) ≤ d2c x HasBc.val` for `sc·y < b`, `sc·z < c` has the *same* proof as in
  `Work.FIChain.assemblyC` (`hδ2`, lines 1238–1272), since `sc·y ≥ sc·Yc` and `sc·z ≥ sc·zc`;
* `∀ c ∈ cseg x (sc·z) (sc·y), c ≤ Mc x HasBc.val` is `z`-free: `c ≤ x/(sc·y) ≤ x/(sc·Yc) ≤ Mc x HasBc.val`
  (`chainRangeFactsC`, `assemblyC` line 1273–1283);
and `L6 FIgtil x (sc·z) (sc·y) ≤ L6 FIgtil x (sc·zc) (sc·y) ≤ C₆·(1+loglog x)` needs a small
monotonicity statement for `Submission.ASP.L6` in its *first* argument (`lo ≤ lo'` gives
`cseg x lo' sy ⊆ cseg x lo sy`, the summands `Λ(c)·g(c)` being nonnegative), to be proved in your
own file.  The final rate arithmetic is `assemblyC`'s `hδ2eps`/`hE3le` (lines 1028–1161) with
`(d2c x HasBc.val)^{1/log Δ}·C_sieve ≤ exp 2 · K₀` (this is exactly where `C_sieve ≤ K₀` is consumed). -/
theorem S3phiS1_Bstar (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve → C_sieve ≤ K₀ →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiS1 x lam y z| ≤ K * AcountAtilC x * s3phiRate x := by
  classical
  have hBpos : (0 : ℝ) < HasBc.val := by have := HasBc.ge_two; linarith
  have hgnn : ∀ n : ℕ, 0 ≤ Submission.ASP.FIgtil n := Submission.ASP.FIgtil_nonneg
  have hgmul : ∀ m n : ℕ, Nat.Coprime m n →
      Submission.ASP.FIgtil (m * n) = Submission.ASP.FIgtil m * Submission.ASP.FIgtil n :=
    fun m n hmn => Submission.ASP.FIgtil_mul hmn
  have hg1 : Submission.ASP.FIgtil 1 = 1 := Submission.ASP.FIgtil_one
  obtain ⟨Chb, hChbpos, hboundFI⟩ := Submission.ASP.FIgtil_bound
  obtain ⟨C1p, hC1ppos, hprodsubUse⟩ := FIgtil_prod_sub_le
  obtain ⟨Xr, hRemAll⟩ := remainder_all
  obtain ⟨C00, hC00pos, hIocle⟩ :=
    Commons.NumberTheory.Chebyshev.sum_prime_log_mul_g_Ioc_le
      (g := Submission.ASP.FIgtil) (fun p _ => hgnn p) ⟨Chb, hChbpos, hboundFI⟩
  obtain ⟨C6, hC6pos, hC6le_ev⟩ := L6_param_le HasBc.val C00 hBpos hC00pos hIocle
  obtain ⟨X6, hC6le⟩ := Filter.eventually_atTop.mp hC6le_ev
  have hC0pos : 0 < max Chb 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC0b : ∀ p : ℕ, Nat.Prime p → Submission.ASP.FIgtil p ≤ max Chb 1 / (p : ℝ) :=
    fun p hp => le_trans (hboundFI p hp)
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  set K : ℝ := 200 * C6 * Real.exp 2 * K₀ * Real.exp (32 * max Chb 1) * C1p + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hev : ∀ᶠ x : ℕ in Filter.atTop, s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve → C_sieve ≤ K₀ →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiS1 x lam y z| ≤ K * AcountAtilC x * s3phiRate x := by
    filter_upwards [scale_factsC HasBc.val hBpos,
      window_marginsC (1 / 64) HasBc.val (by norm_num) (by norm_num) hBpos,
      chainRangeFactsC HasBc.val hBpos, ev_LLN_le HasBc.val hBpos,
      Filter.eventually_ge_atTop Xr, Filter.eventually_ge_atTop X6]
      with x hs hw hch hLLNthresh hxr hx6
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15,
      hs16⟩ := hs
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hw
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := hch
    intro hcond lam Cs hSI hCsle y hy z hz
    simp only [s3phiYwin, Set.mem_Icc] at hy
    simp only [s3phiZwin, Set.mem_Icc] at hz
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hz
    show |Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)|
      ≤ K * AcountAtilC x * s3phiRate x
    -- ## 1. the elementary log facts
    have hx3R : (3 : ℝ) ≤ (x : ℝ) := hw6
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hLNpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < (x : ℝ))
    have hLN1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hx3R])
    have hLLN1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith [hw7]
    set Dn : ℕ := Deltac x with hDndef
    set Zn : ℕ := Zc x HasBc.val with hZndef
    set d2n : ℕ := d2c x HasBc.val with hd2ndef
    set Mcn : ℕ := Mc x HasBc.val with hMcndef
    set sr : ℝ := sc x HasBc.val with hsrdef
    set Yr : ℝ := Yc x HasBc.val with hYrdef
    set LN : ℝ := Real.log (x : ℝ) with hLNdef
    set LLN : ℝ := Real.log (Real.log (x : ℝ)) with hLLNdef
    set Abar : ℝ := AcountAtilC x with hAbardef
    have hLNp : 0 < LN := hLNpos
    have hLNone : (1 : ℝ) ≤ LN := hLN1
    have hLLNone : (1 : ℝ) ≤ LLN := by rw [hLLNdef]; exact hLLN1
    have hLLN_le : LLN ≤ LN := by
      rw [hLLNdef, hLNdef]
      exact Real.log_le_self hLNpos.le
    have hAbar0 : 0 ≤ Abar := by
      rw [hAbardef, AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount,
        Nat.floor_natCast]
      exact Finset.sum_nonneg (fun n _ => atilc_nonneg n)
    have hsr_pos : 0 < sr := by rw [hsrdef, sc]; positivity
    have hsr_one : (1 : ℝ) ≤ sr := by rw [hsrdef, sc]; exact one_le_pow₀ (by norm_num)
    have hYr_pos : 0 < Yr := hc3
    have hSrYr_pos : 0 < sr * Yr := mul_pos hsr_pos hYr_pos
    -- ## 2. the sieve weight
    have hlam1 : lam 1 = 1 := hSI.1
    have hΔsupp : ∀ ν : ℕ, Dn < ν → lam ν = 0 := hSI.2.1
    have hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0 := hSI.2.2.1
    have hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1 := hSI.2.2.2.1
    have hrho : ∀ n : ℕ, 0 ≤ Submission.ASP.rhoOf lam n := hSI.2.2.2.2.1
    have hpos : ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Dn,
        lam ν * Submission.ASP.FIgtil (Nat.lcm ν d) := hSI.2.2.2.2.2.1
    have hpos' : ∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Dn,
        lam ν * Submission.ASP.FIgtil (ν / Nat.gcd ν d) := hSI.2.2.2.2.2.2.1
    have hCs0 : 0 < Cs := hSI.2.2.2.2.2.2.2.1
    have hCsie : ∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
          lam ν * (Submission.ASP.FIgtil ν *
            Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) ν)
        ≤ Cs * ∏ p ∈ Nat.primesBelow (Dn),
            (1 - Submission.ASP.FIgtil p *
              Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) p) :=
      hSI.2.2.2.2.2.2.2.2
    have hCsie' : ∑ ν ∈ (Finset.Icc 1 (Dn)).filter Squarefree,
          lam ν * (Submission.ASP.FIgtil ν *
            Submission.ASP.hSieve Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) ν)
        ≤ Cs * ∏ p ∈ Nat.primesBelow (Dn),
            (1 - Submission.ASP.FIgtil p *
              Submission.ASP.hSieve Submission.ASP.FIgtil (1 / Real.log (Dn : ℝ)) p) := by
      simpa only [Work.FIChain.hSieveC, Submission.ASP.hSieve] using hCsie
    -- ## 3. the level `Δ` and the sequence
    have hDn3 : 3 ≤ Dn := hc6
    have hDn1R : (1 : ℝ) ≤ (Dn : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 3) hc6)
    have hΔN : Dn ≤ x := hc5
    have hLΔpos : 0 < Real.log (Dn : ℝ) := by
      have h3 : (3 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast hDn3
      exact Real.log_pos (by linarith [Real.exp_one_lt_three, h3])
    have hLΔ1 : (1 : ℝ) ≤ Real.log (Dn : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by
        have h3 : (3 : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast hDn3
        linarith [Real.exp_one_lt_three, h3])
    have hLΔ_le : Real.log (Dn : ℝ) ≤ LN := by
      rw [hLNdef]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hΔN)
    have hLΔ_low : LN / 100 ≤ Real.log (Dn : ℝ) := by
      have h1 : (x : ℝ) ^ ((1 : ℝ) / 100) ≤ (Dn : ℝ) := by
        rw [hDndef, Deltac, Work.FITop.Delta1, Work.FITop.Lam1]
        exact Nat.le_ceil _
      have h2 : Real.log ((x : ℝ) ^ ((1 : ℝ) / 100)) ≤ Real.log (Dn : ℝ) :=
        Real.log_le_log (Real.rpow_pos_of_pos hxpos _) h1
      rw [Real.log_rpow hxpos, ← hLNdef] at h2
      linarith [h2]
    have hε0 : 0 < 1 / Real.log (Dn : ℝ) := div_pos one_pos hLΔpos
    have hε1 : 1 / Real.log (Dn : ℝ) ≤ 1 := by
      rw [div_le_one hLΔpos]; exact hLΔ1
    have hεΔ : (1 / Real.log (Dn : ℝ)) * Real.log (Dn : ℝ) = 1 :=
      div_mul_cancel₀ _ (ne_of_gt hLΔpos)
    have hAd : Submission.ASP.Approx atilc Submission.ASP.FIgtil
        (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
          Submission.ASP.FIa) (x : ℝ) :=
      Submission.ASP.approx_atil Submission.ASP.FIa Submission.ASP.FIg Submission.ASP.FIr
        Submission.ASP.FIgtil (x : ℝ) (Submission.ASP.FI_approx (x : ℝ))
    have hRemUse : ∀ m : ℕ, m ≤ x →
        Submission.ASP.RemainderSum
          (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
            Submission.ASP.FIa) (Submission.Rcut x) m ≤ Abar * LN ^ (-(3 : ℤ)) := by
      intro m hm
      have h1 := hRemAll x hxr m hm
      have h2 : (Real.log (x : ℝ)) ^ (-(3 : ℝ)) = LN ^ (-(3 : ℤ)) := by
        rw [hLNdef, show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num]
        exact Real.rpow_intCast _ _
      rw [h2] at h1
      exact h1
    have hsupp : ∀ ν : ℕ, ν ∉ Finset.Icc 1 Dn → lam ν = 0 := by
      intro ν hν
      rcases Nat.eq_zero_or_pos ν with h0 | hposν
      · subst h0
        exact hlam_sq 0 (fun h => h.ne_zero rfl)
      · refine hΔsupp ν ?_
        rw [Finset.mem_Icc] at hν
        by_contra hle
        exact hν ⟨hposν, Nat.le_of_not_lt hle⟩
    -- ## 4. the `δ₂`-arithmetic
    have hδ2le : ((d2n : ℕ) : ℝ) ≤ 3 * LN ^ (2 * HasBc.val + 4) := by
      rw [hd2ndef, d2c]
      have h1 : ((⌈2 * (Real.log (x : ℝ)) ^ (2 * HasBc.val + 4)⌉₊ : ℕ) : ℝ)
          < 2 * LN ^ (2 * HasBc.val + 4) + 1 := by
        have := Nat.ceil_lt_add_one
          (show (0 : ℝ) ≤ 2 * (Real.log (x : ℝ)) ^ (2 * HasBc.val + 4) by positivity)
        rw [hLNdef]
        exact this
      have h2 : (1 : ℝ) ≤ LN ^ (2 * HasBc.val + 4) := Real.one_le_rpow hLNone (by linarith)
      linarith
    have hδ2pos : (0 : ℝ) < ((d2n : ℕ) : ℝ) := by
      rw [hd2ndef, d2c]
      exact_mod_cast Nat.ceil_pos.mpr (by positivity)
    have hδ2ge1 : (1 : ℝ) ≤ ((d2n : ℕ) : ℝ) := by
      rw [hd2ndef, d2c]
      exact_mod_cast Nat.ceil_pos.mpr (by positivity)
    have hlogδ2 : Real.log (((d2n : ℕ) : ℝ)) ≤ Real.log 3 + (2 * HasBc.val + 4) * LLN := by
      have h1 := Real.log_le_log hδ2pos hδ2le
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hLNp _)),
        Real.log_rpow hLNp] at h1
      linarith [h1]
    have hthresh : 100 * (Real.log 3 + (2 * HasBc.val + 4) * LLN) ≤ LN := by
      have hLLN_le2 : Real.log 3 ≤ 2 * LLN := by
        have h4 : Real.log 3 ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
          linarith
        linarith [hLLNone]
      have h1 : 100 * (Real.log 3 + (2 * HasBc.val + 4) * LLN)
          ≤ 100 * (2 * LLN + (2 * HasBc.val + 4) * LLN) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hLLN_le2]
      have h2 : 100 * (2 * LLN + (2 * HasBc.val + 4) * LLN) = 100 * (2 * HasBc.val + 6) * LLN := by
        ring
      linarith [h1, h2, hLLNthresh]
    have hδ2eps : ((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ)) ≤ Real.exp 2 :=
      d2c_rpow_eps_le hBpos hLNone hLΔ_low hthresh
    have hMcge1 : (1 : ℝ) ≤ (Mcn : ℝ) := by
      rw [hMcndef, Mc]
      have h1 : (0 : ℝ) < Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (HasBc.val + 2) :=
        mul_pos (Real.sqrt_pos.mpr hxpos) (Real.rpow_pos_of_pos hLNpos _)
      exact_mod_cast Nat.ceil_pos.mpr h1
    have hMcδ2 : Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) ≤ LN := by
      have h1 : (Dn : ℝ) * ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) ≤ (Submission.Rcut x : ℝ) := by
        have h := hc7
        rw [Dc, Work.FITop.Dcut] at h
        exact_mod_cast h
      have h2 : (1 : ℝ) ≤ (Dn : ℝ) := hDn1R
      have h3 : (Submission.Rcut x : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast Submission.Rcut_le_self x
      have h4 : (0 : ℝ) ≤ (Mcn : ℝ) * ((d2n : ℕ) : ℝ) :=
        mul_nonneg (le_trans zero_le_one hMcge1) hδ2pos.le
      have h5 : (Mcn : ℝ) * ((d2n : ℕ) : ℝ) ≤ (x : ℝ) := by nlinarith only [h1, h2, h3, h4]
      calc Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) ≤ Real.log (x : ℝ) :=
            Real.log_le_log (by positivity) h5
        _ = LN := by rw [hLNdef]
    -- ## 5. the `L6` bound
    have hL6mono : Submission.ASP.L6 Submission.ASP.FIgtil x (sr * z) (sr * y)
        ≤ Submission.ASP.L6 Submission.ASP.FIgtil x (sr * (Zn : ℝ)) (sr * y) := by
      refine L6_lo_le (fun n => hgnn n) x ?_
      exact mul_le_mul_of_nonneg_left hz1 hsr_pos.le
    have hL6le : Submission.ASP.L6 Submission.ASP.FIgtil x (sr * (Zn : ℝ)) (sr * y)
        ≤ C6 * (1 + LLN) :=
      hC6le x hx6 (sr * y) (mul_le_mul_of_nonneg_left hy1 hsr_pos.le)
    have hC5pos : 0 ≤ C6 * (1 + LLN) :=
      mul_nonneg hC6pos.le (by linarith)
    -- ## 6. monotonicity of the `z`-dependent hypotheses
    have hΔsz : (Dn : ℝ) < sr * z := by
      have h12 : (Dn : ℝ) < sr * (Zn : ℝ) := hs12
      have hle : sr * (Zn : ℝ) ≤ sr * z := mul_le_mul_of_nonneg_left hz1 hsr_pos.le
      linarith
    have hhypos : 0 < sr * y := mul_pos hsr_pos (lt_of_lt_of_le hYr_pos hy1)
    have hδ2cond : ∀ b c : ℕ, sr * y < (b : ℝ) → sr * z < (c : ℝ) → x / (b * c) ≤ d2n := by
      intro b c hb hc
      have hzn : (0 : ℝ) < z := by
        have h1 : (0 : ℝ) < (Zn : ℝ) := by
          have h0 : (0 : ℕ) < Zn := by omega
          exact_mod_cast h0
        exact lt_of_lt_of_le h1 hz1
      have hsz0 : (0 : ℝ) < sr * z := mul_pos hsr_pos hzn
      have hcb : (0 : ℝ) < (c : ℝ) := lt_of_lt_of_le hsz0 (le_of_lt hc)
      have hb' : sr * Yr < (b : ℝ) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy1 hsr_pos.le) hb
      have hzc_lt : sr * (Zn : ℝ) < (c : ℝ) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz1 hsr_pos.le) hc
      have hb0 : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le hhypos (le_of_lt hb)
      have hZn256 : (256 : ℕ) ≤ Zn := by rw [hZndef]; exact hs1
      have hB0 : (0 : ℝ) < sr * (Zn : ℝ) :=
        mul_pos hsr_pos (by exact_mod_cast (by omega : 0 < Zn))
      have h2a : (sr * Yr) * (sr * (Zn : ℝ)) < (b : ℝ) * (sr * (Zn : ℝ)) :=
        mul_lt_mul_of_pos_right hb' hB0
      have h2b : (b : ℝ) * (sr * (Zn : ℝ)) < (b : ℝ) * (c : ℝ) :=
        mul_lt_mul_of_pos_left hzc_lt hb0
      have h2 : (sr * Yr) * (sr * (Zn : ℝ)) < (b : ℝ) * (c : ℝ) := lt_trans h2a h2b
      have h2c : (sr * Yr) * (sr * (Zn : ℝ)) = sr ^ 2 * Yr * (Zn : ℝ) := by ring
      rw [h2c] at h2
      have h6 : (0 : ℝ) < 2 * LN ^ (2 * HasBc.val + 4) := by positivity
      have h4 : (x : ℝ) < (b : ℝ) * (c : ℝ) * (2 * LN ^ (2 * HasBc.val + 4)) := by
        have h2d : (sr ^ 2 * Yr * (Zn : ℝ)) * (2 * LN ^ (2 * HasBc.val + 4))
            < ((b : ℝ) * (c : ℝ)) * (2 * LN ^ (2 * HasBc.val + 4)) :=
          mul_lt_mul_of_pos_right h2 h6
        have hs13b : (x : ℝ) ≤ 2 * (sr ^ 2 * Yr * (Zn : ℝ) * LN ^ (2 * HasBc.val + 4)) := hs13
        have heq : 2 * (sr ^ 2 * Yr * (Zn : ℝ) * LN ^ (2 * HasBc.val + 4))
            = (sr ^ 2 * Yr * (Zn : ℝ)) * (2 * LN ^ (2 * HasBc.val + 4)) := by ring
        have heq2 : ((b : ℝ) * (c : ℝ)) * (2 * LN ^ (2 * HasBc.val + 4))
            = (b : ℝ) * (c : ℝ) * (2 * LN ^ (2 * HasBc.val + 4)) := by ring
        linarith only [hs13b, h2d, heq, heq2]
      have h9 : (2 * LN ^ (2 * HasBc.val + 4)) ≤ (d2n : ℝ) := by
        rw [hd2ndef, d2c]
        exact Nat.le_ceil _
      have hbcpos : (0 : ℝ) < (b : ℝ) * (c : ℝ) := mul_pos hb0 hcb
      have h10 : (x : ℝ) < (b : ℝ) * (c : ℝ) * (d2n : ℝ) := by nlinarith only [h4, h9, hbcpos]
      have h11 : x < b * c * d2n := by exact_mod_cast h10
      exact Nat.div_le_of_le_mul (le_of_lt h11)
    have hMran : ∀ c ∈ Submission.ASP.cseg x (sr * z) (sr * y), c ≤ Mcn := by
      intro c hc
      rw [Submission.ASP.cseg, Finset.mem_filter, Submission.ASP.seg, Finset.mem_filter] at hc
      obtain ⟨⟨hcIcc, hcgt⟩, hcle⟩ := hc
      have h1 : (c : ℝ) ≤ (x : ℝ) / (sr * y) := hcle
      have h2 : (x : ℝ) / (sr * y) ≤ (x : ℝ) / (sr * Yr) :=
        div_le_div_of_nonneg_left (by positivity) hSrYr_pos
          (mul_le_mul_of_nonneg_left hy1 hsr_pos.le)
      have h3 : (x : ℝ) / (sr * Yr) ≤ (Mcn : ℝ) := hc8
      exact_mod_cast le_trans (le_trans h1 h2) h3
    -- ## 7. the §6 estimate
    have hres := Submission.ASP.S1_bound_of_sieve Work.FIChain.atilc Submission.ASP.FIgtil
      (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil
        Submission.ASP.FIa) lam x (sy := sr * y) (sz := sr * z)
      (δ2 := d2n) (Δ := Dn) (M := Mcn) (D := Submission.Rcut x)
      (Y := max Dn d2n)
      (ε := 1 / Real.log (Dn : ℝ)) (C_sieve := Cs) (C₁ := C1p)
      (C₀ := max Chb 1) (C₅ := C6 * (1 + LLN))
      (fun n => atilc_nonneg n) hrho hhypos hδ2cond
      (fun n hn => atilc_eq_zero_of_not_sqfree hn) hAd hΔN hsupp hΔsz hg1 hgmul
      (fun n => hgnn n) hDn3 hε0 hε1 hεΔ
      (le_max_right _ _) (le_max_left _ _) hC0pos hC0b hC1ppos hCs0.le hprodsubUse hlam_sq hlam_le
      hpos hpos' hMran (by simpa [Dc, Work.FITop.Dcut] using hc7) hC5pos
      (le_trans hL6mono hL6le) hCsie'
    have hAac : Submission.ASP.Acount Work.FIChain.atilc (x : ℝ) = Abar := by
      rw [hAbardef, AcountAtilC, Work.FITop.AcountAtil]
    have hstep : |Submission.ASP.S1 atilc lam x (sr * y) (sr * z)|
        ≤ Abar * (C6 * (1 + LLN))
            * (((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ)) * Cs
                * Real.exp (32 * max Chb 1) * C1p / Real.log (Dn : ℝ))
          + Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)) * (Abar * LN ^ (-(3 : ℤ))) := by
      rw [hAac] at hres
      refine le_trans hres ?_
      refine add_le_add le_rfl ?_
      refine mul_le_mul_of_nonneg_left (hRemUse x le_rfl) ?_
      exact Real.log_nonneg (by nlinarith only [hMcge1, hδ2ge1])
    have hrate := S1_rate_le (Abar := Abar) (LN := LN) (LLN := LLN)
      (LΔ := Real.log (Dn : ℝ)) (C6 := C6) (K₀ := K₀) (C0 := max Chb 1) (C1p := C1p)
      (Cs := Cs) (X := ((d2n : ℕ) : ℝ) ^ (1 / Real.log (Dn : ℝ)))
      (Mδ := Real.log ((Mcn : ℝ) * ((d2n : ℕ) : ℝ)))
      hAbar0 hLNone hLLNone hLΔpos hLΔ_low hC6pos hK₀.le hC0pos.le hC1ppos hCs0.le hCsle
      hδ2eps hMcδ2
    refine le_trans hstep (le_trans hrate (le_of_eq ?_))
    rw [hKdef, s3phiRate, ← hLNdef, ← hLLNdef]
    ring
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨K, x₀, hKpos, hx₀⟩

end

end Work.FIPiChain
