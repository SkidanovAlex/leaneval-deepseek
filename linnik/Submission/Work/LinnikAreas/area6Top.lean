import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec

/-!
# The top-level argument of AREA 6: from `ExpansionInput` + `BoxSumBound` to `Area6`

`Siegel.area6_of` and its two ingredients (`vmClassSum_eq_prime_add_nonPrime`,
`prime_of_classSum_pos`) are extracted from `LinnikAreas/area6.lean` into this module so that the
capped assembly (`LinnikAreas/area6CapChain.lean`) can import them without the cycle
`area6 → area6Chain → area6Final → area6Sound → area6`: `area6.lean` imports this file, so every
name here is also visible to any file importing `area6`. -/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option linter.unusedVariables false

namespace Siegel

open Work.LinnikContract

/-- The von Mangoldt class sum splits into its prime and non-prime parts. -/
theorem vmClassSum_eq_prime_add_nonPrime (q : ℕ) [NeZero q] (L K : ℝ) (a : ℕ) :
    primeClassSum q L K a + nonPrimeClassSum q L K a = vmClassSum q L K a := by
  simp only [primeClassSum, nonPrimeClassSum, vmClassSum]
  exact Finset.sum_filter_add_sum_filter_not _ (fun n : ℕ => n.Prime) _

/-- **Prime extraction** (HB §13, step 1 of the Siegel case): a positive weighted *prime* class
sum exhibits a prime `p ≡ a (q)` with `p ≤ q^L`.  (Same content as
`Work.LinnikAreas.siegelPrimeExtract`; reproved here so that this module is self-contained, since
that lemma's file imports this one.) -/
theorem prime_of_classSum_pos {q : ℕ} [NeZero q] {L K : ℝ} {a : ℕ}
    (h : 0 < primeClassSum q L K a) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ (q : ℝ) ^ L := by
  rw [primeClassSum] at h
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  obtain ⟨hpS, hpprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpIcc, hpmod⟩ := Finset.mem_filter.mp hpS
  have hple : p ≤ classLimit q L := (Finset.mem_Icc.mp hpIcc).2
  refine ⟨p, hpprime, hpmod, ?_⟩
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hlim : (classLimit q L : ℝ) ≤ (q : ℝ) ^ L := by
    rw [classLimit]
    exact Nat.floor_le (Real.rpow_nonneg hqnonneg L)
  have hp' : (p : ℝ) ≤ (classLimit q L : ℝ) := by exact_mod_cast hple
  linarith

/-- **The assembly of AREA 6 in the Siegel case.**  The class-sum expansion (S4) with the
Siegel-case zero-sum bound (S5) -- which is what the repulsion (S1), the `λ₁`-saving density
estimate (S2) and the simplicity of the exceptional zero (S3) deliver -- give Area 6, via Siegel's
theorem (`lamOf_lower_bound`) to dominate the polynomial error by `λ₁`.

Concretely, with `𝓛 = log q`, `λ = lamOf q β₁`, `V = signedBoxSumAll q L K R a + farZeroSum q L K R`
and `S = primeClassSum q L K a`:

* (S4) gives `S ≥ 𝓛·(φ(q)⁻¹(K² - V) - q⁻²)`;
* (S5) gives `V ≤ K²(1 - a₀λ/2)`, i.e. `K² - V ≥ K²a₀λ/2`;
* `λ ≥ C log q/√q` (Siegel) and `φ(q) ≤ q` make `𝓛·φ(q)⁻¹K²a₀λ/2 > 𝓛·q⁻²` for `q ≥ q₀`;

so `S > 0`, and `prime_of_classSum_pos` produces the prime. -/
theorem area6_of (R : ℝ) (hExp : ExpansionInput R) (hBox : BoxSumBound R) :
    Work.LinnikContract.Area6 := by
  obtain ⟨lamS, hlamS0, hlamSle, q₀B, hB⟩ := hBox
  obtain ⟨q₀E, hE⟩ := hExp
  obtain ⟨C, hCpos, hC⟩ := lamOf_lower_bound
  -- the constant `D = C·K²·a₀/2` of the closing inequality
  set D : ℝ := C * ((3 / 10 : ℝ) ^ 2 * (49 / 10) / 2) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hK2a : (0 : ℝ) < (3 / 10 : ℝ) ^ 2 * (49 / 10) / 2 := by norm_num
  refine ⟨lamS, hlamS0, max (max q₀E q₀B) (max 3 (⌊1 / D ^ 2⌋₊ + 1)), ?_⟩
  intro q hq hqne hSz a ha
  haveI := hqne
  obtain ⟨χ₁, hχ1, hsq, β₁, hβ1, hz, hle⟩ := hSz
  have hSz' : SiegelZero q lamS := ⟨χ₁, hχ1, hsq, β₁, hβ1, hz, hle⟩
  have hq2 : 2 ≤ q := two_le_level hSz'
  have hqE : q₀E ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqB : q₀B ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqthr : ⌊1 / D ^ 2⌋₊ + 1 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  -- inputs
  have hexp := hE q hqE a ha
  have hbox := hB q hqB χ₁ β₁ hχ1 hsq hβ1 hz hle a ha
  have hlow := hC q hq2 χ₁ β₁ hχ1 hsq hβ1 hz
  have hlam0 : 0 < lamOf q (β₁ : ℂ) := lamOf_pos hχ1 hβ1 hz
  -- notation
  set lam : ℝ := lamOf q (β₁ : ℂ) with hlam
  have hlampos : 0 < lam := by rw [hlam]; exact hlam0
  set V : ℝ := signedBoxSumAll q (11 / 2) (3 / 10) R a + farZeroSum q (11 / 2) (3 / 10) R with hV
  set S : ℝ := primeClassSum q (11 / 2) (3 / 10) a with hS
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hphipos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hphile : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hfar_nonneg : 0 ≤ farZeroSum q (11 / 2) (3 / 10) R := by
    rw [farZeroSum]
    refine Finset.sum_nonneg fun χ _ => ?_
    refine tsum_nonneg fun ρ => ?_
    split_ifs with h
    · exact le_rfl
    · exact mul_nonneg (by positivity) (norm_nonneg _)
  -- (S4) specialised: `𝓛·φ(q)⁻¹(K² - V) - 𝓛·q⁻² ≤ S`
  have hS4 : Real.log q * ((q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - V)) - Real.log q * (1 / (q : ℝ) ^ 2) ≤ S := by
    have h2 := (abs_le.mp hexp).1
    have h3 : (Real.log q)⁻¹ * S - (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - V) ≥ -(1 / (q : ℝ) ^ 2) := by
      have h4 : (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - (V - farZeroSum q (11 / 2) (3 / 10) R))
          = (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - signedBoxSumAll q (11 / 2) (3 / 10) R a) := by
        rw [hV]; ring
      have h5 : -(1 / (q : ℝ) ^ 2 + (q.totient : ℝ)⁻¹ * farZeroSum q (11 / 2) (3 / 10) R)
          ≤ -(1 / (q : ℝ) ^ 2) := by
        have h6 : 0 ≤ (q.totient : ℝ)⁻¹ * farZeroSum q (11 / 2) (3 / 10) R :=
          mul_nonneg (inv_nonneg.mpr hphipos.le) hfar_nonneg
        linarith
      linarith [h2, h4, h5]
    have h7 := mul_le_mul_of_nonneg_left h3 hlogpos.le
    have h8 : Real.log q * ((Real.log q)⁻¹ * S) = S := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlogpos), one_mul]
    linarith [h7, h8]
  -- (S5) specialised: `K²a₀λ/2 ≤ K² - V`
  have hS5 : (3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2) ≤ (3 / 10 : ℝ) ^ 2 - V := by
    rw [hV]
    nlinarith [hbox]
  -- the closing inequality `𝓛/q² < 𝓛·φ(q)⁻¹K²a₀λ/2`
  have hQK : (3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2)
      = ((3 / 10 : ℝ) ^ 2 * (49 / 10) / 2) * lam := by ring
  have hclose : Real.log q * (1 / (q : ℝ) ^ 2)
      < Real.log q * ((q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2))) := by
    have hsqrtq_pos : (0 : ℝ) < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
    -- the threshold `1 < D·√q`
    have hthr : (1 / D ^ 2 : ℝ) < (q : ℝ) := by
      have h0 : (1 / D ^ 2 : ℝ) < ((⌊(1 / D ^ 2)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h1 : ((⌊1 / D ^ 2⌋₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
        exact_mod_cast hqthr
      linarith
    have hsqrtgt : 1 / D < Real.sqrt (q : ℝ) := by
      have h3 : Real.sqrt (1 / D ^ 2) < Real.sqrt (q : ℝ) := Real.sqrt_lt_sqrt (by positivity) hthr
      have h4 : Real.sqrt (1 / D ^ 2) = 1 / D := by
        have h5 : (1 / D) ^ 2 = 1 / D ^ 2 := by ring
        rw [← h5, Real.sqrt_sq (by positivity)]
      linarith
    have hDsqrt : 1 < D * Real.sqrt (q : ℝ) := by
      have h6 := mul_lt_mul_of_pos_left hsqrtgt hDpos
      have h7 : D * (1 / D) = 1 := by field_simp
      linarith [h6, h7]
    -- `1 ≤ log q`
    have hlog1 : 1 ≤ Real.log q := by
      have h8 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      have h9 : (1 : ℝ) < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr h8
      have h10 : Real.log 3 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
      linarith
    -- `C/√q ≤ λ`
    have hClam : C / Real.sqrt (q : ℝ) ≤ lam := by
      have h11 : C / Real.sqrt (q : ℝ) ≤ C * Real.log q / Real.sqrt (q : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith [hCpos, hlog1]) hsqrtq_pos.le
      rw [hlam]
      exact le_trans h11 hlow
    -- `1/q² < D/(q√q)`
    have h14 : 1 / (q : ℝ) ^ 2 < D / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
      have hq2pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      have hden : (0 : ℝ) < (q : ℝ) * Real.sqrt (q : ℝ) := by positivity
      rw [lt_div_iff₀ hden]
      have h15 : (1 / (q : ℝ) ^ 2) * ((q : ℝ) * Real.sqrt (q : ℝ)) = Real.sqrt (q : ℝ) / (q : ℝ) := by
        field_simp
      rw [h15]
      rw [div_lt_iff₀ hqpos]
      have h18 := mul_lt_mul_of_pos_right hDsqrt hsqrtq_pos
      have h19 : D * Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = D * (q : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt hqpos.le]
      linarith [h18, h19]

    -- `D/(q√q) ≤ φ(q)⁻¹·K²a₀λ/2`
    have h20 : D / ((q : ℝ) * Real.sqrt (q : ℝ))
        ≤ (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2)) := by
      have h21 : D / ((q : ℝ) * Real.sqrt (q : ℝ))
          = (q : ℝ)⁻¹ * (D / Real.sqrt (q : ℝ)) := by ring
      have h22 : D / Real.sqrt (q : ℝ) ≤ ((3 / 10 : ℝ) ^ 2 * (49 / 10) / 2) * lam := by
        have h23 : D / Real.sqrt (q : ℝ) = ((3 / 10 : ℝ) ^ 2 * (49 / 10) / 2) * (C / Real.sqrt (q : ℝ)) := by
          rw [hD]; ring
        rw [h23]
        exact mul_le_mul_of_nonneg_left hClam (by norm_num)
      have h24 : (q : ℝ)⁻¹ * (D / Real.sqrt (q : ℝ))
          ≤ (q : ℝ)⁻¹ * (((3 / 10 : ℝ) ^ 2 * (49 / 10) / 2) * lam) :=
        mul_le_mul_of_nonneg_left h22 (by positivity)
      have h25 : ((3 / 10 : ℝ) ^ 2 * (49 / 10) / 2) * lam
          = (3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2) := by ring
      rw [h25] at h24
      have h26 : (q : ℝ)⁻¹ ≤ (q.totient : ℝ)⁻¹ := inv_anti₀ hphipos hphile
      have h27 : (0 : ℝ) ≤ (3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2) :=
        mul_nonneg (by norm_num) (by nlinarith [hlampos])
      rw [h21]
      exact le_trans h24 (mul_le_mul_of_nonneg_right h26 h27)
    exact mul_lt_mul_of_pos_left (lt_of_lt_of_le h14 h20) hlogpos
  -- conclusion
  have hK2lam : Real.log q * ((q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2)))
      ≤ Real.log q * ((q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - V)) := by
    have h25 : (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 * ((49 / 10) * lam / 2))
        ≤ (q.totient : ℝ)⁻¹ * ((3 / 10 : ℝ) ^ 2 - V) :=
      mul_le_mul_of_nonneg_left hS5 (inv_nonneg.mpr hphipos.le)
    exact mul_le_mul_of_nonneg_left h25 hlogpos.le
  have hSpos : 0 < S := by linarith [hS4, hK2lam, hclose]
  rw [hS] at hSpos
  exact prime_of_classSum_pos hSpos

/- The box part of HB §§13--14 (`norm_char_apply_eq_one` … `siegel_close_arith`) now lives in
`Submission.Work.LinnikAreas.area6Box`, so that the capped assembly
(`LinnikAreas/boxSumCap.lean`) and this file can both use it. -/

end Siegel

end

end Work.LinnikAreas
