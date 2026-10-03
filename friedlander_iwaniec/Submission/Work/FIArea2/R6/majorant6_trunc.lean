import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea2.R6.Cutoffs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open scoped BigOperators

noncomputable section

/-!
# `Work.FIArea2.R6.majorant6_trunc`

`Work.FITop4.IsMajorant6 Pa f` supplies a `C⁴` interpolant `F₀` of the sequence `f` together with
the *fixed* absolute derivative constants `|F₀^{(j)}| ≤ cMaj j · Pa.M^{-j}` (`j ≤ 4`) and the
support condition `f n ≠ 0 → Pa.M/4 ≤ n ≤ 4·Pa.M` on the integers.  It does **not** say anything
about `F₀` off the integers.

Multiplying `F₀` by the annulus cutoff `χ` of `Submission.Work.FIArea2.R6.Cutoffs6`
(`χ = 1` on `[Pa.M/4, 4·Pa.M]`, `χ = 0` off `[Pa.M/8, 8·Pa.M]`, with
`|χ^{(j)}| ≤ 10^{11}·Pa.M^{-j}`) keeps the trace `f` on `ℤ`, makes the product compactly supported
inside `[Pa.M/8, 8·Pa.M] ⊆ [Pa.M/64, 64·Pa.M]`, and costs only an absolute constant in the
derivative bounds: the Leibniz rule turns the two factorwise bounds
`10^{11}·M^{-i}` and `cMaj (j-i)·M^{-(j-i)}` into `16·10^{11}·K·M^{-j}` per term, with
`K = Σ_{k ≤ 4} cMaj k`, so that `Cder = 80·10^{11}·K + 1` works uniformly.
-/

/-- The sum of the fixed majorant derivative constants `cMaj 0, …, cMaj 4`. -/
private def cMajSum : ℝ := ∑ i ∈ Finset.range 5, Work.FITop4.cMaj i

private lemma cMaj_nonneg (k : ℕ) : 0 ≤ Work.FITop4.cMaj k := by
  rw [Work.FITop4.cMaj]
  split <;> positivity

private lemma cMajSum_nonneg : 0 ≤ cMajSum := by
  rw [cMajSum]
  exact Finset.sum_nonneg fun i _ => cMaj_nonneg i

private lemma cMaj_le_cMajSum (k : ℕ) (hk : k ≤ 4) : Work.FITop4.cMaj k ≤ cMajSum := by
  rw [cMajSum]
  exact Finset.single_le_sum (fun i _ => cMaj_nonneg i) (Finset.mem_range.mpr (by omega))

private lemma one_le_cMajSum : (1 : ℝ) ≤ cMajSum := by
  have h0 : Work.FITop4.cMaj 0 = 1 := by
    rw [Work.FITop4.cMaj]; norm_num
  calc (1 : ℝ) = Work.FITop4.cMaj 0 := h0.symm
    _ ≤ cMajSum := cMaj_le_cMajSum 0 (by norm_num)

theorem majorant6_trunc :
    ∃ Cder : ℝ, 0 < Cder ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ),
      Work.FITop4.IsMajorant6 Pa f →
      ∃ F : ℝ → ℝ, ContDiff ℝ 4 F ∧ HasCompactSupport F ∧
        (∀ n : ℤ, F (n : ℝ) = f n) ∧
        (∀ u : ℝ, F u ≠ 0 → Pa.M / 64 ≤ u ∧ u ≤ 64 * Pa.M) ∧
        (∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Cder * Pa.M ^ (-(j : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hcut⟩ := exists_cutoffs6
  refine ⟨80 * C₀ * cMajSum + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < cMajSum := lt_of_lt_of_le zero_lt_one one_le_cMajSum
    positivity
  · intro Pa f hf
    obtain ⟨F₀, hF₀cd, hF₀eq, hF₀der⟩ := hf.1
    have hf_supp : ∀ u : ℤ, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M := hf.2.2.2.2
    have hM1 : (1 : ℝ) ≤ Pa.M := Pa.hM1
    have hMpos : (0 : ℝ) < Pa.M := lt_of_lt_of_le zero_lt_one hM1
    obtain ⟨χ, ψ, hχcd, hχcs, -, -, -, -, hχeq1, hχsupp, -, -, hχder, -⟩ := hcut Pa.M hM1
    refine ⟨χ * F₀, hχcd.mul hF₀cd, hχcs.mul_right, ?_, ?_, ?_⟩
    · -- agreement with `f` at the integers
      intro n
      change χ (n : ℝ) * F₀ (n : ℝ) = f n
      rw [hF₀eq n]
      by_cases hn : f n = 0
      · rw [hn, mul_zero]
      · rw [hχeq1 (n : ℝ) (hf_supp n hn).1 (hf_supp n hn).2, one_mul]
    · -- support inside the ratio-`64` window
      intro u hu
      change χ u * F₀ u ≠ 0 at hu
      have hne : χ u ≠ 0 := fun h0 => hu (by rw [h0, zero_mul])
      obtain ⟨hb1, hb2⟩ := hχsupp u hne
      constructor <;> linarith
    · -- the four derivative bounds, by the Leibniz rule
      intro j hj u
      have hmul := iteratedDeriv_mul (n := j) (f := χ) (g := F₀) (x := u)
        (hχcd.contDiffAt.of_le (by exact_mod_cast hj))
        (hF₀cd.contDiffAt.of_le (by exact_mod_cast hj))
      rw [hmul]
      have hbound : ∀ i ∈ Finset.range (j + 1),
          |(j.choose i : ℝ) * iteratedDeriv i χ u * iteratedDeriv (j - i) F₀ u|
            ≤ 16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ)) := by
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hi4 : i ≤ 4 := le_trans hij hj
        have hji4 : j - i ≤ 4 := by omega
        have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
        have hA := hχder i hi4 u
        have hB := hF₀der (j - i) hji4 u
        have hKcm : Work.FITop4.cMaj (j - i) ≤ cMajSum := cMaj_le_cMajSum _ hji4
        have hpow_i : 0 ≤ Pa.M ^ (-(i : ℝ)) := Real.rpow_nonneg hMpos.le _
        have hpow_ji : 0 ≤ Pa.M ^ (-((j - i : ℕ) : ℝ)) := Real.rpow_nonneg hMpos.le _
        have hpow_j : 0 ≤ Pa.M ^ (-(j : ℝ)) := Real.rpow_nonneg hMpos.le _
        have hpow_eq :
            Pa.M ^ (-(i : ℝ)) * Pa.M ^ (-((j - i : ℕ) : ℝ)) = Pa.M ^ (-(j : ℝ)) := by
          rw [← Real.rpow_add hMpos]
          congr 1
          rw [Nat.cast_sub hij]
          ring
        have hc16 : (j.choose i : ℝ) ≤ 16 := by
          have h1 : j.choose i ≤ 2 ^ j := Nat.choose_le_two_pow j i
          have h2 : (2 : ℕ) ^ j ≤ 16 := by
            calc (2 : ℕ) ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj
              _ = 16 := by norm_num
          exact_mod_cast le_trans h1 h2
        calc |(j.choose i : ℝ) * iteratedDeriv i χ u * iteratedDeriv (j - i) F₀ u|
            = (j.choose i : ℝ) * |iteratedDeriv i χ u| * |iteratedDeriv (j - i) F₀ u| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hc]
          _ ≤ (j.choose i : ℝ) * (C₀ * Pa.M ^ (-(i : ℝ)))
                * (cMajSum * Pa.M ^ (-((j - i : ℕ) : ℝ))) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hA hc) ?_ (abs_nonneg _) ?_
              · calc |iteratedDeriv (j - i) F₀ u|
                    ≤ Work.FITop4.cMaj (j - i) * Pa.M ^ (-((j - i : ℕ) : ℝ)) := hB
                  _ ≤ cMajSum * Pa.M ^ (-((j - i : ℕ) : ℝ)) :=
                      mul_le_mul_of_nonneg_right hKcm hpow_ji
              · exact mul_nonneg hc (mul_nonneg hC₀pos.le hpow_i)
          _ = (j.choose i : ℝ) * C₀ * cMajSum * Pa.M ^ (-(j : ℝ)) := by
              rw [← hpow_eq]; ring
          _ ≤ 16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ hpow_j
              have h1 : (j.choose i : ℝ) * C₀ ≤ 16 * C₀ :=
                mul_le_mul_of_nonneg_right hc16 hC₀pos.le
              calc (j.choose i : ℝ) * C₀ * cMajSum ≤ (16 * C₀) * cMajSum :=
                    mul_le_mul_of_nonneg_right h1 cMajSum_nonneg
                _ = 16 * C₀ * cMajSum := by ring
      calc |∑ i ∈ Finset.range (j + 1),
              (j.choose i : ℝ) * iteratedDeriv i χ u * iteratedDeriv (j - i) F₀ u|
          ≤ ∑ i ∈ Finset.range (j + 1),
              |(j.choose i : ℝ) * iteratedDeriv i χ u * iteratedDeriv (j - i) F₀ u| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (j + 1), (16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ))) :=
            Finset.sum_le_sum hbound
        _ = ((j : ℝ) + 1) * (16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ (80 * C₀ * cMajSum + 1) * Pa.M ^ (-(j : ℝ)) := by
            have hw : 0 ≤ Pa.M ^ (-(j : ℝ)) := Real.rpow_nonneg hMpos.le _
            have hj5 : ((j : ℝ) + 1) ≤ 5 := by
              have h4 : (j : ℝ) ≤ 4 := by exact_mod_cast hj
              linarith
            have hc0 : 0 ≤ 16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ)) :=
              mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) cMajSum_nonneg) hw
            calc ((j : ℝ) + 1) * (16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ)))
                ≤ 5 * (16 * C₀ * cMajSum * Pa.M ^ (-(j : ℝ))) :=
                  mul_le_mul_of_nonneg_right hj5 hc0
              _ = (80 * C₀ * cMajSum) * Pa.M ^ (-(j : ℝ)) := by ring
              _ ≤ (80 * C₀ * cMajSum + 1) * Pa.M ^ (-(j : ℝ)) :=
                  mul_le_mul_of_nonneg_right (by linarith) hw

end

end Work.FIArea2.R6
