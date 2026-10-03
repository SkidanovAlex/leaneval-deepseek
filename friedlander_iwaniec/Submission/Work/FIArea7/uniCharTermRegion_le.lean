import Mathlib
import Submission.Work.FIArea7.Area7Char6
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The complex norm of a mode weight `1/|k|` of the (17.10) expansion, written as a quotient in
`ℂ`.  (Local copy of the helper of `WUniOmega6Pull6CharLow_le`, which is not imported here.) -/
lemma norm_one_div_abs_cast' (k : ℤ) :
    ‖(1 : ℂ) / (((|(k : ℝ)| : ℝ)) : ℂ)‖ = 1 / ((|k| : ℤ) : ℝ) := by
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_abs, ← Int.cast_abs]

/-- **The per-`(b,e)` bound on the mode of region I of the (17.10) main term.**  If the §16
coefficient sums satisfy `‖S^k_χ(β')‖ ≤ c₁N^{1-δ₁}` for every modulus `Q` with `Q(|k|+1) ≤ N^{δ₁}`
(FI Proposition 17.2), then for every pair with `1 ≤ b`, `1 ≤ e` and `4be(2K+1) ≤ N^{δ₁}` — so that
the hypothesis applies to every mode `k = 0` and `k ∈ evenFreq K` — one has

  `‖uniCharTerm Pa b e β K ε‖ ≤ (1/b)·H_K·√(4be)·(c₁²N^{2-2δ₁})`,

where `H_K = 2log2 + log4 + Σ_{k ∈ evenFreq K} 1/|k|` is the mode weight of `logFac6Series`.

SUGGESTED ROUTE: copy the `hmode` / `hmain` / `hterm` blocks of the already compiled
`Submission/Work/FIArea7/WUniOmega6Pull6CharLow_le.lean` (same imports), which prove exactly this
with `1/b` replaced by the weaker `1`; then use `|μ(b)| ≤ 1` and `b ≥ 1` for the sharper `1/b`.
Concretely: `hmode` gives `‖uniModeCharSum Pa b e β k ε‖ ≤ √(4be)·(c₁²N^{2-2δ₁})` for every `k` with
`4be(|k|+1) ≤ N^{δ₁}` (from `sum_norm_uniJChar_le` + `norm_inv_card_mul_sum_chi_le` + `hhyp`;
for `k = 0` and `k ∈ evenFreq K` this follows from `hreg`), and `hmain` sums the mode weight. -/
theorem uniCharTermRegion_le (Pa : Work.FITop.Params) (K : ℕ) (β : GaussianInt → ℂ)
    (ε : GaussianInt → ℤ) (δ₁ c₁ : ℝ) (hδ : 0 < δ₁) (hc : 0 < c₁)
    (hhyp : ∀ (Q : ℕ) [NeZero Q] (k : ℤ)
      (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ),
        (Q : ℝ) * (|(k : ℝ)| + 1) ≤ Pa.N ^ δ₁ →
        ‖Work.FIArea7.uniSChar Pa Q ε β k χ‖ ≤ c₁ * Pa.N ^ (1 - δ₁))
    {b e : ℕ} (hb : 1 ≤ b) (he : 1 ≤ e)
    (hreg : 4 * (b:ℝ) * (e:ℝ) * (2*(K:ℝ)+1) ≤ Pa.N ^ δ₁) :
    ‖Work.FIArea7.uniCharTerm Pa b e β K ε‖
      ≤ (1/(b:ℝ)) * (2*Real.log 2 + Real.log 4 + ∑ k ∈ Work.FIArea7.evenFreq K, (1/((|k|:ℤ):ℝ)))
          * Real.sqrt (4*(b:ℝ)*(e:ℝ)) * (c₁^2 * Pa.N ^ (2 - 2*δ₁)) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one hN1
  have hsq : (c₁ * Pa.N ^ (1 - δ₁)) ^ 2 = c₁ ^ 2 * Pa.N ^ (2 - 2 * δ₁) := by
    have h1 : (Pa.N ^ (1 - δ₁)) ^ 2 = Pa.N ^ (2 - 2 * δ₁) := by
      rw [pow_two, ← Real.rpow_add hNpos]
      congr 1
      ring
    rw [mul_pow, h1]
  have hb0 : 0 < b := by omega
  have he0 : 0 < e := by omega
  have hbe0 : 4 * b * e ≠ 0 := by
    have : (0 : ℕ) < 4 * b * e := Nat.mul_pos (Nat.mul_pos (by norm_num) hb0) he0
    omega
  haveI hQ : NeZero (4 * b * e) := ⟨hbe0⟩
  have hcast : ((4 * b * e : ℕ) : ℝ) = 4 * (b : ℝ) * (e : ℝ) := by push_cast; ring
  set M : ℝ := Real.sqrt (4 * (b : ℝ) * (e : ℝ)) * (c₁ ^ 2 * Pa.N ^ (2 - 2 * δ₁)) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  -- the per-mode bound: the L1-mass of the omega-weights times c₁² N^(2-2δ₁)
  have hmode : ∀ k : ℤ, ((4 * b * e : ℕ) : ℝ) * (|(k : ℝ)| + 1) ≤ Pa.N ^ δ₁ →
      ‖Work.FIArea7.uniModeCharSum Pa b e β k ε‖ ≤ M := by
    intro k hkr
    have hJ : ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
        ‖Work.FIArea7.uniJChar (4 * b * e) e χ‖
        ≤ (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ)
          * Real.sqrt (4 * (b : ℝ) * (e : ℝ)) := by
      have h := Work.FIArea7.sum_norm_uniJChar_le (4 * b * e) e
      rwa [hcast] at h
    have hS : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
        ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ ≤ c₁ * Pa.N ^ (1 - δ₁) :=
      fun χ => hhyp (4 * b * e) k χ hkr
    have hB0 : (0 : ℝ) ≤ c₁ * Pa.N ^ (1 - δ₁) :=
      mul_nonneg (le_of_lt hc) (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hm := Work.FIArea7.norm_inv_card_mul_sum_chi_le
      (G := Work.FIArea7.GaussUnit (4 * b * e))
      (Work.FIArea7.uniJChar (4 * b * e) e)
      (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k) hB0 hJ hS
    have hm' : ‖Work.FIArea7.uniModeCharSum Pa b e β k ε‖
        ≤ Real.sqrt (4 * (b : ℝ) * (e : ℝ)) * (c₁ ^ 2 * Pa.N ^ (2 - 2 * δ₁)) := by
      simpa only [Work.FIArea7.uniModeCharSum, hsq] using hm
    rwa [hM]
  -- the zero mode: 4be * (0+1) ≤ 4be(2K+1) ≤ N^δ₁
  have hk0 : ‖Work.FIArea7.uniModeCharSum Pa b e β 0 ε‖ ≤ M := by
    refine hmode 0 ?_
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have h2K : (1 : ℝ) ≤ 2 * (K : ℝ) + 1 := by linarith
    have h4be0 : (0 : ℝ) ≤ 4 * (b : ℝ) * (e : ℝ) := by positivity
    have hprod := mul_le_mul_of_nonneg_left h2K h4be0
    simp only [Int.cast_zero, abs_zero, zero_add, mul_one]
    rw [hcast]
    linarith
  -- the non-zero modes: |k| ≤ 2K, so 4be(|k|+1) ≤ 4be(2K+1) ≤ N^δ₁
  have hkK : ∀ k ∈ Work.FIArea7.evenFreq K,
      ‖Work.FIArea7.uniModeCharSum Pa b e β k ε‖ ≤ M := by
    intro k hk
    refine hmode k ?_
    have hIcc : k ∈ Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ)) := by
      rw [Work.FIArea7.evenFreq] at hk; exact (Finset.mem_filter.mp hk).1
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hIcc
    have h2 : |k| ≤ 2 * (K : ℤ) := abs_le.mpr ⟨hk1, hk2⟩
    have h3 : |(k : ℝ)| ≤ 2 * (K : ℝ) := by
      have h4 : ((|k| : ℤ) : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast h2
      rwa [Int.cast_abs] at h4
    have h5 : |(k : ℝ)| + 1 ≤ 2 * (K : ℝ) + 1 := by linarith
    have h4be0 : (0 : ℝ) ≤ 4 * (b : ℝ) * (e : ℝ) := by positivity
    have hprod := mul_le_mul_of_nonneg_left h5 h4be0
    rw [hcast]
    linarith
  -- the norm of the whole mode expansion
  have hmain : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β 0 ε
        + ∑ k ∈ Work.FIArea7.evenFreq K,
            (1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β k ε‖
      ≤ (2 * Real.log 2 + Real.log 4 + ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ))) * M := by
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β 0 ε‖
        ≤ (2 * Real.log 2 + Real.log 4) * M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hk0 (by positivity)
    have h2 : ‖∑ k ∈ Work.FIArea7.evenFreq K,
          (1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β k ε‖
        ≤ (∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ))) * M := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ k ∈ Work.FIArea7.evenFreq K,
            ‖(1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β k ε‖
          ≤ ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ)) * M := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            rw [norm_mul, norm_one_div_abs_cast']
            exact mul_le_mul_of_nonneg_left (hkK k hk) (by positivity)
        _ = (∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ))) * M := by rw [Finset.sum_mul]
    linarith [h1, h2]
  -- unfold the (17.10) term
  have hunfold : Work.FIArea7.uniCharTerm Pa b e β K ε
      = (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
        ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β 0 ε
          + ∑ k ∈ Work.FIArea7.evenFreq K,
              (1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa b e β k ε) := by
    rw [Work.FIArea7.uniCharTerm, dif_neg hbe0]
  rw [hunfold, norm_mul]
  -- the Möbius weight: |μ(b)|/b ≤ 1/b
  have hmu : ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (b : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ))]
    have h1 : |((ArithmeticFunction.moebius b : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
    calc |((ArithmeticFunction.moebius b : ℤ) : ℝ)| / (b : ℝ) ≤ 1 / (b : ℝ) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = 1 / (b : ℝ) := rfl
  refine le_trans (mul_le_mul hmu hmain (norm_nonneg _) (by positivity)) (le_of_eq ?_)
  rw [hM]
  ring

end

end Work.FIArea7
