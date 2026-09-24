import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.H1.Defs
import Submission.Work.ChenPlan.H1.isLinear_chenSieve

/-!
# The 2026-09-24 range hypothesis `IsLinearRange` for Chen's sieve

`Submission/ChenPlan/Interfaces.lean` (2026-09-24) requires, besides `IsLinear`, the one-sided
dimension bound on **every sub-range**:

`IsLinearRange s z K := ∀ w z', 2 ≤ w → w < z' → z' ≤ z → ∏_{p ∣ P, w ≤ p < z'} (1-ν p)⁻¹ ≤
  (log z'/log w)(1 + K/log w)`.

This module proves it for the sieve `chenSieve x M` (density `ν p = 1/φ(p) = 1/(p-1)` on the odd
primes below `M`), with the explicit constant `rangeK Z₀`, where `Z₀` is the Mertens threshold of
`Commons.NumberTheory.Sieve.oddEulerProduct_ratio_le_log_p5`.

The proof is the range analogue of `isLinear_chenSieve`:
* write `w` and `z'` as `k = ⌈w⌉`, `K' = ⌈z'⌉`: the sub-range product over `[w, z')` inside `M`
  is exactly `∏_{p ∈ oddLt K', p ≥ k} (1-1/(p-1))⁻¹ = oddProd (k-1)/oddProd (K'-1)`;
* if `z'` is below the Mertens threshold `max Z₀ 5`, the product is a product over a *fixed* finite
  range, bounded crudely by `2^{K'} ≤ 2^{max Z₀ 5}`, which the huge constant `rangeK Z₀` absorbs
  (`log w ≤ log (max Z₀ 5)`, `log z'/log w ≥ 1`);
* if `z' ≥ max Z₀ 5`, use the already-proved ratio bounds `oddProd_ratio_small` /
  `oddProd_ratio_large` (both uniform in the upper limit) with the upper limit `K'`, and convert
  `(log K'/log k)(1 + 100/log k)` into `(log z'/log w)(1 + K/log w)`:
  `log K' ≤ log z' + 1/z'`, `log k ≥ log w`, so `log K'/log k ≤ (log z'/log w)(1+1/log w)`, and
  `(1+1/L)(1+100/L) ≤ 1+K/L` as soon as `L ≥ 0.69` and `K ≥ 246`.

Also here: monotonicity of the two sieve predicates in `K` (`isLinear_mono`, `isLinearRange_mono`),
used to raise the constant of the proved `IsLinear (chenSieve x M) M 100` to `rangeK Z₀`.
-/

open Finset
open scoped BigOperators
open Commons.NumberTheory.Chen.ChenEight
open Commons.NumberTheory.Sieve (oddProd primeProd)

namespace Work.ChenPlan.H1

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The sieve constant good enough for the range hypothesis for `chenSieve`, given the Mertens
threshold `Z₀` of `oddEulerProduct_ratio_le_log_p5`. -/
noncomputable def rangeK (Z₀ : ℕ) : ℝ :=
  (2 : ℝ) ^ (max Z₀ 5 + 1) * (((max Z₀ 5 : ℕ) : ℝ) + 246)

lemma rangeK_pos (Z₀ : ℕ) : 0 < rangeK Z₀ := by
  unfold rangeK; positivity

lemma rangeK_ge (Z₀ : ℕ) : 246 ≤ rangeK Z₀ := by
  unfold rangeK
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (max Z₀ 5 + 1) := one_le_pow₀ (by norm_num)
  have h2 : (246 : ℝ) ≤ ((max Z₀ 5 : ℕ) : ℝ) + 246 := by
    have : (0 : ℝ) ≤ ((max Z₀ 5 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  calc (246 : ℝ) = 1 * 246 := by ring
    _ ≤ (2 : ℝ) ^ (max Z₀ 5 + 1) * (((max Z₀ 5 : ℕ) : ℝ) + 246) :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

lemma rangeK_ge_100 (Z₀ : ℕ) : (100 : ℝ) ≤ rangeK Z₀ :=
  le_trans (by norm_num) (rangeK_ge Z₀)

/-- `2^(max Z₀ 5) ≤ rangeK Z₀ / log (max Z₀ 5)`: the crude constant absorbs the fixed-range bound. -/
lemma rangeK_div_log (Z₀ : ℕ) :
    (2 : ℝ) ^ (max Z₀ 5) ≤ rangeK Z₀ / Real.log ((((max Z₀ 5 : ℕ)) : ℝ)) := by
  have hpos : (0 : ℝ) < ((max Z₀ 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < max Z₀ 5)
  have hlogpos : 0 < Real.log (((max Z₀ 5 : ℕ)) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < max Z₀ 5))
  rw [rangeK, le_div_iff₀ hlogpos]
  have hlogle : Real.log (((max Z₀ 5 : ℕ)) : ℝ) ≤ 2 * (((max Z₀ 5 : ℕ) : ℝ) + 246) := by
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 : (0 : ℝ) ≤ ((max Z₀ 5 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hpow2 : (2 : ℝ) ^ (max Z₀ 5 + 1) = 2 * (2 : ℝ) ^ (max Z₀ 5) := by rw [pow_succ]; ring
  rw [hpow2]
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (max Z₀ 5) := by positivity
  nlinarith [hlogle, hpowpos]

/-- Monotonicity of `IsLinear` in the constant `K`. -/
lemma isLinear_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinear s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinear s z K' := by
  refine ⟨h.1, fun w hw2 hwz => ?_⟩
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 ≤ Real.log z := le_of_lt (Real.log_pos (by linarith))
  calc _ ≤ (Real.log z / Real.log w) * (1 + K / Real.log w) := h.2 w hw2 hwz
    _ ≤ (Real.log z / Real.log w) * (1 + K' / Real.log w) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz (le_of_lt hlogw))
        have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK' (le_of_lt hlogw)
        linarith

/-- Monotonicity of `IsLinearRange` in the constant `K`. -/
lemma isLinearRange_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearRange s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinearRange s z K' := by
  intro w z' hw2 hwz hz'z
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 ≤ Real.log z' := le_of_lt (Real.log_pos (by linarith))
  calc _ ≤ (Real.log z' / Real.log w) * (1 + K / Real.log w) := h w z' hw2 hwz hz'z
    _ ≤ (Real.log z' / Real.log w) * (1 + K' / Real.log w) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz' (le_of_lt hlogw))
        have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK' (le_of_lt hlogw)
        linarith

/-- `log K'/log k ≤ (log z'/log w)(1 + 1/log w)` when `w ≤ k`, `k ≤ K'`, `K' ≤ z'+1`. -/
lemma log_ratio_le {w z' : ℝ} {k K' : ℕ} (hw2 : 2 ≤ w) (hwz : w < z')
    (hk : w ≤ (k : ℝ)) (hkK' : k ≤ K') (hK' : (K' : ℝ) ≤ z' + 1) :
    Real.log (K' : ℝ) / Real.log (k : ℝ) ≤ (Real.log z' / Real.log w) * (1 + 1 / Real.log w) := by
  have hw1 : (1 : ℝ) < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hlogkge : Real.log w ≤ Real.log (k : ℝ) := Real.log_le_log (by linarith) hk
  have hz'pos : (0 : ℝ) < z' := by linarith
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  have hK'pos : (0 : ℝ) < (K' : ℝ) := by
    have h2 : (k : ℝ) ≤ (K' : ℝ) := by exact_mod_cast hkK'
    linarith
  have hlogK' : Real.log (K' : ℝ) ≤ Real.log (z' + 1) := Real.log_le_log hK'pos hK'
  have hlogsucc : Real.log (z' + 1) ≤ Real.log z' + 1/z' := by
    have hsplit : Real.log (z' + 1) = Real.log z' + Real.log (1 + 1/z') := by
      rw [show z' + 1 = z' * (1 + 1/z') by field_simp]
      rw [Real.log_mul (ne_of_gt hz'pos) (by positivity)]
    have hle : Real.log (1 + 1/z') ≤ 1/z' := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1/z' by positivity)
      linarith
    linarith
  have hnum_nonneg : (0 : ℝ) ≤ Real.log z' + 1/z' := by positivity
  have hstep1 : Real.log (K' : ℝ) / Real.log (k : ℝ)
      ≤ (Real.log z' + 1/z') / Real.log (k : ℝ) :=
    div_le_div_of_nonneg_right (le_trans hlogK' hlogsucc) hlogk.le
  have hstep2 : (Real.log z' + 1/z') / Real.log (k : ℝ) ≤ (Real.log z' + 1/z') / Real.log w :=
    div_le_div_of_nonneg_left hnum_nonneg hlogw hlogkge
  have hkey : (1 : ℝ)/z' ≤ Real.log z' / Real.log w := by
    rw [div_le_div_iff₀ hz'pos hlogw]
    have hzlog : Real.log w ≤ z' * Real.log z' := by
      have h1 : Real.log w < Real.log z' := Real.log_lt_log (by linarith) hwz
      have h2 : Real.log z' ≤ z' * Real.log z' := by nlinarith [hlogz', hz'pos]
      linarith
    linarith [hzlog]
  have hstep3 : (Real.log z' + 1/z') / Real.log w
      ≤ (Real.log z' / Real.log w) * (1 + 1/Real.log w) := by
    have hL : (0 : ℝ) < 1/Real.log w := by positivity
    have hmain := mul_le_mul_of_nonneg_right hkey hL.le
    rw [add_div, mul_add, mul_one]
    have heq : (1/z') * (1/Real.log w) = (1/z')/Real.log w := by ring
    rw [← heq]
    linarith [hmain]
  linarith [hstep1, hstep2, hstep3]

/-- `(1 + 1/L)(1 + 100/L) ≤ 1 + K/L` for `L ≥ 0.69` and `K ≥ 246`. -/
lemma one_add_bounds {L K : ℝ} (hL : 0.69 ≤ L) (hK : 246 ≤ K) :
    (1 + 1/L) * (1 + 100/L) ≤ 1 + K/L := by
  have hLpos : 0 < L := by linarith
  have hnum : 101*L + 100 ≤ K*L := by
    have h1 := mul_le_mul hL (by linarith : (145 : ℝ) ≤ K - 101) (by norm_num)
      (by linarith : (0 : ℝ) ≤ L)
    nlinarith [h1]
  have h2 : (0 : ℝ) < L^2 := by positivity
  have h3 : (1 + 1/L) * (1 + 100/L) = 1 + (101*L + 100)/L^2 := by field_simp; ring
  have h4 : (1 : ℝ) + K/L = 1 + (K*L)/L^2 := by field_simp
  rw [h3, h4]
  have := div_le_div_of_nonneg_right hnum h2.le
  linarith

/-- The crude bound of the small-`z'` case: `2^T` is at most the right-hand side. -/
lemma two_pow_le_ratio_mul {w z' : ℝ} {T : ℕ} {K : ℝ}
    (hw2 : 2 ≤ w) (hwz : w < z') (hz'T : z' < (T : ℝ)) (hT2 : 2 ≤ T)
    (hKT : (2 : ℝ)^T ≤ K / Real.log (T : ℝ)) :
    (2 : ℝ)^T ≤ (Real.log z' / Real.log w) * (1 + K / Real.log w) := by
  have hw1 : (1 : ℝ) < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by linarith)
  have hlogwT : Real.log w ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by linarith) (by linarith : w ≤ (T : ℝ))
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < (2 : ℝ)^T := by positivity
    have h2 : (0 : ℝ) < K / Real.log (T : ℝ) := lt_of_lt_of_le h1 hKT
    exact (div_pos_iff_of_pos_right hlogT).mp h2
  have hratio : 1 ≤ Real.log z' / Real.log w := by
    rw [le_div_iff₀ hlogw]
    have := Real.log_lt_log (by linarith : (0 : ℝ) < w) hwz
    linarith
  have h1 : K / Real.log (T : ℝ) ≤ K / Real.log w :=
    div_le_div_of_nonneg_left hKpos.le hlogw hlogwT
  have h2 : K / Real.log w ≤ 1 + K / Real.log w := by
    have : (0 : ℝ) ≤ K / Real.log w := div_nonneg hKpos.le hlogw.le
    linarith
  have h3 : (2 : ℝ)^T ≤ 1 + K/Real.log w := le_trans hKT (le_trans h1 h2)
  have h4 : (0 : ℝ) ≤ 1 + K/Real.log w :=
    le_of_lt (lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ)^T) h3)
  calc (2 : ℝ)^T ≤ 1 + K/Real.log w := h3
    _ = 1 * (1 + K/Real.log w) := by ring
    _ ≤ (Real.log z' / Real.log w) * (1 + K / Real.log w) :=
        mul_le_mul_of_nonneg_right hratio h4

/-- **The range hypothesis `IsLinearRange` for Chen's sieve**, with the Mertens threshold `Z₀` of
`oddEulerProduct_ratio_le_log_p5` and the explicit constant `rangeK Z₀`. -/
theorem isLinearRange_chenSieve (Z₀ : ℕ)
    (hZ₀ : ∀ z : ℕ, Z₀ ≤ z → ∀ p : ℕ, Nat.Prime p → 5 ≤ p → p ≤ z →
      oddProd (p - 1) ≤ (6/5) * (Real.log z / Real.log p) * oddProd z)
    (x M : ℕ) : Submission.ChenPlan.IsLinearRange (chenSieve x M) (M : ℝ) (rangeK Z₀) := by
  intro w z' hw2 hwz hz'M
  rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl, primeFactors_oddPrimLt M]
  have hnu : ∀ p ∈ oddLt M, (chenSieve x M).nu p = 1/((p : ℝ) - 1) := by
    intro p hp
    have hpp : Nat.Prime p := (Submission.mem_oddLt.mp hp).1
    have hp1 : 1 ≤ p := hpp.one_le
    rw [show (chenSieve x M).nu = invTotient from rfl, invTotient_apply, Nat.totient_prime hpp,
        Nat.cast_sub hp1, one_div]
    norm_num
  set k : ℕ := ⌈w⌉₊ with hkdef
  set K' : ℕ := ⌈z'⌉₊ with hK'def
  have hwk : w ≤ (k : ℝ) := by rw [hkdef]; exact Nat.le_ceil w
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ (k : ℝ) := le_trans hw2 hwk
    exact_mod_cast this
  have hkK' : k ≤ K' := by
    rw [hkdef, hK'def]; exact Nat.ceil_mono (le_of_lt hwz)
  have hK'M : K' ≤ M := by rw [hK'def]; exact Nat.ceil_le.mpr hz'M
  have hfilt : (oddLt M).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
      = (oddLt K').filter (fun p : ℕ => k ≤ p) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpM, hwp, hpz⟩
      refine ⟨mem_oddLt_of hpM ?_, ?_⟩
      · rw [hK'def]; exact Nat.lt_ceil.mpr hpz
      · rw [hkdef]; exact Nat.ceil_le.mpr hwp
    · rintro ⟨hpK', hkp⟩
      refine ⟨oddLt_mono hK'M hpK', ?_, ?_⟩
      · exact le_trans hwk (by exact_mod_cast hkp)
      · exact Nat.lt_ceil.mp (by rw [← hK'def]; exact (Submission.mem_oddLt.mp hpK').2.2)
  have hmid : ∏ p ∈ (oddLt M).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
        (1 - (chenSieve x M).nu p)⁻¹
      = ∏ p ∈ (oddLt K').filter (fun p : ℕ => k ≤ p), (1 - 1/((p : ℝ) - 1))⁻¹ := by
    rw [hfilt]
    exact Finset.prod_congr rfl
      (fun p hp => by rw [hnu p (oddLt_mono hK'M (Finset.mem_filter.mp hp).1)])
  by_cases hcase : z' < (((max Z₀ 5 : ℕ)) : ℝ)
  · -- `z'` below the Mertens threshold: the product is over a fixed finite range.
    have hK'T : K' ≤ max Z₀ 5 := by rw [hK'def]; exact Nat.ceil_le.mpr (le_of_lt hcase)
    have hsmall : ∏ p ∈ (oddLt K').filter (fun p : ℕ => k ≤ p), (1 - 1/((p : ℝ) - 1))⁻¹
        ≤ (2 : ℝ)^K' := by
      calc ∏ p ∈ (oddLt K').filter (fun p : ℕ => k ≤ p), (1 - 1/((p : ℝ) - 1))⁻¹
          ≤ ∏ p ∈ (oddLt K').filter (fun p : ℕ => k ≤ p), (2 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro p hp
              have hp3 : 3 ≤ p := (Submission.mem_oddLt.mp (Finset.mem_filter.mp hp).1).2.1
              have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
              have h2 : (0 : ℝ) < 1 - 1/((p : ℝ) - 1) := by
                have h1 : (1 : ℝ)/((p : ℝ) - 1) < 1 := by
                  rw [div_lt_one (by linarith)]; linarith
                linarith
              positivity
            · intro p hp
              have hp3 : 3 ≤ p := (Submission.mem_oddLt.mp (Finset.mem_filter.mp hp).1).2.1
              have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
              have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              have h2 : (0 : ℝ) < 1 - 1/((p : ℝ) - 1) := by
                have h1 : (1 : ℝ)/((p : ℝ) - 1) < 1 := by
                  rw [div_lt_one (by linarith)]; linarith
                linarith
              rw [inv_le_comm₀ h2 (by norm_num : (0 : ℝ) < 2)]
              have h1 : (1 : ℝ)/((p : ℝ) - 1) ≤ 1/2 := by
                rw [div_le_div_iff₀ hpos (by norm_num)]; linarith
              linarith
        _ = (2 : ℝ)^((oddLt K').filter (fun p : ℕ => k ≤ p)).card := by rw [Finset.prod_const]
        _ ≤ (2 : ℝ)^K' := by
            apply pow_le_pow_right₀ (by norm_num)
            calc ((oddLt K').filter (fun p : ℕ => k ≤ p)).card ≤ (oddLt K').card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
              _ ≤ K' := by
                  calc (oddLt K').card ≤ (Finset.range K').card :=
                        Finset.card_le_card (Finset.filter_subset _ _)
                    _ = K' := Finset.card_range K'
    rw [hmid]
    refine le_trans hsmall ?_
    refine le_trans (pow_le_pow_right₀ (by norm_num) hK'T) ?_
    exact two_pow_le_ratio_mul hw2 hwz hcase (by omega) (rangeK_div_log Z₀)
  · -- `z'` above the Mertens threshold: Mertens' ratio bound with upper limit `K'`.
    have hTz : (((max Z₀ 5 : ℕ)) : ℝ) ≤ z' := not_lt.mp hcase
    have hTK' : max Z₀ 5 ≤ K' := by
      rw [hK'def]
      calc max Z₀ 5 = ⌈(((max Z₀ 5 : ℕ)) : ℝ)⌉₊ := (Nat.ceil_natCast (max Z₀ 5)).symm
        _ ≤ ⌈z'⌉₊ := Nat.ceil_mono hTz
    have hZ₀K' : Z₀ ≤ K' := le_trans (le_max_left _ _) hTK'
    have h5K' : 5 ≤ K' := le_trans (le_max_right _ _) hTK'
    have hK'le : (K' : ℝ) ≤ z' + 1 :=
      le_of_lt (by rw [hK'def]; exact Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ z'))
    have hratio : oddProd (k-1)/oddProd (K'-1)
        ≤ (Real.log (K' : ℝ)/Real.log (k : ℝ)) * (1 + 100/Real.log (k : ℝ)) := by
      by_cases hk2049 : k ≤ 2049
      · exact oddProd_ratio_small Z₀ hZ₀ K' k hZ₀K' h5K' hk2 hk2049 hkK'
      · exact oddProd_ratio_large K' k (by omega) hkK'
    have hmid' : ∏ p ∈ (oddLt M).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
          (1 - (chenSieve x M).nu p)⁻¹ = oddProd (k-1)/oddProd (K'-1) := by
      rw [hmid, sieveProd_eq_VsieveOdd_div K' k hk2 hkK',
        ← oddProd_pred_eq_VsieveOdd K' (by omega : 1 ≤ K'),
        ← oddProd_pred_eq_VsieveOdd k (by omega : 1 ≤ k)]
    rw [hmid']
    refine le_trans hratio ?_
    have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
    have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
    have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hlogkge : Real.log w ≤ Real.log (k : ℝ) := Real.log_le_log (by linarith) hwk
    have hlogw69 : 0.69 ≤ Real.log w := by
      have h1 : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw2
      linarith [Real.log_two_gt_d9]
    have hA := log_ratio_le hw2 hwz hwk hkK' hK'le
    have hB : (1 + 100/Real.log (k : ℝ)) ≤ (1 + 100/Real.log w) := by
      have h1 : 100/Real.log (k : ℝ) ≤ 100/Real.log w :=
        div_le_div_of_nonneg_left (by norm_num) hlogw hlogkge
      linarith
    have hC := one_add_bounds hlogw69 (rangeK_ge Z₀)
    calc (Real.log (K' : ℝ)/Real.log (k : ℝ)) * (1 + 100/Real.log (k : ℝ))
        ≤ ((Real.log z'/Real.log w) * (1 + 1/Real.log w)) * (1 + 100/Real.log w) := by
          apply mul_le_mul hA hB ?_ ?_
          · have : (0 : ℝ) ≤ 100/Real.log (k : ℝ) := div_nonneg (by norm_num) hlogk.le
            linarith
          · exact mul_nonneg (div_nonneg hlogz'.le hlogw.le) (by positivity)
      _ = (Real.log z'/Real.log w) * ((1 + 1/Real.log w) * (1 + 100/Real.log w)) := by ring
      _ ≤ (Real.log z'/Real.log w) * (1 + rangeK Z₀/Real.log w) :=
          mul_le_mul_of_nonneg_left hC (div_nonneg hlogz'.le hlogw.le)

end

end Work.ChenPlan.H1
