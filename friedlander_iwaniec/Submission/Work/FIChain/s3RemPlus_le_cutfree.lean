import Mathlib
import Submission.Work.FIChain.s3RemPlus_cutfree_defs
import Submission.Work.FIChain.remainder_all_at_07
import Submission.Work.FIChain.S3plusC_aux2
import Submission.Work.FIChain.s3SplitDefs
import Submission.Work.FIChain.cfPairs_le
import Submission.Work.FIChain.cfRsum_le

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The sieve weight of the outer `ℓ`-sum in `s3RemPlus` is bounded by `τ(ℓ)²`: the Möbius sum
runs over a *subset* of the divisors of `ℓ` and `|ρ(ℓ)| ≤ τ(ℓ)`. -/
lemma cfWeight_abs_le (lam : ℕ → ℝ) (sy : ℝ) (ℓ : ℕ)
    (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) :
    |(∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ|
      ≤ ((ℓ.divisors.card : ℝ)) ^ 2 := by
  have hμ : |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
      (ArithmeticFunction.moebius b : ℝ)| ≤ ((ℓ.divisors.card : ℝ)) := by
    calc |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)|
        ≤ ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            |(ArithmeticFunction.moebius b : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), (1 : ℝ) := by
          refine Finset.sum_le_sum (fun b _ => ?_)
          rcases ArithmeticFunction.moebius_eq_or b with h | h | h <;> simp [h]
      _ = (((ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ))).card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ((ℓ.divisors.card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hρ : |Submission.ASP.rhoOf lam ℓ| ≤ ((ℓ.divisors.card : ℕ) : ℝ) :=
    abs_rhoOf_le_card lam hlam ℓ
  rw [abs_mul]
  calc |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)| * |Submission.ASP.rhoOf lam ℓ|
      ≤ ((ℓ.divisors.card : ℝ)) * ((ℓ.divisors.card : ℝ)) :=
        mul_le_mul hμ hρ (abs_nonneg _) (by positivity)
    _ = ((ℓ.divisors.card : ℝ)) ^ 2 := by ring

/-- **An interval integral of a function vanishing below `1` over a reversed interval is `0`.**
If `U < 1` and `f` vanishes on `(-∞,1)`, then `∫_1^U f = 0` (the interval of integration lies
below `1` up to a null set). -/
lemma intervalIntegral_eq_zero_of_forall_lt_one (f : ℝ → ℝ) {U : ℝ} (hU : U < 1)
    (h : ∀ u, u < 1 → f u = 0) : ∫ u in (1 : ℝ)..U, f u = 0 := by
  rw [intervalIntegral.integral_symm]
  simp only [neg_eq_zero]
  refine intervalIntegral.integral_zero_ae ?_
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun u hu => ?_) (measure_singleton (1 : ℝ))
  simp only [Set.mem_setOf_eq] at hu
  push_neg at hu
  rcases Set.mem_uIoc.mp hu.1 with ⟨-, hu1⟩ | ⟨h1u, huU⟩
  · rw [Set.mem_singleton_iff]
    by_contra hne
    exact hu.2 (h u (lt_of_le_of_ne hu1 hne))
  · exact absurd (lt_of_lt_of_le h1u huU) (not_lt.mpr (le_of_lt hU))

/-- `Σ_{ℓ ∣ ζ} τ(ℓ)² ≤ τ(ζ)^5`. -/
lemma sum_divisors_card_sq_le (ζ : ℕ) :
    (∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2) ≤ ((ζ.divisors.card : ℝ)) ^ 5 := by
  have h := Submission.ASP.sum_divisors_card_pow_le 2 ζ
  have h35 : ((ζ.divisors.card : ℝ)) ^ 3 ≤ ((ζ.divisors.card : ℝ)) ^ 5 := by
    rcases Nat.eq_zero_or_pos ζ.divisors.card with h0 | hpos
    · rw [h0]; norm_num
    · exact pow_le_pow_right₀ (by exact_mod_cast hpos) (by norm_num)
  calc (∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2)
      = (((∑ ℓ ∈ ζ.divisors, (ℓ.divisors.card) ^ 2) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl (fun ℓ _ => (Nat.cast_pow _ _).symm)
    _ ≤ ((ζ.divisors.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
    _ = ((ζ.divisors.card : ℝ)) ^ 3 := by rw [Nat.cast_pow]
    _ ≤ ((ζ.divisors.card : ℝ)) ^ 5 := h35

/-- Pointwise fibre bound, self-contained version. -/
lemma cf_fibre_le_self :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ Cm : ℕ, ∀ t : ℝ,
      (1 : ℝ) ≤ (Cm : ℝ) → (x : ℝ) ^ ((3 : ℝ) / 10) ≤ (Cm : ℝ) →
      t ∈ Set.Icc (Cm : ℝ) (x : ℝ) →
      ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 * |cfT x Cm ℓ t|
        ≤ 2 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨Xr, hr⟩ := cfRsum_le
  refine ⟨max Xr 1, fun x hx Cm t hCm1 hCm3 ht => ?_⟩
  have hxr : Xr ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by linarith
  have htx : t ≤ (x : ℝ) := ht.2
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by linarith [hCm1] : (0 : ℝ) < (Cm : ℝ)) ht.1
  have hNx : ⌊t / (Cm : ℝ)⌋₊ ≤ x := by
    have h1 : t / (Cm : ℝ) ≤ (x : ℝ) := by
      rw [div_le_iff₀ hCmpos]; nlinarith [htx, hCm1]
    calc ⌊t / (Cm : ℝ)⌋₊ ≤ ⌊(x : ℝ)⌋₊ := Nat.floor_mono h1
      _ = x := Nat.floor_natCast x
  have hNM : ⌊t / (Cm : ℝ)⌋₊ ≤ ⌊(x : ℝ) / (Cm : ℝ)⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right htx hCmpos.le)
  have hxrpow : (x : ℝ) / (Cm : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
    rw [div_le_iff₀ hCmpos]
    calc (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ = (x : ℝ) ^ ((7 : ℝ) / 10 + (3 : ℝ) / 10) := by norm_num
      _ = (x : ℝ) ^ ((7 : ℝ) / 10) * (x : ℝ) ^ ((3 : ℝ) / 10) := Real.rpow_add hxpos _ _
      _ ≤ (x : ℝ) ^ ((7 : ℝ) / 10) * (Cm : ℝ) :=
          mul_le_mul_of_nonneg_left hCm3 (Real.rpow_nonneg hxpos.le _)
  have hN7 : ⌊t / (Cm : ℝ)⌋₊ ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
    have h1 : ((⌊t / (Cm : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) := by
      have h2 : ((⌊t / (Cm : ℝ)⌋₊ : ℕ) : ℝ) ≤ t / (Cm : ℝ) :=
        Nat.floor_le (le_of_lt (div_pos ht0 hCmpos))
      have h3 : t / (Cm : ℝ) ≤ (x : ℝ) / (Cm : ℝ) := by gcongr
      linarith [h2, h3, hxrpow]
    exact_mod_cast le_trans h1 (Nat.le_ceil _)
  have hfloor_t : ⌊t⌋₊ ≤ x := by
    calc ⌊t⌋₊ ≤ ⌊(x : ℝ)⌋₊ := Nat.floor_mono htx
      _ = x := Nat.floor_natCast x
  have hA : ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 * |cfT x Cm ℓ t|
      ≤ ∑ ℓ ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
          (if ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
            (|cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊|) else 0) := by
    refine Finset.sum_le_sum (fun ℓ _ => ?_)
    have h1 : |cfT x Cm ℓ t| ≤ ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
        (if (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) ≤ t then
          |cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊| else 0) := by
      rw [cfT]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun d _ => ?_))
      by_cases hc : (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) ≤ t
      · rw [if_pos hc, if_pos hc, abs_mul]
        calc |(ArithmeticFunction.moebius d : ℝ)| * |cfR (ℓ * d) x - cfR (ℓ * d) ⌊t⌋₊|
            ≤ 1 * (|cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊|) :=
              mul_le_mul (by rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h])
                (by rw [sub_eq_add_neg]; exact le_trans (abs_add_le _ _) (by rw [abs_neg]))
                (abs_nonneg _) (by norm_num)
          _ = |cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊| := one_mul _
      · rw [if_neg hc, if_neg hc, abs_zero]
    have h2 : ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
        (if (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) ≤ t then
          |cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊| else 0)
        ≤ ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
          (if ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ then
            |cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊| else 0) := by
      refine Finset.sum_le_sum (fun d _ => ?_)
      have he : ((ℓ * d : ℕ) : ℝ) * (Cm : ℝ) = (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) := by
        push_cast; ring
      by_cases hc : (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) ≤ t
      · have hld : ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ := by
          apply Nat.le_floor
          rw [le_div_iff₀ hCmpos]
          rw [he]; exact hc
        rw [if_pos hc, if_pos hld]
      · have hnot : ¬ ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ := by
          intro hld
          apply hc
          have hle : ((ℓ * d : ℕ) : ℝ) ≤ t / (Cm : ℝ) := by
            have h1 : ((ℓ * d : ℕ) : ℝ) ≤ ((⌊t / (Cm : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hld
            have h2 : ((⌊t / (Cm : ℝ)⌋₊ : ℕ) : ℝ) ≤ t / (Cm : ℝ) :=
        Nat.floor_le (le_of_lt (div_pos ht0 hCmpos))
            linarith
          have hmul := mul_le_mul_of_nonneg_right hle hCmpos.le
          rw [div_mul_cancel₀ _ hCmpos.ne'] at hmul
          rw [he] at hmul
          exact hmul
        rw [if_neg hc, if_neg hnot]
    calc ((ℓ.divisors.card : ℝ)) ^ 2 * |cfT x Cm ℓ t|
        ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
            (if ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ then |cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊| else 0)) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
      _ = ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
            (if ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
              (|cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊|) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          split_ifs with h <;> ring
  have hB : ∑ ℓ ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
          (if ℓ * d ≤ ⌊t / (Cm : ℝ)⌋₊ then ((ℓ.divisors.card : ℝ)) ^ 2 *
            (|cfR (ℓ * d) x| + |cfR (ℓ * d) ⌊t⌋₊|) else 0)
      ≤ ∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, (∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2) *
          (|cfR ζ x| + |cfR ζ ⌊t⌋₊|) := by
    have hpair := cfPairs_le x ⌊(x : ℝ) / (Cm : ℝ)⌋₊ ⌊t / (Cm : ℝ)⌋₊
      (fun ℓ => ((ℓ.divisors.card : ℝ)) ^ 2) (fun ζ => |cfR ζ x| + |cfR ζ ⌊t⌋₊|)
      (fun n => by positivity) (fun n => by positivity) hNM hNx
    rw [Finset.sum_product] at hpair
    exact hpair
  have hC : ∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, (∑ ℓ ∈ ζ.divisors, ((ℓ.divisors.card : ℝ)) ^ 2) *
          (|cfR ζ x| + |cfR ζ ⌊t⌋₊|)
      ≤ ∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, ((ζ.divisors.card : ℝ)) ^ 5 *
          (|cfR ζ x| + |cfR ζ ⌊t⌋₊|) := by
    refine Finset.sum_le_sum (fun ζ _ => mul_le_mul_of_nonneg_right (sum_divisors_card_sq_le ζ) ?_)
    positivity
  have hD : ∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, ((ζ.divisors.card : ℝ)) ^ 5 *
          (|cfR ζ x| + |cfR ζ ⌊t⌋₊|)
      ≤ 2 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
    have hsplit : ∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, ((ζ.divisors.card : ℝ)) ^ 5 *
          (|cfR ζ x| + |cfR ζ ⌊t⌋₊|)
        = (∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ x|)
          + (∑ ζ ∈ Finset.Icc 1 ⌊t / (Cm : ℝ)⌋₊, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ ⌊t⌋₊|) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ζ _ => mul_add _ _ _)
    rw [hsplit]
    have h1 := hr x hxr ⌊t / (Cm : ℝ)⌋₊ x hN7 le_rfl
    have h2 := hr x hxr ⌊t / (Cm : ℝ)⌋₊ ⌊t⌋₊ hN7 hfloor_t
    linarith
  exact le_trans hA (le_trans hB (le_trans hC hD))
end

end Work.FIChain
