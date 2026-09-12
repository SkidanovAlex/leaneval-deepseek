import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.EstimateLib

/-!
# Truncated second moment for a spread weight function

This is the core estimate (12) of Mossel--Niles-Weed--Sun--Zadik, "A Bayesian proof of the
spread lemma".  Everything is self-contained.
-/

open scoped BigOperators
open Classical

namespace Submission
namespace TruncMom

universe u
variable {X : Type u} [Fintype X]

/-- shadow mass. -/
noncomputable def sh (w : Set X → ℝ) (T : Set X) : ℝ :=
  ∑ E : Set X, if T ⊆ E then w E else 0

/-- the truncation condition on cardinalities: `ℓ` above the cutoff relative to `n`. -/
noncomputable def condN (n ℓ : ℕ) : Prop :=
  ((ℓ : ℝ) > ((2 : ℝ) ^ 9)⁻¹ * (n : ℝ))

/-- the truncation condition: `|T|` above the cutoff relative to `|A|`. -/
noncomputable def condC (A T : Set X) : Prop := condN A.ncard T.ncard

/-- a single term of the inner double-sum over `(T, A0)` with `T = A ∩ A0`. -/
noncomputable def iterm (w : Set X → ℝ) (q : ℝ) (A T A0 : Set X) : ℝ :=
  if (T ⊆ A ∧ A ∩ A0 = T) then
    if condC A T then w A0 * (q ^ T.ncard)⁻¹ else 0
  else 0

/-- delta-sum at `U` with an extra subset condition. -/
lemma sum_delta_subset (A U : Set X) (hUA : U ⊆ A) (f : Set X → ℝ) :
    (∑ T : Set X, if (T ⊆ A ∧ T = U) then f T else 0) = f U := by
  have hpoint : ∀ T : Set X, (if (T ⊆ A ∧ T = U) then f T else 0) = (if T = U then f T else 0) := by
    intro T
    by_cases hT : T = U
    · have hTA : T ⊆ A := by
        rw [hT]
        exact hUA
      rw [if_pos ⟨hTA, hT⟩, if_pos hT]
    · have hneg : ¬ (T ⊆ A ∧ T = U) := fun hc => hT hc.2
      rw [if_neg hneg, if_neg hT]
  calc
    (∑ T : Set X, if (T ⊆ A ∧ T = U) then f T else 0)
        = (∑ T : Set X, if T = U then f T else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact hpoint T
    _ = f U := by simp

/-- each `A0`-summand expands to the sum over `T = A ∩ A0`. -/
lemma expand_A0 (w : Set X → ℝ) (q : ℝ) (A A0 : Set X) :
    (∑ T : Set X, iterm w q A T A0)
      = (if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0) := by
  have hUA : (A ∩ A0) ⊆ A := Set.inter_subset_left (s := A) (t := A0)
  have hiff : ∀ T : Set X, (T ⊆ A ∧ A ∩ A0 = T) ↔ (T ⊆ A ∧ T = A ∩ A0) := by
    intro T
    constructor
    · intro h; exact ⟨h.1, h.2.symm⟩
    · intro h; exact ⟨h.1, h.2.symm⟩
  calc
    (∑ T : Set X, iterm w q A T A0)
        = (∑ T : Set X, if (T ⊆ A ∧ T = A ∩ A0) then
            if condC A T then w A0 * (q ^ T.ncard)⁻¹ else 0
          else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          unfold iterm
          by_cases hp : T ⊆ A ∧ A ∩ A0 = T
          · have hq : T ⊆ A ∧ T = A ∩ A0 := (hiff T).1 hp
            rw [if_pos hp, if_pos hq]
          · have hq : ¬ (T ⊆ A ∧ T = A ∩ A0) := fun hq => hp ((hiff T).2 hq)
            rw [if_neg hp, if_neg hq]
    _ = (if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0) := by
          let f : Set X → ℝ := fun T => if condC A T then w A0 * (q ^ T.ncard)⁻¹ else 0
          have hsum : (∑ T : Set X, if (T ⊆ A ∧ T = A ∩ A0) then f T else 0) = f (A ∩ A0) := by
            exact sum_delta_subset A (A ∩ A0) hUA f
          calc
            (∑ T : Set X, if (T ⊆ A ∧ T = A ∩ A0) then
                if condC A T then w A0 * (q ^ T.ncard)⁻¹ else 0
              else 0)
                = (∑ T : Set X, if (T ⊆ A ∧ T = A ∩ A0) then f T else 0) := by
                  apply Finset.sum_congr rfl
                  intro T hT
                  rfl
            _ = f (A ∩ A0) := hsum
            _ = (if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0) := by
                  rfl

/-- the inner sum over `A0` equals the double sum over `(T, A0)`. -/
lemma inner_eq_Tsum (w : Set X → ℝ) (q : ℝ) (A : Set X) :
    (∑ A0 : Set X,
        if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0)
      = ∑ T : Set X, ∑ A0 : Set X, iterm w q A T A0 := by
  calc
    (∑ A0 : Set X,
        if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0)
        = ∑ A0 : Set X, (∑ T : Set X, iterm w q A T A0) := by
          apply Finset.sum_congr rfl
          intro A0 hA0
          exact (expand_A0 w q A A0).symm
    _ = ∑ T : Set X, ∑ A0 : Set X, iterm w q A T A0 := by
          rw [Finset.sum_comm]

/-- the mass of sets whose intersection with `A` equals `T` is at most the shadow of `T`. -/
lemma sumA0_le_shadow (w : Set X → ℝ) (hw0 : ∀ S, 0 ≤ w S) (T A : Set X) :
    (∑ A0 : Set X, if A ∩ A0 = T then w A0 else 0) ≤ sh w T := by
  apply Finset.sum_le_sum
  intro A0 hA0
  by_cases hT : A ∩ A0 = T
  · have hsub : T ⊆ A0 := by
      rw [← hT]
      exact Set.inter_subset_right (s := A) (t := A0)
    simp [hT, hsub]
  · by_cases hTA0 : T ⊆ A0
    · simp [hT, hTA0, hw0 A0]
    · simp [hT, hTA0]

/-- pointwise: for fixed `T` the `A0`-sum is bounded by the shadow-based term. -/
lemma pt_inner_le (w : Set X → ℝ) (q : ℝ) (A T : Set X)
    (hw0 : ∀ S : Set X, 0 ≤ w S) (hq0 : 0 < q) :
    (∑ A0 : Set X, iterm w q A T A0)
      ≤ (if T ⊆ A then
          if condC A T then (q ^ T.ncard)⁻¹ * sh w T else 0
        else 0) := by
  by_cases hTA : T ⊆ A
  · by_cases hc : condC A T
    · have hsumA0 : (∑ A0 : Set X, iterm w q A T A0)
          = (q ^ T.ncard)⁻¹ * (∑ A0 : Set X, if A ∩ A0 = T then w A0 else 0) := by
            calc
              (∑ A0 : Set X, iterm w q A T A0)
                  = (∑ A0 : Set X, if A ∩ A0 = T then w A0 * (q ^ T.ncard)⁻¹ else 0) := by
                    apply Finset.sum_congr rfl
                    intro A0 hA0'
                    unfold iterm
                    by_cases h : A ∩ A0 = T
                    · rw [if_pos ⟨hTA, h⟩, if_pos h]
                      rw [if_pos hc]
                    · have hneg : ¬ (T ⊆ A ∧ A ∩ A0 = T) := fun hc2 => h hc2.2
                      rw [if_neg hneg, if_neg h]
              _ = (q ^ T.ncard)⁻¹ * (∑ A0 : Set X, if A ∩ A0 = T then w A0 else 0) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro A0 hA0'
                    by_cases h : A ∩ A0 = T
                    · simp [h]
                      ring
                    · simp [h]
      have hqinv : 0 ≤ (q ^ T.ncard)⁻¹ := by
        exact inv_nonneg.mpr (pow_nonneg hq0.le _)
      calc
        (∑ A0 : Set X, iterm w q A T A0)
            = (q ^ T.ncard)⁻¹ * (∑ A0 : Set X, if A ∩ A0 = T then w A0 else 0) := hsumA0
        _ ≤ (q ^ T.ncard)⁻¹ * sh w T := by
              exact mul_le_mul_of_nonneg_left (sumA0_le_shadow w hw0 T A) hqinv
        _ = (if T ⊆ A then
              if condC A T then (q ^ T.ncard)⁻¹ * sh w T else 0
            else 0) := by
              rw [if_pos hTA, if_pos hc]
    · have hz : (∑ A0 : Set X, iterm w q A T A0) = 0 := by
        apply Finset.sum_eq_zero
        intro A0 hA0'
        unfold iterm
        by_cases h : T ⊆ A ∧ A ∩ A0 = T
        · rw [if_pos h]
          rw [if_neg hc]
        · rw [if_neg h]
      calc
        (∑ A0 : Set X, iterm w q A T A0) = 0 := hz
        _ ≤ (if T ⊆ A then
              if condC A T then (q ^ T.ncard)⁻¹ * sh w T else 0
            else 0) := by
              rw [if_pos hTA, if_neg hc]
  · have hz : (∑ A0 : Set X, iterm w q A T A0) = 0 := by
      apply Finset.sum_eq_zero
      intro A0 hA0'
      unfold iterm
      rw [if_neg (fun hc => hTA hc.1)]
    calc
      (∑ A0 : Set X, iterm w q A T A0) = 0 := hz
      _ ≤ (if T ⊆ A then
            if condC A T then (q ^ T.ncard)⁻¹ * sh w T else 0
          else 0) := by
            rw [if_neg hTA]

/-- pointwise: shadow-based term ≤ spread-based term. -/
lemma pt_shadow_le (w : Set X → ℝ) (q δ0 : ℝ) (A T : Set X)
    (hsp : ∀ T : Set X, sh w T ≤ δ0 ^ T.ncard) (hq0 : 0 < q) :
    (if T ⊆ A then
        if condC A T then (q ^ T.ncard)⁻¹ * sh w T else 0
      else 0)
      ≤ (if T ⊆ A then
          if condC A T then (δ0 / q) ^ T.ncard else 0
        else 0) := by
  by_cases hTA : T ⊆ A
  · by_cases hc : condC A T
    · have hqinv : 0 ≤ (q ^ T.ncard)⁻¹ := by
        exact inv_nonneg.mpr (pow_nonneg hq0.le _)
      have hprod : (q ^ T.ncard)⁻¹ * δ0 ^ T.ncard = (δ0 / q) ^ T.ncard := by
        rw [div_pow]
        rw [div_eq_mul_inv]
        ring
      rw [if_pos hTA, if_pos hc, if_pos hTA, if_pos hc]
      calc
        (q ^ T.ncard)⁻¹ * sh w T ≤ (q ^ T.ncard)⁻¹ * δ0 ^ T.ncard := by
          exact mul_le_mul_of_nonneg_left (hsp T) hqinv
        _ = (δ0 / q) ^ T.ncard := hprod
    · rw [if_pos hTA, if_neg hc, if_pos hTA, if_neg hc]
  · rw [if_neg hTA, if_neg hTA]

/-- count of subsets of `A` of cardinality `ℓ` equals a binomial coefficient. -/
lemma count_choose (A : Set X) (ℓ : ℕ) :
    (∑ T : Set X, if T ⊆ A ∧ T.ncard = ℓ then (1 : ℝ) else 0) = (A.ncard.choose ℓ : ℝ) := by
  let B : Set (Set X) := {T : Set X | T ⊆ A ∧ T.ncard = ℓ}
  have hBfin : B.Finite := by
    exact Set.toFinite B
  have hcardB : B.ncard = A.ncard.choose ℓ := by
    exact Set.ncard_powerset_ncard (Set.toFinite A) ℓ
  have hmem : ∀ T : Set X, (T ⊆ A ∧ T.ncard = ℓ) ↔ T ∈ B := by
    intro T
    rfl
  calc
    (∑ T : Set X, if T ⊆ A ∧ T.ncard = ℓ then (1 : ℝ) else 0)
        = (∑ T : Set X, if T ∈ B then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          by_cases h : T ⊆ A ∧ T.ncard = ℓ
          · have hB : T ∈ B := (hmem T).1 h
            simp [h, hB]
          · have hB : T ∉ B := fun hb => h ((hmem T).2 hb)
            simp [h, hB]
    _ = (B.ncard : ℝ) := by
          calc
            (∑ T : Set X, if T ∈ B then (1 : ℝ) else 0)
                = ∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T : Set X => T ∈ B), (1 : ℝ) := by
                  rw [Finset.sum_filter]
            _ = ∑ T ∈ hBfin.toFinset, (1 : ℝ) := by
                  apply Finset.sum_congr
                  · ext T
                    simp [(hmem T).symm]
                  · intro T hT
                    rfl
            _ = (hBfin.toFinset.card : ℝ) := by simp
            _ = (B.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card B hBfin]
    _ = (A.ncard.choose ℓ : ℝ) := by rw [hcardB]

/-- for each `T`, the sum over `ℓ` of the ℓ-indexed term picks `ℓ = T.ncard`. -/
lemma sum_Icc_delta (A T : Set X) (f : ℕ → ℝ) :
    (∑ ℓ ∈ Finset.Icc 0 (A.ncard), if T ⊆ A ∧ T.ncard = ℓ then f ℓ else 0)
      = if T ⊆ A then f (T.ncard) else 0 := by
  by_cases hTA : T ⊆ A
  · have hn : T.ncard ≤ A.ncard := Set.ncard_le_ncard hTA (Set.toFinite A)
    have hmemℓ : T.ncard ∈ Finset.Icc 0 (A.ncard) := by
      simp [hn]
    calc
      (∑ ℓ ∈ Finset.Icc 0 (A.ncard), if T ⊆ A ∧ T.ncard = ℓ then f ℓ else 0)
          = (∑ ℓ ∈ Finset.Icc 0 (A.ncard), if T.ncard = ℓ then f ℓ else 0) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            by_cases h : T.ncard = ℓ
            · rw [if_pos ⟨hTA, h⟩, if_pos h]
            · rw [if_neg (fun hc => h hc.2), if_neg h]
      _ = f (T.ncard) := by
            simp [hmemℓ]
      _ = if T ⊆ A then f (T.ncard) else 0 := by simp [hTA]
  · have hz : (∑ ℓ ∈ Finset.Icc 0 (A.ncard), if T ⊆ A ∧ T.ncard = ℓ then f ℓ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      rw [if_neg (fun hc => hTA hc.1)]
    calc
      (∑ ℓ ∈ Finset.Icc 0 (A.ncard), if T ⊆ A ∧ T.ncard = ℓ then f ℓ else 0) = 0 := hz
      _ = if T ⊆ A then f (T.ncard) else 0 := by simp [hTA]

/-- regroup a sum over subsets of `A` by cardinality. -/
lemma sum_subset_eq (A : Set X) (f : ℕ → ℝ) :
    (∑ T : Set X, if T ⊆ A then f (T.ncard) else 0)
      = ∑ ℓ ∈ Finset.Icc 0 (A.ncard),
          f ℓ * (∑ T : Set X, if T ⊆ A ∧ T.ncard = ℓ then (1 : ℝ) else 0) := by
  calc
    (∑ T : Set X, if T ⊆ A then f (T.ncard) else 0)
        = ∑ T : Set X, (∑ ℓ ∈ Finset.Icc 0 (A.ncard), if T ⊆ A ∧ T.ncard = ℓ then f ℓ else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact (sum_Icc_delta A T f).symm
    _ = ∑ ℓ ∈ Finset.Icc 0 (A.ncard), ∑ T : Set X, if T ⊆ A ∧ T.ncard = ℓ then f ℓ else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ Finset.Icc 0 (A.ncard),
          f ℓ * (∑ T : Set X, if T ⊆ A ∧ T.ncard = ℓ then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T hT
          by_cases h : T ⊆ A ∧ T.ncard = ℓ
          · rw [if_pos h, if_pos h]
            ring
          · rw [if_neg h, if_neg h]
            ring


/-- inner sum bounded by the spread-based sum over subsets of `A`. -/
lemma inner_le_spread (w : Set X → ℝ) (q δ0 : ℝ) (A : Set X)
    (hw0 : ∀ S : Set X, 0 ≤ w S) (hq0 : 0 < q)
    (hsp : ∀ T : Set X, sh w T ≤ δ0 ^ T.ncard) :
    (∑ A0 : Set X,
        if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0)
      ≤ ∑ T : Set X, (if T ⊆ A then
          if condC A T then (δ0 / q) ^ T.ncard else 0
        else 0) := by
  calc
    (∑ A0 : Set X,
        if condC A (A ∩ A0) then w A0 * (q ^ (A ∩ A0).ncard)⁻¹ else 0)
        = ∑ T : Set X, ∑ A0 : Set X, iterm w q A T A0 := inner_eq_Tsum w q A
    _ ≤ ∑ T : Set X, (if T ⊆ A then
          if condC A T then (q ^ T.ncard)⁻¹ * sh w T else 0
        else 0) := by
          apply Finset.sum_le_sum
          intro T hT
          exact pt_inner_le w q A T hw0 hq0
    _ ≤ ∑ T : Set X, (if T ⊆ A then
          if condC A T then (δ0 / q) ^ T.ncard else 0
        else 0) := by
          apply Finset.sum_le_sum
          intro T hT
          exact pt_shadow_le w q δ0 A T hsp hq0

/-- `δ0 / q ≤ 2^-27` from `q ≥ 2^27 · δ0`. -/
lemma ratio_le (δ0 q : ℝ) (hq0 : 0 < q) (hδ0 : 0 < δ0)
    (hB : (2^27 : ℝ) * δ0 ≤ q) : δ0 / q ≤ ((2 : ℝ)^27)⁻¹ := by
  have h2 : 0 < (2 : ℝ)^27 := by positivity
  have hB' : (2 : ℝ)^27 * (δ0 / q) ≤ 1 := by
    calc
      (2 : ℝ)^27 * (δ0 / q) = ((2 : ℝ)^27 * δ0) / q := by ring
      _ ≤ q / q := by gcongr
      _ = 1 := by field_simp [ne_of_gt hq0]
  calc
    δ0 / q = ((2 : ℝ)^27)⁻¹ * ((2 : ℝ)^27 * (δ0 / q)) := by
      field_simp [ne_of_gt h2]
    _ ≤ ((2 : ℝ)^27)⁻¹ * 1 := by
      exact mul_le_mul_of_nonneg_left hB' (inv_nonneg.mpr h2.le)
    _ = ((2 : ℝ)^27)⁻¹ := by simp

/-- a single term of the regrouped sum (binomial count times `(δ0/q)^ℓ`) is ≤ `ρ^ℓ`. -/
lemma term_le (n ℓ : ℕ) (δ0 q : ℝ) (hℓ0 : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (hq0 : 0 < q) (hδ0 : 0 < δ0)
    (hB : (2^27 : ℝ) * δ0 ≤ q)
    (hc : (ℓ : ℝ) > ((2 : ℝ)^9)⁻¹ * (n : ℝ)) :
    (n.choose ℓ : ℝ) * (δ0 / q) ^ ℓ ≤ (3 * ((2 : ℝ) ^ 18)⁻¹) ^ ℓ := by
  have hr0 : 0 ≤ δ0 / q := le_of_lt (div_pos hδ0 hq0)
  have hc0 := Submission.Est.choose_le_three_pow_div (n := n) (ℓ := ℓ) hℓ0 hℓn
  have hrpow : 0 ≤ (δ0 / q) ^ ℓ := pow_nonneg hr0 ℓ
  have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hℓ0)
  have hα0 : 0 < (2 : ℝ)^9 := by norm_num
  have hαne : (2 : ℝ)^9 ≠ 0 := ne_of_gt hα0
  have hcond' : (n : ℝ) < (2 : ℝ)^9 * (ℓ : ℝ) := by
    calc
      (n : ℝ) = ((2 : ℝ)^9 * ((2 : ℝ)^9)⁻¹) * (n : ℝ) := by
        field_simp [hαne]
      _ = (2 : ℝ)^9 * (((2 : ℝ)^9)⁻¹ * (n : ℝ)) := by ring
      _ < (2 : ℝ)^9 * (ℓ : ℝ) := by
        exact mul_lt_mul_of_pos_left hc hα0
  have hdiv : (n : ℝ) / (ℓ : ℝ) ≤ (2 : ℝ)^9 := by
    exact le_of_lt ((div_lt_iff₀ hℓpos).2 hcond')
  have hδq : δ0 / q ≤ ((2 : ℝ)^27)⁻¹ := ratio_le δ0 q hq0 hδ0 hB
  have hb : 3 * (n : ℝ) * (δ0 / q) / (ℓ : ℝ) ≤ 3 * ((2 : ℝ)^18)⁻¹ := by
    have hb0 : 3 * (n : ℝ) * (δ0 / q) / (ℓ : ℝ) ≤ 3 * (2 : ℝ)^9 * (δ0 / q) := by
      calc
        3 * (n : ℝ) * (δ0 / q) / (ℓ : ℝ) = (3 * (δ0 / q)) * ((n : ℝ) / (ℓ : ℝ)) := by ring
        _ ≤ (3 * (δ0 / q)) * (2 : ℝ)^9 := by
          exact mul_le_mul_of_nonneg_left hdiv (by nlinarith [hr0])
        _ = 3 * (2 : ℝ)^9 * (δ0 / q) := by ring
    calc
      3 * (n : ℝ) * (δ0 / q) / (ℓ : ℝ) ≤ 3 * (2 : ℝ)^9 * (δ0 / q) := hb0
      _ ≤ 3 * (2 : ℝ)^9 * ((2 : ℝ)^27)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hδq (by nlinarith)
      _ = 3 * ((2 : ℝ)^18)⁻¹ := by norm_num
  have hb0pos : 0 ≤ 3 * (n : ℝ) * (δ0 / q) / (ℓ : ℝ) := by positivity
  calc
    (n.choose ℓ : ℝ) * (δ0 / q) ^ ℓ ≤ ((3 * (n : ℝ)) / ℓ) ^ ℓ * (δ0 / q) ^ ℓ := by
      exact mul_le_mul_of_nonneg_right hc0 hrpow
    _ = (3 * (n : ℝ) * (δ0 / q) / (ℓ : ℝ)) ^ ℓ := by
      rw [← mul_pow]
      ring
    _ ≤ (3 * ((2 : ℝ) ^ 18)⁻¹) ^ ℓ := by
      exact pow_le_pow_left₀ hb0pos hb ℓ

/-- the spread sum over subsets of `A`, regrouped by size, is at most the geometric sum. -/
lemma spread_le_geom (δ0 q : ℝ) (A : Set X)
    (hq0 : 0 < q) (hδ0 : 0 < δ0) (hB : (2^27 : ℝ) * δ0 ≤ q) :
    (∑ T : Set X, (if T ⊆ A then
          if condC A T then (δ0 / q) ^ T.ncard else 0
        else 0))
      ≤ ∑ ℓ ∈ Finset.Icc 1 (A.ncard), (3 * ((2 : ℝ) ^ 18)⁻¹) ^ ℓ := by
  let f : ℕ → ℝ := fun ℓ => if condN (A.ncard) ℓ then (δ0 / q) ^ ℓ else 0
  have hdef : (∑ T : Set X, (if T ⊆ A then
          if condC A T then (δ0 / q) ^ T.ncard else 0
        else 0))
      = ∑ T : Set X, (if T ⊆ A then f (T.ncard) else 0) := by
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hTA : T ⊆ A
    · rw [if_pos hTA, if_pos hTA]
      rfl
    · rw [if_neg hTA, if_neg hTA]
  have hreg : (∑ T : Set X, (if T ⊆ A then f (T.ncard) else 0))
      = ∑ ℓ ∈ Finset.Icc 0 (A.ncard), f ℓ * (A.ncard.choose ℓ : ℝ) := by
    calc
      (∑ T : Set X, (if T ⊆ A then f (T.ncard) else 0))
          = ∑ ℓ ∈ Finset.Icc 0 (A.ncard),
              f ℓ * (∑ T : Set X, if T ⊆ A ∧ T.ncard = ℓ then (1 : ℝ) else 0) := sum_subset_eq A f
      _ = ∑ ℓ ∈ Finset.Icc 0 (A.ncard), f ℓ * (A.ncard.choose ℓ : ℝ) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [count_choose A ℓ]
  have hf0 : f 0 = 0 := by
    unfold f condN
    have h1 : 0 ≤ ((2 : ℝ)^9)⁻¹ * (A.ncard : ℝ) := by positivity
    have hx : ((0 : ℕ) : ℝ) ≤ ((2 : ℝ)^9)⁻¹ * (A.ncard : ℝ) := by simpa using h1
    rw [if_neg]
    exact not_lt_of_ge hx
  have hterm : ∀ ℓ : ℕ, ℓ ∈ Finset.Icc 1 (A.ncard) →
      f ℓ * (A.ncard.choose ℓ : ℝ) ≤ (3 * ((2 : ℝ) ^ 18)⁻¹) ^ ℓ := by
    intro ℓ hℓmem
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓmem).1
    have hℓn : ℓ ≤ A.ncard := (Finset.mem_Icc.mp hℓmem).2
    unfold f condN
    by_cases hc : ((ℓ : ℝ) > ((2 : ℝ)^9)⁻¹ * (A.ncard : ℝ))
    · rw [if_pos hc]
      rw [mul_comm]
      exact term_le (A.ncard) ℓ δ0 q hℓ1 hℓn hq0 hδ0 hB hc
    · rw [if_neg hc]
      have hρ0 : 0 ≤ (3 * ((2 : ℝ)^18)⁻¹)^ℓ := by positivity
      simpa using hρ0
  calc
    (∑ T : Set X, (if T ⊆ A then
          if condC A T then (δ0 / q) ^ T.ncard else 0
        else 0))
        = ∑ T : Set X, (if T ⊆ A then f (T.ncard) else 0) := hdef
    _ = ∑ ℓ ∈ Finset.Icc 0 (A.ncard), f ℓ * (A.ncard.choose ℓ : ℝ) := hreg
    _ ≤ ∑ ℓ ∈ Finset.Icc 1 (A.ncard), (3 * ((2 : ℝ) ^ 18)⁻¹) ^ ℓ := by
          have hIcc : Finset.Icc (0 : ℕ) (A.ncard) = insert 0 (Finset.Icc 1 (A.ncard)) := by
            ext ℓ
            simp
            omega
          calc
            (∑ ℓ ∈ Finset.Icc 0 (A.ncard), f ℓ * (A.ncard.choose ℓ : ℝ))
                = f 0 * (A.ncard.choose 0 : ℝ)
                    + (∑ ℓ ∈ Finset.Icc 1 (A.ncard), f ℓ * (A.ncard.choose ℓ : ℝ)) := by
                      rw [hIcc]
                      rw [Finset.sum_insert]
                      simp
            _ = ∑ ℓ ∈ Finset.Icc 1 (A.ncard), f ℓ * (A.ncard.choose ℓ : ℝ) := by
                  have h0 : f 0 * (A.ncard.choose 0 : ℝ) = 0 := by simp [hf0]
                  rw [h0]
                  simp
            _ ≤ ∑ ℓ ∈ Finset.Icc 1 (A.ncard), (3 * ((2 : ℝ) ^ 18)⁻¹) ^ ℓ := by
                  apply Finset.sum_le_sum
                  intro ℓ hℓmem
                  exact hterm ℓ hℓmem

/--
Truncated second-moment estimate for a nonnegative weight `w` of total mass 1 which is
`δ0`-spread (`sh w T ≤ δ0^|T|` for every `T`), with a round probability `q ≥ 2^27·δ0`:

`Σ_{A,A0} w A · w A0 · 1[|A∩A0| > 2^{-9}·|A|] · q^{-|A∩A0|} ≤ 6·(2^{-9})^2`.
-/
theorem truncMoment (w : Set X → ℝ) (δ0 q : ℝ)
    (hw0 : ∀ S : Set X, 0 ≤ w S)
    (hw1 : (∑ S : Set X, w S) = 1)
    (hsp : ∀ T : Set X, sh w T ≤ δ0 ^ T.ncard)
    (hδ0 : 0 < δ0) (hq0 : 0 < q)
    (hB : (2^27 : ℝ) * δ0 ≤ q) :
    (∑ A : Set X,
      w A * (∑ A0 : Set X,
        if ((A ∩ A0).ncard : ℝ) > ((2 : ℝ) ^ 9)⁻¹ * (A.ncard : ℝ)
        then w A0 * (q ^ (A ∩ A0).ncard)⁻¹
        else 0)) ≤ 6 * (((2 : ℝ) ^ 9)⁻¹) ^ 2 := by
  let rho : ℝ := 3 * ((2 : ℝ) ^ 18)⁻¹
  have hrho0 : 0 ≤ rho := by norm_num [rho]
  have hrho : rho ≤ 1 / 2 := by norm_num [rho]
  have hRHS : 2 * rho = 6 * (((2 : ℝ) ^ 9)⁻¹) ^ 2 := by
    norm_num [rho, pow_mul]
  have hinner : ∀ A : Set X,
      (∑ A0 : Set X,
        if ((A ∩ A0).ncard : ℝ) > ((2 : ℝ) ^ 9)⁻¹ * (A.ncard : ℝ)
        then w A0 * (q ^ (A ∩ A0).ncard)⁻¹
        else 0) ≤ 2 * rho := by
    intro A
    have h1 := inner_le_spread w q δ0 A hw0 hq0 hsp
    have h2 := spread_le_geom δ0 q A hq0 hδ0 hB
    have hg : (∑ ℓ ∈ Finset.Icc 1 (A.ncard), rho ^ ℓ) ≤ 2 * rho := by
      exact Submission.Est.geom_Icc_le_two_mul (ρ := rho) hrho0 hrho (A.ncard)
    calc
      (∑ A0 : Set X,
        if ((A ∩ A0).ncard : ℝ) > ((2 : ℝ) ^ 9)⁻¹ * (A.ncard : ℝ)
        then w A0 * (q ^ (A ∩ A0).ncard)⁻¹
        else 0)
          ≤ ∑ T : Set X, (if T ⊆ A then
              if condC A T then (δ0 / q) ^ T.ncard else 0
            else 0) := h1
      _ ≤ ∑ ℓ ∈ Finset.Icc 1 (A.ncard), rho ^ ℓ := by
            simpa [rho] using h2
      _ ≤ 2 * rho := hg
  calc
    (∑ A : Set X,
      w A * (∑ A0 : Set X,
        if ((A ∩ A0).ncard : ℝ) > ((2 : ℝ) ^ 9)⁻¹ * (A.ncard : ℝ)
        then w A0 * (q ^ (A ∩ A0).ncard)⁻¹
        else 0))
        ≤ ∑ A : Set X, w A * (2 * rho) := by
          apply Finset.sum_le_sum
          intro A hA
          exact mul_le_mul_of_nonneg_left (hinner A) (hw0 A)
    _ = 2 * rho := by
          have hmul : (∑ A : Set X, w A * (2 * rho)) = (2 * rho) * (∑ A : Set X, w A) := by
            calc
              (∑ A : Set X, w A * (2 * rho)) = (∑ A : Set X, (2 * rho) * w A) := by
                apply Finset.sum_congr rfl
                intro A hA
                ring
              _ = (2 * rho) * (∑ A : Set X, w A) := by
                rw [Finset.mul_sum]
          calc
            (∑ A : Set X, w A * (2 * rho)) = (2 * rho) * (∑ A : Set X, w A) := hmul
            _ = (2 * rho) * 1 := by rw [hw1]
            _ = 2 * rho := by ring
    _ = 6 * (((2 : ℝ) ^ 9)⁻¹) ^ 2 := hRHS


end TruncMom
end Submission
