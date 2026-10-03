/-
# Auxiliary lemmas for the high–high case of area A6

Elementary tools for `Work.KMTPlan.A6.highHighCase`:

* the position of `kmtM l₁ l₂ k₁ k₂` with respect to `l₁,l₂,k₁,k₂`;
* the arithmetic of the gain: `2^{-cL} ≤ 2^{2c}·2^{-(c/2)M}` when `M ≤ L+2`, and the
  comparison used at the exceptional quadruple `(l₁,l₂,k₁,k₂) = (0,0,1,1)`, where `M = 1`;
* the *case analysis on the height* `L` at which the `improv` estimate is applied: for every
  quadruple which is not exceptional there is a height `L ≤ M` with `M ≤ L+2` which is
  admissible either for the `F`-side (`L < l₁ ∨ L+2 ≤ k₁`) or for the `G`-side
  (`L < l₂ ∨ L+2 ≤ k₂`);
* `MemLp` of the pieces and the crude `ℓ²` bounds for the pieces, deduced from the
  corresponding statements about the projections;
* `logN (2^m) = m` and the indicator-count bound underneath the "bad scales" estimate.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.HHBasic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## `kmtM` dominates its arguments -/

theorem kmtM_ge_l₁ (l₁ l₂ k₁ k₂ : ℕ) : l₁ ≤ kmtM l₁ l₂ k₁ k₂ := by
  rw [kmtM]; omega

theorem kmtM_ge_l₂ (l₁ l₂ k₁ k₂ : ℕ) : l₂ ≤ kmtM l₁ l₂ k₁ k₂ := by
  rw [kmtM]; omega

theorem kmtM_ge_k₁ (l₁ l₂ k₁ k₂ : ℕ) : k₁ ≤ kmtM l₁ l₂ k₁ k₂ := by
  rw [kmtM]; omega

theorem kmtM_ge_k₂ (l₁ l₂ k₁ k₂ : ℕ) : k₂ ≤ kmtM l₁ l₂ k₁ k₂ := by
  rw [kmtM]; omega

/-- **The height at which `improv` is applied.**  For every quadruple which is not the
exceptional one `(0,0,1,1)` there is a height `L ≤ M` with `M ≤ L+2` which is admissible either
for the `F`-side (`L < l₁ ∨ L+2 ≤ k₁`) or for the `G`-side (`L < l₂ ∨ L+2 ≤ k₂`). -/
theorem exists_height_cases (l₁ l₂ k₁ k₂ : ℕ)
    (h : 1 ≤ l₁ ∨ 2 ≤ k₁ ∨ 1 ≤ l₂ ∨ 2 ≤ k₂) :
    ∃ L : ℕ, L ≤ kmtM l₁ l₂ k₁ k₂ ∧ kmtM l₁ l₂ k₁ k₂ ≤ L + 2 ∧
      ((L < l₁ ∨ L + 2 ≤ k₁) ∨ (L < l₂ ∨ L + 2 ≤ k₂)) := by
  rcases lt_or_ge (max l₁ l₂) (max k₁ k₂) with hBA | hAB
  · have hM : kmtM l₁ l₂ k₁ k₂ = max k₁ k₂ := by rw [kmtM, max_eq_right (le_of_lt hBA)]
    have hB2 : 2 ≤ max k₁ k₂ := by
      rcases h with h | h | h | h
      · have h1 : 1 ≤ max l₁ l₂ := le_trans h (le_max_left l₁ l₂)
        omega
      · exact le_trans h (le_max_left k₁ k₂)
      · have h1 : 1 ≤ max l₁ l₂ := le_trans h (le_max_right l₁ l₂)
        omega
      · exact le_trans h (le_max_right k₁ k₂)
    refine ⟨max k₁ k₂ - 2, by omega, by omega, ?_⟩
    rcases le_total k₁ k₂ with h12 | h21
    · right; right
      have hmax : max k₁ k₂ = k₂ := max_eq_right h12
      omega
    · left; right
      have hmax : max k₁ k₂ = k₁ := max_eq_left h21
      omega
  · have hM : kmtM l₁ l₂ k₁ k₂ = max l₁ l₂ := by rw [kmtM, max_eq_left hAB]
    have hA1 : 1 ≤ max l₁ l₂ := by
      rcases h with h | h | h | h
      · exact le_trans h (le_max_left l₁ l₂)
      · have h2 : 2 ≤ max l₁ l₂ := le_trans h (le_trans (le_max_left k₁ k₂) hAB)
        omega
      · exact le_trans h (le_max_right l₁ l₂)
      · have h2 : 2 ≤ max l₁ l₂ := le_trans h (le_trans (le_max_right k₁ k₂) hAB)
        omega
    refine ⟨max l₁ l₂ - 1, by omega, by omega, ?_⟩
    rcases le_total l₁ l₂ with h12 | h21
    · right; left
      have hmax : max l₁ l₂ = l₂ := max_eq_right h12
      omega
    · left; left
      have hmax : max l₁ l₂ = l₁ := max_eq_left h21
      omega

/-! ## The arithmetic of the gain -/

/-- **The gain comparison.**  If `M ≤ L + 2` and `0 ≤ c` then
`2^{-cL} ≤ 2^{2c}·2^{-(c/2)M}`. -/
theorem rpow_gain_le (c : ℝ) (hc : 0 ≤ c) (L M : ℕ) (hLM : M ≤ L + 2) :
    (2 : ℝ) ^ (-(c * (L : ℝ))) ≤ (2 : ℝ) ^ (2 * c) * (2 : ℝ) ^ (-(c / 2 * (M : ℝ))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [← Real.rpow_add h2]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
  have hL : (M : ℝ) ≤ (L : ℝ) + 2 := by exact_mod_cast hLM
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  nlinarith

/-- The weight at the exceptional quadruple `(0,0,1,1)`, where `M = 1`. -/
theorem hhWeight_exc (c : ℝ) : hhWeight c 0 0 1 1 = (2 : ℝ) ^ (-(c * 1)) := by
  rw [hhWeight, kmtM]
  norm_num

/-- The gain at the exceptional quadruple: `2^{c/2}·2^{-(c/2)} = 1`, so the crude bound
(carried by `2^{c/2}`) suffices there. -/
theorem rpow_exc_eq (c : ℝ) :
    (2 : ℝ) ^ (c / 2) * (2 : ℝ) ^ (-(c / 2 * ((kmtM 0 0 1 1 : ℕ) : ℝ))) = 1 := by
  have h1 : ((kmtM 0 0 1 1 : ℕ) : ℝ) = 1 := by norm_num [kmtM]
  rw [h1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_zero (2 : ℝ)]
  congr 1
  ring

/-! ## `logN` and indicators -/

/-- `logN (2 ^ m) = m` for `m ≥ 1`. -/
theorem logN_two_pow {m : ℕ} (hm : 1 ≤ m) : logN (2 ^ m) = (m : ℤ) := by
  have h2 : (2 : ℕ) ≤ 2 ^ m := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [logN, max_eq_left h2, Nat.log_pow (by norm_num) m]

/-- The sum of the indicator of a set of natural numbers bounded by `K` is at most `K`. -/
theorem tsum_indicator_le (Pm : ℕ → Prop) [DecidablePred Pm] (K : ℕ)
    (h : ∀ n, Pm n → n < K) :
    (∑' n : ℕ, if Pm n then (1 : ℝ≥0∞) else 0) ≤ (K : ℝ≥0∞) := by
  rw [tsum_eq_sum (s := Finset.range K) (fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    exact if_neg (fun hp => absurd (h n hp) (not_lt.mpr hn)))]
  calc ∑ n ∈ Finset.range K, (if Pm n then (1 : ℝ≥0∞) else 0)
      ≤ ∑ _n ∈ Finset.range K, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        split <;> simp
    _ = (K : ℝ≥0∞) := by simp

/-! ## `MemLp` of the pieces -/

/-- `MemLp` of the exact-height projections, from the corresponding statement for `kmtProj`. -/
theorem memLp_piExact_of (hmem : ∀ (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
      MemLp f 2 Measure.count → MemLp (kmtProj ρ l k f) 2 Measure.count)
    (ρ : ℝ) (l : ℕ) (k : ℤ) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    MemLp (piExact (kmtPj ρ) l k f) 2 Measure.count := by
  rw [piExact]
  split
  · exact hmem ρ 0 k f hf
  · exact (hmem ρ l k f hf).sub (hmem ρ (l - 1) k f hf)

/-- `MemLp` of the `F`-pieces. -/
theorem memLp_Fpiece_of (hmem : ∀ (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
      MemLp f 2 Measure.count → MemLp (kmtProj ρ l k f) 2 Measure.count)
    (ρ : ℝ) (l k N : ℕ) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    MemLp (Fpiece (kmtPj ρ) 0 l (k : ℤ) N f) 2 Measure.count := by
  rw [Fpiece_eq, piece]
  split
  · exact memLp_piExact_of hmem ρ l _ hf
  · exact (memLp_piExact_of hmem ρ l _ hf).sub (memLp_piExact_of hmem ρ l _ hf)

/-- `MemLp` of the `G`-pieces. -/
theorem memLp_Gpiece_of (hmem : ∀ (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
      MemLp f 2 Measure.count → MemLp (kmtProj ρ l k f) 2 Measure.count)
    (ρ : ℝ) (d : ℤ) (l k N : ℕ) {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) :
    MemLp (Gpiece (kmtPj ρ) d 0 l (k : ℤ) N g) 2 Measure.count := by
  rw [Gpiece_eq, piece]
  split
  · exact memLp_piExact_of hmem ρ l _ hg
  · exact (memLp_piExact_of hmem ρ l _ hg).sub (memLp_piExact_of hmem ρ l _ hg)

/-! ## The crude `ℓ²` bounds for the pieces -/

/-- `(C·u) + (C·u) ≤ (2C)·u`, the arithmetic of the triangle inequality for the crude bounds. -/
theorem two_mul_le (C : ℝ≥0) (A : ℝ≥0∞) :
    (C : ℝ≥0∞) * A + (C : ℝ≥0∞) * A ≤ ((2 * C : ℝ≥0) : ℝ≥0∞) * A := by
  refine le_of_eq ?_
  rw [ENNReal.coe_mul, ENNReal.coe_ofNat, mul_assoc, two_mul]

/-- The crude bound for the exact-height projections on an explicit rectangle of heights. -/
theorem crude_piExact_of (hbound : ∀ (ρ : ℝ) (S : Finset (ℕ × ℤ)), ∃ C : ℝ≥0, 0 < C ∧
      ∀ p ∈ S, ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count)
    (ρ : ℝ) (B : ℕ) (Kg : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (l : ℕ) (κ : ℤ) (f : ℤ → ℂ), l ≤ B → -((Kg : ℤ)) ≤ κ → κ ≤ (B : ℤ) →
      eLpNorm (piExact (kmtPj ρ) l κ f) 2 Measure.count ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hbound ρ
    (Finset.Icc ((0 : ℕ), -((Kg : ℤ))) ((B : ℕ), (B : ℤ)))
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro l κ f hl hκ hκB
  have hmemS : ∀ l' : ℕ, l' ≤ B →
      (l', κ) ∈ Finset.Icc ((0 : ℕ), -((Kg : ℤ))) ((B : ℕ), (B : ℤ)) := by
    intro l' hl'
    rw [Finset.mem_Icc]
    exact ⟨⟨by omega, hκ⟩, ⟨by omega, hκB⟩⟩
  have hle := hC₀ (l, κ) (hmemS l hl) f
  have hle2 := hC₀ (l - 1, κ) (hmemS (l - 1) (by omega)) f
  have hmain : eLpNorm (piExact (kmtPj ρ) l κ f) 2 Measure.count
      ≤ (C₀ : ℝ≥0∞) * eLpNorm f 2 Measure.count
        + (C₀ : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
    rw [piExact]
    split
    · rename_i hl0
      rw [hl0] at hle
      exact hle.trans (le_add_of_nonneg_right zero_le)
    · exact (eLpNorm_sub_le (by norm_num)).trans
        (add_le_add hle hle2)
  exact hmain.trans (two_mul_le C₀ _)

/-- The crude bound for a general dyadic piece, given bounds on the two frequency scales
`κ s` and `κ (s-1)` which occur in it. -/
theorem crude_piece_of (hbound : ∀ (ρ : ℝ) (S : Finset (ℕ × ℤ)), ∃ C : ℝ≥0, 0 < C ∧
      ∀ p ∈ S, ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count)
    (ρ : ℝ) (B : ℕ) (Kg : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) (f : ℤ → ℂ), l ≤ B →
      (∀ t : ℤ, (t = s ∨ t = s - 1) → -((Kg : ℤ)) ≤ κ t ∧ κ t ≤ (B : ℤ)) →
      eLpNorm (piece (kmtPj ρ) l κ a s f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := crude_piExact_of hbound ρ B Kg
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro l κ a s f hl hκ
  have hmain : eLpNorm (piece (kmtPj ρ) l κ a s f) 2 Measure.count
      ≤ (C₀ : ℝ≥0∞) * eLpNorm f 2 Measure.count
        + (C₀ : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
    rw [piece]
    split
    · exact (hC₀ l (κ s) f hl (hκ s (Or.inl rfl)).1 (hκ s (Or.inl rfl)).2).trans
        (le_add_of_nonneg_right zero_le)
    · exact (eLpNorm_sub_le (by norm_num)).trans
        (add_le_add (hC₀ l (κ s) f hl (hκ s (Or.inl rfl)).1 (hκ s (Or.inl rfl)).2)
          (hC₀ l (κ (s - 1)) f hl (hκ (s - 1) (Or.inr rfl)).1
            (hκ (s - 1) (Or.inr rfl)).2))
  exact hmain.trans (two_mul_le C₀ _)

/-- The crude bound for the `F`-pieces on an explicit range of frequency scales. -/
theorem crude_Fpiece_of (hbound : ∀ (ρ : ℝ) (S : Finset (ℕ × ℤ)), ∃ C : ℝ≥0, 0 < C ∧
      ∀ p ∈ S, ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count)
    (ρ : ℝ) (B : ℕ) (Kg : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (l k N : ℕ) (f : ℤ → ℂ), l ≤ B →
      -((Kg : ℤ)) ≤ (k : ℤ) - logN N - 1 → (k : ℤ) - logN N ≤ (B : ℤ) →
      eLpNorm (Fpiece (kmtPj ρ) 0 l (k : ℤ) N f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := crude_piece_of hbound ρ B Kg
  refine ⟨C, hCpos, ?_⟩
  intro l k N f hl hκ hκB
  refine hC l (fun s => -(logN N) + s) 0 (k : ℤ) f hl ?_
  intro t ht
  rcases ht with ht | ht
  · subst ht
    constructor <;> omega
  · have h2 : t = (k : ℤ) - 1 := by omega
    subst h2
    constructor <;> omega

/-- The crude bound for the `G`-pieces on an explicit range of frequency scales. -/
theorem crude_Gpiece_of (hbound : ∀ (ρ : ℝ) (S : Finset (ℕ × ℤ)), ∃ C : ℝ≥0, 0 < C ∧
      ∀ p ∈ S, ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count)
    (ρ : ℝ) (d : ℤ) (hd : 0 ≤ d) (B : ℕ) (Kg : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (l k N : ℕ) (g : ℤ → ℂ), l ≤ B →
      -((Kg : ℤ)) ≤ d * (-(logN N) + (k : ℤ)) - d → d * (-(logN N) + (k : ℤ)) ≤ (B : ℤ) →
      eLpNorm (Gpiece (kmtPj ρ) d 0 l (k : ℤ) N g) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm g 2 Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := crude_piece_of hbound ρ B Kg
  refine ⟨C, hCpos, ?_⟩
  intro l k N g hl hκ hκB
  refine hC l (fun s => d * (-(logN N) + s)) 0 (k : ℤ) g hl ?_
  intro t ht
  rcases ht with ht | ht
  · subst ht
    constructor <;> omega
  · have h2 : t = (k : ℤ) - 1 := by omega
    have hval : d * (-(logN N) + t) = d * (-(logN N) + (k : ℤ)) - d := by
      rw [h2]; ring
    constructor
    · omega
    · omega

end

end Work.KMTPlan.A6
