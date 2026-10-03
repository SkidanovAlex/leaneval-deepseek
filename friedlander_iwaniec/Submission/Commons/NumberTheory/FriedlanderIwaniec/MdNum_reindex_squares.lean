import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-! ## Elementary reindexing lemmas for sums over `[1, r]`

These are the combinatorial core of the reindexing: splitting off the `b = 0`
term of a sum over `range (r + 1)`, and reindexing the terms with `b` a nonzero
perfect square by their square roots. -/

/-- Splitting off the `b = 0` term from a sum over `range (r + 1)`. -/
private lemma fi_sum_range_split (f : ℕ → ℕ) (r : ℕ) :
    (∑ b ∈ Finset.range (r + 1),
        (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) * f b)
      = f 0 + ∑ b ∈ Finset.Icc 1 r, (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b := by
  rw [Finset.sum_range_succ']
  have hI : Finset.Ico 1 (r + 1) = Finset.Icc 1 r := by
    ext b; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hg0 : (if (0:ℕ) = 0 then 1 else if Nat.sqrt 0 ^ 2 = 0 then 2 else 0) * f 0 = f 0 := by
    simp
  have hsum : (∑ k ∈ Finset.range r,
        (if k + 1 = 0 then 1 else if Nat.sqrt (k + 1) ^ 2 = k + 1 then 2 else 0) * f (k + 1))
      = ∑ b ∈ Finset.Icc 1 r, (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b := by
    rw [← hI, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    rw [if_neg (by omega : ¬ (k + 1 = 0)), Nat.add_comm 1 k]
  rw [hsum, hg0, add_comm]

/-- Reindexing the square terms of `[1, r]` by their square roots. -/
private lemma fi_sum_squares (f : ℕ → ℕ) (r : ℕ) :
    (∑ b ∈ (Finset.Icc 1 r).filter (fun b => Nat.sqrt b ^ 2 = b), f b)
      = ∑ c ∈ Finset.Icc 1 (Nat.sqrt r), f (c ^ 2) := by
  have hF : (Finset.Icc 1 r).filter (fun b => Nat.sqrt b ^ 2 = b)
      = (Finset.Icc 1 (Nat.sqrt r)).image (fun c => c ^ 2) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hb1, hbr⟩, hbsq⟩
      exact ⟨Nat.sqrt b, ⟨by rw [Nat.le_sqrt']; omega,
        by rw [Nat.le_sqrt']; rw [hbsq]; exact hbr⟩, hbsq⟩
    · rintro ⟨c, ⟨hc1, hcr⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · calc 1 = 1 ^ 2 := by norm_num
          _ ≤ c ^ 2 := Nat.pow_le_pow_left hc1 2
      · exact Nat.le_sqrt'.mp hcr
      · rw [Nat.sqrt_eq']
  rw [hF]
  exact Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)

/-- Reindexing the weighted sum over `[1, r]` using the square-root bijection. -/
private lemma fi_sum_weight (f : ℕ → ℕ) (r : ℕ) :
    (∑ b ∈ Finset.Icc 1 r, (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b)
      = 2 * ∑ c ∈ Finset.Icc 1 (Nat.sqrt r), f (c ^ 2) := by
  have h1 : ∀ b ∈ Finset.Icc 1 r,
      (if Nat.sqrt b ^ 2 = b then 2 else 0) * f b
        = 2 * (if Nat.sqrt b ^ 2 = b then f b else 0) := by
    intro b _
    by_cases h : Nat.sqrt b ^ 2 = b <;> simp [h]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.sum_filter,
    fi_sum_squares f r]

/-- **The reindexing identity.**  For any `f`,
`∑_{b ≤ r} Z(b) f b = f 0 + 2 ∑_{1 ≤ c ≤ √r} f (c²)`, where `Z` is the
square-indicator `Z(0) = 1`, `Z(b²) = 2` for `b ≠ 0`. -/
private lemma fi_reindex (f : ℕ → ℕ) (r : ℕ) :
    (∑ b ∈ Finset.range (r + 1),
        (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) * f b)
      = f 0 + 2 * ∑ c ∈ Finset.Icc 1 (Nat.sqrt r), f (c ^ 2) := by
  rw [fi_sum_range_split f r, fi_sum_weight f r]

theorem MdNum_reindex_squares (d x : ℕ) :
    (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) *
          ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - b ^ 2) + 1))
      - ({α : ZMod d | α ^ 2 = 0}.ncard)
    = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        ({α : ZMod d | α ^ 2 + (((c ^ 2 : ℕ) : ZMod d)) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - c ^ 4) + 1))
      + 2 * (Nat.sqrt x) * ({α : ZMod d | α ^ 2 = 0}.ncard) := by
  classical
  -- left-associate the triple product in the summand
  have hL : (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) *
          ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - b ^ 2) + 1))
      = (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) *
          (({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - b ^ 2) + 1))) := by
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hL, fi_reindex
        (fun b => ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - b ^ 2) + 1)) (Nat.sqrt x)]
  -- head term
  have hc0 : ({α : ZMod d | α ^ 2 + (((0 : ℕ)) : ZMod d) ^ 2 = 0}.ncard) *
        (2 * Nat.sqrt (x - ((0 : ℕ)) ^ 2) + 1)
      = ({α : ZMod d | α ^ 2 = 0}.ncard) * (2 * Nat.sqrt x + 1) := by
    rw [show ((0 : ℕ)) ^ 2 = 0 by norm_num, Nat.sub_zero]
    congr 1
    · congr 1
      ext α
      simp
  -- summand term
  have hsum : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        ({α : ZMod d | α ^ 2 + (((c ^ 2 : ℕ) : ZMod d)) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - (c ^ 2) ^ 2) + 1))
      = (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        ({α : ZMod d | α ^ 2 + (((c ^ 2 : ℕ) : ZMod d)) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - c ^ 4) + 1)) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [show ((c ^ 2 : ℕ)) ^ 2 = c ^ 4 by ring]
  rw [hc0, hsum]
  -- arithmetic
  rw [show ({α : ZMod d | α ^ 2 = 0}).ncard * (2 * Nat.sqrt x + 1)
      = ({α : ZMod d | α ^ 2 = 0}).ncard * (2 * Nat.sqrt x)
        + ({α : ZMod d | α ^ 2 = 0}).ncard by ring]
  rw [add_right_comm, Nat.add_sub_cancel]
  ring

end Commons.NumberTheory.FriedlanderIwaniec
