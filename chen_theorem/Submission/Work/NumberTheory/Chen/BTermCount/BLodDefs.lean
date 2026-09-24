import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# B-term level of distribution: the dyadic block vocabulary

This module collects the definitions used by the proof of
`Work.NumberTheory.Chen.BTermCount.bRemCorrLevelOfDistribution`:

* `blockStart M j = M * 2 ^ j`: the start of the `j`-th dyadic block of the window `[M,Y)`;
* `aCoeff M Y j u`: the indicator of the primes of the block `[M,Y) ∩ [Q_j, 2Q_j)`;
* `bCoeff Y v`: the indicator of the integers `v = q₂ q₃` with `Y ≤ q₂ ≤ q₃` prime;
* `bPairCount Y N`: the number of such pairs with `q₂ q₃ ≤ N` (so `q₂, q₃ ≤ N` too),
  which bounds `Σ_{v ≤ N} ‖bCoeff Y v‖ ^ 2`;
* `aCoeffC`, `bCoeffC`: the same coefficients cut down by coprimality to a modulus `d`;
  these are the coefficient sequences (one for each `d`) to which the bilinear character
  large sieve is applied.

The coprimality cuts factor out as a multiplicative factor of norm `≤ 1`
(`aCoeffC_eq`, `bCoeffC_eq`), so they are *dominated* by the uncut coefficients
(`norm_aCoeffC_le`, `norm_bCoeffC_le`) — which is what makes the large-sieve bound
uniform in `d`.
-/

/-- The `j`-th dyadic block of the window `[M,Y)`: `Q_j = M * 2^j`. -/
def blockStart (M j : ℕ) : ℕ := M * 2 ^ j

/-- Number of dyadic blocks covering `[M,Y)`. -/
noncomputable def blockCount (M Y : ℕ) : ℕ := Nat.log 2 (Y / M + 1) + 1

/-- The `a`-coefficient of block `j`: the indicator of the primes in the window block
`[Q_j, 2 Q_j) ∩ [M, Y)`. -/
noncomputable def aCoeff (M Y j u : ℕ) : ℂ :=
  if u.Prime ∧ M ≤ u ∧ u < Y ∧ blockStart M j ≤ u ∧ u < 2 * blockStart M j then 1 else 0

/-- The coprimality-cut `a`-coefficient of block `j` for the modulus `d`. -/
noncomputable def aCoeffC (M Y j d u : ℕ) : ℂ :=
  aCoeff M Y j u * (if Nat.Coprime u d then (1 : ℂ) else 0)

/-- The `b`-coefficient: the number of ways of writing `v` as a product `q₂ q₃` of primes `≥ Y`
with `q₂ ≤ q₃`.  This number is `0` or `1`. -/
noncomputable def bCoeff (Y v : ℕ) : ℂ :=
  if ∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = v then 1 else 0

/-- The coprimality-cut `b`-coefficient for the modulus `d`. -/
noncomputable def bCoeffC (Y d v : ℕ) : ℂ :=
  bCoeff Y v * (if Nat.Coprime v d then (1 : ℂ) else 0)

/-- The number of pairs `(q₂, q₃)` of primes `≥ Y` with `q₂ ≤ q₃` and `q₂ q₃ ≤ N`. -/
noncomputable def bPairCount (Y N : ℕ) : ℕ :=
  ((Finset.Icc Y N ×ˢ Finset.Icc Y N).filter
    (fun t : ℕ × ℕ => t.1.Prime ∧ t.2.Prime ∧ t.1 ≤ t.2 ∧ t.1 * t.2 ≤ N)).card

/-- The pair-set of `bPairCount`. -/
noncomputable def bPairSet (Y N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc Y N ×ˢ Finset.Icc Y N).filter
    (fun t : ℕ × ℕ => t.1.Prime ∧ t.2.Prime ∧ t.1 ≤ t.2 ∧ t.1 * t.2 ≤ N)

theorem bPairCount_eq_card (Y N : ℕ) : bPairCount Y N = (bPairSet Y N).card := rfl

/-! ### Elementary norm bounds -/

theorem aCoeffC_eq (M Y j d u : ℕ) :
    aCoeffC M Y j d u = aCoeff M Y j u * (if Nat.Coprime u d then (1 : ℂ) else 0) := rfl

theorem bCoeffC_eq (Y d v : ℕ) :
    bCoeffC Y d v = bCoeff Y v * (if Nat.Coprime v d then (1 : ℂ) else 0) := rfl

theorem norm_bCoeff_le_one (Y v : ℕ) : ‖bCoeff Y v‖ ≤ 1 := by
  unfold bCoeff
  split_ifs <;> simp

theorem norm_aCoeff_le_one (M Y j u : ℕ) : ‖aCoeff M Y j u‖ ≤ 1 := by
  unfold aCoeff
  split_ifs <;> simp

/-- The auxiliary factor `if Nat.Coprime u d then 1 else 0` has norm `≤ 1`. -/
theorem norm_coprime_ite_le_one (u d : ℕ) :
    ‖(if Nat.Coprime u d then (1 : ℂ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

theorem norm_bCoeffC_le (Y d v : ℕ) : ‖bCoeffC Y d v‖ ≤ ‖bCoeff Y v‖ := by
  rw [bCoeffC_eq, norm_mul]
  calc ‖bCoeff Y v‖ * ‖(if Nat.Coprime v d then (1 : ℂ) else 0)‖
      ≤ ‖bCoeff Y v‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_coprime_ite_le_one v d) (norm_nonneg _)
    _ = ‖bCoeff Y v‖ := by ring

theorem norm_aCoeffC_le (M Y j d u : ℕ) :
    ‖aCoeffC M Y j d u‖ ≤ ‖aCoeff M Y j u‖ := by
  rw [aCoeffC_eq, norm_mul]
  calc ‖aCoeff M Y j u‖ * ‖(if Nat.Coprime u d then (1 : ℂ) else 0)‖
      ≤ ‖aCoeff M Y j u‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_coprime_ite_le_one u d) (norm_nonneg _)
    _ = ‖aCoeff M Y j u‖ := by ring

theorem norm_bCoeffC_le_one (Y d v : ℕ) : ‖bCoeffC Y d v‖ ≤ 1 :=
  le_trans (norm_bCoeffC_le Y d v) (norm_bCoeff_le_one Y v)

theorem norm_aCoeffC_le_one (M Y j d u : ℕ) : ‖aCoeffC M Y j d u‖ ≤ 1 :=
  le_trans (norm_aCoeffC_le M Y j d u) (norm_aCoeff_le_one M Y j u)

/-! ### Sums of squares -/

theorem sum_sq_aCoeffC_le (M Y j d U : ℕ) :
    ∑ u ∈ Finset.Icc 1 U, ‖aCoeffC M Y j d u‖ ^ 2 ≤ (U : ℝ) := by
  have h1 : ∑ u ∈ Finset.Icc 1 U, ‖aCoeffC M Y j d u‖ ^ 2
      ≤ ∑ _u ∈ Finset.Icc 1 U, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun u _ => ?_)
    have h2 := norm_aCoeffC_le_one M Y j d u
    have h3 : (0:ℝ) ≤ ‖aCoeffC M Y j d u‖ := norm_nonneg _
    rw [sq]
    nlinarith [h2, h3]
  simpa using h1

/-- Since `bCoeff` is `{0,1}`-valued, the sum of its squares equals the sum of its real parts. -/
theorem sum_sq_bCoeff_eq_sum_bCoeff (Y N : ℕ) :
    (∑ v ∈ Finset.Icc 1 N, ‖bCoeff Y v‖ ^ 2) = ∑ v ∈ Finset.Icc 1 N, (bCoeff Y v).re := by
  refine Finset.sum_congr rfl (fun v _ => ?_)
  unfold bCoeff
  split_ifs <;> simp

/-- The `v`-set is contained in the image of the pair-set of `bPairCount`. -/
theorem filter_bCoeff_ne_zero_subset_image (Y N : ℕ) :
    (Finset.Icc 1 N).filter (fun v => bCoeff Y v ≠ 0)
      ⊆ (bPairSet Y N).image (fun t : ℕ × ℕ => t.1 * t.2) := by
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_Icc] at hv
  obtain ⟨⟨hvlo, hvhi⟩, hne⟩ := hv
  unfold bCoeff at hne
  by_cases hex : ∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = v
  · rw [if_pos hex] at hne
    obtain ⟨q₂, q₃, hq₂, hq₃, hY, hle, hprod⟩ := hex
    refine Finset.mem_image.mpr ⟨(q₂, q₃), ?_, ?_⟩
    · simp only [bPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      have hpq : q₂ * q₃ ≤ N := by rw [hprod]; exact hvhi
      have hq₃N : q₃ ≤ N := by nlinarith [hq₂.two_le]
      exact ⟨⟨⟨hY, hle.trans hq₃N⟩, ⟨hY.trans hle, hq₃N⟩⟩, ⟨hq₂, hq₃, hle, hpq⟩⟩
    · exact hprod
  · rw [if_neg hex] at hne
    exact absurd rfl hne

/-- The number of `v ∈ [1,N]` that are a product of two primes `≥ Y` (with `q₂ ≤ q₃`) is at
most `bPairCount Y N`. -/
theorem card_filter_bCoeff_ne_zero_le_bPairCount (Y N : ℕ) :
    ((Finset.Icc 1 N).filter (fun v => bCoeff Y v ≠ 0)).card ≤ bPairCount Y N := by
  rw [bPairCount_eq_card]
  refine le_trans (Finset.card_le_card (filter_bCoeff_ne_zero_subset_image Y N)) ?_
  exact Finset.card_image_le

/-- The sum of squares of the `b`-coefficients over `[1,N]` is at most `bPairCount Y N`. -/
theorem sum_sq_bCoeff_le_bPairCount (Y N : ℕ) :
    ∑ v ∈ Finset.Icc 1 N, ‖bCoeff Y v‖ ^ 2 ≤ (bPairCount Y N : ℝ) := by
  rw [sum_sq_bCoeff_eq_sum_bCoeff]
  have hcard : ((Finset.Icc 1 N).filter (fun v => bCoeff Y v ≠ 0)).card
      = ∑ v ∈ Finset.Icc 1 N, (if bCoeff Y v ≠ 0 then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcongr : ∀ v ∈ Finset.Icc 1 N,
      (bCoeff Y v).re = (if bCoeff Y v ≠ 0 then (1 : ℝ) else 0) := by
    intro v _
    unfold bCoeff
    by_cases h : ∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = v
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  have hsum : (∑ v ∈ Finset.Icc 1 N, (bCoeff Y v).re)
      = ((Finset.Icc 1 N).filter (fun v => bCoeff Y v ≠ 0)).card := by
    rw [hcard]
    exact Finset.sum_congr rfl hcongr
  rw [hsum]
  exact_mod_cast card_filter_bCoeff_ne_zero_le_bPairCount Y N

/-- The sum of squares of the coprimality-cut `b`-coefficients is at most `bPairCount Y N`. -/
theorem sum_sq_bCoeffC_le_bPairCount (Y d N : ℕ) :
    ∑ v ∈ Finset.Icc 1 N, ‖bCoeffC Y d v‖ ^ 2 ≤ (bPairCount Y N : ℝ) := by
  have h1 : ∑ v ∈ Finset.Icc 1 N, ‖bCoeffC Y d v‖ ^ 2
      ≤ ∑ v ∈ Finset.Icc 1 N, ‖bCoeff Y v‖ ^ 2 := by
    refine Finset.sum_le_sum (fun v _ => ?_)
    have h2 := norm_bCoeffC_le Y d v
    have h3 : (0:ℝ) ≤ ‖bCoeffC Y d v‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ ‖bCoeff Y v‖ := norm_nonneg _
    calc ‖bCoeffC Y d v‖ ^ 2 = ‖bCoeffC Y d v‖ * ‖bCoeffC Y d v‖ := by rw [sq]
      _ ≤ ‖bCoeff Y v‖ * ‖bCoeffC Y d v‖ := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ ‖bCoeff Y v‖ * ‖bCoeff Y v‖ := mul_le_mul_of_nonneg_left h2 h4
      _ = ‖bCoeff Y v‖ ^ 2 := by rw [sq]
  exact le_trans h1 (sum_sq_bCoeff_le_bPairCount Y N)

/-! ### The plain (unblocked) `a`-coefficient, and the change-of-level character evaluation -/

/-- The plain `a`-coefficient: the indicator of the primes in `[M,Y)`. -/
noncomputable def aCoeff0 (M Y u : ℕ) : ℂ :=
  if u.Prime ∧ M ≤ u ∧ u < Y then 1 else 0

/-- The coprimality-cut plain `a`-coefficient. -/
noncomputable def aCoeff0C (M Y d u : ℕ) : ℂ :=
  aCoeff0 M Y u * (if Nat.Coprime u d then (1 : ℂ) else 0)

theorem aCoeff0C_eq (M Y d u : ℕ) :
    aCoeff0C M Y d u = aCoeff0 M Y u * (if Nat.Coprime u d then (1 : ℂ) else 0) := rfl

theorem norm_aCoeff0_le_one (M Y u : ℕ) : ‖aCoeff0 M Y u‖ ≤ 1 := by
  unfold aCoeff0
  split_ifs <;> simp

theorem norm_aCoeff0C_le_one (M Y d u : ℕ) : ‖aCoeff0C M Y d u‖ ≤ 1 := by
  rw [aCoeff0C_eq, norm_mul]
  calc ‖aCoeff0 M Y u‖ * ‖(if Nat.Coprime u d then (1 : ℂ) else 0)‖
      ≤ 1 * 1 := by
        refine mul_le_mul (norm_aCoeff0_le_one M Y u) (norm_coprime_ite_le_one u d)
          (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem sum_sq_aCoeff0C_le (M Y d U : ℕ) :
    ∑ u ∈ Finset.Icc 1 U, ‖aCoeff0C M Y d u‖ ^ 2 ≤ (U : ℝ) := by
  have h1 : ∑ u ∈ Finset.Icc 1 U, ‖aCoeff0C M Y d u‖ ^ 2
      ≤ ∑ _u ∈ Finset.Icc 1 U, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun u _ => ?_)
    have h2 := norm_aCoeff0C_le_one M Y d u
    have h3 : (0:ℝ) ≤ ‖aCoeff0C M Y d u‖ := norm_nonneg _
    rw [sq]
    nlinarith [h2, h3]
  simpa using h1

/-- **The change-of-level character evaluation.**  If `r ∣ d`, then the lift of `ψ` from level
`r` to level `d` is `ψ` on the integers coprime to `d` and `0` on the others. -/
theorem changeLevel_apply_nat {r d : ℕ} [NeZero d] (h : r ∣ d) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) :
    (DirichletCharacter.changeLevel h ψ) ((n : ℕ) : ZMod d)
      = if Nat.Coprime n d then ψ ((n : ℕ) : ZMod r) else 0 := by
  by_cases hc : Nat.Coprime n d
  · rw [if_pos hc]
    exact Commons.NumberTheory.DirichletCharacter.changeLevel_stable_nat h ψ hc
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun hu => hc ((ZMod.isUnit_iff_coprime n d).mp hu))


end Work.NumberTheory.Chen.BTermCount
