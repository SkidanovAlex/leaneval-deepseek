import ChallengeDeps
import Submission.Vdw.ImprimitiveBlock
import Submission.Vdw.SchmidtCount

open Polynomial Filter Asymptotics
open scoped BigOperators
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The imprimitive slice, sliced by the block size, with general exponents

`ImprimitiveBlock.ImprimitiveBlockBound` records Widmer's counting input in the
form "the `(k, m)`-slice of the imprimitive polynomials is `O(H^(k+m))`".  This
module generalises the interface: it allows an *arbitrary* exponent function
`E : ℕ → ℕ → ℝ` on the finitely many divisor pairs `(k, m)` of `n`, and derives

* `#ImprimitiveBad n H = O(H^(n-1))`  (`imprimitiveBad_isBigO_of_sliceExp`) as
  soon as `E k m ≤ n - 1` for all divisor pairs, and
* the challenge theorem for composite `n ≥ 6` (`theorem_1_of_sliceExp`), using
  Schmidt's field count (a theorem of this project) for the Case-II input.

The point of the generalisation is that the per-slice counting arguments
below deliver exponents such as `k + 1` (quadratic block systems), `k + m`
(the sharp block-polynomial count) or `k + m + 2` (the soft `λ`-form count),
and *any* of these is sufficient as soon as it is `≤ n - 1`.
-/

namespace Submission.Vdw

noncomputable section

/-- The `(k,·)`-**slice** of the imprimitive bad set: box polynomials of degree
`n` which are irreducible over `ℚ` and admit a block of size `k` for the
natural action of their Galois group on the `n` roots. -/
def imprimSlice (n H k : ℕ) : Set ℤ[X] :=
  {f : ℤ[X] | f ∈ Box n H ∧ Irreducible (f.map φℚ) ∧
    ∃ h : Irreducible (f.map φℚ), HasBlockSize f h k}

lemma imprimSlice_finite (n H k : ℕ) : (imprimSlice n H k).Finite :=
  (box_finite n H).subset fun f hf => hf.1

/-- `imprimSlice` as a function of the pair `(k, m)`, for use in finite unions
(indexed by `blockPairs n`). -/
def imprimSlicePair (n H : ℕ) (p : ℕ × ℕ) : Set ℤ[X] := imprimSlice n H p.1

lemma imprimSlicePair_finite (n H : ℕ) (p : ℕ × ℕ) : (imprimSlicePair n H p).Finite :=
  imprimSlice_finite n H p.1

/-- **The slice counting input, with an exponent function `E`.**  For every
divisor pair `(k, m)` of `n` with `k, m ≥ 2`, the `k`-slice of the imprimitive
box is `O(H^(E k m))`. -/
def ImprimitiveSliceBoundExp (n : ℕ) (E : ℕ → ℕ → ℝ) : Prop :=
  ∀ k m : ℕ, 2 ≤ k → 2 ≤ m → k * m = n → ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ,
    ((imprimSlice n H k).ncard : ℝ) ≤ C * ((H : ℝ) + 1) ^ (E k m)

/-- The slice sets cover the imprimitive bad set: every imprimitive bad
polynomial of height `≤ H` admits a nontrivial block, hence lies in the
`k`-slice for some divisor pair `(k, m)` of `n`. -/
lemma imprimitiveBad_subset_iUnion_slice (n H : ℕ) (hn : 3 ≤ n) :
    ImprimitiveBad n H ⊆ ⋃ p ∈ blockPairs n, imprimSlicePair n H p := by
  intro f hf
  obtain ⟨h, k, m, hk2, hm2, hkm, hbk⟩ := imprimitiveBad_has_block n H hn hf
  refine Set.mem_iUnion.mpr ⟨(k, m), Set.mem_iUnion.mpr ⟨mem_blockPairs hk2 hm2 hkm, ?_⟩⟩
  exact ⟨Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1),
    irreducibleBad_mem_irreducible_rat (by omega) hf.1, h, hbk⟩

/-- **Widmer's bound from slice bounds with exponents.**  If every divisor
pair `(k, m)` of `n` carries a slice bound with exponent `E k m ≤ n - 1`, then
the whole imprimitive bad set is `O(H^(n-1))`. -/
theorem imprimitiveBad_isBigO_of_sliceExp (n : ℕ) (hn : 3 ≤ n) (ee : ℕ → ℕ → ℝ)
    (hE : ∀ k m : ℕ, 2 ≤ k → 2 ≤ m → k * m = n → ee k m ≤ (n : ℝ) - 1)
    (hbb : ImprimitiveSliceBoundExp n ee) :
    (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ (n - 1 : ℕ)) := by
  classical
  let C : ℕ × ℕ → ℝ := fun p =>
    if h : (2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = n) then (hbb p.1 p.2 h.1 h.2.1 h.2.2).choose else 0
  have hC0 : ∀ p, 0 ≤ C p := by
    intro p
    by_cases h : (2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 = n)
    · dsimp only [C]
      rw [dif_pos h]
      exact (hbb p.1 p.2 h.1 h.2.1 h.2.2).choose_spec.1
    · dsimp only [C]
      rw [dif_neg h]
  have hCbd : ∀ k m : ℕ, 2 ≤ k → 2 ≤ m → k * m = n → ∀ H : ℕ,
      ((imprimSlice n H k).ncard : ℝ) ≤ C (k, m) * ((H : ℝ) + 1) ^ (ee k m) := by
    intro k m h1 h2 h3 H
    dsimp only [C]
    rw [dif_pos ⟨h1, h2, h3⟩]
    exact (hbb k m h1 h2 h3).choose_spec.2 H
  refine IsBigO.of_bound ((∑ p ∈ blockPairs n, C p) * 2 ^ ((n : ℝ) - 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with H hH1
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hbase : (1 : ℝ) ≤ (H : ℝ) + 1 := by linarith
  -- the finite union is finite
  have hfin : (⋃ p ∈ blockPairs n, imprimSlicePair n H p).Finite :=
    (box_finite n H).subset fun f hf => by
      simp only [Set.mem_iUnion] at hf
      obtain ⟨p, hp, hfp⟩ := hf
      exact hfp.1
  have hstep1 : (ImprimitiveBad n H).ncard ≤ ∑ p ∈ blockPairs n, (imprimSlicePair n H p).ncard :=
    (Set.ncard_le_ncard (imprimitiveBad_subset_iUnion_slice n H hn) hfin).trans
      (ncard_biUnion_le _ _)
  have hstep2 : ∀ p : ℕ × ℕ, p ∈ blockPairs n →
      ((imprimSlicePair n H p).ncard : ℝ) ≤ C p * ((H : ℝ) + 1) ^ ((n : ℝ) - 1) := by
    intro p hp
    obtain ⟨hk2, hm2, hkm⟩ := (Finset.mem_filter.mp hp).2
    refine (hCbd p.1 p.2 hk2 hm2 hkm H).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC0 p)
    exact Real.rpow_le_rpow_of_exponent_le hbase (hE p.1 p.2 hk2 hm2 hkm)
  have hstep3 : ∑ p ∈ blockPairs n, ((imprimSlice n H p.1).ncard : ℝ)
      ≤ (∑ p ∈ blockPairs n, C p) * ((H : ℝ) + 1) ^ ((n : ℝ) - 1) := by
    calc ∑ p ∈ blockPairs n, ((imprimSlicePair n H p).ncard : ℝ)
        ≤ ∑ p ∈ blockPairs n, C p * ((H : ℝ) + 1) ^ ((n : ℝ) - 1) :=
          Finset.sum_le_sum hstep2
      _ = (∑ p ∈ blockPairs n, C p) * ((H : ℝ) + 1) ^ ((n : ℝ) - 1) := (Finset.sum_mul ..).symm
  have hcast : ((∑ p ∈ blockPairs n, (imprimSlicePair n H p).ncard : ℕ) : ℝ)
      = ∑ p ∈ blockPairs n, ((imprimSlicePair n H p).ncard : ℝ) := by
    push_cast
    ring
  have hmain : ((ImprimitiveBad n H).ncard : ℝ)
      ≤ (∑ p ∈ blockPairs n, C p) * ((H : ℝ) + 1) ^ ((n : ℝ) - 1) := by
    calc ((ImprimitiveBad n H).ncard : ℝ)
        ≤ ((∑ p ∈ blockPairs n, (imprimSlicePair n H p).ncard : ℕ) : ℝ) := by exact_mod_cast hstep1
      _ = ∑ p ∈ blockPairs n, ((imprimSlicePair n H p).ncard : ℝ) := hcast
      _ ≤ _ := hstep3
  -- bound `(H+1)^(n-1) ≤ 2^(n-1) * H^(n-1)`
  have hsplit : ((H : ℝ) + 1) ^ ((n : ℝ) - 1) ≤ (2 : ℝ) ^ ((n : ℝ) - 1) * (H : ℝ) ^ ((n : ℝ) - 1) := by
    have h2H : (H : ℝ) + 1 ≤ 2 * (H : ℝ) := by linarith
    have h0 : (0 : ℝ) ≤ (H : ℝ) + 1 := by linarith
    calc ((H : ℝ) + 1) ^ ((n : ℝ) - 1)
        ≤ ((2 : ℝ) * (H : ℝ)) ^ ((n : ℝ) - 1) :=
          Real.rpow_le_rpow h0 h2H (by
            have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith)
      _ = (2 : ℝ) ^ ((n : ℝ) - 1) * (H : ℝ) ^ ((n : ℝ) - 1) :=
          Real.mul_rpow (by norm_num) (by positivity)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have heq : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  calc ((ImprimitiveBad n H).ncard : ℝ)
      ≤ (∑ p ∈ blockPairs n, C p) * ((H : ℝ) + 1) ^ ((n : ℝ) - 1) := hmain
    _ ≤ (∑ p ∈ blockPairs n, C p) * ((2 : ℝ) ^ ((n : ℝ) - 1) * (H : ℝ) ^ ((n : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hsplit
          (Finset.sum_nonneg fun p _ => hC0 p)
    _ = ((∑ p ∈ blockPairs n, C p) * 2 ^ ((n : ℝ) - 1)) * (H : ℝ) ^ ((n : ℝ) - 1) := by ring
    _ = ((∑ p ∈ blockPairs n, C p) * 2 ^ ((n : ℝ) - 1)) * ((H : ℝ) ^ (n - 1 : ℕ)) := by
        rw [← Real.rpow_natCast (H : ℝ) (n - 1), heq]

/-- **The challenge theorem for composite `n ≥ 6`** from slice bounds with
exponents `E k m ≤ n - 1`: van der Waerden's conjecture in degree `n` follows
from the imprimitive slice bounds together with Schmidt's field count (a
theorem of this project). -/
theorem theorem_1_of_sliceExp (n : ℕ) (hn : 6 ≤ n) (ee : ℕ → ℕ → ℝ)
    (hE : ∀ k m : ℕ, 2 ≤ k → 2 ≤ m → k * m = n → ee k m ≤ (n : ℝ) - 1)
    (hbb : ImprimitiveSliceBoundExp n ee) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact theorem_1_of_fieldCountBound n (by omega) (((n : ℝ) + 2) / 4) hβ
    (weylM_exponent_schmidt n hn) (fieldCountBound_schmidt n (by omega))
    (imprimitiveBad_isBigO_of_sliceExp n (by omega) ee hE hbb)

end

end Submission.Vdw
