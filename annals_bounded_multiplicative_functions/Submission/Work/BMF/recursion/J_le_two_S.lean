import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.struct
import Submission.Work.BMF.recursion.card_pair_fibre_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Wooley's AM–GM step for the Vinogradov–Linnik recursion

We prove `Work.BMF.recursion.J_le_two_S`: the number of matching pairs `J S k Q` is at most
twice the sum of the two "head-distinct on both sides" counts `S1pair` and `S2pair`
(Wooley, Michigan Math. J. **40** (1993), 175–180, §2).

The argument is the one described in the statement of the theorem:

* `solSet_card_split` splits `J = S1pair + mixedPair + S2pair`, and `card_mixed_swap` shows the
  two "mixed" parts have equal cardinality, so `mixedPair = 2 · headMix`.
* The fibre decomposition `card_pair_fibre_sum` of the moment map `powerSums k` over the two
  fibres `A = hdSet` and `B = nhdSet` identifies
  `headMix = Σ_v R₁(v)·R₂(v)`, `S1pair = Σ_v R₁(v)²` and `S2pair = Σ_v R₂(v)²`.
* The termwise AM–GM inequality `2·a·b ≤ a² + b²` then gives `2·headMix ≤ S1pair + S2pair`.

The auxiliary lemmas are collected in the namespace `Work.BMF.recursion.JleTwoS` so that they
can be reused without clashing with colleagues' names.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

noncomputable section

namespace JleTwoS

open Submission.Vinogradov (powerSums)

/-- `Finset.card`-valued form of `card_pair_fibre_sum`: the number of pairs `(x,y) ∈ A × B` with
`f x = f y` is the sum over the fibres of `f` of the products of the two fibre counts. -/
theorem card_pair_fibre_sum_nat {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (A B : Finset α) :
    ((Finset.univ : Finset (α × α)).filter
        (fun p => f p.1 = f p.2 ∧ p.1 ∈ A ∧ p.2 ∈ B)).card
      = ∑ v ∈ Finset.univ.image f,
          (A.filter (fun x => f x = v)).card * (B.filter (fun x => f x = v)).card := by
  have h := card_pair_fibre_sum f A B
  exact_mod_cast h

/-- Fibre decomposition of the mixed count: `headMix` is the sum over the fibres of the moment map
of the products `R₁(v)·R₂(v)` of the fibre counts with distinct and non-distinct head. -/
theorem headMix_eq_sum (S k Q : ℕ) (hkS : k ≤ S) :
    headMix S k Q hkS
      = ∑ v ∈ momImg S k Q,
          ((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card *
          ((nhdSet S k Q hkS).filter (fun x => powerSums k x = v)).card := by
  classical
  rw [headMix]
  rw [show (solSet S k Q).filter (fun p : PairSpace S Q => HD hkS p.1 ∧ ¬ HD hkS p.2)
      = (Finset.univ : Finset (PairSpace S Q)).filter
          (fun p => powerSums k p.1 = powerSums k p.2 ∧
            p.1 ∈ hdSet S k Q hkS ∧ p.2 ∈ nhdSet S k Q hkS)
      from by ext p; simp [solSet, hdSet, nhdSet, matches_iff]]
  rw [card_pair_fibre_sum_nat (powerSums k) (hdSet S k Q hkS) (nhdSet S k Q hkS)]
  simp only [momImg]

/-- Fibre decomposition of `S1pair`: the sum of squares of the fibre counts with distinct head. -/
theorem S1pair_eq_sum (S k Q : ℕ) (hkS : k ≤ S) :
    S1pair S k Q hkS
      = ∑ v ∈ momImg S k Q,
          ((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card *
          ((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card := by
  classical
  rw [S1pair]
  rw [show (solSet S k Q).filter (fun p : PairSpace S Q => HD hkS p.1 ∧ HD hkS p.2)
      = (Finset.univ : Finset (PairSpace S Q)).filter
          (fun p => powerSums k p.1 = powerSums k p.2 ∧
            p.1 ∈ hdSet S k Q hkS ∧ p.2 ∈ hdSet S k Q hkS)
      from by ext p; simp [solSet, hdSet, matches_iff]]
  rw [card_pair_fibre_sum_nat (powerSums k) (hdSet S k Q hkS) (hdSet S k Q hkS)]
  simp only [momImg]

/-- Fibre decomposition of `S2pair`: the sum of squares of the fibre counts with non-distinct
head. -/
theorem S2pair_eq_sum (S k Q : ℕ) (hkS : k ≤ S) :
    S2pair S k Q hkS
      = ∑ v ∈ momImg S k Q,
          ((nhdSet S k Q hkS).filter (fun x => powerSums k x = v)).card *
          ((nhdSet S k Q hkS).filter (fun x => powerSums k x = v)).card := by
  classical
  rw [S2pair]
  rw [show (solSet S k Q).filter (fun p : PairSpace S Q => ¬ HD hkS p.1 ∧ ¬ HD hkS p.2)
      = (Finset.univ : Finset (PairSpace S Q)).filter
          (fun p => powerSums k p.1 = powerSums k p.2 ∧
            p.1 ∈ nhdSet S k Q hkS ∧ p.2 ∈ nhdSet S k Q hkS)
      from by ext p; simp [solSet, nhdSet, matches_iff]]
  rw [card_pair_fibre_sum_nat (powerSums k) (nhdSet S k Q hkS) (nhdSet S k Q hkS)]
  simp only [momImg]

/-- The mixed part of the solution set splits into the two one-sided parts. -/
theorem mixedPair_eq_headMix_add_headMix2 (S k Q : ℕ) (hkS : k ≤ S) :
    mixedPair S k Q hkS = headMix S k Q hkS + headMix2 S k Q hkS := by
  classical
  rw [mixedPair, headMix, headMix2]
  rw [Finset.filter_or]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    tauto)]

/-- Wooley's AM–GM step: the mixed count is at most the average of the two head-distinct counts. -/
theorem two_headMix_le (S k Q : ℕ) (hkS : k ≤ S) :
    2 * headMix S k Q hkS ≤ S1pair S k Q hkS + S2pair S k Q hkS := by
  rw [headMix_eq_sum, S1pair_eq_sum, S2pair_eq_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have h := two_mul_le_add_sq
    (((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card)
    (((nhdSet S k Q hkS).filter (fun x => powerSums k x = v)).card)
  nlinarith [h]

end JleTwoS

/-- The solution count is at most twice the sum of the two "head-distinct" counts
(Wooley, Michigan Math. J. **40** (1993), 175–180, §2).  `J S k Q` is the Vinogradov count,
`S1pair S k Q hkS` counts the matching pairs of `S`-tuples in `[1,Q]` whose head (first `k`
coordinates) is pairwise distinct on both sides, and `S2pair S k Q hkS` the matching pairs whose
head is non-distinct on both sides.

Route.  `solSet_card_split` (`Submission.Work.BMF.recursion.struct`) gives
`J = S1pair + mixedPair + S2pair` (as reals, via `J_eq_solSet`), `card_mixed_swap` gives
`headMix2 = headMix`, hence `mixedPair = 2·headMix`.  For the AM-GM step use the fibre
decomposition `card_pair_fibre_sum` with `f := powerSums k`, `A := hdSet S k Q hkS`,
`B := nhdSet S k Q hkS` (and the identifications `R1 v = #(hdSet ∩ fib v)`,
`R2 v = #(nhdSet ∩ fib v)`, `p ∈ solSet ↔ Matches S k Q p ↔ powerSums k p.1 = powerSums k p.2`):
it gives `headMix = Σ_v R1 v · R2 v`, `S1pair = Σ_v (R1 v)²`, `S2pair = Σ_v (R2 v)²`, and
`2·a·b ≤ a² + b²` termwise yields `2·headMix ≤ S1pair + S2pair`. -/
theorem J_le_two_S (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) :
    LeanEval.NumberTheory.VinogradovMeanValue.J S k Q ≤
      2 * ((S1pair S k Q hkS : ℝ) + (S2pair S k Q hkS : ℝ)) := by
  rw [J_eq_solSet, solSet_card_split S k Q hkS]
  have hmix : (mixedPair S k Q hkS : ℝ) = 2 * (headMix S k Q hkS : ℝ) := by
    rw [JleTwoS.mixedPair_eq_headMix_add_headMix2, card_mixed_swap S k Q hkS]
    push_cast
    ring
  have hAM : (2 : ℝ) * (headMix S k Q hkS : ℝ)
      ≤ (S1pair S k Q hkS : ℝ) + (S2pair S k Q hkS : ℝ) := by
    exact_mod_cast JleTwoS.two_headMix_le S k Q hkS
  rw [hmix]
  linarith

end

end Work.BMF.recursion
