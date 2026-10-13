import Mathlib
import Submission.Work.DSM5b.honestVanishingDefs
import Submission.Work.DSM5b.tupRng_del_eq_of_card_le
import Submission.Work.DSM5b.HCd_block_vanishing

/-!
# DSM5b — raising the image-size support condition by one

`SuppAbove j z` (`Submission/Work/DSM5b/honestVanishingDefs.lean`) says that `z` vanishes on every
tuple whose range has fewer than `j` elements.  This file proves that if, in addition, for each
`j`-element subset `S ⊆ ι` there is a *block solution* `y_S` — a cochain of degree one less, carried
by the tuples of range exactly `S`, whose coboundary reproduces `z` on all of those tuples — then a
single cochain `y` exists with `SuppAbove (j + 1) (z - HCd t m y)`: the support condition can be
raised by one at the price of subtracting one coboundary.

The point is that the block solutions add up without interference.  Take `y = ∑_S y_S`, the sum over
the `j`-element subsets `S`.  For a tuple `τ` of range `T`:

* every deleted tuple `tupDel i τ` has range `⊆ T`, so if `S` has `j` elements and
  `tupRng (tupDel i τ) = S`, then `S ⊆ T` and `card S = j ≥ card T ≥ card S`, whence `S = T`
  (`Work.DSM5b.tupRng_del_eq_of_card_le`); consequently `y_S` contributes to `(HCd t m y) τ` only
  when `S = T`;
* if `S ≠ T` and `card S = j` the contribution is therefore zero — this is the block-diagonality of
  `HCd` on the graded piece `card = j` of the filtration, `Work.DSM5b.HCd_block_vanishing`; note
  that it is the *cardinality* hypothesis `card S = j` that makes a single `y` work for all the
  blocks at once;
* if `S = T` the block condition gives `(HCd t m y_S) τ = z τ`, and it gives it *only there* —
  which is why the block solutions may be summed without further bookkeeping.

Hence `(HCd t m y) τ = z τ` for every `τ` with `card (tupRng τ) = j`, and `(HCd t m y) τ = 0` for
every `τ` with `card (tupRng τ) < j` (where already `z τ = 0` by `hsupp`): that is,
`z - HCd t m y` vanishes on all tuples of range `< j + 1`, as claimed.
-/

namespace Work.DSM5b

open DSMap DSMap.Mix DSMap.Mix2

universe a

set_option linter.unusedVariables false

lemma honestVanishingRaise {ι : Type a} [Fintype ι] [DecidableEq ι] {R : Type a} [CommRing R]
    (t : ι → R) {j m : ℕ} (hj : j ≤ m + 1) (z : HCX t (m + 1)) (hsupp : SuppAbove j z)
    (hblock : ∀ S : Finset ι, S.card = j → ∃ y : HCX t m,
      (∀ σ : Fin (m + 1) → ι, tupRng σ ≠ S → y σ = 0) ∧
      ∀ τ : Fin (m + 2) → ι, tupRng τ = S → (HCd t m y) τ = z τ) :
    ∃ y : HCX t m, SuppAbove (j + 1) (z - HCd t m y) := by
  classical
  -- a block solution for every `j`-element subset, and `0` elsewhere
  let yf : Finset ι → HCX t m :=
    fun S => if h : S.card = j then Classical.choose (hblock S h) else 0
  have hyf_eq : ∀ (S : Finset ι) (hS : S.card = j), yf S = Classical.choose (hblock S hS) := by
    intro S hS
    show (if h : S.card = j then Classical.choose (hblock S h) else 0) =
      Classical.choose (hblock S hS)
    rw [dite_eq_left hS]
  have hyf_zero : ∀ (S : Finset ι) (hS : S.card = j) (σ : Fin (m + 1) → ι),
      tupRng σ ≠ S → yf S σ = 0 := by
    intro S hS σ hσ
    rw [hyf_eq S hS]
    exact (Classical.choose_spec (hblock S hS)).1 σ hσ
  have hyf_block : ∀ (S : Finset ι) (hS : S.card = j) (τ : Fin (m + 2) → ι),
      tupRng τ = S → HCd t m (yf S) τ = z τ := by
    intro S hS τ hτ
    rw [hyf_eq S hS]
    exact (Classical.choose_spec (hblock S hS)).2 τ hτ
  have hyf_zero' : ∀ S : Finset ι, S.card ≠ j → yf S = 0 := by
    intro S hS
    show (if h : S.card = j then Classical.choose (hblock S h) else 0) = 0
    rw [dite_eq_right hS]
  -- the candidate: the sum of the block solutions
  refine ⟨∑ S : Finset ι, yf S, ?_⟩
  intro τ hτ
  have hcard : (tupRng τ).card ≤ j := by omega
  have hsum : HCd t m (∑ S : Finset ι, yf S) τ = ∑ S : Finset ι, HCd t m (yf S) τ := by
    simp only [map_sum, Finset.sum_apply]
  -- a block is invisible away from its own range
  have hzero : ∀ S : Finset ι, S.card = j → tupRng τ ≠ S → HCd t m (yf S) τ = 0 :=
    fun S hS hne => HCd_block_vanishing t hS (hyf_zero S hS) hcard hne
  have hzero_nj : ∀ S : Finset ι, S.card ≠ j → HCd t m (yf S) τ = 0 := by
    intro S hS
    rw [hyf_zero' S hS]
    simp
  rw [Pi.sub_apply, hsum]
  rcases lt_or_eq_of_le hcard with hlt | heq
  · -- fewer than `j` values: `z` vanishes and so does the whole coboundary
    have hz0 : z τ = 0 := hsupp τ hlt
    have hzsum : ∑ S : Finset ι, HCd t m (yf S) τ = 0 := by
      refine Finset.sum_eq_zero fun S _ => ?_
      by_cases hS : S.card = j
      · refine hzero S hS fun hc => ?_
        rw [hc] at hlt
        omega
      · exact hzero_nj S hS
    rw [hzsum, hz0]
    simp
  · -- exactly `j` values: only the block of `tupRng τ` contributes, and it gives `z τ`
    have hsingle : ∀ S : Finset ι, HCd t m (yf S) τ = if S = tupRng τ then z τ else 0 := by
      intro S
      by_cases h : S = tupRng τ
      · rw [ite_eq_left h, h]
        exact hyf_block (tupRng τ) heq τ rfl
      · rw [ite_eq_right h]
        by_cases hS : S.card = j
        · exact hzero S hS fun hc => h hc.symm
        · exact hzero_nj S hS
    rw [Finset.sum_congr rfl fun S _ => hsingle S]
    simp

end Work.DSM5b
