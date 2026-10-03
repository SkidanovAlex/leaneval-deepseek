import Mathlib
import Submission.Work.KMTAreas.A4Z.SivLocal

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4Z

/-!
# The block remainder is small on the complement of a large finite set of blocks

`blockRemainder L f S = f - ∑_{i ∈ S} zPiece L f i` is `f` with the blocks indexed by `S` removed.
Since the pieces `zPiece L f i` are the restrictions of `f` to the disjoint blocks
`[iL, (i+1)L)`, the remainder is exactly the part of `f` carried by the *complementary* blocks, so

`l2sq (blockRemainder L f S) = ∑'_i [i ∉ S] l2sq (zPiece L f i)`,

and the right-hand side is the tail `l2sq f - ∑_{i∈S} l2sq (zPiece L f i)` of a summable family.
As `S` grows to exhaust `ℤ` this tends to `0`; taking square roots gives the `ℓ²` statement.

The main consumers are the assembly of Corollary `siv-second` (see `SivMainCore.lean`) and the
`ℓ²`-continuity of the operator `T = (1-Π)Ã_N^{**}(·,h)` over block sums.
-/

/-- **The pointwise form of the block remainder.**  At `x` the remainder keeps `f x` unless the
block index `x / L` has been removed. -/
theorem blockRemainder_apply (L : ℤ) (f : ℤ → ℂ) (S : Finset ℤ) (x : ℤ) :
    blockRemainder L f S x = if x / L ∈ S then 0 else f x := by
  have h : (∑ i ∈ S, zPiece L f i x) = if x / L ∈ S then f x else 0 := by
    simp only [zPiece_apply]
    exact Finset.sum_ite_eq' S (x / L) (fun _ => f x)
  simp only [blockRemainder, h]
  split_ifs <;> simp

/-- **The squared `ℓ²` norm of the block remainder is the sum of the squared `ℓ²` norms of the
complementary blocks.** -/
theorem l2sq_blockRemainder_eq {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ}
    (hf : Summable (fun x : ℤ => ‖f x‖ ^ 2)) (S : Finset ℤ) :
    l2sq (blockRemainder L f S)
      = ∑' i : ℤ, if i ∈ S then 0 else l2sq (zPiece L f i) := by
  have hpt : ∀ x : ℤ, ‖blockRemainder L f S x‖ ^ 2
      = (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ) := by
    intro x
    rw [blockRemainder_apply]
    split_ifs <;> simp
  have h1 : l2sq (blockRemainder L f S)
      = ∑' x : ℤ, (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ) := by
    simp only [l2sq]
    exact tsum_congr hpt
  have hgnn : ∀ x : ℤ, 0 ≤ (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ) := by
    intro x
    split_ifs with hx
    · exact le_refl 0
    · exact sq_nonneg _
  have hgle : ∀ x : ℤ, (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ) ≤ ‖f x‖ ^ 2 := by
    intro x
    split_ifs with hx
    · exact sq_nonneg _
    · exact le_refl _
  have hgsum : Summable (fun x : ℤ => (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ)) :=
    Summable.of_nonneg_of_le hgnn hgle hf
  have hgnorm : Summable (fun x : ℤ => ‖(if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ)‖) := by
    have h : (fun x : ℤ => ‖(if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ)‖)
        = fun x : ℤ => (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ) := by
      funext x
      exact Real.norm_of_nonneg (hgnn x)
    rw [h]
    exact hgsum
  have hblocks := tsum_eq_sum_blocks hL
    (g := fun x : ℤ => (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ)) hgnorm
  have hinner : ∀ m : ℤ,
      (∑ x ∈ Finset.Ico (m * L) ((m + 1) * L), (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ))
        = (if m ∈ S then 0 else l2sq (zPiece L f m) : ℝ) := by
    intro m
    have hstep : (∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
          (if x / L ∈ S then 0 else ‖f x‖ ^ 2 : ℝ))
        = (if m ∈ S then 0 else ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L), ‖f x‖ ^ 2 : ℝ) := by
      by_cases hm : m ∈ S
      · rw [if_pos hm]
        refine Finset.sum_eq_zero fun x hxmem => ?_
        have hx : x / L = m :=
          (ediv_eq_of_mem_Ico hL (Finset.mem_Ico.mp hxmem).1 (Finset.mem_Ico.mp hxmem).2).symm
        rw [hx, if_pos hm]
      · rw [if_neg hm]
        refine Finset.sum_congr rfl fun x hxmem => ?_
        have hx : x / L = m :=
          (ediv_eq_of_mem_Ico hL (Finset.mem_Ico.mp hxmem).1 (Finset.mem_Ico.mp hxmem).2).symm
        rw [hx, if_neg hm]
    rw [hstep]
    by_cases hm : m ∈ S
    · simp [hm]
    · rw [if_neg hm, if_neg hm]
      exact (l2sq_zPiece hL f m).symm
  rw [h1, hblocks]
  exact tsum_congr hinner

/-- **The tail of a summable family over the complement of `S` tends to `0` as `S` exhausts the
index set.** -/
theorem tendsto_tsum_ite_compl {a : ℤ → ℝ} (ha : Summable a) :
    Tendsto (fun S : Finset ℤ => ∑' i : ℤ, if i ∈ S then 0 else a i)
      atTop (nhds 0) := by
  have hb : ∀ S : Finset ℤ, Summable (fun i : ℤ => if i ∈ S then a i else 0) := by
    intro S
    exact summable_of_ne_finset_zero (s := S) fun i hi => by simp [hi]
  have hkey : ∀ S : Finset ℤ,
      (∑' i : ℤ, if i ∈ S then 0 else a i) = (∑' i : ℤ, a i) - ∑ i ∈ S, a i := by
    intro S
    have hbS : Summable (fun i : ℤ => if i ∈ S then a i else 0) := hb S
    calc (∑' i : ℤ, if i ∈ S then 0 else a i)
        = ∑' i : ℤ, (a i - (if i ∈ S then a i else 0)) :=
          tsum_congr fun i => by by_cases hi : i ∈ S <;> simp [hi]
      _ = (∑' i : ℤ, a i) - ∑' i : ℤ, (if i ∈ S then a i else 0) :=
          Summable.tsum_sub ha hbS
      _ = (∑' i : ℤ, a i) - ∑ i ∈ S, a i := by
          congr 1
          rw [tsum_eq_sum (α := ℝ) (L := SummationFilter.unconditional ℤ) (s := S)
            (f := fun i : ℤ => if i ∈ S then a i else 0) (fun i hi => by simp [hi])]
          exact Finset.sum_congr rfl fun i hi => by simp [hi]
  have hsub : Tendsto (fun S : Finset ℤ => (∑' i : ℤ, a i) - ∑ i ∈ S, a i)
      atTop (nhds ((∑' i : ℤ, a i) - (∑' i : ℤ, a i))) :=
    ha.hasSum.const_sub _
  have hsub' : Tendsto (fun S : Finset ℤ => (∑' i : ℤ, a i) - ∑ i ∈ S, a i)
      atTop (nhds 0) := by
    simpa using hsub
  refine hsub'.congr (fun S => ?_)
  exact (hkey S).symm

theorem tendsto_l2norm_blockRemainder {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    Filter.Tendsto (fun S : Finset ℤ =>
        Work.KMTAreas.A4Z.l2norm (Work.KMTAreas.A4Z.blockRemainder L f S))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hf2 : Summable (fun x : ℤ => ‖f x‖ ^ 2) :=
    Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hf
  have ha : Summable (fun i : ℤ => l2sq (zPiece L f i)) := summable_l2sq_zPiece hL hf2
  have hF : Tendsto (fun S : Finset ℤ => l2sq (blockRemainder L f S)) atTop (nhds 0) := by
    have htail := tendsto_tsum_ite_compl ha
    have hfun : (fun S : Finset ℤ => l2sq (blockRemainder L f S))
        = fun S : Finset ℤ => ∑' i : ℤ, if i ∈ S then 0 else l2sq (zPiece L f i) :=
      funext fun S => l2sq_blockRemainder_eq hL hf2 S
    rw [hfun]
    exact htail
  have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hF
  simpa only [l2norm, Function.comp_def, Real.sqrt_zero] using hcomp

end Work.KMTAreas.A4Z
