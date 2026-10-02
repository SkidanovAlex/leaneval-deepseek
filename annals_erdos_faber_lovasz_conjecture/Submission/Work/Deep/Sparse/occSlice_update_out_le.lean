/-
# The one-vertex recolouring estimate for `occSlice`

`occSlice G f v J = ∑_{2 ≤ j ≤ J} occW j · #{c : j ≤ colourClassCount G f v c}` is the
truncated occupancy statistic of `Submission.Work.Deep.Sparse.NcpDefs` (the slice form of
`occClass`), the quantity whose concentration drives the naive colouring procedure.

This module proves the *stability* estimate used when a single coordinate of the random
colouring is varied: recolouring one vertex `z` (not a neighbour of `v`) changes `occSlice`
by at most `occWsum J` times the number of common neighbours of `z` and `v` carrying the two
colours involved in the recolouring.  Concretely, for `f' = update f z x`,

  `|occSlice G f' v J - occSlice G f v J| ≤ occWsum J · (t_{f z} + t_x)`,

where `t_c = #{y ∈ N(z) ∩ N(v) : f y = c}` counts the common neighbours of `z` and `v`
carrying the colour `c` in the *original* colouring `f`.

The two ingredients are:

* the class sizes `colourClassCount G · v c` change only for the two colours `f z` and `x`
  (`colourClassCount_update_eq_of_ne`), because for any other colour `c` the recolouring
  changes neither the colour of any vertex of colour `c` nor the retainedness of any such
  vertex (the only vertex whose colour moved is `z`, and it moved to `x ≠ c`);
* the truncated class contribution `occHtrunc J` is `occWsum J`-Lipschitz in the class size
  (`occHtrunc_sub_le`), and each of the two surviving class sizes moves by at most `t_c`
  (`colourClassCount_update_abs_le`).

The statistic is first rewritten in the class form `occClass` so that the already-proved
Lipschitz bound `occHtrunc_sub_le` applies termwise.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.occHtrunc_eq_sum
import Submission.Work.Deep.Sparse.occHtrunc_sub_le
import Submission.Work.Deep.Sparse.colourClassCount_update_abs_le

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

/-! ## Auxiliary lemmas -/

/-- The slice form `occSlice` and the class form `occClass` of the truncated occupancy
statistic agree.  Both are partial sums of the increments `occW j`: `occHtrunc J n` is
`∑_{2 ≤ j ≤ J} occW j · [j ≤ n]`, and summing the indicator over the colours counts the
colour classes of size at least `j`. -/
private lemma occClass_eq_occSlice_aux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (f : V → Fin k) (v : V) (J : ℕ) :
    occClass G f v J = occSlice G f v J := by
  classical
  unfold occClass occSlice
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ (Finset.univ : Finset (Fin k))) =>
        occHtrunc_eq_sum J (colourClassCount G f v c))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.natCast_card_filter (fun c => j ≤ colourClassCount G f v c) Finset.univ).symm

/-- **Only two colours move.**  If `c` is neither the old colour `f z` nor the new colour `x`
of the recoloured vertex, then the `c`-class size of `v` is unchanged by the recolouring of
`z`.  Indeed, for a vertex `w ≠ z` the colours agree, and `w` is retained after the
recolouring exactly when it was before: the only colour that changed is the one at `z`, which
is neither `c` (before) nor `c` (after). -/
private lemma colourClassCount_update_eq_of_ne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k)
    (v z : V) (x c : Fin k) (hzc : c ≠ f z) (hxc : c ≠ x) :
    colourClassCount G (Function.update f z x) v c = colourClassCount G f v c := by
  classical
  -- the colour `c` is avoided by the same vertices before and after the update
  have hpt : ∀ u : V, Function.update f z x u ≠ c ↔ f u ≠ c := by
    intro u
    by_cases hu : u = z
    · rw [hu, Function.update_self]
      exact iff_of_true (fun h => hxc h.symm) (fun h => hzc h.symm)
    · rw [Function.update_of_ne hu]
  -- hence the two filtered predicates on `N(v)` are equivalent
  have hiff : ∀ w : V, (Retained G (Function.update f z x) w ∧ Function.update f z x w = c)
      ↔ (Retained G f w ∧ f w = c) := by
    intro w
    by_cases hw : w = z
    · rw [hw, Function.update_self]
      constructor
      · exact fun h => (hxc h.2.symm).elim
      · exact fun h => (hzc h.2.symm).elim
    · have hfw : Function.update f z x w = f w := Function.update_of_ne hw x f
      rw [hfw]
      constructor
      · rintro ⟨hr, hwc⟩
        refine ⟨?_, hwc⟩
        intro u hu
        have h1 : Function.update f z x u ≠ Function.update f z x w := hr u hu
        rw [hfw, hwc] at h1
        rw [hpt u] at h1
        rw [hwc]
        exact h1
      · rintro ⟨hr, hwc⟩
        refine ⟨?_, hwc⟩
        intro u hu
        have h1 : f u ≠ f w := hr u hu
        rw [hwc] at h1
        rw [← hpt u] at h1
        have h2 : Function.update f z x w = c := by rw [hfw, hwc]
        rw [h2]
        exact h1
  unfold colourClassCount
  congr 1
  exact Finset.filter_congr fun w _ => hiff w

/-- A sum over `Fin k` against a function vanishing off two points.  This is the bookkeeping
lemma that concentrates the sum `∑_c |colourClassCount G f' v c - colourClassCount G f v c|`
onto the two colours `a = f z` and `b = x` that can actually move. -/
private lemma sum_univ_le_two {k : ℕ} {A B : ℝ} (g : Fin k → ℝ) (a b : Fin k)
    (h0 : ∀ c, c ≠ a → c ≠ b → g c = 0) (ha : g a ≤ A) (hb : g b ≤ B) (hB : 0 ≤ B) :
    ∑ c : Fin k, g c ≤ A + B := by
  classical
  rcases eq_or_ne a b with rfl | hab
  · have h1 : ∑ c : Fin k, g c = g a :=
      (Finset.sum_subset (Finset.subset_univ ({a} : Finset (Fin k))) ?_).symm.trans
        (Finset.sum_singleton g a)
    · rw [h1]; linarith
    · intro c _ hc
      simp only [Finset.mem_singleton] at hc
      exact h0 c hc hc
  · have h1 : ∑ c : Fin k, g c = g a + g b :=
      (Finset.sum_subset (Finset.subset_univ (insert a ({b} : Finset (Fin k)))) ?_).symm.trans
        (by rw [Finset.sum_insert (by simpa using hab)]; simp)
    · rw [h1]; exact add_le_add ha hb
    · intro c _ hc
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      exact h0 c hc.1 hc.2

/-! ## The one-vertex recolouring estimate -/

theorem occSlice_update_out_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k J : ℕ} (f : V → Fin k)
    (v : V) {z : V} (hz : z ∉ G.neighborFinset v) (x : Fin k) :
    |occSlice G (Function.update f z x) v J - occSlice G f v J|
      ≤ occWsum J * (((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = f z)).card : ℝ)
          + ((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = x)).card : ℝ)) := by
  classical
  -- the colours other than `f z` and `x` do not move
  have h0 : ∀ c : Fin k, c ≠ f z → c ≠ x →
      |((colourClassCount G (Function.update f z x) v c : ℝ)
        - (colourClassCount G f v c : ℝ))| = 0 := by
    intro c hc1 hc2
    rw [colourClassCount_update_eq_of_ne G f v z x c hc1 hc2, sub_self, abs_zero]
  -- so the total variation of the class sizes is at most `t_{f z} + t_x`
  have hsum : ∑ c : Fin k, |((colourClassCount G (Function.update f z x) v c : ℝ)
        - (colourClassCount G f v c : ℝ))|
      ≤ (((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = f z)).card : ℝ)
          + ((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = x)).card : ℝ)) :=
    sum_univ_le_two (fun c => |((colourClassCount G (Function.update f z x) v c : ℝ)
        - (colourClassCount G f v c : ℝ))|) (f z) x h0
      (colourClassCount_update_abs_le G f v hz x (f z))
      (colourClassCount_update_abs_le G f v hz x x)
      (Nat.cast_nonneg _)
  -- rewrite the slice statistic in the class form, where the differences telescope
  have hstep : occSlice G (Function.update f z x) v J - occSlice G f v J
      = ∑ c : Fin k, (occHtrunc J (colourClassCount G (Function.update f z x) v c)
          - occHtrunc J (colourClassCount G f v c)) := by
    rw [← occClass_eq_occSlice_aux G, ← occClass_eq_occSlice_aux G]
    unfold occClass
    rw [← Finset.sum_sub_distrib]
  rw [hstep]
  calc |∑ c : Fin k, (occHtrunc J (colourClassCount G (Function.update f z x) v c)
          - occHtrunc J (colourClassCount G f v c))|
      ≤ ∑ c : Fin k, |occHtrunc J (colourClassCount G (Function.update f z x) v c)
          - occHtrunc J (colourClassCount G f v c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Fin k, occWsum J * |((colourClassCount G (Function.update f z x) v c : ℝ)
          - (colourClassCount G f v c : ℝ))| := Finset.sum_le_sum fun c _ => occHtrunc_sub_le J _ _
    _ = occWsum J * ∑ c : Fin k, |((colourClassCount G (Function.update f z x) v c : ℝ)
          - (colourClassCount G f v c : ℝ))| := (Finset.mul_sum _ _ _).symm
    _ ≤ occWsum J * (((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = f z)).card : ℝ)
          + ((((G.neighborFinset z) ∩ (G.neighborFinset v)).filter (fun y => f y = x)).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg fun j _ => abs_nonneg _)

end Work.Deep.Sparse
