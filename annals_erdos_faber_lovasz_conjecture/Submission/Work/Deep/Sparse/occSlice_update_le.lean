/-
# A single-coordinate change moves `occSlice` by at most `2 * occWsum J`

`occSlice G f v J` counts, for each level `2 ≤ j ≤ J`, the colours carried by at
least `j` retained neighbours of `v`, weighted by the increment `occW j` of the
class contribution `occH`.

The point of the present lemma (the coordinate Lipschitz bound used by the
Azuma/fibre-mean argument) is that changing the colour of a *single* vertex `u`
can only move mass between **two** colour classes, namely the old colour `f u`
of `u` and the new colour `x`:

* a common neighbour `w` of `u` and `v` that *gains* retention when `f u` is
  changed must have had `f u` as the unique witness of its non-retention, so
  `f w = f u`;
* a common neighbour `w` that *loses* retention must have `f w = x`;
* `u` itself moves from the class of `f u` to the class of `x`.

Consequently every slice cardinality `#{c : j ≤ colourClassCount G f v c}`
changes by at most `2` (the two special colours), and summing the increments
with weights `occW j` gives the bound `2 * occWsum J`.

The identity `occClass = occSlice` (`Submission/Work/Deep/Sparse/occClass_eq_sum_occW.lean`)
gives the same statement in the "classes" reading; here we work directly with
the slices.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Changing `f` at the single vertex `u` does not change the retention status of a
vertex `w ≠ u` whose colour differs from both the old colour `f u` and the new colour `x`. -/
private lemma retained_update_iff {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    {f : V → Fin k} {u : V} {x : Fin k} {w : V} (hw : w ≠ u) {c : Fin k}
    (hc1 : c ≠ f u) (hc2 : c ≠ x) (hfw : f w = c) :
    Retained G (Function.update f u x) w ↔ Retained G f w := by
  have hw' : Function.update f u x w = f w := Function.update_of_ne hw x f
  have key : ∀ z : V, (Function.update f u x z ≠ f w) ↔ (f z ≠ f w) := by
    intro z
    by_cases hzu : z = u
    · have hxu : ¬ (Function.update f u x z = f w) := by
        rw [hzu, Function.update_self]
        exact fun h => hc2 (h.trans hfw).symm
      have hzu' : ¬ (f z = f w) := by
        rw [hzu]
        exact fun h => hc1 (h.trans hfw).symm
      exact iff_of_true hxu hzu'
    · simp only [Function.update_of_ne hzu x f]
  constructor
  · intro h z hz
    exact (key z).mp (by have hh := h z hz; rwa [hw'] at hh)
  · intro h z hz
    have hh := (key z).mpr (h z hz)
    rw [← hw'] at hh
    exact hh

/-- Only the two colour classes of the old colour `f u` and of the new colour `x` can
change when `f` is updated at `u`; every other class keeps its cardinality. -/
private lemma colourClassCount_update_of_ne {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    {f : V → Fin k} {u : V} {x : Fin k} {v : V} {c : Fin k}
    (hc1 : c ≠ f u) (hc2 : c ≠ x) :
    colourClassCount G (Function.update f u x) v c = colourClassCount G f v c := by
  unfold colourClassCount
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro w _
  by_cases hw : w = u
  · rw [hw, Function.update_self]
    constructor
    · rintro ⟨-, h⟩; exact absurd h.symm hc2
    · rintro ⟨-, h⟩; exact absurd h.symm hc1
  · have hw' : Function.update f u x w = f w := Function.update_of_ne hw x f
    rw [hw']
    by_cases hfc : f w = c
    · exact and_congr (retained_update_iff G hw hc1 hc2 hfc) Iff.rfl
    · exact iff_of_false (fun h => hfc h.2) (fun h => hfc h.2)

/-- If two colourings have the same class cardinalities off the two colours `a`, `b`, then
the occupancy numbers of every slice differ by at most `2` (the two exceptional colours). -/
private lemma card_filter_le_add_two {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    {g h : V → Fin k} {a b : Fin k} {j : ℕ}
    (key : ∀ c : Fin k, c ≠ a → c ≠ b → colourClassCount G g v c = colourClassCount G h v c) :
    ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G g v c)).card ≤
      ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G h v c)).card + 2 := by
  classical
  have hsub : ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G g v c)) ⊆
      ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G h v c)) ∪
        ({a, b} : Finset (Fin k)) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    by_cases h1 : c = a
    · exact Finset.mem_union_right _ (by simp [h1])
    · by_cases h2 : c = b
      · exact Finset.mem_union_right _ (by simp [h2])
      · exact Finset.mem_union_left _ (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rwa [key c h1 h2] at hc)
  refine le_trans (Finset.card_le_card hsub) ?_
  have h2 : ({a, b} : Finset (Fin k)).card ≤ 2 := by
    have h := Finset.card_insert_le a ({b} : Finset (Fin k))
    rw [Finset.card_singleton] at h
    simpa using h
  have h3 := Finset.card_union_le
    (Finset.univ.filter (fun c => j ≤ colourClassCount G h v c)) ({a, b} : Finset (Fin k))
  omega

/-- The weighted-slice estimate: if every slice number moves by at most `2`, the weighted
combination with the increments `occW j` moves by at most `2 * occWsum J`. -/
private lemma abs_sum_occW_mul_sub_le {J : ℕ} (S S' : ℕ → ℝ)
    (h : ∀ j, S' j ≤ S j + 2) (h' : ∀ j, S j ≤ S' j + 2) :
    |∑ j ∈ Finset.Icc 2 J, occW j * (S' j - S j)| ≤ 2 * occWsum J := by
  calc |∑ j ∈ Finset.Icc 2 J, occW j * (S' j - S j)|
      ≤ ∑ j ∈ Finset.Icc 2 J, |occW j * (S' j - S j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 2 J, 2 * |occW j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have hd : |S' j - S j| ≤ 2 := abs_le.mpr ⟨by linarith [h' j], by linarith [h j]⟩
        calc |occW j| * |S' j - S j| ≤ |occW j| * 2 := by gcongr
          _ = 2 * |occW j| := by ring
    _ = 2 * occWsum J := by
        rw [occWsum, Finset.mul_sum]

/-- **Lipschitz bound for `occSlice`.** Changing the colour of a single vertex `u` changes the
truncated occupancy statistic of `v` by at most `2 * occWsum J`. -/
theorem occSlice_update_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k J : ℕ} (f : V → Fin k)
    (v u : V) (x : Fin k) :
    |occSlice G (Function.update f u x) v J - occSlice G f v J| ≤ 2 * occWsum J := by
  classical
  set g : V → Fin k := Function.update f u x with hg
  have key : ∀ c : Fin k, c ≠ f u → c ≠ x →
      colourClassCount G g v c = colourClassCount G f v c := by
    intro c h1 h2
    rw [hg]
    exact colourClassCount_update_of_ne G h1 h2
  have hle : ∀ j : ℕ,
      (((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G g v c)).card : ℝ) ≤
      (((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c)).card : ℝ)
        + 2 := by
    intro j
    have := card_filter_le_add_two G (v := v) (g := g) (h := f) (a := f u) (b := x) (j := j) key
    exact_mod_cast this
  have hle' : ∀ j : ℕ,
      (((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c)).card : ℝ) ≤
      (((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G g v c)).card : ℝ)
        + 2 := by
    intro j
    have := card_filter_le_add_two G (v := v) (g := f) (h := g) (a := f u) (b := x) (j := j)
      (fun c h1 h2 => (key c h1 h2).symm)
    exact_mod_cast this
  have hdiff : occSlice G g v J - occSlice G f v J =
      ∑ j ∈ Finset.Icc 2 J, occW j *
        ((((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G g v c)).card : ℝ) -
         (((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c)).card : ℝ)) := by
    unfold occSlice
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (mul_sub _ _ _).symm
  rw [hdiff]
  exact abs_sum_occW_mul_sub_le _ _ hle hle'

end Work.Deep.Sparse
