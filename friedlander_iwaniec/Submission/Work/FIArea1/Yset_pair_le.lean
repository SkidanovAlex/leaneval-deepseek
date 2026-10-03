import Mathlib
import Submission.Work.FIArea1.QboxDefs

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Abstract splitting lemma.**  If `s` and `t` are disjoint finsets, `F : α → α → ℝ` is
dominated by the product `a x * a y` of a function `a : α → ℝ`, and `F` is nonpositive on `t × t`,
then the double sum over `s ∪ t` is at most the double sum over `s` plus the two cross terms.
The `(s,s)` piece is kept exactly; the `(s,t)` and `(t,s)` pieces are estimated by the products of
the one-variable sums; the `(t,t)` piece is discarded. -/
lemma sum_union_pair_le {α : Type*} [DecidableEq α] (s t : Finset α) (hdisj : Disjoint s t)
    (a : α → ℝ) (F : α → α → ℝ)
    (hF : ∀ x y, F x y ≤ a x * a y)
    (htt : ∀ x ∈ t, ∀ y ∈ t, F x y ≤ 0) :
    ∑ x ∈ s ∪ t, ∑ y ∈ s ∪ t, F x y
      ≤ (∑ x ∈ s, ∑ y ∈ s, F x y) + (∑ x ∈ s, a x) * (∑ y ∈ t, a y)
        + (∑ x ∈ t, a x) * (∑ y ∈ s, a y) := by
  have hsplit : ∑ x ∈ s ∪ t, ∑ y ∈ s ∪ t, F x y
      = (∑ x ∈ s ∪ t, ∑ y ∈ s, F x y) + (∑ x ∈ s ∪ t, ∑ y ∈ t, F x y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_union hdisj)
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
  have hst : (∑ x ∈ s, ∑ y ∈ t, F x y) ≤ (∑ x ∈ s, a x) * (∑ y ∈ t, a y) := by
    calc ∑ x ∈ s, ∑ y ∈ t, F x y
        ≤ ∑ x ∈ s, a x * (∑ y ∈ t, a y) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro y hy
          exact hF x y
      _ = (∑ x ∈ s, a x) * (∑ y ∈ t, a y) :=
          (Finset.sum_mul s (fun x => a x) (∑ y ∈ t, a y)).symm
  have hts : (∑ x ∈ t, ∑ y ∈ s, F x y) ≤ (∑ x ∈ t, a x) * (∑ y ∈ s, a y) := by
    calc ∑ x ∈ t, ∑ y ∈ s, F x y
        ≤ ∑ x ∈ t, a x * (∑ y ∈ s, a y) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro y hy
          exact hF x y
      _ = (∑ x ∈ t, a x) * (∑ y ∈ s, a y) :=
          (Finset.sum_mul t (fun x => a x) (∑ y ∈ s, a y)).symm
  have htt' : (∑ x ∈ t, ∑ y ∈ t, F x y) ≤ 0 := by
    apply Finset.sum_nonpos
    intro x hx
    apply Finset.sum_nonpos
    intro y hy
    exact htt x hx y hy
  linarith

/-- **Splitting the pair sum over `Yset X = Qbim X ∪ {1,-1}`.**  The pair sum over `Yset X`
(restricted to `Δ ≠ 0`) is at most the pair sum over the non-real part `Qbim X` plus twice the
cross product with the two units.

Route: `Yset X` is the union of `Qbim X` and the two-element set `{1,-1}`, and `Qbim X` meets it in
nothing (`1.im = -1.im = 0` while `Qbim X` requires `im ≠ 0`).  Summing over the union splits the
double sum into four pieces; the `(Qbim,Qbim)` piece is the first term of the right-hand side, the
two mixed pieces are at most
`(Σ_{y∈Qbim X} Z(Re Wy)) · (Σ_{y∈{±1}} Z(Re Wy)) = (Σ_{y∈Qbim X} Z(Re Wy)) · (Z(W.re) + Z(-W.re))`,
and the `({±1},{±1})` piece vanishes because `Δ(±1,±1) = 0`. -/
theorem Yset_pair_le (X : ℝ) (W : GaussianInt) :
    (∑ y1 ∈ Work.FIArea1.Yset X, ∑ y2 ∈ Work.FIArea1.Yset X,
        (if Work.FIPlan.Delta y1 y2 = 0 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm W y1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W y2) : ℝ)))
    ≤ (∑ y1 ∈ Work.FIArea1.Qbim X, ∑ y2 ∈ Work.FIArea1.Qbim X,
        (if Work.FIPlan.Delta y1 y2 = 0 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm W y1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W y2) : ℝ)))
      + 2 * (((Work.FIPlan.Zint W.re : ℝ) + (Work.FIPlan.Zint (-W.re) : ℝ))
          * (∑ y ∈ Work.FIArea1.Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ))) := by
  -- `Qbim X` and `{±1}` are disjoint (`Qbim X` consists of non-real points).
  have hdisj : Disjoint (Qbim X) ({1, -1} : Finset GaussianInt) := by
    rw [Finset.disjoint_left]
    intro z hz hz2
    rw [mem_Qbim_iff] at hz
    obtain ⟨-, -, him⟩ := hz
    fin_cases hz2 <;> simp at him
  -- The summand is dominated by the product of the one-variable weights `a`.
  have hF : ∀ x y, (if Work.FIPlan.Delta x y = 0 then 0
      else (Work.FIPlan.Zint (Work.FIPlan.cForm W x) : ℝ)
           * (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ))
      ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm W x) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ) := by
    intro x y
    split_ifs with h
    · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_rfl
  -- On the units the determinant vanishes, so the `({±1},{±1})` piece is nonpositive.
  have htt : ∀ x ∈ ({1, -1} : Finset GaussianInt), ∀ y ∈ ({1, -1} : Finset GaussianInt),
      (if Work.FIPlan.Delta x y = 0 then 0
        else (Work.FIPlan.Zint (Work.FIPlan.cForm W x) : ℝ)
             * (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ)) ≤ 0 := by
    intro x hx y hy
    fin_cases hx <;> fin_cases hy <;> simp [Work.FIPlan.Delta]
  -- The one-variable weight of `{±1}` is `Z(Re W) + Z(-Re W)`.
  have hT : (∑ y ∈ ({1, -1} : Finset GaussianInt),
        (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ))
      = (Work.FIPlan.Zint W.re : ℝ) + (Work.FIPlan.Zint (-W.re) : ℝ) := by
    rw [Finset.sum_insert (by decide : (1 : GaussianInt) ∉ ({-1} : Finset GaussianInt)),
        Finset.sum_singleton]
    simp [Work.FIPlan.cForm]
  have hmain := sum_union_pair_le (Qbim X) ({1, -1} : Finset GaussianInt) hdisj
    (fun y => (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ))
    (fun y1 y2 => (if Work.FIPlan.Delta y1 y2 = 0 then 0
        else (Work.FIPlan.Zint (Work.FIPlan.cForm W y1) : ℝ)
             * (Work.FIPlan.Zint (Work.FIPlan.cForm W y2) : ℝ)))
    hF htt
  rw [Yset]
  refine le_trans hmain ?_
  rw [hT]
  ring_nf
  exact le_of_eq rfl

end

end Work.FIArea1
