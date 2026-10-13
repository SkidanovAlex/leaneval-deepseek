/-
# `Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc`

`rgF1 α m c t = c t · t^{q-1}` with `q = rgQ α m = (2m+5)/α ≥ 28`, and the task is the
integrability of `rgF1` on the half-open interval `(0, X]` for every `X > 0`.

The two hypotheses are the honest near field and far field bounds on `c`:

* `hnear : ∫_{(0,1)} (c t)²/t⁴ < ∞`,
* `hfar  : ∫_{(1,∞)} (c t)²   < ∞`.

Both halves of the interval are already available from `rgHonest_aemeas`
(`Work.FTS.PhiStar.Honesty.rgHonest_aemeas`), namely

* `IntegrableOn (rgF1 α m c) (Ioc 0 1)`                            (from `hnear`), and
* `∀ z, 1 ≤ z → IntegrableOn (rgF1 α m c) (Ioc 1 z)`               (from `hfar`).

The two are glued by `IntegrableOn.union`: for `X ≤ 1` the second is a subset of the first,
and for `1 < X` one has the exact decomposition `(0, X] = (0, 1] ∪ (1, X]`.  (On the near
field no `ε`-room is needed: on `(0,1]` the weight `t^{q-1}` is `≤ 1` and `(c t)² ≤ (c t)²/t⁴`
there; that is precisely how `rgHonest_aemeas` proceeds.)
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.rgHonest_aemeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

theorem rgF1_integrableOn_Ioc {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ X : ℝ, 0 < X →
      MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 X) := by
  intro X _
  obtain ⟨h0, h1, -⟩ := rgHonest_aemeas hα hα4 hm hc hnear hfar
  rcases le_or_gt X 1 with hX1 | hX1
  · -- `X ≤ 1`: `(0,X] ⊆ (0,1]`
    exact h0.mono_set (Set.Ioc_subset_Ioc_right hX1)
  · -- `1 < X`: `(0,X] = (0,1] ∪ (1,X]`
    have h2 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 1 X) :=
      h1 X hX1.le
    have hun : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc (1 : ℝ) X = Set.Ioc (0 : ℝ) X := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
        · exact ⟨ha, le_trans hb hX1.le⟩
        · exact ⟨lt_trans zero_lt_one ha, hb⟩
      · intro ht
        by_cases hc1 : t ≤ 1
        · exact Or.inl ⟨ht.1, hc1⟩
        · exact Or.inr ⟨lt_of_not_ge hc1, ht.2⟩
    rw [← hun]
    exact h0.union h2

end Work.FTS.PhiStar.Honesty
