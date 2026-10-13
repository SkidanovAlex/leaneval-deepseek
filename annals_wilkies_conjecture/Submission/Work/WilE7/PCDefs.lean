/-
  Area E7: local preconnectedness of cylindrical cells.

  A cylindrical cell of the frozen decomposition `WilkiesDesign.IsCell` is built from
  `ℝ⁰`, graphs and bands, so at every one of its points it looks like a product of an
  interval with the (smaller dimensional) base cell near that point. This file collects
  the vocabulary used to turn that intuition into an induction: the predicate `IsLocPC`
  ("locally preconnected at every point") plus two elementary facts about the extended
  reals that the band case needs to cut a finite vertical window out of a fibre.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.band_preconn
import Submission.Work.WilE7.singleton_cylDecomp

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-- `A ⊆ ℝⁿ` is locally preconnected: around every point of `A`, and inside every open
neighbourhood `W` of it, there is an open set `V` whose trace `V ∩ A` on `A` is
preconnected. -/
def IsLocPC {n : ℕ} (A : Set (Fin n → ℝ)) : Prop :=
  ∀ c ∈ A, ∀ W : Set (Fin n → ℝ), IsOpen W → c ∈ W →
    ∃ V : Set (Fin n → ℝ), IsOpen V ∧ c ∈ V ∧ V ⊆ W ∧ IsPreconnected (V ∩ A)

/-- Between an extended real `a` and a real `t` with `a < t` there is a real of the form
`t - δ`, `δ > 0`. -/
lemma exists_lt_coe_sub (a : EReal) (t : ℝ) (h : a < (t : EReal)) :
    ∃ δ > 0, a < ((t - δ : ℝ) : EReal) := by
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real h
  rw [EReal.coe_lt_coe_iff] at hy2
  exact ⟨(t - y) / 2, by linarith, hy1.trans (EReal.coe_lt_coe_iff.mpr (by linarith))⟩

/-- Between a real `t` and an extended real `b` with `t < b` there is a real of the form
`t + δ`, `δ > 0`. -/
lemma exists_coe_add_lt (b : EReal) (t : ℝ) (h : (t : EReal) < b) :
    ∃ δ > 0, ((t + δ : ℝ) : EReal) < b := by
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real h
  rw [EReal.coe_lt_coe_iff] at hy1
  exact ⟨(y - t) / 2, by linarith, (EReal.coe_lt_coe_iff.mpr (by linarith)).trans hy2⟩

end Work.WilE7
