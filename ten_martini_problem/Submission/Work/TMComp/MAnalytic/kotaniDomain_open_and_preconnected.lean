import Mathlib
import Submission.Work.TMContract.Defs

/-!
# `kotaniDomain` is open and preconnected

`Work.TMContract.kotaniDomain a b = {z : ℂ | z.im ≠ 0 ∨ (z.im = 0 ∧ a < z.re ∧ z.re < b)}`
is the plane slit along the two real rays `(-∞, a]` and `[b, ∞)` (with `a < b`).  It is the
domain on which Kotani's holomorphic continuation of the `m`-function lives.

We prove here that it is open and preconnected.  The complement is the closed set
`{z | z.im = 0 ∧ (z.re ≤ a ∨ b ≤ z.re)}`, whence openness.  For preconnectedness we write the
domain as the union of the two preconnected pieces

* `{z | 0 < z.im} ∪ {z | z.im = 0 ∧ a < z.re ∧ z.re < b}` (upper half plane together with
  the open slit, preconnected because the slit lies in the closure of the half plane), and
* `{z | z.im < 0} ∪ {z | z.im = 0 ∧ a < z.re ∧ z.re < b}` (same for the lower half plane),

which meet in the nonempty open slit.
-/

open Set

namespace Work.TMComp.MAnalytic

/-- The complement of `kotaniDomain a b` inside `ℂ` is closed: it is the union of the two
closed real rays `(-∞, a]` and `[b, ∞)`. -/
private theorem isClosed_compl_kotaniDomain (a b : ℝ) :
    IsClosed {z : ℂ | z.im = 0 ∧ (z.re ≤ a ∨ b ≤ z.re)} := by
  rw [show {z : ℂ | z.im = 0 ∧ (z.re ≤ a ∨ b ≤ z.re)}
        = {z : ℂ | z.im = 0} ∩ ({z : ℂ | z.re ≤ a} ∪ {z : ℂ | b ≤ z.re}) by
      ext z; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]]
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    ((isClosed_le Complex.continuous_re continuous_const).union
      (isClosed_le continuous_const Complex.continuous_re))

theorem kotaniDomain_open_and_preconnected (a b : ℝ) (hab : a < b) :
    IsOpen (Work.TMContract.kotaniDomain a b) ∧
      IsPreconnected (Work.TMContract.kotaniDomain a b) := by
  constructor
  · -- Openness: `kotaniDomain a b` is the complement of a closed set.
    have hcomp : Work.TMContract.kotaniDomain a b =
        {z : ℂ | z.im = 0 ∧ (z.re ≤ a ∨ b ≤ z.re)}ᶜ := by
      unfold Work.TMContract.kotaniDomain
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_and, not_or, not_le]
      tauto
    rw [hcomp]
    exact (isClosed_compl_kotaniDomain a b).isOpen_compl
  · -- Preconnectedness: union of the upper and lower half planes, glued along the open slit.
    have hUM : IsConnected
        ({z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b}) :=
      Complex.isConnected_of_upperHalfPlane (r := 0)
        (by intro z hz; exact Or.inl hz)
        (by
          intro z hz
          simp only [Set.mem_union, Set.mem_setOf_eq] at hz ⊢
          rcases hz with h | h
          · exact le_of_lt h
          · exact h.1.ge)
    have hLM : IsConnected
        ({z : ℂ | z.im < 0} ∪ {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b}) :=
      Complex.isConnected_of_lowerHalfPlane (r := 0)
        (by intro z hz; exact Or.inl hz)
        (by
          intro z hz
          simp only [Set.mem_union, Set.mem_setOf_eq] at hz ⊢
          rcases hz with h | h
          · exact le_of_lt h
          · exact h.1.le)
    have hMne : ({z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b}).Nonempty :=
      ⟨((a + b) / 2 : ℂ), ⟨by simp, by simp; linarith, by simp; linarith⟩⟩
    have hunion : IsPreconnected
        (({z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b}) ∪
         ({z : ℂ | z.im < 0} ∪ {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b})) :=
      IsPreconnected.union' (hMne.mono (fun z hz => ⟨Or.inr hz, Or.inr hz⟩))
        hUM.isPreconnected hLM.isPreconnected
    have hdom : Work.TMContract.kotaniDomain a b =
        ({z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b}) ∪
        ({z : ℂ | z.im < 0} ∪ {z : ℂ | z.im = 0 ∧ a < z.re ∧ z.re < b}) := by
      unfold Work.TMContract.kotaniDomain
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro (him | ⟨him, ha, hb⟩)
        · rcases lt_or_gt_of_ne him with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨him, ha, hb⟩)
      · rintro ((h | ⟨him, ha, hb⟩) | (h | ⟨him, ha, hb⟩))
        · exact Or.inl (ne_of_gt h)
        · exact Or.inr ⟨him, ha, hb⟩
        · exact Or.inl (ne_of_lt h)
        · exact Or.inr ⟨him, ha, hb⟩
    rw [hdom]
    exact hunion

end Work.TMComp.MAnalytic
