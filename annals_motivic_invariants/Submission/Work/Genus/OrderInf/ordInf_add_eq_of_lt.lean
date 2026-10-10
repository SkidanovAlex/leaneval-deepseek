import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

/-- The strict non-archimedean equality for the order at infinity: if `ordInf f < ordInf g` then
`ordInf (f + g) = ordInf f` (the case `f + g = 0` is impossible, since it would force
`ordInf g = ordInf f`).

Since `ordInf x = -x.intDegree`, the hypothesis translates to `g.intDegree < f.intDegree` and the
conclusion to `(f + g).intDegree = f.intDegree`.  Mathlib's `RatFunc.intDegree_add_le`
gives both bounds: applied to `f` and `g` it bounds `(f + g).intDegree` above by
`max f.intDegree g.intDegree = f.intDegree`, and applied to `f + g` and `-g` it bounds
`f.intDegree` above by `max (f + g).intDegree g.intDegree`, which forces
`(f + g).intDegree ≥ f.intDegree` because `g.intDegree < f.intDegree`. -/
theorem ordInf_add_eq_of_lt {F : Type*} [Field F] {f g : RatFunc F} (hf : f ≠ 0)
    (h : Work.Genus.ordInf f < Work.Genus.ordInf g) :
    Work.Genus.ordInf (f + g) = Work.Genus.ordInf f := by
  -- Translate the hypothesis `-f.intDegree < -g.intDegree` into `g.intDegree < f.intDegree`.
  have hdeg : g.intDegree < f.intDegree := by
    simp only [Work.Genus.ordInf] at h
    linarith
  -- The degenerate case `g = 0` is immediate.
  by_cases hg : g = 0
  · rw [hg, add_zero]
  -- `f + g ≠ 0`: otherwise `g = -f` and `ordInf g = ordInf f`, contradicting strictness.
  have hfg : f + g ≠ 0 := by
    intro hc
    have hg_eq : g = -f := by
      rw [eq_neg_iff_add_eq_zero]; rw [add_comm]; exact hc
    have : Work.Genus.ordInf g = Work.Genus.ordInf f := by
      rw [hg_eq, Work.Genus.ordInf, Work.Genus.ordInf, RatFunc.intDegree_neg]
    rw [this] at h
    exact lt_irrefl _ h
  -- Upper bound: `(f + g).intDegree ≤ max f.intDegree g.intDegree = f.intDegree`.
  have h1 : (f + g).intDegree ≤ max f.intDegree g.intDegree :=
    RatFunc.intDegree_add_le hg hfg
  -- Lower bound, via `(f + g) + (-g) = f`: `f.intDegree ≤ max (f + g).intDegree g.intDegree`.
  have h2 : f.intDegree ≤ max (f + g).intDegree g.intDegree := by
    have h2' := RatFunc.intDegree_add_le (x := f + g) (y := -g) (neg_ne_zero.mpr hg)
      (by simpa using hf)
    simpa [RatFunc.intDegree_neg, add_assoc] using h2'
  have hle : (f + g).intDegree ≤ f.intDegree := by
    rw [max_eq_left (le_of_lt hdeg)] at h1
    exact h1
  have hge : f.intDegree ≤ (f + g).intDegree := by
    rcases le_max_iff.mp h2 with h' | h'
    · exact h'
    · exact absurd h' (not_le.mpr hdeg)
  have hdeg_eq : (f + g).intDegree = f.intDegree := le_antisymm hle hge
  simp only [Work.Genus.ordInf]
  rw [hdeg_eq]

end Work.Genus.OrderInf
