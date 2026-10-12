import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG21_measurable` — measurability of the block II.1 fibre

The block II.1 fibre of `Work.BoseBoxFock.pairRowGDefs` is

    pairG21 p Θ A u y = ∫ x, star (Θ x) · A (x p.1) · A (x p.2)
                             · Θ ((x[p.1 ↦ y])[p.2 ↦ u]) ,

i.e. a **single Bochner integral** over the whole configuration space, whose integrand couples the
state `Θ` to the two external kernel variables `u`, `y` through the two-fold update of the slots
`p.1`, `p.2`.  Its measurability in the pair `(u, y)` — equivalently the strong measurability of the
integrand jointly in `((u, y), x)` plus `StronglyMeasurable.integral_prod_right'` — is the
`Measurable` input consumed by the `(S2)` substitution lemmas of the `Q₂` row for block II.1 (the
same role that `Work.BoseBoxFock.pairG13_measurable` plays for blocks I/III.1 and
`Work.BoseBoxFock.pairG23_measurable` for block II.2).

Two layers, each done once:

* `m_upd21` — the joint update map `(u, y, x) ↦ (x[p.1 ↦ y])[p.2 ↦ u]` is measurable.  This is a
  purely coordinatewise statement (`measurable_pi_iff`): after `Function.update_apply` the `k`-th
  coordinate is `u` (if `k = p.2`), `y` (if `k = p.1`) or `x k`.  Note that, unlike in
  `pairG13_measurable`, **no hypothesis `p.1 ≠ p.2` is needed here**: the update at `p.2` is
  outermost, so on the diagonal `p.1 = p.2` it simply overwrites the update at `p.1`.
* the four factors `star (Θ x)`, `A (x p.1)`, `A (x p.2)`, `Θ ((x[p.1 ↦ y])[p.2 ↦ u])` of the
  integrand, jointly measurable in `((u, y), x)` by `Measurable.comp` / `Measurable.mul`, and then
  the Bochner integral over `x` (`StronglyMeasurable.integral_prod_right'`; `ℂ` is second-countable
  and Borel, so strongly measurable `=` measurable).

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The joint update map** of block II.1: `(u, y, x) ↦ (x[p.1 ↦ y])[p.2 ↦ u]` is measurable.
Coordinatewise: the `k`-th coordinate is `u`, `y` or `x k` according to whether `k = p.2`,
`k = p.1` (and `k ≠ p.2`) or neither. -/
private lemma m_upd21 {n : ℕ} (p : Fin n × Fin n) :
    Measurable (fun q : (E3 × E3) × Work.BoseDict.Xn n =>
      Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1) := by
  refine measurable_pi_iff.2 (fun k => ?_)
  simp only [Function.update_apply]
  split_ifs with h2 h1
  · exact measurable_fst.fst
  · exact measurable_fst.snd
  · exact (measurable_pi_apply k).comp measurable_snd

theorem pairG21_measurable {n : ℕ} (p : Fin n × Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : Measurable Θ) (hAm : Measurable A) :
    Measurable (Function.uncurry (pairG21 p Θ A)) := by
  classical
  change Measurable (fun q : E3 × E3 => ∫ x : Work.BoseDict.Xn n,
    star (Θ x) * A (x p.1) * A (x p.2)
      * Θ (Function.update (Function.update x p.1 q.2) p.2 q.1))
  -- the four factors of the integrand, jointly in `((u, y), x)`
  have hf : StronglyMeasurable (fun q : (E3 × E3) × Work.BoseDict.Xn n =>
      star (Θ q.2) * A (q.2 p.1) * A (q.2 p.2)
        * Θ (Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1)) :=
    (((continuous_star.measurable.comp (hΘm.comp measurable_snd)).mul
      (hAm.comp ((measurable_pi_apply p.1).comp measurable_snd))).mul
      (hAm.comp ((measurable_pi_apply p.2).comp measurable_snd))).mul
      (hΘm.comp (m_upd21 p)) |>.stronglyMeasurable
  -- the Bochner integral over the configuration space
  have step : StronglyMeasurable (fun q : E3 × E3 => ∫ x : Work.BoseDict.Xn n,
      star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 q.2) p.2 q.1)) :=
    StronglyMeasurable.integral_prod_right' (α := E3 × E3) (β := Work.BoseDict.Xn n)
      (ν := (volume : Measure (Work.BoseDict.Xn n)))
      (f := fun q : (E3 × E3) × Work.BoseDict.Xn n =>
        star (Θ q.2) * A (q.2 p.1) * A (q.2 p.2)
          * Θ (Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1)) hf
  exact step.measurable

end Work.BoseBoxFock
