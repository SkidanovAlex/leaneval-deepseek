import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.B13Aux
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG13_measurable` — measurability of the block I/III.1 fibre

The FS `Q₂` row's block I and III.1 fibre of `Work.BoseBoxFock.pairRowGDefs` is

    pairG13 p Θ A B w y = ∫ x' ∫ u star (Θ (w at p.2 in x')) · A ((w at p.2 in x') p.1)
                              · star (B u) · Θ (((w at p.2 in x')[p.1 ↦ y])[p.2 ↦ u]) ,

a **double Bochner integral** of a ℂ-valued integrand.  Its measurability in the pair `(w, y)` is
what `pairRowS2`'s hypotheses (`hCsupp`, the `L²` estimate, …) and the `pairRowS2Inst` instances
consume; it is the `Measurable` input of every "`AEMeasurable`-of-the-fibre" argument of the row.

Nothing here is deep, but the bookkeeping has three distinct layers, and each is done once:

* `m_insertCoord_proj` — inserting `w` into slot `p.2` of a fibre is a measurable operation.  By
  `measurable_pi_iff` every coordinate of `insertCoord p.2 w x'` is either the projection `w` or an
  evaluation `x' ⟨k, _⟩`, hence measurable.
* `m_updInsert` — the *joint* map
  `(w, y, x', u) ↦ ((insertCoord p.2 w x')[p.1 ↦ y])[p.2 ↦ u]` is measurable.  Again coordinatewise:
  after `Function.update_apply` the `k`-th coordinate is `u` (if `k = p.2`), `y` (if `k = p.1`) or
  `x' ⟨k, _⟩`; `insertCoord_eq` removes the last `dite`.  (The two cases `k = p.2`, `k = p.1` are
  exhaustive as they stand, so `hp : p.1 ≠ p.2` — which belongs to the *pair* reading of the row, and
  is part of the frozen statement — is not needed for the measurability statement itself: when
  `p.1 = p.2` the second `Function.update` simply overwrites the first, and the map is still
  measurable.  It is kept in the statement, and the proof is `hp`-free.)
* the multiplication of the four measurable factors and the two `integral_prod_right` passages
  (Bochner integrals of a strongly measurable integrand are strongly measurable; ℂ is
  second-countable and Borel, so strongly measurable = measurable).

-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Insertion of `w` into slot `j` of a fibre is measurable in `(w, x')`. -/
private lemma m_insertCoord {n : ℕ} (j : Fin n) :
    Measurable (fun q : E3 × ({k : Fin n // k ≠ j} → E3) => insertCoord j q.1 q.2) := by
  change Measurable (fun q : E3 × ({k : Fin n // k ≠ j} → E3) => fun k =>
    if h : k = j then q.1 else q.2 ⟨k, h⟩)
  refine measurable_pi_iff.2 (fun k => ?_)
  by_cases hk : k = j
  · subst hk
    simpa using measurable_fst
  · simp only [dif_neg hk]
    exact (measurable_pi_apply (⟨k, hk⟩ : {k : Fin n // k ≠ j})).comp measurable_snd

/-- The same insertion, as a map of the *fully flattened* parameter `((w,y),x'),u`. -/
private lemma m_insertCoord_proj {n : ℕ} (j : Fin n) :
    Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ j} → E3)) × E3 =>
      insertCoord j w.1.1.1 w.1.2) := by
  refine measurable_pi_iff.2 (fun k => ?_)
  simp only [insertCoord_eq]
  split_ifs with h
  · exact measurable_fst.comp (measurable_fst.comp measurable_fst)
  · exact (measurable_pi_apply (⟨k, h⟩ : {k : Fin n // k ≠ j})).comp
      (measurable_snd.comp measurable_fst)

/-- **The joint update map**: `(w, y, x', u) ↦ ((x'[p.2 ↦ w])[p.1 ↦ y])[p.2 ↦ u]` is measurable. -/
private lemma m_updInsert {n : ℕ} (p : Fin n × Fin n) :
    Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      Function.update (Function.update (insertCoord p.2 w.1.1.1 w.1.2) p.1 w.1.1.2) p.2 w.2) := by
  refine measurable_pi_iff.2 (fun k => ?_)
  simp only [Function.update_apply, insertCoord_eq]
  split_ifs with h2 h1
  · exact measurable_snd
  · exact measurable_fst.fst.snd
  · exact (measurable_pi_apply (⟨k, h2⟩ : {k : Fin n // k ≠ p.2})).comp measurable_fst.snd

set_option linter.unusedVariables false in
theorem pairG13_measurable {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : Measurable Θ) (hAm : Measurable A) (hBm : Measurable B) :
    Measurable (Function.uncurry (pairG13 p Θ A B)) := by
  classical
  change Measurable (fun q : E3 × E3 => ∫ (x' : {k : Fin n // k ≠ p.2} → E3), ∫ (u : E3),
    star (Θ (insertCoord p.2 q.1 x'))
      * A ((insertCoord p.2 q.1 x') p.1) * star (B u)
      * Θ (Function.update (Function.update (insertCoord p.2 q.1 x') p.1 q.2) p.2 u))
  -- the four factors of the integrand, jointly in `(w, y, x', u)`
  have hTH1 : Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      star (Θ (insertCoord p.2 w.1.1.1 w.1.2))) :=
    continuous_star.measurable.comp (hΘm.comp (m_insertCoord_proj p.2))
  have hA1 : Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      A ((insertCoord p.2 w.1.1.1 w.1.2) p.1)) :=
    hAm.comp ((measurable_pi_apply p.1).comp (m_insertCoord_proj p.2))
  have hB1 : Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      star (B w.2)) :=
    continuous_star.measurable.comp (hBm.comp measurable_snd)
  have hTupd : Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      Θ (Function.update (Function.update (insertCoord p.2 w.1.1.1 w.1.2)
        p.1 w.1.1.2) p.2 w.2)) := hΘm.comp (m_updInsert p)
  have hjoint : Measurable (fun w : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
      star (Θ (insertCoord p.2 w.1.1.1 w.1.2))
        * A ((insertCoord p.2 w.1.1.1 w.1.2) p.1) * star (B w.2)
        * Θ (Function.update (Function.update (insertCoord p.2 w.1.1.1 w.1.2)
            p.1 w.1.1.2) p.2 w.2)) :=
    ((hTH1.mul hA1).mul hB1).mul hTupd
  -- the two Bochner integrals, innermost first
  have step1 : StronglyMeasurable (Function.uncurry (fun
      (z : (E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) (u : E3) =>
      star (Θ (insertCoord p.2 z.1.1 z.2))
        * A ((insertCoord p.2 z.1.1 z.2) p.1) * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 z.1.1 z.2) p.1 z.1.2) p.2 u))) :=
    hjoint.stronglyMeasurable
  have step2 : StronglyMeasurable (fun q : E3 × E3 => ∫ (x' : {k : Fin n // k ≠ p.2} → E3),
      ∫ (u : E3), star (Θ (insertCoord p.2 q.1 x'))
        * A ((insertCoord p.2 q.1 x') p.1) * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 q.1 x') p.1 q.2) p.2 u)) :=
    StronglyMeasurable.integral_prod_right (f := fun
      (q : E3 × E3) (x' : {k : Fin n // k ≠ p.2} → E3) => ∫ (u : E3),
      star (Θ (insertCoord p.2 q.1 x'))
        * A ((insertCoord p.2 q.1 x') p.1) * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 q.1 x') p.1 q.2) p.2 u))
      (StronglyMeasurable.integral_prod_right (f := fun
        (z : (E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) (u : E3) =>
        star (Θ (insertCoord p.2 z.1.1 z.2))
          * A ((insertCoord p.2 z.1.1 z.2) p.1) * star (B u)
          * Θ (Function.update (Function.update (insertCoord p.2 z.1.1 z.2) p.1 z.1.2) p.2 u))
        step1)
  exact step2.measurable

end Work.BoseBoxFock
