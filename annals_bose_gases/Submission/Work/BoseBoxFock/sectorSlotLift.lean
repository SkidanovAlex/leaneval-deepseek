import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotSum_sector_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sectorSlotLift` — the `V`-supported slot operators act only on the
`V`-slots of a sector

BF3c (`box_to_model`, fourth session).  The fibre selection of `BF3C_PLAN_S7.md` §1 works on the
`V`/`W` sectors `slotExact e S Φ` of a box state `Φ` (`V = span{e l}`, `W = Vᗮ`): the model can
only see the `V`-slots, so a `V`-supported slot operator must act on the slots *in* `S` and
nothing else, and its quadratic form on the sector must factorise into a pointwise (`y`-wise)
form on the `S`-slots.

This module proves the two *first* steps of that factorisation for a one-body slot sum
`Work.BoseDict.boxSlotSum e T`:

* `boxSlotOf_eq_zero_of_slotProj1_eq_zero` — the slot-`j` rank-one operator
  `|e l⟩⟨e l'|` (`Work.BoseDict.boxSlotOf`) **kills** any state whose slot `j` lies in `W`
  (i.e. `slotProj1 e j Θ = 0`).  Mathematically: `|e l⟩⟨e l'| P_j = |e l⟩⟨e l'|` because
  `e l' ∈ V` and `P_V e l' = e l'`; the corpus's `boxSlotOf_slotProj1_self` is exactly this
  identity, and the vanishing follows from it.
* `boxSlotSum_sector_eq_sum_mem` — consequently, on the sector `slotExact e S Φ`, the slot sum
  `∑_{j : Fin n}` collapses to the sum over the *occupied* slots `j ∈ S`:
  every term with `j ∉ S` vanishes (the slot `j` of a sector state lies in `W`,
  `slotProj1_slotExact_eq_zero`).

This is the "spectator" statement of `BF3B_PLAN_S5.md` §2 at the level of a single sector, and
the entry point of the pointwise decoupling (`BF3C_PLAN_S7.md` §1(a)-(b)): the remaining step is
the reindexing of the `j ∈ S` sum by the subtype `{i // i ∈ S}` together with the Fubini
identification `⟨Θ_S, boxSlotSum e T Θ_S⟩ = ∫_y ⟨Θ_S(·,y), (the x-side slot sum) Θ_S(·,y)⟩`.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **A `V`-supported rank-one slot operator kills the `W`-slots.**  If the `j`-th slot of `Θ`
carries no `V`-component (`slotProj1 e j Θ = 0`), then the slot-`j` operator `|e l⟩⟨e l'|` of the
box-side dictionary annihilates `Θ`.  This is `boxSlotOf_slotProj1_self`
(`|e l⟩⟨e l'| P_j = |e l⟩⟨e l'|`) evaluated at `P_j Θ = 0`. -/
theorem boxSlotOf_eq_zero_of_slotProj1_eq_zero {m d : ℕ}
    (e : Fin m → Ω → ℂ) (l l' : Fin m) (j : Fin d)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (hint : ∀ k k', MeasureTheory.Integrable
      (fun z : Ω => star (e k z) * e k' z))
    (Θ : (Fin d → Ω) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (h0 : slotProj1 e j Θ = 0) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ = 0 := by
  have h1 := boxSlotOf_slotProj1_self e l l' j he hec horth hint Θ hΘm hΘb
  rw [h0] at h1
  rw [← h1]
  funext x
  simp [Work.BoseDict.boxSlotOf]

/-- **The slot sum of a sector lives on the occupied slots.**  On the `S`-sector
`slotExact e S Φ`, the one-body slot sum `boxSlotSum e T` is the sum over the slots `j ∈ S` only;
all the other slots carry a `W`-component, on which the `V`-supported rank-one pieces vanish
(`boxSlotOf_eq_zero_of_slotProj1_eq_zero`, `slotProj1_slotExact_eq_zero`). -/
theorem boxSlotSum_sector_eq_sum_mem {m n : ℕ}
    (e : Fin m → Ω → ℂ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (hint : ∀ k k', MeasureTheory.Integrable
      (fun z : Ω => star (e k z) * e k' z))
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    Work.BoseDict.boxSlotSum e T (slotExact e S Φ)
      = ∑ j ∈ S, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
              (slotExact e S Φ) := by
  classical
  obtain ⟨hsecm, hsecb, -⟩ :=
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hzero : ∀ j : Fin n, j ∉ S →
      (∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (slotExact e S Φ)) = 0 := by
    intro j hj
    refine Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun l' _ => ?_))
    rw [boxSlotOf_eq_zero_of_slotProj1_eq_zero e l l' j he hec horth hint
        (slotExact e S Φ) hsecm hsecb
        (slotProj1_slotExact_eq_zero e he hec horth S j hj Φ hΦ.measurable hΦb)]
    exact smul_zero _
  rw [Work.BoseDict.boxSlotSum]
  exact (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj)).symm

end Work.BoseBoxFock
