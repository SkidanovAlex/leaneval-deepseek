import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotContactChemAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotContactChemEval` — the condensate half of the contact row

The contact/chemical group of the row table (`Work.BoseBoxFock.potContactChem`) is built from
`B r = boxSlotSum e r` with `r = rankOne (evec0 m)`, i.e. from the *condensate number* `n₀`.
This module evaluates the pairing of `B r` against an arbitrary (symmetric) box state:

    `(cIPn d Θ (boxSlotSum e (rankOne (evec0 m)) Θ)).re = cS1C ℓ Θ`

with **no** continuity hypothesis on the modes `e` (only the weak bundle: measurable, everywhere
bounded, box-supported) — the evaluation is `boxSlotSum_proj0` (`boxSlotSum e (proj0 m) =
Σ_j uSlot (e 0) j`, with `proj0 m = rankOne (evec0 m)`) followed by
`uSlot_sum_cIPn_eq_cS1C`, whose integrability side conditions are `uSlot_regular`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.BoseDict

/-- The application of the rank-one operator `|v⟩⟨v|`. -/
lemma rankOne_apply' {m : ℕ} (v x : Fin m → ℝ) :
    rankOne v x = (∑ l : Fin m, v l * x l) • v := by
  simp only [rankOne, LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

/-- The projection `proj0 m` onto the condensate direction is the rank-one operator
`|evec0⟩⟨evec0|`. -/
lemma proj0_eq_rankOne (m : ℕ) [NeZero m] : proj0 m = rankOne (evec0 m) := by
  refine LinearMap.ext (fun v => ?_)
  rw [rankOne_apply']
  show v 0 • Work.BoseB4.evec m 0 = (∑ l : Fin m, evec0 m l * v l) • Work.BoseB4.evec m 0
  congr 1
  rw [Finset.sum_eq_single (0 : Fin m)]
  · rw [evec0_apply_zero, one_mul]
  · intro l _ hl
    rw [evec0_apply_ne hl, zero_mul]
  · intro h0
    exact absurd (Finset.mem_univ (0 : Fin m)) h0

/-- **The condensate-number evaluation at the weak mode bundle**: the pairing of a box state with
its slot-projection word `B r` (`r = |evec0⟩⟨evec0|`) is the condensate count `cS1C`. -/
theorem cIPn_boxSlotSum_rankOne_evec0_re {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (horth : ∀ l l', (∫ z : Sp, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {c : ℂ} (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hun : ∀ᵐ z ∂(volume : Measure Sp), e 0 z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {C : ℝ} (hC : 0 ≤ C) {Θ : Xn d → ℂ}
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ)
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ MeasureTheory.volume)
    (hΘb : ∀ᵐ x ∂(volume : MeasureTheory.Measure (Xn d)), ‖Θ x‖ ≤ C) :
    (cIPn d Θ (boxSlotSum e (rankOne (evec0 m)) Θ)).re = cS1C ℓ Θ := by
  have hp0 : boxSlotSum e (rankOne (evec0 m)) Θ = boxSlotSum e (proj0 m) Θ := by
    rw [proj0_eq_rankOne]
  rw [hp0, boxSlotSum_proj0]
  exact uSlot_sum_cIPn_eq_cS1C hℓ hun hcc hΘsupp
    (fun j => (uSlot_regular hℓ j hC hun hcc hΘsupp hΘm hΘb).1)
    (fun j => (uSlot_regular hℓ j hC hun hcc hΘsupp hΘm hΘb).2)

end Work.BoseBoxFock
