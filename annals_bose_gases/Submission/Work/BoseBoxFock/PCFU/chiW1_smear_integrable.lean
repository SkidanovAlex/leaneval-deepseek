import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.chiW1_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiW1_smear_integrable`

Bochner-integrability of the **`χ`-smear of the windowed two-body kernel**

`z ↦ χ_ℓ(z) · ∫_y χ_ℓ(y) · W₁(y − z)`,   `W₁ = W1fun v h ℓ = wScaled ℓ (g₀ v h)`.

This is the *section* form of the already-proved pair integrability
`Work.BoseBoxFock.PCFU.chiW1_integrable`, which states that

`(p : ℝ³ × ℝ³) ↦ χ_ℓ(p.1) · W₁(p.1 − p.2) · χ_ℓ(p.2)`

is integrable for `volume × volume`, i.e. (definitionally) that the localised pair
kernel `wPairC ℓ (g₀ v h) p.1 p.2` is integrable.  Since
`wPairC ℓ g x y = (χ_ℓ(x) W₁(x − y)) · χ_ℓ(y)`, the Bochner section in the second
variable is *exactly* the smeared function of the target
(`wPairC_section_eq_smear`), and the section of an integrable function is integrable
(`Integrable.integral_prod_right`, Fubini for the Bochner integral).  So no further
analysis of `g₀` is needed: the only analytic input is the corpus's pair integrability.

The two helper lemmas are the vocabulary bridges: `wPairC_g0_integrable` re-spells
`chiW1_integrable` with `wPairC`, and `wPairC_section_eq_smear` identifies the section
with the smear of `W1fun`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The localised pair kernel of the numerator `g₀ = v(1−w)` is integrable for
`volume × volume` — `chiW1_integrable` re-spelled with `wPairC` (the two integrands
are definitionally equal). -/
lemma wPairC_g0_integrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable
      (fun p : E3 × E3 => Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume) :=
  chiW1_integrable h hℓ

/-- **The section of the pair kernel is the smear of the window.**  For every `z`,
the Bochner integral of `y ↦ wPairC ℓ (g₀ v h) y z` equals
`χ_ℓ(z) · ∫_y χ_ℓ(y) W₁(y − z)`: pull the (`y`-independent) factor `χ_ℓ(z)` out of the
integral. -/
lemma wPairC_section_eq_smear {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ : ℝ} (z : E3) :
    (∫ y : E3, Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) y z)
      = Submission.BoseGases.chiScale ℓ z
        * (∫ y : E3, Submission.BoseGases.chiScale ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ)) := by
  rw [show (∫ y : E3, Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) y z)
      = ∫ y : E3, (Submission.BoseGases.chiScale ℓ y
          * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ)) * Submission.BoseGases.chiScale ℓ z
      from rfl]
  rw [MeasureTheory.integral_mul_const]
  ring

theorem chiW1_smear_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ z
        * (∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.chiScale ℓ y * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ))) := by
  refine (wPairC_g0_integrable h hℓ).integral_prod_right.congr
    (Filter.Eventually.of_forall (fun z => ?_))
  exact wPairC_section_eq_smear h z

end Work.BoseBoxFock.PCFU
