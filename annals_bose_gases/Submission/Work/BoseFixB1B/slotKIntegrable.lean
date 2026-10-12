import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.LocPotential
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.slotKIntegrable` — the slot kernel's partial integral is `L¹`

The corner kernel of the corpus is

    wLoc ℓ g u x y = chiU ℓ u x · wScaled ℓ g (x − y) · chiU ℓ u y ,

with `chiU ℓ u x = χ((ℓ⁻¹) • x − u)` and `χ = chi` supported in `closedBall 0 (1/2)`
(`Submission.BoseGases.chi_eq_zero_of_norm_gt`).  Hence for every `u` the two `chiU` factors
vanish outside `closedBall 0 (ℓ/2)`, and `closedBall 0 (ℓ/2) ⊆ acube ℓ`.  In particular the
function `p ↦ wLoc ℓ g u p.1 p.2` (for `u = 0`) **vanishes off** `acube ℓ ×ˢ acube ℓ`, so its
integrability *on* the product of cubes upgrades to integrability on all of `ℝ³ × ℝ³`
(`IntegrableOn.integrable_of_forall_notMem_eq_zero`).  Fubini
(`Integrable.integral_prod_left`) then gives integrability of the partial integral `a ↦ ∫ y, … a y`
against the full Lebesgue measure, and restricting to the (finite measure) set `acube ℓ`
monotonises the measure (`Integrable.mono_measure`, `Measure.restrict_le_self`).

Note the inner integral in the conclusion is over *all* of `ℝ³`, and it is the *unrestricted*
`y`-integrand that we integrate; the support of `chiU ℓ 0` makes this harmless.

Content:
* `chiU_zero_of_notMem_acube` — the support fact for the localisation factor;
* `wLoc_zero_of_notMem_acube_prod` — `wLoc ℓ g 0 · ·` vanishes off the product of cubes;
* `slotKIntegrable` — the requested statement.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseFixB1B

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The localisation factor `chiU ℓ 0` vanishes outside the centred cube `acube ℓ`: indeed
`chiU ℓ 0 x = χ((ℓ⁻¹) • x)` and `χ` vanishes off `closedBall 0 (1/2)`. -/
lemma chiU_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiU ℓ 0 x = 0 := by
  have hnorm : ℓ / 2 < ‖x‖ := by
    by_contra hcon
    push Not at hcon
    exact hx (by
      intro m
      have hm : |x m| ≤ ℓ / 2 := le_trans (Submission.BoseGases.abs_coord_le_norm x m) hcon
      obtain ⟨h1, h2⟩ := abs_le.mp hm
      exact ⟨by linarith, by linarith⟩)
  have h1 : (1 / 2 : ℝ) < ‖(ℓ⁻¹ : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
    calc (1 : ℝ) / 2 = ℓ⁻¹ * (ℓ / 2) := by
          rw [← mul_div_assoc, inv_mul_cancel₀ (ne_of_gt hℓ), one_div]
      _ < ℓ⁻¹ * ‖x‖ := mul_lt_mul_of_pos_left hnorm (inv_pos.mpr hℓ)
  have h2 : Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x - 0) = 0 :=
    Submission.BoseGases.chi_eq_zero_of_norm_gt _ (by simpa using h1)
  simpa [Submission.BoseGases.chiU] using h2

/-- `wLoc ℓ g 0 · ·` vanishes off the product `acube ℓ ×ˢ acube ℓ`. -/
lemma wLoc_zero_of_notMem_acube_prod {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℝ} {p : E3 × E3}
    (hp : p ∉ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :
    Submission.BoseGases.wLoc ℓ g 0 p.1 p.2 = 0 := by
  by_cases h1 : p.1 ∈ Submission.BoseGases.acube ℓ
  · have h2 : p.2 ∉ Submission.BoseGases.acube ℓ := fun h2 => hp (Set.mem_prod.mpr ⟨h1, h2⟩)
    simp [Submission.BoseGases.wLoc, chiU_zero_of_notMem_acube hℓ h2]
  · simp [Submission.BoseGases.wLoc, chiU_zero_of_notMem_acube hℓ h1]

theorem slotKIntegrable {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wLoc ℓ g 0 p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    MeasureTheory.Integrable
      (fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 a y)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)) := by
  -- the joint kernel is actually supported in the product of cubes, hence globally integrable
  have hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wLoc ℓ g 0 p.1 p.2) MeasureTheory.volume :=
    hInt.integrable_of_forall_notMem_eq_zero fun _ hp => wLoc_zero_of_notMem_acube_prod hℓ hp
  -- Fubini: the partial integral is integrable against the full Lebesgue measure
  have hfib : MeasureTheory.Integrable
      (fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 a y)
      MeasureTheory.volume := hint.integral_prod_left
  -- and restricting the measure to the (finite measure) cube preserves integrability
  exact hfib.mono_measure Measure.restrict_le_self

end Work.BoseFixB1B
