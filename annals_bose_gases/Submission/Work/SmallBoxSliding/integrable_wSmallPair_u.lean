import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.qLHSBAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the localized kernel `wSmallPair M ℓ d · h x y` in the sliding variable

`wSmallPair M ℓ d u h x y = χ_{B(u)}(x)·W(x−y)·χ_{B(u)}(y)` with
`χ_{B(u)}(z) = χ_M(z/ℓ)·χ_M(z/(ℓd) − u)`.  As a function of the sliding
variable `u` this is (a constant times) a *translate/dilate* product of the
`L¹ ∩ L^∞` bump `χ_M` with itself, hence integrable: `χ_M` is continuous with
compact support, so `u ↦ χ_M(c⁻¹·z − u)` is integrable for every `z`, and it is
bounded by `chiSmallDecay M`, so the product of the two factors is integrable
(`Integrable.bdd_mul`).  No hypothesis on `h` is needed: `W(x−y)` is constant in
`u`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- Auxiliary: the sliding-variable profile `u ↦ χ_M(κ⁻¹•z − u)` is integrable
(it is a translate-reflection of the `L¹` bump `χ_M`). -/
lemma integrable_chiSmall_translate {M : ℕ} (hM : 1 ≤ M) (c : ℝ) (z : ℝ³) :
    MeasureTheory.Integrable (fun u : ℝ³ => chiSmall M (c⁻¹ • z - u)) := by
  have hchi_int : MeasureTheory.Integrable (fun w : ℝ³ => chiSmall M w) (volume : Measure ℝ³) :=
    (chiSmall_continuous hM).integrable_of_hasCompactSupport (chiSmall_hasCompactSupport hM)
  have hh := (hchi_int.comp_add_left (c⁻¹ • z)).comp_neg
  simpa [sub_eq_add_neg] using hh

/-- Auxiliary: the sliding-variable profile `u ↦ χ_M(c⁻¹•z − u)` is bounded by
the decay constant `chiSmallDecay M` and continuous, hence `AEStronglyMeasurable`
with a uniform bound. -/
lemma chiSmall_translate_continuous {M : ℕ} (hM : 1 ≤ M) (c : ℝ) (z : ℝ³) :
    Continuous (fun u : ℝ³ => chiSmall M (c⁻¹ • z - u)) :=
  (chiSmall_continuous hM).comp (by fun_prop)

theorem integrable_wSmallPair_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (h : EuclideanSpace ℝ (Fin 3) → ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wSmallPair M ℓ d u h x y) := by
  have hB : MeasureTheory.Integrable (fun u : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • y - u)) :=
    integrable_chiSmall_translate hM (ℓ * d) y
  have hAcont : Continuous (fun u : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    chiSmall_translate_continuous hM (ℓ * d) x
  have hbd : ∀ᵐ u : ℝ³ ∂(volume : Measure ℝ³),
      ‖chiSmall M ((ℓ * d)⁻¹ • x - u)‖ ≤ chiSmallDecay M :=
    ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs]
      exact chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u))
  have hprod : MeasureTheory.Integrable (fun u : ℝ³ =>
      chiSmall M ((ℓ * d)⁻¹ • x - u) * chiSmall M ((ℓ * d)⁻¹ • y - u)) :=
    hB.bdd_mul hAcont.aestronglyMeasurable hbd
  have hK : MeasureTheory.Integrable (fun u : ℝ³ =>
      (chiScale ℓ x * (wSmallScaled M (ℓ * d) h (x - y) / convScale ℓ (x - y)) * chiScale ℓ y)
        * (chiSmall M ((ℓ * d)⁻¹ • x - u) * chiSmall M ((ℓ * d)⁻¹ • y - u))) :=
    hprod.const_mul _
  refine hK.congr (ae_of_all _ (fun u => ?_))
  simp only [wSmallPair, chiSmallB]
  ring

end Work.SmallBoxSliding
