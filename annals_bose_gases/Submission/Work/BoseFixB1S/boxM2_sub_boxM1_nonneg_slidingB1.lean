import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1`

The sliding-box, *abstract-parameters* form of the mass comparison `M₁ ≤ M₂`
(FS `lm:w2>w1`): for the localised kernels of the small box `dlBox ℓ d u`,

`boxM2 (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g₂ v h))`
  `- boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u) ≥ 0`,

with the regularity integer `M` **arbitrary** (`1 ≤ M`) rather than pinned to
`Work.BoseBox.mValue`, and the parameters `ℓ, d` arbitrary positive reals satisfying the
dilute small-box regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` (no `Adm`/`sideAt` parametrisation).

Both localised kernels vanish as soon as one argument leaves the sliding box
(`wSmallPair_eq_zero_of_notMem_dlBox`), so by
`boxM1_eq_acubePair` / `boxM2_eq_acubePair` (both from
`Work.BoseFixB1S.boxM1Info`) the difference is the difference of the two pair integrals
over the big box `acube ℓ ×ˢ acube ℓ`:

* `boxM1 ℓ (dlBox ℓ d u) w₁ = ∬_{acube ℓ × acube ℓ} w₁` (needs integrability of the
  localised one-body kernel on the big box, `integrableOn_wSmallPair_cube` at the
  numerator `g₀`),
* `boxM2 V (dlBox ℓ d u) w₂ = ∬_{acube ℓ × acube ℓ} w₂` (definitional, plus vanishing).

The comparison `∬ w₁ ≤ ∬ w₂` over the big box is exactly
`Work.BoseFixB1.w1MassB_le_w2MassB_localised` (the a.e. pointwise bound
`w₁ ≤ w₂` = `g₀ ≤ g₂`, i.e. `0 ≤ ω₀ ≤ 1`, integrated).
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option linter.unusedVariables false

theorem boxM2_sub_boxM1_nonneg_slidingB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) := by
  -- ### Both localised kernels vanish off the sliding box
  have hvan1 : ∀ x y : ℝ³, (x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) →
      wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y hxy => wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hvan2 : ∀ x y : ℝ³, (x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) →
      wSmallPair M ℓ d u (g2 v h) x y = 0 :=
    fun x y hxy => wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  -- ### Integrability of the localised one-body kernel over the big box
  have hInt : IntegrableOn
      (fun p : ℝ³ × ℝ³ => wSmall1Pair h M ℓ d u p.1 p.2) (acube ℓ ×ˢ acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube (f := g0 v h)
      (g0_integrable (R := R) hR0 hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR hRχ u
  -- ### Transport both masses to the big-box pair integrals
  rw [boxM1_eq_acubePair u hvan1 hInt, boxM2_eq_acubePair u hvan2]
  -- ### The pair-integral comparison `∬ w₁ ≤ ∬ w₂`
  have hle := Work.BoseFixB1.w1MassB_le_w2MassB_localised (v := v) (R0 := R)
    hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u
  linarith

end Work.BoseFixB1S
