import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
import Submission.Work.BoseFixB3.CS.Pieces.leakCoupl_swap
import Submission.Work.BoseFixB3.CS.Pieces.leakFn_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.integrable_leakCoupl_integrand`

Joint integrability (on `volume.prod volume`) of the **leakage coupling integrand**

    (a, b) ↦ χ_Λ(a) · F(a − b) · χ_Λ(b) · L(b),

with `χ_Λ = chiU ℓ 0` the scaled cubic bump centred at `0`, `L = leakFn fc κ ℓ` the leakage
function `1 − lowMult fc κ ℓ (fun _ => 1)`, and `F` an integrable function on `ℝ³`.

Although `F` is only integrable on `ℝ³`, the extra factor `χ_Λ(b)` localises the *second*
variable to a bounded region (`support χ_Λ ⊆ closedBall 0 (ℓ/2)`), which is what makes the
double integral finite.  Concretely:

* the pairing bound `Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral`, applied to
  `χ = chiScale ℓ` (which is `chiU ℓ 0` up to rewriting), gives integrability of
  `(a,b) ↦ χ_Λ(a)|F(a−b)|χ_Λ(b)` on the product, with the finite bound `(∫χ_Λ²)(∫|F|)`;
* `|L(b)|` is bounded uniformly in `b` by `Work.BoseFixB3.CS.Pieces.leakFn_abs_le`;
* hence the target integrand, whose absolute value is `χ_Λ(a)|F(a−b)|χ_Λ(b)|L(b)|`, is
  dominated by an integrable function, and it is a.e. strongly measurable (a product of the
  continuous `χ_Λ`-factors, the measurable `F(p.1 − p.2)` and the strongly measurable
  `L(p.2)`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 400000

/-- `chiU ℓ 0` is the scaled bump `chiScale ℓ` (since `chiU ℓ 0 x = χ((ℓ⁻¹)•x − 0)`). -/
lemma integrable_leakCoupl_chiU_eq (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiU ℓ 0 x = Submission.BoseGases.chiScale ℓ x :=
  Work.BoseFixB3.chiU_zero_eq_chiScale ℓ x

theorem integrable_leakCoupl_integrand (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) {F : EuclideanSpace ℝ (Fin 3) → ℝ} (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable
      (Function.uncurry (fun a b : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiU ℓ 0 a * F (a - b) * Submission.BoseGases.chiU ℓ 0 b *
          Work.BoseFixB3.CS.leakFn fc κ ℓ b))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hχpt : ∀ x : E3, Submission.BoseGases.chiU ℓ 0 x = Submission.BoseGases.chiScale ℓ x :=
    fun x => integrable_leakCoupl_chiU_eq ℓ x
  -- the pairing bound for the scaled bump: `(a,b) ↦ χ_Λ a · |F (a−b)| · χ_Λ b` is integrable
  obtain ⟨hpair, -⟩ := Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
    (χ := Submission.BoseGases.chiScale ℓ) (f := F)
    (fun x => Submission.BoseGases.chiScale_nonneg ℓ x)
    (Submission.BoseGases.chiScale_continuous ℓ)
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)) hF
  -- the dominating function: the `|L|`-bound times the pairing integrand
  have hdom : MeasureTheory.Integrable
      (fun p : E3 × E3 =>
        (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
            (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) *
          (Submission.BoseGases.chiScale ℓ p.1 * |F (p.1 - p.2)| *
            Submission.BoseGases.chiScale ℓ p.2)) :=
    hpair.const_mul _
  -- a.e. strong measurability of the target integrand
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 =>
        Submission.BoseGases.chiU ℓ 0 p.1 * F (p.1 - p.2) *
        Submission.BoseGases.chiU ℓ 0 p.2 * Work.BoseFixB3.CS.leakFn fc κ ℓ p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hchiU_cont : Continuous (fun x : E3 => Submission.BoseGases.chiU ℓ 0 x) := by
      rw [show (fun x : E3 => Submission.BoseGases.chiU ℓ 0 x)
            = Submission.BoseGases.chiScale ℓ from funext hχpt]
      exact Submission.BoseGases.chiScale_continuous ℓ
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × E3 => Submission.BoseGases.chiU ℓ 0 p.1)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hchiU_cont.comp continuous_fst).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × E3 => F (p.1 - p.2))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (Work.BoseFixB1S.subPair_aemeasurable hF.aemeasurable).aestronglyMeasurable
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × E3 => Submission.BoseGases.chiU ℓ 0 p.2)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hchiU_cont.comp continuous_snd).aestronglyMeasurable
    have h4 : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ p.2)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (Work.BoseFixB3.CS.Pieces.leakSwap_leakFn_sm fc κ ℓ).aestronglyMeasurable.comp_snd
    exact ((h1.mul h2).mul h3).mul h4
  have hmain : MeasureTheory.Integrable
      (fun p : E3 × E3 =>
        Submission.BoseGases.chiU ℓ 0 p.1 * F (p.1 - p.2) *
        Submission.BoseGases.chiU ℓ 0 p.2 * Work.BoseFixB3.CS.leakFn fc κ ℓ p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hdom.mono' hAESM (Filter.Eventually.of_forall fun p => ?_)
  · simpa only [Function.uncurry_def] using hmain
  · -- pointwise domination of the integrand by the `|L|`-bound times the pairing integrand
    simp only [Real.norm_eq_abs, hχpt p.1, hχpt p.2, abs_mul, abs_of_nonneg,
      Submission.BoseGases.chiScale_nonneg]
    have hL := Work.BoseFixB3.CS.Pieces.leakFn_abs_le fc hκ hℓ p.2
    have hA : (0 : ℝ) ≤ Submission.BoseGases.chiScale ℓ p.1 * |F (p.1 - p.2)| *
        Submission.BoseGases.chiScale ℓ p.2 :=
      mul_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ p.1) (abs_nonneg _))
        (Submission.BoseGases.chiScale_nonneg ℓ p.2)
    refine le_trans (mul_le_mul_of_nonneg_left hL hA) (le_of_eq ?_)
    ring

end Work.BoseFixB3.CS.Pieces
