import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Basic
import Submission.Work.SmallBoxTBWord.dirichlet_boxQ_le
import Submission.Work.SmallBoxTBWord.tBampForm_integrable
import Submission.Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The spectral half `𝒯_B`-kinetic is dominated by the honest kinetic word

This module proves the domination **(b)** of the `SmallBoxTBWord` chapter's header
(`Defs.lean`): the spectrally cutoff, `Q_B`-projected box kinetic

    `tBwordKin a A volA χ c Ψ = Σ_i (2π)⁻³∫_p [‖p‖−c]₊²·(a³)⁻¹∫_{abox}‖tBamp χ p (Q_{B,i}Ψ) i x‖²`

is bounded by twice the window mass times the corpus's honest position-space kinetic word plus
twice the window-derivative error:

    `tBwordKin ≤ 2·Cχ²·kinWord (n+1) a Ψ + 2·winErrBox a A volA χ Ψ`.

## The chain

1. **symbol step** — `[·−c]₊² ≤ (·)²` (`fsKinCoeff_le_sq_all`), applied inside the `p`-integral
   slot by slot (`integral_mono_of_nonneg`, whose only integrability input is
   `tBampForm_integrable` for the *larger* symbol `‖·‖²`);
2. **fibre Plancherel** — `tBdiagForm_sq_eq_dirichlet`: with the squared symbol the `p`-form
   *is* the sum of the slot Dirichlet energies of the windowed `Q_B`-projected fibres;
3. **Leibniz / window** — `dirichlet_boxQ_le`: `∂_k(χ(x_i)·Q_{B,i}Ψ) = (∂_kχ)(x_i)·Q_{B,i}Ψ +
   χ(x_i)·∂_k(Q_{B,i}Ψ)`, with `|χ| ≤ Cχ` and `∂_{ik}(Q_{B,i}Ψ) = ∂_{ik}Ψ` (the box projection is
   free in its own slot), turning the Dirichlet energy into `2Cχ²·kinWord + 2·winErrBox`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem tBwordKin_le_kinWord {a Cχ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ} {c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hCχ : 0 ≤ Cχ) (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ Submission.BoseGases.acube a) (hA : IsCompact A) (hsup : ∀ x, |χ x| ≤ Cχ) {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) : Work.SmallBoxTBWord.tBwordKin a A volA χ c Ψ ≤ 2 * Cχ ^ 2 * Submission.BoseGases.kinWord (n + 1) a Ψ + 2 * Work.SmallBoxTBWord.winErrBox a A volA χ Ψ := by
  -- the `‖·‖²`-weighted `p`-integrand is integrable (Fourier decay of the windowed fibre)
  have hintG : ∀ i : Fin (n + 1), Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
      ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) a,
        ‖tBamp χ p (boxQ volA A i Ψ) i x‖ ^ 2)) :=
    fun i => tBampForm_integrable (n := n) (a := a) (A := A) (volA := volA) (χ := χ) hχ hcs hA hΨ i
  -- (1) the symbol inequality, slot by slot
  have hmono : tBwordKin a A volA χ c Ψ ≤ tBdiagForm a A volA χ (fun r => r ^ 2) Ψ := by
    unfold tBwordKin tBdiagForm
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt twoPiInv3_pos)
    refine integral_mono_of_nonneg (Eventually.of_forall (fun p => ?_)) (hintG i)
      (Eventually.of_forall (fun p => ?_))
    · exact mul_nonneg (fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha.le 3))
          (integral_nonneg (fun x => sq_nonneg _)))
    · exact mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq_all hc)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha.le 3))
          (integral_nonneg (fun x => sq_nonneg _)))
  -- (2) the fibre Plancherel identity for the squared symbol
  have hid := tBdiagForm_sq_eq_dirichlet (a := a) (A := A) (volA := volA) (χ := χ) (n := n)
    ha hχ hcs htsupp hA hΨ
  -- (3) the Leibniz / window bound
  have hleib := dirichlet_boxQ_le (a := a) (Cχ := Cχ) (A := A) (volA := volA) (χ := χ) (n := n)
    ha hCχ hχ hA hsup hΨ
  calc tBwordKin a A volA χ c Ψ ≤ tBdiagForm a A volA χ (fun r => r ^ 2) Ψ := hmono
    _ = ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) a, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Submission.BoseGases.X (n + 1) =>
              χ (y i) * boxQ volA A i Ψ y) x
            (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := hid
    _ ≤ 2 * Cχ ^ 2 * Submission.BoseGases.kinWord (n + 1) a Ψ
        + 2 * winErrBox a A volA χ Ψ := hleib

end Work.SmallBoxTBWord
