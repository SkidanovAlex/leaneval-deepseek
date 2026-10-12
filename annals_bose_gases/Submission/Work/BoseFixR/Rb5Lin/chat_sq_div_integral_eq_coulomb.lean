import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal
import Submission.Work.BoseFixR.mass_le_W1omega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.chat_sq_div_integral_eq_coulomb`

The **Coulomb / Newtonian-energy identity** in the corpus's `chat` (cosine) Fourier
convention: for an integrable, a.e. nonnegative, even `W : ℝ³ → ℝ`,

  `(2π)⁻³ ∫ q, Ŵ(q)²/(2‖q‖²) = (1/8π) ∫∫ W(x)W(y)/‖x−y‖ dxdy`,

with `Ŵ(q) = ∫ W(y) cos⟨q,y⟩ dy` (`Work.BoseFixR.chat`).

Route (all in terms of the module
`Submission.Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal`, which proves the same
identity with the *position-space* double integral kept as the `.toReal` of an iterated
`∫⁻`):

* that corpus theorem gives
  `(2π)⁻³ ∫ q, Ŵ(q)²/(2‖q‖²) = (1/8π) (∫⁻x ∫⁻y, ofReal (W x W y/‖x−y‖)).toReal`;
* `integral_coulomb_eq_toReal_lintegral` below identifies that `.toReal` with the *product
  measure* Bochner integral `∫ p : ℝ³×ℝ³, W p.1 * W p.2/‖p.1−p.2‖` appearing in the target:
  the a.e. nonnegativity of `W` (only assumed a.e. — the corpus lemma reduces to `max W 0`)
  makes `integral_eq_lintegral_of_nonneg_ae` applicable, and Tonelli's theorem
  (`MeasureTheory.lintegral_prod`) converts the product `∫⁻` into the iterated one.

The two finiteness hypotheses `hint`, `hint2` are not needed for the identity itself (both
sides are the same real number, `0 = 0` included in the degenerate case), but they are kept:
they are part of the requested statement.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.Rb5Lin

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The Coulomb double integral: product-measure Bochner integral versus iterated `∫⁻`.**

For an integrable a.e. nonnegative `W`,

  `∫ p : E3 × E3, W p.1 * W p.2 / ‖p.1 − p.2‖ = (∫⁻ x, ∫⁻ y, ofReal (W x * W y / ‖x − y‖)).toReal`.

The left side is `_root_.integral_eq_lintegral_of_nonneg_ae` (the integrand is a.e.
nonnegative because both `W`-factors are, and the `‖·‖`-division cannot make it negative),
and the resulting product `∫⁻` is the iterated one by `MeasureTheory.lintegral_prod`
(the measure on `E3 × E3` is `volume × volume` by definition). -/
lemma integral_coulomb_eq_toReal_lintegral {W : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W) :
    (∫ p : E3 × E3, W p.1 * W p.2 / ‖p.1 - p.2‖)
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal := by
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] fun p : E3 × E3 =>
      W p.1 * W p.2 / ‖p.1 - p.2‖ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hWnn,
      Measure.quasiMeasurePreserving_snd.ae hWnn] with p hp1 hp2
    exact div_nonneg (mul_nonneg hp1 hp2) (norm_nonneg _)
  have hae : AEMeasurable (fun p : E3 × E3 =>
      ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2‖)) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_snd
    have h3 : AEMeasurable (fun p : E3 × E3 => ‖p.1 - p.2‖) (volume.prod volume) :=
      ((measurable_fst.sub measurable_snd).norm).aemeasurable
    exact ((h1.mul h2).div h3).ennreal_ofReal
  have hmeas : AEStronglyMeasurable (fun p : E3 × E3 =>
      W p.1 * W p.2 / ‖p.1 - p.2‖) volume := by
    have h1 : AEMeasurable (fun p : E3 × E3 => W p.1) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_fst
    have h2 : AEMeasurable (fun p : E3 × E3 => W p.2) (volume.prod volume) :=
      hW.aestronglyMeasurable.aemeasurable.comp_snd
    have h3 : AEMeasurable (fun p : E3 × E3 => ‖p.1 - p.2‖) (volume.prod volume) :=
      ((measurable_fst.sub measurable_snd).norm).aemeasurable
    exact ((h1.mul h2).div h3).aestronglyMeasurable
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  congr 1
  exact MeasureTheory.lintegral_prod _ hae

theorem chat_sq_div_integral_eq_coulomb {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (heven : ∀ x, W (-x) = W x)
    (hint : (∫⁻ q, ENNReal.ofReal ((Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2))) < ⊤)
    (hint2 : (∫⁻ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2‖)) < ⊤) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)
      = (1 / (8 * Real.pi)) * ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          W p.1 * W p.2 / ‖p.1 - p.2‖ := by
  have hmain := Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal hW hWnn heven
  rw [integral_coulomb_eq_toReal_lintegral hW hWnn]
  exact hmain

end Work.BoseFixR.Rb5Lin
