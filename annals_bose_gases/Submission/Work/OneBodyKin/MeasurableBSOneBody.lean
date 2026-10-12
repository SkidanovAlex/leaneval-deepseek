import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Measurability of the one-body big-box kinetic form in the box centre

The one-body big-box kinetic form of FS `lem:LocKinEn` is

    `bsOneBody ℓ F u ψ = (2π)⁻³ ∫_p F(‖p‖)·‖kinFT (χ_u · Q_{Λ(u)}ψ) p‖²`,

where `χ_u(x) = chiScale ℓ (x − ℓu)` and `Q_{Λ(u)}ψ = ψ − bsMean ℓ u ψ`, and
`kinFT v p = ∫_y e^{−i⟪p,y⟫} v(y) dy`.  Any use of this object inside an
integral over the box centre `u` (e.g. `bsFamilyForm`) needs at least that it is
measurable in `u`; this file provides exactly that.

The subtlety is that `kinFT` is a *parametric Bochner integral over all of `ℝ³`*:
there is no integrability hypothesis available on the integrand (`ψ` need not
decay, `G` is merely measurable), so the classical
"measurable-parameter ⇒ continuous/measurable integral" lemmas do not apply.
The right tool is `MeasureTheory.StronglyMeasurable.integral_prod_right'`, which
turns strong measurability of a jointly strongly measurable integrand into strong
measurability of its partial integral, with **no** integrability assumption
(it is compatible with the total, i.e. zero-on-non-integrable, Bochner
integral).  This is the same device the corpus uses for the per-fibre kinetic
energy (`Work.SmallBoxTBWord.fibre_energy_aestronglyMeasurable`) and for the
sliding box mean (`Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean`).

The proof is therefore a two-fold application of that lemma:

* the `u`-dependent box mean `u ↦ bsMean ℓ u ψ` is strongly measurable because
  it is the partial integral of the jointly continuous `(u,z) ↦ ψ(ℓu + z)`;
* hence the full integrand `(u,p,y) ↦ e^{−i⟪p,y⟫}χ_u(y)(ψ(y) − bsMean ℓ u ψ)`
  is jointly strongly measurable, so integrating out `y` gives `(u,p) ↦ kinFT …`,
  multiplying by the continuous `p ↦ G‖p‖` and `‖·‖²` is harmless, and
  integrating out `p` gives strong measurability of `u ↦ bsOneBody ℓ G u ψ`.

Note that neither `0 < ℓ` nor `HasCompactSupport ψ` is used: measurability needs
only the continuity of `ψ` (and the measurability of `G`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The moving-box mean `u ↦ bsMean ℓ u ψ = (ℓ³)⁻¹∫_{acube ℓ} ψ(ℓu + z)dz` is
strongly measurable in the box centre `u` for continuous `ψ`.

It is the partial integral of the jointly continuous function
`(u,z) ↦ ψ(ℓ·u + z)`, so `MeasureTheory.StronglyMeasurable.integral_prod_right'`
applies to the measure `volume.restrict (acube ℓ)`. -/
private theorem stronglyMeasurable_bsMean {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    StronglyMeasurable (fun u : ℝ³ => Work.BSKinetic.bsMean ℓ u ψ) := by
  have hg : StronglyMeasurable (fun q : ℝ³ × ℝ³ => ψ (ℓ • q.1 + q.2)) :=
    (hψ.comp (by fun_prop)).stronglyMeasurable
  have hint := hg.integral_prod_right'
    (ν := (volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
  exact hint.const_mul ((ℓ ^ 3)⁻¹)

theorem MeasurableBSOneBody {ℓ : ℝ} (hℓ : 0 < ℓ) {G : ℝ → ℝ} (hG : Measurable G)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ G u ψ) := by
  -- **Step 0.** The `u`-box mean, and hence the mean-free part of `ψ`.
  have hMean : StronglyMeasurable (fun u : ℝ³ => Work.BSKinetic.bsMean ℓ u ψ) :=
    stronglyMeasurable_bsMean hψ
  have hQ : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.ofReal (ψ q.2 - Work.BSKinetic.bsMean ℓ q.1.1 ψ)) := by
    apply Complex.continuous_ofReal.comp_stronglyMeasurable
    exact (hψ.comp (by fun_prop)).stronglyMeasurable.sub
      (hMean.comp_measurable (by fun_prop))
  -- **Step 1.** The integrand of `kinFT`, jointly in `(u,p,y)`.
  have hexp : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ)))) :=
    (by fun_prop : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ))))).stronglyMeasurable
  have hwin : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      (Submission.BoseGases.chiScale ℓ (q.2 - ℓ • q.1.1) : ℂ)) :=
    (by
      apply Complex.continuous_ofReal.comp
      apply (Submission.BoseGases.chiScale_continuous ℓ).comp
      fun_prop : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        (Submission.BoseGases.chiScale ℓ (q.2 - ℓ • q.1.1) : ℂ))).stronglyMeasurable
  have hf : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiScale ℓ (q.2 - ℓ • q.1.1) : ℂ) *
          Complex.ofReal (ψ q.2 - Work.BSKinetic.bsMean ℓ q.1.1 ψ))) :=
    hexp.mul (hwin.mul hQ)
  -- **Step 2.** Integrate out the position `y`: this is `(u,p) ↦ kinFT (χ_u·Q_uψ) p`.
  have hK : StronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      ∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ q.2 y : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiScale ℓ (y - ℓ • q.1) : ℂ) *
          Complex.ofReal (ψ y - Work.BSKinetic.bsMean ℓ q.1 ψ))) :=
    hf.integral_prod_right' (ν := (volume : Measure ℝ³))
  -- **Step 3.** Multiply by the symbol `G‖p‖` and take the squared norm.
  have hGp : StronglyMeasurable (fun q : ℝ³ × ℝ³ => G ‖q.2‖ *
      ‖(∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ q.2 y : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiScale ℓ (y - ℓ • q.1) : ℂ) *
          Complex.ofReal (ψ y - Work.BSKinetic.bsMean ℓ q.1 ψ)))‖ ^ 2) := by
    have hGm : StronglyMeasurable (fun q : ℝ³ × ℝ³ => G ‖q.2‖) :=
      (hG.comp continuous_norm.measurable).stronglyMeasurable.comp_measurable (by fun_prop)
    exact hGm.mul (hK.norm.pow 2)
  -- **Step 4.** Integrate out the momentum `p`.
  have hF : StronglyMeasurable (fun u : ℝ³ =>
      ∫ p : ℝ³, G ‖p‖ *
        ‖(∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chiScale ℓ (y - ℓ • u) : ℂ) *
            Complex.ofReal (ψ y - Work.BSKinetic.bsMean ℓ u ψ)))‖ ^ 2) :=
    hGp.integral_prod_right' (ν := (volume : Measure ℝ³))
  -- **Step 5.** Restore the normalisation constant and weaken to a.e. strong measurability.
  exact (hF.const_mul (((2 * Real.pi) ^ 3)⁻¹)).aestronglyMeasurable

end Work.OneBodyKin
