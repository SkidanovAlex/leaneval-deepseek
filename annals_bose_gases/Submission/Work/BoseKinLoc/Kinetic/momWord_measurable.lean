import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.momWord_measurable` — measurability of the large-momentum word

FS `eq:DefT`'s third kinetic piece is the one-body quadratic form
(`Work.BoseKinLoc.momWord`, node C of the audit)

    `momWord ℓ d εT b u ψ = b·ε_T·(dℓ)⁻² · (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}(p)·‖𝓕(1_{Λ(u)}·Q_uψ)(p)‖²`,

as a function of the *moving-box* parameter `u ∈ ℝ³`.  This module proves that it is
(strongly, hence a.e.) measurable in `u`.

The only `u`-dependence sits in the box indicator `1_{Λ(u)}` and in the box mean
`m_u(ψ) = |Λ(u)|⁻¹∫_{Λ(u)}ψ` entering `Q_uψ = ψ − m_u(ψ)`.  Both are handled by
joint measurability of the two nested integrands:

* `(u,x) ↦ 1_{Λ(u)}(x)` is measurable: `Λ(u) = ℓu + acube ℓ`, so it is the indicator of the
  closed set `{(u,x) | x − ℓu ∈ acube ℓ}` (`Submission.BoseGases.acube_measurable`);
* `u ↦ m_u(ψ)` is in fact *continuous* for smooth compactly supported `ψ`
  (`Work.BSKinetic.continuous_bsMean_of_ne`), so it contributes no difficulty;
* the `p`-Fourier transform is an integral over `y` of a jointly measurable function of
  `((u,p),y)`, hence strongly measurable in `(u,p)`
  (`MeasureTheory.StronglyMeasurable.integral_prod_right'`);
* integrating the resulting `(u,p)`-measurable weight against `p` twice, once more by the same
  lemma, gives strong measurability in `u`.

No integrability (indeed no decay of the Fourier transform) is needed: the Bochner integral is
defined for every function, and the Fubini-measurability lemma used is unconditional.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The box indicator `(u,x) ↦ 1_{Λ(u)}(x)` is jointly measurable. -/
private lemma measurable_uncurry_indU (ℓ : ℝ) :
    Measurable (fun q : E3 × E3 => Work.BoseKinLoc.indU ℓ q.1 q.2) := by
  classical
  have hset : MeasurableSet {q : E3 × E3 | q.2 - ℓ • q.1 ∈ Submission.BoseGases.acube ℓ} :=
    (Submission.BoseGases.acube_measurable ℓ).preimage
      ((continuous_snd.sub (continuous_fst.const_smul ℓ)).measurable)
  have heq : (fun q : E3 × E3 => Work.BoseKinLoc.indU ℓ q.1 q.2)
      = fun q => if q.2 - ℓ • q.1 ∈ Submission.BoseGases.acube ℓ then (1 : ℝ) else 0 := by
    funext q
    rfl
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

/-- The mean-free projection `(u,x) ↦ Q_uψ(x) = ψ(x) − m_u(ψ)` is jointly measurable. -/
private lemma measurable_uncurry_Qfree {ℓ : ℝ} {ψ : E3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (hℓ : ℓ ≠ 0) :
    Measurable (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 ψ q.2) := by
  have heq : (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 ψ q.2)
      = fun q => ψ q.2 - Work.BSKinetic.bsMean ℓ q.1 ψ := rfl
  rw [heq]
  exact (hψ.continuous.measurable.comp measurable_snd).sub
    ((Work.BSKinetic.continuous_bsMean_of_ne hℓ hψ hcs).measurable.comp measurable_fst)

/-- The spectral cutoff `p ↦ 1_{(d²ℓ)⁻¹<‖p‖}(p)` is measurable. -/
private lemma measurable_momProj (ℓ d : ℝ) :
    Measurable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p) := by
  classical
  have heq : (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p)
      = fun p => if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0 := by
    funext p
    rfl
  rw [heq]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    measurable_const measurable_const

theorem momWord_measurable {ℓ d εT b : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.momWord ℓ d εT b u ψ) := by
  classical
  have hInd : Measurable (fun q : E3 × E3 => Work.BoseKinLoc.indU ℓ q.1 q.2) :=
    measurable_uncurry_indU ℓ
  have hQ : Measurable (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 ψ q.2) :=
    measurable_uncurry_Qfree hψ hcs hℓ.ne'
  have hproj : Measurable (fun p : (E3 × E3) × E3 => (p.1.1, p.2)) :=
    Measurable.prodMk (measurable_fst.fst) measurable_snd
  -- joint measurability of the Fourier integrand `(u,p,y) ↦ e^{-i⟪p,y⟫}·1_{Λ(u)}(y)·Q_uψ(y)`
  have hft : Measurable (fun p : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p.1.2 p.2 : ℂ))) *
        (((Work.BoseKinLoc.indU ℓ p.1.1 p.2 : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ p.1.1 ψ p.2 : ℝ) : ℂ))) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact Complex.continuous_exp.measurable.comp (by fun_prop)
    · exact Complex.continuous_ofReal.measurable.comp (hInd.comp hproj)
    · exact Complex.continuous_ofReal.measurable.comp (hQ.comp hproj)
  -- hence the `p`-Fourier transform is strongly measurable in `(u,p)`
  have hFT : StronglyMeasurable (fun q : E3 × E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => ((Work.BoseKinLoc.indU ℓ q.1 z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.Qfree ℓ q.1 ψ z : ℝ) : ℂ)) q.2) := by
    simp only [Submission.BoseGases.kinFT]
    refine MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
      (f := fun p : (E3 × E3) × E3 => Complex.exp (-(Complex.I * (inner ℝ p.1.2 p.2 : ℂ))) *
        (((Work.BoseKinLoc.indU ℓ p.1.1 p.2 : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ p.1.1 ψ p.2 : ℝ) : ℂ))) (hft.stronglyMeasurable)
  -- the `(u,p)`-integrand of `momForm`
  have hD : StronglyMeasurable (fun q : E3 × E3 =>
      Work.BoseKinLoc.momProj ℓ d q.2 *
        ‖Submission.BoseGases.kinFT (fun z : E3 => ((Work.BoseKinLoc.indU ℓ q.1 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ q.1 ψ z : ℝ) : ℂ)) q.2‖ ^ 2) :=
    ((measurable_momProj ℓ d).comp measurable_snd).stronglyMeasurable.mul (hFT.norm.pow 2)
  have hout : StronglyMeasurable (fun u : E3 =>
      ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (fun z : E3 => ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3)) hD
  have hform : StronglyMeasurable (fun u : E3 => Work.BoseKinLoc.momForm ℓ d u ψ) := by
    have heq : (fun u : E3 => Work.BoseKinLoc.momForm ℓ d u ψ)
        = fun u => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (fun z : E3 => ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) *
              ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
      funext u
      rfl
    rw [heq]
    exact hout.const_mul _
  have hword : StronglyMeasurable (fun u : E3 => Work.BoseKinLoc.momWord ℓ d εT b u ψ) := by
    have heq : (fun u : E3 => Work.BoseKinLoc.momWord ℓ d εT b u ψ)
        = fun u => (b * εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.momForm ℓ d u ψ := by
      funext u
      rfl
    rw [heq]
    exact hform.const_mul _
  exact hword.aestronglyMeasurable

end Work.BoseKinLoc.Kinetic
