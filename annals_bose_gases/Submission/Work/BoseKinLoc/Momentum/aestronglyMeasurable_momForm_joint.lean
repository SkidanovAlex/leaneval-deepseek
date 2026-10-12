import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Kinetic.momWord_measurable
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.aestronglyMeasurable_momForm_joint`

**Joint** (a.e.) strong measurability in `(u,p)` of the `momForm` integrand written through the
complexified mean-free box state `statU ℓ u ψ = 1_{Λ(u)}(ψ − m_u)`:

  `(u,p) ↦ momProj ℓ d p · ‖kinFT (statU ℓ u ψ) p‖²`.

This is the two-variable version of `Work.BoseKinLoc.Kinetic.momWord_measurable` (which is the
`u`-only statement), and it is what Fubini/Tonelli on the product measure `volume ⊗ volume`
needs in order to interchange the `u`- and `p`-integrations of the sliding kinetic word.

The proof is a purely measure-theoretic `(u,x)`-joint-measurability argument; no integrability,
no decay and no compact support are required (Bochner integration is total, and
`StronglyMeasurable.integral_prod_right'` is unconditional in the integrand):

* `(u,x) ↦ 1_{Λ(u)}(x)` is jointly measurable, since `Λ(u) = ℓu + acube ℓ` is the preimage of
  the measurable set `acube ℓ` under the continuous map `(u,x) ↦ x − ℓu`
  (`Submission.BoseGases.acube_measurable`), so it is an indicator of a measurable set;
* `u ↦ m_u(ψ) = (ℓ³)⁻¹∫_{acube ℓ} ψ(ℓu+z) dz` is strongly measurable for merely *continuous*
  `ψ`, because `(u,z) ↦ ψ(ℓu+z)` is jointly measurable and the box integral is a parametric
  Bochner integral (`StronglyMeasurable.integral_prod_right'`); hence
  `(u,x) ↦ Q_uψ(x) = ψ(x) − m_u(ψ)` is jointly measurable;
* the `p`-Fourier transform is the parametric integral over `y` of the jointly measurable
  integrand `((u,p),y) ↦ e^{−i⟪p,y⟫}·1_{Λ(u)}(y)·Q_uψ(y)`, hence strongly measurable in `(u,p)`
  by the same lemma applied with the product index `(u,p)`;
* taking norms, squaring and multiplying by the (measurable) spectral cutoff
  `p ↦ momProj ℓ d p` preserves strong measurability.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Joint measurability of the two `u`-dependent factors -/

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

/-- The box mean `(u,x) ↦ m_u(ψ)` is jointly measurable as soon as `ψ` is measurable.

(`m_u(ψ) = (ℓ³)⁻¹∫_{acube ℓ} ψ(ℓu+z) dz` does not depend on `x`, but it is convenient to state
it in the joint form used below; no compact support of `ψ` is needed.) -/
private lemma measurable_uncurry_bsMean (ℓ : ℝ) (ψ : E3 → ℝ) (hψ : Measurable ψ) :
    Measurable (fun q : E3 × E3 => Work.BSKinetic.bsMean ℓ q.1 ψ) := by
  have hf : StronglyMeasurable (fun s : (E3 × E3) × E3 => ψ (ℓ • s.1.1 + s.2)) :=
    (hψ.comp (by fun_prop : Measurable fun s : (E3 × E3) × E3 => ℓ • s.1.1 + s.2)).stronglyMeasurable
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Submission.BoseGases.acube ℓ)) hf
  have h2 : StronglyMeasurable (fun q : E3 × E3 => Work.BSKinetic.bsMean ℓ q.1 ψ) := by
    simpa only [Work.BSKinetic.bsMean] using h.const_mul ((ℓ ^ 3)⁻¹)
  exact h2.measurable

/-- The mean-free projection `(u,x) ↦ Q_uψ(x) = ψ(x) − m_u(ψ)` is jointly measurable. -/
private lemma measurable_uncurry_Qfree (ℓ : ℝ) (ψ : E3 → ℝ) (hψ : Measurable ψ) :
    Measurable (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 ψ q.2) := by
  have hQ : (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 ψ q.2)
      = fun q : E3 × E3 => ψ q.2 - Work.BSKinetic.bsMean ℓ q.1 ψ := rfl
  rw [hQ]
  exact (hψ.comp measurable_snd).sub (measurable_uncurry_bsMean ℓ ψ hψ)

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

/-! ## The statement -/

theorem aestronglyMeasurable_momForm_joint (ℓ d : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hℓ : 0 < ℓ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun u p : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momProj ℓ d p * ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Momentum.statU ℓ u ψ) p‖ ^ 2)) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hInd : Measurable (fun q : E3 × E3 => Work.BoseKinLoc.indU ℓ q.1 q.2) :=
    measurable_uncurry_indU ℓ
  have hQ : Measurable (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 ψ q.2) :=
    measurable_uncurry_Qfree ℓ ψ hψm
  -- the projections onto `(u,y)` and `(p,y)` out of `((u,p),y)`
  have hproj : Measurable (fun s : (E3 × E3) × E3 => (s.1.1, s.2)) :=
    Measurable.prodMk measurable_fst.fst measurable_snd
  -- joint measurability of the complexified mean-free state `(u,y) ↦ statU ℓ u ψ y`
  have hStat : Measurable (fun s : (E3 × E3) × E3 =>
      Work.BoseKinLoc.Momentum.statU ℓ s.1.1 ψ s.2) := by
    have h1 : Measurable (fun s : (E3 × E3) × E3 =>
        ((Work.BoseKinLoc.indU ℓ s.1.1 s.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hInd.comp hproj)
    have h2 : Measurable (fun s : (E3 × E3) × E3 =>
        ((Work.BoseKinLoc.Qfree ℓ s.1.1 ψ s.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hQ.comp hproj)
    exact h1.mul h2
  -- hence the `p`-Fourier transform is strongly measurable in `(u,p)`
  have hFT : StronglyMeasurable (fun q : E3 × E3 =>
      Submission.BoseGases.kinFT (Work.BoseKinLoc.Momentum.statU ℓ q.1 ψ) q.2) := by
    simp only [Submission.BoseGases.kinFT]
    refine MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3))
      (f := fun s : (E3 × E3) × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ))) *
          Work.BoseKinLoc.Momentum.statU ℓ s.1.1 ψ s.2) ?_
    have hexp : StronglyMeasurable (fun s : (E3 × E3) × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ)))) :=
      (by fun_prop : Continuous fun s : (E3 × E3) × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ)))).stronglyMeasurable
    exact hexp.mul hStat.stronglyMeasurable
  -- the joint `(u,p)`-integrand of `momForm`
  have hD : StronglyMeasurable (fun q : E3 × E3 => Work.BoseKinLoc.momProj ℓ d q.2 *
      ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Momentum.statU ℓ q.1 ψ) q.2‖ ^ 2) :=
    ((measurable_momProj ℓ d).comp measurable_snd).stronglyMeasurable.mul (hFT.norm.pow 2)
  exact hD.aestronglyMeasurable

end Work.BoseKinLoc.Momentum
