import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.momFormIntegrandMeasurable`

**Joint strong measurability of the `momForm` integrand** on `(u,p) ∈ ℝ³ × ℝ³`:

  `(u,p) ↦ momProj ℓ d p · ‖kinFT (1_{Λ(u)}·Q_u g) p‖²`,

for a **merely measurable** (not smooth, not compactly supported, not `L²`) one-body state
`g : ℝ³ → ℝ`.

This is the integrand of `Work.BoseKinLoc.momForm` (`Defs.lean`), namely

  `momForm ℓ d u g = (2π)⁻³ ∫_p momProj ℓ d p · ‖kinFT (1_{Λ(u)}(g − m_u)) p‖² `,

written through the complexified mean-free box state
`statU ℓ u g = 1_{Λ(u)}·(g − m_u)` (`momDefs.lean`).  The statement is the key input to
Fubini/Tonelli on the product measure `volume ⊗ volume`, which interchanges the `u`- and
`p`-integrations of the sliding kinetic word.

Nothing beyond measurability is used — no integrability, no decay of the Fourier transform,
no compact support: the Bochner integral is total, and the parametric-integral measurability
lemma `StronglyMeasurable.integral_prod_right'` is unconditional in the integrand.

The three `(u,x)`-joint measurability inputs are:

* `(u,x) ↦ 1_{Λ(u)}(x)`: `Λ(u) = ℓu + acube ℓ` is the preimage of the measurable set
  `acube ℓ` under the continuous map `(u,x) ↦ x − ℓu`
  (`Submission.BoseGases.acube_measurable`);
* `(u,x) ↦ m_u(g) = (ℓ³)⁻¹∫_{acube ℓ} g(ℓu+z) dz`: the parametric integral of the jointly
  measurable `((u,x),z) ↦ g(ℓu+z)` (`StronglyMeasurable.integral_prod_right'`), whence
  `(u,x) ↦ Q_u g(x) = g(x) − m_u(g)` is jointly measurable;
* `p ↦ momProj ℓ d p = 1_{(d²ℓ)⁻¹<‖p‖}(p)`: an indicator of an open set.

Then the `p`-Fourier transform is the parametric `y`-integral of the jointly measurable
`((u,p),y) ↦ e^{−i⟪p,y⟫}·1_{Λ(u)}(y)·Q_u g(y)`, so it is strongly measurable in `(u,p)`;
norms, squares and the product with the cutoff preserve strong measurability.
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

/-- The box mean `(u,x) ↦ m_u(ψ) = (ℓ³)⁻¹∫_{acube ℓ}ψ(ℓu+z) dz` is jointly measurable as soon
as `ψ` is measurable.  (It does not depend on `x`; the joint form is what is used below, and
the parametric-integral lemma is unconditional in the integrand.) -/
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

theorem momFormIntegrandMeasurable (ℓ d : ℝ) {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Measurable g) :
    MeasureTheory.StronglyMeasurable (fun w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.momProj ℓ d w.2 *
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ w.1 z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ w.1 g z : ℝ) : ℂ)) w.2‖ ^ 2) := by
  classical
  have hInd : Measurable (fun q : E3 × E3 => Work.BoseKinLoc.indU ℓ q.1 q.2) :=
    measurable_uncurry_indU ℓ
  have hQ : Measurable (fun q : E3 × E3 => Work.BoseKinLoc.Qfree ℓ q.1 g q.2) :=
    measurable_uncurry_Qfree ℓ g hg
  -- the projection `((u,p),y) ↦ (u,y)`
  have hproj : Measurable (fun s : (E3 × E3) × E3 => (s.1.1, s.2)) :=
    Measurable.prodMk measurable_fst.fst measurable_snd
  -- joint measurability of the complexified mean-free state `(u,y) ↦ 1_{Λ(u)}(y)·Q_u g(y)`
  have hft : Measurable (fun s : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ))) *
        (((Work.BoseKinLoc.indU ℓ s.1.1 s.2 : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ s.1.1 g s.2 : ℝ) : ℂ))) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact Complex.continuous_exp.measurable.comp (by fun_prop)
    · exact Complex.continuous_ofReal.measurable.comp (hInd.comp hproj)
    · exact Complex.continuous_ofReal.measurable.comp (hQ.comp hproj)
  -- hence the `p`-Fourier transform is strongly measurable in `(u,p)`
  have hFT : StronglyMeasurable (fun q : E3 × E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => ((Work.BoseKinLoc.indU ℓ q.1 z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.Qfree ℓ q.1 g z : ℝ) : ℂ)) q.2) := by
    simp only [Submission.BoseGases.kinFT]
    refine MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
      (f := fun s : (E3 × E3) × E3 => Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ))) *
        (((Work.BoseKinLoc.indU ℓ s.1.1 s.2 : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ s.1.1 g s.2 : ℝ) : ℂ))) hft.stronglyMeasurable
  -- multiply by the (measurable) spectral cutoff
  exact ((measurable_momProj ℓ d).comp measurable_snd).stronglyMeasurable.mul (hFT.norm.pow 2)

end Work.BoseKinLoc.Momentum
