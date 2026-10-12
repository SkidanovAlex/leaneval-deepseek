import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.aemeasurable_momWord_zero_fibre`

**The large-momentum word `momWord` at the *anchored* box `Λ(0)`, evaluated along the slot-`i`
fibre of a smooth `(n+1)`-body state, is a.e. strongly measurable in the configuration of the
remaining `n` particles.**

The object of the statement is (`Work.BoseKinLoc.momWord`, FS `eq:DefT`'s third piece)

    `momWord ℓ d ε_T b u ψ = b·ε_T·(dℓ)⁻²·(2π)⁻³∫_p 1_{(d²ℓ)⁻¹<‖p‖}(p)·‖𝓕(1_{Λ(u)}·Q_uψ)(p)‖²`

at `u = 0`, `ψ = genFibre i Ψ r`, i.e. the word of the fibre
`genFibre i Ψ r = (z ↦ Ψ(kcInsN n i (z,r)))` in the *box centred at the origin*
`Λ(0) = acube ℓ` (no translation parameter).

## Proof

This is a purely measure-theoretic statement, and in fact the word is *strongly* measurable —
no `a.e.` qualifier is needed, no integrability hypothesis is used (the Bochner integral is
total) and neither `hℓ`, `hL` nor `hsupp` is needed: only smoothness of `Ψ`.

The `r`-dependence of the word enters only through the fibre
`z ↦ Ψ(kcInsN n i (z,r))`, and `kcInsN n i` is a measurable equivalence, so:

* `(r,z) ↦ Ψ(kcInsN n i (z,r))` is jointly measurable (`Ψ` is continuous);
* the box mean `r ↦ m_0(genFibre i Ψ r) = (ℓ³)⁻¹∫_{acube ℓ}Ψ(kcInsN n i (z,r))dz`
  is *strongly* measurable by the unconditional Fubini-type lemma
  `MeasureTheory.StronglyMeasurable.integral_prod_right'` applied to the jointly measurable
  integrand, whence `(r,z) ↦ Q_0(genFibre i Ψ r)(z) = Ψ(kcInsN n i (z,r)) − m_0(·)` is jointly
  measurable;
* the `p`-Fourier transform of `1_{Λ(0)}·Q_0ψ` is an integral over `y` against the jointly
  measurable kernel `((r,p),y) ↦ e^{−i⟪p,y⟫}·1_{Λ(0)}(y)·Q_0ψ(y)`, so it is strongly measurable
  in `(r,p)` by the same lemma applied to the index `r × p`;
* taking norms, squaring and multiplying by the (measurable) spectral cutoff
  `p ↦ 1_{(d²ℓ)⁻¹<‖p‖}(p)` preserves strong measurability, and a final parametric integral over
  `p` gives strong measurability of `r ↦ momForm ℓ d 0 (genFibre i Ψ r)`; multiplying by the
  constant prefactor gives the word.

The sibling modules `Kinetic.momWord_measurable` (fixed `ψ`, variable `u`) and
`Kinetic.momForm_fibre_aemeasurable` (variable `u` and fibre, product measure) contain the same
argument; here it is run at the fixed box `Λ(0)` with the fibre dependence in the configuration
variable only, so that the conclusion is measurability in `r` alone.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Sector

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The two `r`-dependent factors of the windowed mean-free fibre -/

/-- The indicator of the anchored box, `x ↦ 1_{Λ(0)}(x)`, is measurable. -/
private lemma measurable_indU_zero {α : Type*} [MeasurableSpace α] (ℓ : ℝ) :
    Measurable (fun a : α × E3 => Work.BoseKinLoc.indU ℓ 0 a.2) := by
  classical
  have hset : MeasurableSet {a : α × E3 | a.2 - ℓ • (0 : E3) ∈ Submission.BoseGases.acube ℓ} :=
    (Submission.BoseGases.acube_measurable ℓ).preimage
      (measurable_snd.sub measurable_const)
  have heq : (fun a : α × E3 => Work.BoseKinLoc.indU ℓ 0 a.2)
      = fun a => if a.2 - ℓ • (0 : E3) ∈ Submission.BoseGases.acube ℓ then (1 : ℝ) else 0 := by
    funext a
    rfl
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

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

/-- **Joint measurability of the mean-free fibre at the anchored box.**  For a smooth
`(n+1)`-body state `Ψ`, the map
`(r,z) ↦ Q_0(genFibre i Ψ r) z = Ψ(kcInsN n i (z,r)) − (ℓ³)⁻¹∫_{acube ℓ}Ψ(kcInsN n i (z',r))dz'`
is jointly measurable. -/
private lemma measurable_qfree_genFibre_zero {ℓ : ℝ} {n : ℕ}
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) :
    Measurable (fun a : Submission.BoseGases.X n × E3 =>
      Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ a.1) a.2) := by
  have hPsi : Measurable (fun a : Submission.BoseGases.X n × E3 =>
      Ψ (Submission.BoseGases.kcInsN n i (a.2, a.1))) :=
    hΨ.continuous.measurable.comp ((Submission.BoseGases.kcInsN n i).measurable.comp
      (Measurable.prodMk measurable_snd measurable_fst))
  -- the box mean is strongly measurable in the configuration
  have hmean : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) := by
    have hjoint : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
        Ψ (Submission.BoseGases.kcInsN n i (w.2, w.1))) := hPsi.stronglyMeasurable
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
        (Submission.BoseGases.acube ℓ)) hjoint
    have heq : (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => (ℓ ^ 3)⁻¹ * ∫ z : E3, Ψ (Submission.BoseGases.kcInsN n i (z, r))
            ∂(MeasureTheory.volume : MeasureTheory.Measure E3).restrict
              (Submission.BoseGases.acube ℓ) := by
      funext r
      simp [Work.BSKinetic.bsMean, Work.BoseKinLoc.Kinetic.genFibre]
    rw [heq]
    exact h.const_mul _
  have heq2 : (fun a : Submission.BoseGases.X n × E3 =>
      Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ a.1) a.2)
      = fun a => Ψ (Submission.BoseGases.kcInsN n i (a.2, a.1)) -
          Work.BSKinetic.bsMean ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ a.1) := by
    funext a
    rfl
  rw [heq2]
  exact hPsi.sub (hmean.comp_measurable measurable_fst).measurable

/-! ## 2. The Fourier transform of the windowed mean-free fibre -/

/-- Strong measurability of the `p`-convention Fourier transform of the windowed mean-free
fibre, as a function of `(r,p)`. -/
private lemma stronglyMeasurable_kinFT_zero_fibre {ℓ : ℝ} {n : ℕ}
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) :
    StronglyMeasurable (fun q : Submission.BoseGases.X n × E3 =>
      Submission.BoseGases.kinFT (fun z : E3 =>
        ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.1) z : ℝ) : ℂ))
        q.2) := by
  have hproj : Measurable (fun w : (Submission.BoseGases.X n × E3) × E3 =>
      (w.1.1, w.2)) := Measurable.prodMk measurable_fst.fst measurable_snd
  have hstat : Measurable (fun w : (Submission.BoseGases.X n × E3) × E3 =>
      ((Work.BoseKinLoc.indU ℓ 0 w.2 : ℝ) : ℂ) *
      ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ w.1.1) w.2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
        ((measurable_indU_zero (α := Submission.BoseGases.X n) ℓ).comp hproj)).mul
      (Complex.continuous_ofReal.measurable.comp
        ((measurable_qfree_genFibre_zero hΨ i).comp hproj))
  have hker : Measurable (fun w : (Submission.BoseGases.X n × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ)))) :=
    Complex.continuous_exp.measurable.comp
      ((by fun_prop : Continuous fun w : (Submission.BoseGases.X n × E3) × E3 =>
        -(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))).measurable)
  simp only [Submission.BoseGases.kinFT]
  refine MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
    (f := fun w : (Submission.BoseGases.X n × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))) *
      (((Work.BoseKinLoc.indU ℓ 0 w.2 : ℝ) : ℂ) *
      ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ w.1.1) w.2 : ℝ) : ℂ))) ?_
  exact (hker.mul hstat).stronglyMeasurable

/-! ## 3. The word -/

theorem aemeasurable_momWord_zero_fibre {ℓ d εT b L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    {n : ℕ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
  classical
  have hFT := stronglyMeasurable_kinFT_zero_fibre (ℓ := ℓ) hΨ i
  have hD : StronglyMeasurable (fun q : Submission.BoseGases.X n × E3 =>
      Work.BoseKinLoc.momProj ℓ d q.2 *
      ‖Submission.BoseGases.kinFT (fun z : E3 =>
        ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
        ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.1) z : ℝ) : ℂ))
        q.2‖ ^ 2) :=
    ((measurable_momProj ℓ d).comp measurable_snd).stronglyMeasurable.mul (hFT.norm.pow 2)
  have hout : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) z : ℝ) : ℂ))
          p‖ ^ 2) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hD
  have hform : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) := by
    have heq : (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
            ((Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) z : ℝ) : ℂ))
            p‖ ^ 2 := by
      funext r
      rfl
    rw [heq]
    exact hout.const_mul _
  have hword : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) := by
    have heq : (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => (b * εT) * (d * ℓ) ^ (-2 : ℤ) *
            Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) := by
      funext r
      rfl
    rw [heq]
    exact hform.const_mul _
  exact hword.aestronglyMeasurable

end Work.BoseKinLoc.Sector
