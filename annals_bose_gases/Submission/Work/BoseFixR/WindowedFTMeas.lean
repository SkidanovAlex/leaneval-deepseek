import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.aemeasurable_mainWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_momWord_zero_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.WindowedFTMeas`

**The windowed Fourier transform of an inserted fibre, weighted by a measurable window `S` and
integrated against `p` once more, is measurable in the configuration of the remaining particles.**

The object of the statement is the `r`-family

    `r ↦ ∫_p S p · ‖ ∫_z e^{−i⟨p,z⟩} · w z · (Q_{Λ,0} ψ_r)(z) dz ‖² dp`,

where `ψ_r` is the slot-`i` fibre of a one-body configuration `Φ : X (m+1) → ℝ`,
`ψ_r(z) = Φ(kcInsN m i (z, r))` (`Work.BoseKinLoc.Qfree ℓ 0` is the anchored-box mean-free
projection `ψ ↦ ψ − |Λ|⁻¹∫_Λ ψ`).

This is exactly the measurability input needed whenever such a windowed kinetic energy is to be
integrated over the remaining coordinates `r` (Tonelli/Fubini), and its proof is the same
unconditional, Fubini-type argument that the corpus already uses for `momForm`
(`Work.BoseKinLoc.Sector.measurable_momForm_genFibre`):

* the fibre family `(z, r) ↦ Φ(kcInsN m i (z, r))` is jointly measurable (`Φ` is continuous,
  `kcInsN m i` is a measurable equivalence);
* the anchored box mean `r ↦ m_0(ψ_r) = ℓ⁻³∫_{acube ℓ} ψ_r` is strongly measurable: it is an
  integral over the *fixed* cube `acube ℓ` of this jointly measurable family
  (`MeasureTheory.StronglyMeasurable.integral_prod_right'`, no integrability hypothesis);
* hence `(z, r) ↦ (Q_{Λ,0} ψ_r)(z) = ψ_r(z) − m_0(ψ_r)` is jointly measurable, and so is the
  `z`-integrand `e^{−i⟨p,z⟩}·w z·Q_{Λ,0}ψ_r(z)` as a function of `((p,r), z)`;
* the Bochner integral in `z` of a jointly measurable function is strongly measurable
  (`integral_prod_right'`), giving the windowed Fourier transform as a strongly measurable
  function of `(p, r)`; multiplying by `S p` and then integrating in `p` once more (again
  `integral_prod_right'`) gives the claim.

The Bochner integral is total, so no integrability, positivity or support hypothesis on
`w, S, ℓ` is needed: only the measurability of `w` and `S` and the continuity of `Φ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The fibre family and the Fourier kernel -/

/-- The slot-`i` fibre family `r ↦ (z ↦ Φ(kcInsN m i (z, r)))` of an `(m+1)`-body state. -/
private def fibreFam {m : ℕ} (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) : E3 → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN m i (z, r))

/-- The Fourier kernel `e^{−i⟨p,y⟩}` of the `p`-convention transform used in the statement. -/
private def fkern (p y : E3) : ℂ := Complex.exp (-(Complex.I * ↑(inner ℝ p y)))

/-- The joint `z`-integrand of the windowed Fourier transform:
`((p,r),z) ↦ e^{−i⟨p,z⟩}·w z·(Q_{Λ,0}ψ_r)(z)`. -/
private def winZ {m : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (w : E3 → ℂ) (a : (E3 × Submission.BoseGases.X m) × E3) : ℂ :=
  fkern a.1.1 a.2 * (w a.2 * ((Work.BoseKinLoc.Qfree ℓ 0 (fibreFam Φ i a.1.2) a.2 : ℝ) : ℂ))

/-- The windowed Fourier transform `(p,r) ↦ ∫_z winZ` of the fibre family. -/
private def zInt {m : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X (m + 1) → ℝ) (i : Fin (m + 1))
    (w : E3 → ℂ) (q : E3 × Submission.BoseGases.X m) : ℂ :=
  ∫ z : E3, winZ ℓ Φ i w (q, z)

/-! ## 2. Joint measurability of the ingredients -/

/-- The Fourier kernel is jointly measurable. -/
private lemma measurable_fkern : Measurable (fun p : E3 × E3 => fkern p.1 p.2) := by
  have hinner : Continuous (fun p : E3 × E3 => inner ℝ p.1 p.2) := continuous_inner
  exact Complex.continuous_exp.measurable.comp
    (continuous_neg.comp (continuous_const.mul (Complex.continuous_ofReal.comp hinner))).measurable

/-- `q ↦ Φ(kcInsN m i q)` is measurable (for continuous `Φ`). -/
private lemma measurable_Phi_insN {m : ℕ} {Φ : Submission.BoseGases.X (m + 1) → ℝ}
    (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    Measurable (fun q : E3 × Submission.BoseGases.X m =>
      Φ (Submission.BoseGases.kcInsN m i q)) :=
  hΦ.measurable.comp (Submission.BoseGases.kcInsN m i).measurable

/-- The *anchored* (`u = 0`) box mean of the fibre family is strongly measurable in the
configuration `r` of the remaining particles. -/
private lemma stronglyMeasurable_bsMean_fibre_zero {ℓ : ℝ} {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    StronglyMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BSKinetic.bsMean ℓ 0 (fibreFam Φ i r)) := by
  classical
  have hjoint : Measurable (fun w : Submission.BoseGases.X m × E3 =>
      Φ (Submission.BoseGases.kcInsN m i (w.2, w.1))) :=
    (measurable_Phi_insN hΦ i).comp (Measurable.prodMk measurable_snd measurable_fst)
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))
    (f := fun w : Submission.BoseGases.X m × E3 =>
      Φ (Submission.BoseGases.kcInsN m i (w.2, w.1))) hjoint.stronglyMeasurable
  have heq : (fun r : Submission.BoseGases.X m => Work.BSKinetic.bsMean ℓ 0 (fibreFam Φ i r))
      = fun r => (ℓ ^ 3)⁻¹ * ∫ z : E3, Φ (Submission.BoseGases.kcInsN m i (z, r))
          ∂(MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ) := by
    funext r
    simp only [Work.BSKinetic.bsMean, fibreFam, smul_zero, zero_add]
  rw [heq]
  exact h.const_mul _

/-- The mean-free projection of the fibre family is jointly (strongly) measurable in
`((p,r),z)` (the `p`-component is not used, only carried). -/
private lemma stronglyMeasurable_qFibre_zero {ℓ : ℝ} {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X m) × E3 =>
      Work.BoseKinLoc.Qfree ℓ 0 (fibreFam Φ i a.1.2) a.2) := by
  have heq : (fun a : (E3 × Submission.BoseGases.X m) × E3 =>
        Work.BoseKinLoc.Qfree ℓ 0 (fibreFam Φ i a.1.2) a.2)
      = fun a => Φ (Submission.BoseGases.kcInsN m i (a.2, a.1.2))
          - Work.BSKinetic.bsMean ℓ 0 (fibreFam Φ i a.1.2) := by
    funext a; rfl
  rw [heq]
  exact ((measurable_Phi_insN hΦ i).comp
      (Measurable.prodMk measurable_snd measurable_fst.snd)).stronglyMeasurable.sub
    ((stronglyMeasurable_bsMean_fibre_zero (ℓ := ℓ) hΦ i).comp_measurable measurable_fst.snd)

/-- The `z`-integrand of the windowed Fourier transform is strongly measurable in
`((p,r),z)`. -/
private lemma stronglyMeasurable_winZ {ℓ : ℝ} {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    {w : E3 → ℂ} (hw : Measurable w) :
    StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X m) × E3 =>
      winZ ℓ Φ i w a) := by
  have hfun : (fun a : (E3 × Submission.BoseGases.X m) × E3 => winZ ℓ Φ i w a)
      = fun a => fkern a.1.1 a.2 *
          (w a.2 * ((Work.BoseKinLoc.Qfree ℓ 0 (fibreFam Φ i a.1.2) a.2 : ℝ) : ℂ)) := by
    funext a; rfl
  rw [hfun]
  have hk : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X m) × E3 =>
      fkern a.1.1 a.2) :=
    (measurable_fkern.comp (Measurable.prodMk measurable_fst.fst measurable_snd)).stronglyMeasurable
  have hw' : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X m) × E3 => w a.2) :=
    (hw.comp measurable_snd).stronglyMeasurable
  have hq : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X m) × E3 =>
      ((Work.BoseKinLoc.Qfree ℓ 0 (fibreFam Φ i a.1.2) a.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_qFibre_zero hΦ i)
  exact hk.mul (hw'.mul hq)

/-! ## 3. The windowed Fourier transform and its `p`-integral -/

/-- The windowed Fourier transform of the fibre family is strongly measurable in `(p,r)`. -/
private lemma stronglyMeasurable_zInt {ℓ : ℝ} {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    {w : E3 → ℂ} (hw : Measurable w) :
    StronglyMeasurable (fun q : E3 × Submission.BoseGases.X m => zInt ℓ Φ i w q) := by
  have hfun : (fun q : E3 × Submission.BoseGases.X m => zInt ℓ Φ i w q)
      = fun q => ∫ z : E3, winZ ℓ Φ i w (q, z) := by
    funext q; rfl
  rw [hfun]
  exact MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
    (f := fun a : (E3 × Submission.BoseGases.X m) × E3 => winZ ℓ Φ i w a)
    (stronglyMeasurable_winZ hΦ i hw)

/-- The `p`-integrand `(p,r) ↦ S p·‖zInt (p,r)‖²` is strongly measurable. -/
private lemma stronglyMeasurable_pIntegrand {ℓ : ℝ} {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    {w : E3 → ℂ} (hw : Measurable w) {S : E3 → ℝ} (hS : Measurable S) :
    StronglyMeasurable (fun q : E3 × Submission.BoseGases.X m =>
      S q.1 * ‖zInt ℓ Φ i w q‖ ^ 2) :=
  (hS.comp measurable_fst).stronglyMeasurable.mul
    ((stronglyMeasurable_zInt hΦ i hw).norm.pow 2)

/-! ## 4. The theorem -/

/-- **The windowed Fourier transform of an inserted fibre, weighted by `S` and integrated in `p`,
is measurable in the remaining configuration.** -/
theorem WindowedFTMeas {m : ℕ} {ℓ : ℝ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    {w : EuclideanSpace ℝ (Fin 3) → ℂ} (hw : Measurable w)
    {S : EuclideanSpace ℝ (Fin 3) → ℝ} (hS : Measurable S) :
    Measurable (fun r : Submission.BoseGases.X m =>
      ∫ p : EuclideanSpace ℝ (Fin 3), S p *
        ‖∫ z : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (w z * ((Work.BoseKinLoc.Qfree ℓ 0
            (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r))) z
              : ℝ) : ℂ))‖ ^ 2) := by
  classical
  have hz := stronglyMeasurable_pIntegrand (ℓ := ℓ) hΦ i hw hS
  have hout : StronglyMeasurable (fun r : Submission.BoseGases.X m =>
      ∫ p : E3, S p * ‖zInt ℓ Φ i w (p, r)‖ ^ 2) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (f := fun a : Submission.BoseGases.X m × E3 =>
        S a.2 * ‖zInt ℓ Φ i w (a.2, a.1)‖ ^ 2)
      (hz.comp_measurable measurable_swap)
  have heq : (fun r : Submission.BoseGases.X m =>
        ∫ p : E3, S p * ‖zInt ℓ Φ i w (p, r)‖ ^ 2)
      = fun r => ∫ p : E3, S p *
        ‖∫ z : E3, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (w z * ((Work.BoseKinLoc.Qfree ℓ 0
            (fun z : E3 => Φ (Submission.BoseGases.kcInsN m i (z, r))) z
              : ℝ) : ℂ))‖ ^ 2 := by
    funext r
    rfl
  rw [← heq]
  exact hout.measurable

end Work.BoseFixR
