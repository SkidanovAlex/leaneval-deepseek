import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable`

**The large-momentum form `momForm` is a.e. strongly measurable in the box position `u` and in the
`n`-body configuration, along an inserted fibre.**

The object of the statement is (`Work.BoseKinLoc.momForm`, FS `eq:DefT`'s third piece in the
corpus's `p`-convention)

    `momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}(p)·‖𝓕(1_{Λ(u)}·Q_uψ)(p)‖²`,

evaluated on the *fibre* of a smooth `(n+1)`-body state:
`ψ_q(z) = Φ(kcInsN n i (z, q.2))` where `q.1 = u ∈ ℝ³` is the translation parameter of the moving
box `Λ(u) = ℓu + acube ℓ` and `q.2` is the configuration of the remaining `n` particles.

## Proof

The only `u`-dependence sits in the box indicator `1_{Λ(u)}` and in the box mean
`m_u(ψ) = |Λ(u)|⁻¹∫_{Λ(u)}ψ` entering `Q_uψ = ψ − m_u(ψ)`; the `n`-dependence sits in the fibre
family `(v,z) ↦ Φ(kcInsN n i (z,v))`.  Both are handled by joint measurability of the nested
integrands, with the (unconditional, Fubini-type) lemma
`MeasureTheory.StronglyMeasurable.integral_prod_right'`:

* `(v,z) ↦ Φ(kcInsN n i (z,v))` is jointly measurable (`Φ` is smooth, `kcInsN n i` is a measurable
  equivalence);
* the box mean `(u,v) ↦ m_u(ψ_v)` is strongly measurable: after the change of variables to the unit
  cube it is a shift `(u,v,z) ↦ ψ_v(ℓu+z)` integrated in `z` over the *fixed* set `acube ℓ`;
* `p ↦ 1_{(d²ℓ)⁻¹<‖p‖}(p)` is measurable, and the `p`-Fourier transform is an integral over `y` of
  a jointly measurable function of `((u,v,p),y)`;
* integrating the resulting `((u,v),p)`-measurable weight against `p` once more gives strong
  measurability in `(u,v)`.

No integrability (in particular no decay of the Fourier transform) is needed: the Bochner integral
is defined for every function and the Fubini measurability lemma used is unconditional.

The auxiliary definitions below (`fibreFam`, `qFibre`, `winFib`, `fkern`, `momInt`) keep the terms
small so that the definitional equalities used in the assembly are inexpensive.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fibre family `v ↦ (z ↦ Φ(kcInsN n i (z, v)))` of an `(n+1)`-body state. -/
private def fibreFam (n : ℕ) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1))
    (v : Submission.BoseGases.X n) : E3 → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (z, v))

/-- The mean-free part `Q_u` of the fibre family, as a function of `(u,v)`. -/
private def qFibre (ℓ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1))
    (q : E3 × Submission.BoseGases.X n) (z : E3) : ℝ :=
  Work.BoseKinLoc.Qfree ℓ q.1 (fibreFam n Φ i q.2) z

/-- The Fourier kernel of the `p`-convention transform. -/
private def fkern (p y : E3) : ℂ := Complex.exp (-(Complex.I * ↑(inner ℝ p y)))

/-- The windowed mean-free fibre `1_{Λ(u)}·Q_uψ`, as a complex-valued family. -/
private def winFib (ℓ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1))
    (q : E3 × Submission.BoseGases.X n) (z : E3) : ℂ :=
  ((Work.BoseKinLoc.indU ℓ q.1 z : ℝ) : ℂ) * ((qFibre ℓ n Φ i q z : ℝ) : ℂ)

/-- The `p`-integrand of `momForm` for the fibre family. -/
private def momInt (ℓ d : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1))
    (q : E3 × Submission.BoseGases.X n) (p : E3) : ℝ :=
  Work.BoseKinLoc.momProj ℓ d p *
    ‖Submission.BoseGases.kinFT (fun z : E3 => winFib ℓ n Φ i q z) p‖ ^ 2

/-- The Fourier kernel is jointly measurable. -/
private lemma measurable_fkern : Measurable (fun p : E3 × E3 => fkern p.1 p.2) := by
  have hinner : Continuous (fun p : E3 × E3 => inner ℝ p.1 p.2) := continuous_inner
  exact Complex.continuous_exp.measurable.comp
    (continuous_neg.comp (continuous_const.mul (Complex.continuous_ofReal.comp hinner))).measurable

/-- The Fourier transform written with the named kernel. -/
private lemma kinFT_eq (f : E3 → ℂ) (p : E3) :
    Submission.BoseGases.kinFT f p = ∫ y : E3, fkern p y * f y := rfl

/-- The Fourier transform of a strongly measurable family is strongly measurable. -/
private lemma stronglyMeasurable_kinFT_of {α : Type*} [MeasurableSpace α]
    {G : α → E3 → ℂ} (hG : StronglyMeasurable (fun a : α × E3 => G a.1 a.2)) :
    StronglyMeasurable (fun w : α × E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => G w.1 z) w.2) := by
  have hfun : (fun w : α × E3 => Submission.BoseGases.kinFT (fun z : E3 => G w.1 z) w.2)
      = fun w : α × E3 => ∫ y : E3, fkern w.2 y * G w.1 y := by
    funext w
    exact kinFT_eq _ _
  rw [hfun]
  refine MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
    (f := fun w : (α × E3) × E3 => fkern w.1.2 w.2 * G w.1.1 w.2) ?_
  exact (measurable_fkern.comp
      (Measurable.prodMk measurable_fst.snd measurable_snd)).stronglyMeasurable.mul
    (hG.comp_measurable (Measurable.prodMk measurable_fst.fst measurable_snd))

/-- The box indicator along the fibre, `((u,v),x) ↦ 1_{Λ(u)}(x)`, is measurable. -/
private lemma measurable_indU_fibre {n : ℕ} (ℓ : ℝ) :
    Measurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
      Work.BoseKinLoc.indU ℓ a.1.1 a.2) := by
  classical
  have hset : MeasurableSet {a : (E3 × Submission.BoseGases.X n) × E3 |
      a.2 - ℓ • a.1.1 ∈ Submission.BoseGases.acube ℓ} :=
    (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)
  have heq : (fun a : (E3 × Submission.BoseGases.X n) × E3 => Work.BoseKinLoc.indU ℓ a.1.1 a.2)
      = fun a => if a.2 - ℓ • a.1.1 ∈ Submission.BoseGases.acube ℓ then (1 : ℝ) else 0 := by
    funext a; rfl
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

/-- `p ↦ Φ(kcInsN n i p)` is measurable. -/
private lemma measurable_Phi_insN {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Measurable (fun p : E3 × Submission.BoseGases.X n =>
      Φ (Submission.BoseGases.kcInsN n i p)) :=
  hΦ.continuous.measurable.comp (Submission.BoseGases.kcInsN n i).measurable

/-- The box mean of the fibre family is strongly measurable in `(u,v)`. -/
private lemma stronglyMeasurable_bsMean_fibre {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun q : E3 × Submission.BoseGases.X n =>
      Work.BSKinetic.bsMean ℓ q.1 (fibreFam n Φ i q.2)) := by
  classical
  have hjoint : Measurable (fun w : (E3 × Submission.BoseGases.X n) × E3 =>
      Φ (Submission.BoseGases.kcInsN n i (ℓ • w.1.1 + w.2, w.1.2))) :=
    (measurable_Phi_insN hΦ i).comp (by fun_prop)
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ))
    (f := fun w : (E3 × Submission.BoseGases.X n) × E3 =>
      Φ (Submission.BoseGases.kcInsN n i (ℓ • w.1.1 + w.2, w.1.2))) hjoint.stronglyMeasurable
  have heq : (fun q : E3 × Submission.BoseGases.X n =>
      Work.BSKinetic.bsMean ℓ q.1 (fibreFam n Φ i q.2))
      = fun q => (ℓ ^ 3)⁻¹ * ∫ z : E3, Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))
          ∂(MeasureTheory.volume : MeasureTheory.Measure E3).restrict (Submission.BoseGases.acube ℓ) := by
    funext q; rfl
  rw [heq]
  exact h.const_mul _

/-- The mean-free projection of the fibre family is strongly measurable in `((u,v),z)`. -/
private lemma stronglyMeasurable_qFibre {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun w : (E3 × Submission.BoseGases.X n) × E3 => qFibre ℓ n Φ i w.1 w.2) := by
  have heq : (fun w : (E3 × Submission.BoseGases.X n) × E3 => qFibre ℓ n Φ i w.1 w.2)
      = fun w => Φ (Submission.BoseGases.kcInsN n i (w.2, w.1.2))
          - Work.BSKinetic.bsMean ℓ w.1.1 (fibreFam n Φ i w.1.2) := by
    funext w; rfl
  rw [heq]
  exact ((measurable_Phi_insN hΦ i).comp
      (Measurable.prodMk measurable_snd measurable_fst.snd)).stronglyMeasurable.sub
    ((stronglyMeasurable_bsMean_fibre hΦ i).comp_measurable measurable_fst)

/-- The windowed mean-free fibre is strongly measurable in `((u,v),z)`. -/
private lemma stronglyMeasurable_winFib {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 => winFib ℓ n Φ i a.1 a.2) := by
  have hfun : (fun a : (E3 × Submission.BoseGases.X n) × E3 => winFib ℓ n Φ i a.1 a.2)
      = fun a : (E3 × Submission.BoseGases.X n) × E3 =>
          ((Work.BoseKinLoc.indU ℓ a.1.1 a.2 : ℝ) : ℂ) * ((qFibre ℓ n Φ i a.1 a.2 : ℝ) : ℂ) := by
    funext a; rfl
  rw [hfun]
  have hind : Measurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
      Work.BoseKinLoc.indU ℓ a.1.1 a.2) := measurable_indU_fibre ℓ
  have hq : StronglyMeasurable (fun a : (E3 × Submission.BoseGases.X n) × E3 =>
      qFibre ℓ n Φ i a.1 a.2) := stronglyMeasurable_qFibre hΦ i
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable hind.stronglyMeasurable).mul
    (Complex.continuous_ofReal.comp_stronglyMeasurable hq)

/-- The `p`-integrand of `momForm` is strongly measurable in `((u,v),p)`. -/
private lemma stronglyMeasurable_momInt {ℓ d : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun w : (E3 × Submission.BoseGases.X n) × E3 => momInt ℓ d n Φ i w.1 w.2) := by
  have hft : StronglyMeasurable (fun w : (E3 × Submission.BoseGases.X n) × E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => winFib ℓ n Φ i w.1 z) w.2) :=
    stronglyMeasurable_kinFT_of (stronglyMeasurable_winFib hΦ i)
  have hp : Measurable (fun w : (E3 × Submission.BoseGases.X n) × E3 =>
      Work.BoseKinLoc.momProj ℓ d w.2) := by
    have heq : (fun w : (E3 × Submission.BoseGases.X n) × E3 => Work.BoseKinLoc.momProj ℓ d w.2)
        = fun w => if (d ^ 2 * ℓ)⁻¹ < ‖w.2‖ then (1 : ℝ) else 0 := by funext w; rfl
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp measurable_snd))
      measurable_const measurable_const
  have heq : (fun w : (E3 × Submission.BoseGases.X n) × E3 => momInt ℓ d n Φ i w.1 w.2)
      = fun w => Work.BoseKinLoc.momProj ℓ d w.2 *
          ‖Submission.BoseGases.kinFT (fun z : E3 => winFib ℓ n Φ i w.1 z) w.2‖ ^ 2 := by
    funext w; rfl
  rw [heq]
  exact hp.stronglyMeasurable.mul (hft.norm.pow 2)

theorem momForm_fibre_aemeasurable {ℓ d : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.momForm ℓ d q.1 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  have hout : StronglyMeasurable (fun q : E3 × Submission.BoseGases.X n =>
      ∫ p : E3, momInt ℓ d n Φ i q p) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (f := fun w : (E3 × Submission.BoseGases.X n) × E3 => momInt ℓ d n Φ i w.1 w.2)
      (stronglyMeasurable_momInt hΦ i)
  have heq : (fun q : E3 × Submission.BoseGases.X n =>
      Work.BoseKinLoc.momForm ℓ d q.1 (fun z : E3 => Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      = fun q => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, momInt ℓ d n Φ i q p := by
    funext q; rfl
  rw [heq]
  exact (hout.const_mul _).aestronglyMeasurable

end Work.BoseKinLoc.Kinetic
