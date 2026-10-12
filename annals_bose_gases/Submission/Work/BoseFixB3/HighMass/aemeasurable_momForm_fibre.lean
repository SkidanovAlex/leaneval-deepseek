import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.aemeasurable_momForm_fibre`

The target of this module is the parametric a.e.-measurability of the inserted fibre of a
merely **continuous** `(m+1)`-body state.

The sibling `Work.BoseKinLoc.Sector.measurable_momForm_genFibre` proves the *unconditional*
`Measurable` statement for the whole family
`q ↦ momForm ℓ d q.1 (fun z ↦ Φ (kcInsN n i (z, q.2)))`, but only under the hypothesis
`ContDiff ℝ ⊤ Φ`.  That hypothesis is never used: the proof only needs `Φ` continuous (through
`hΦ.measurable`).  Here we rerun the same argument with `Continuous Φ`, obtaining the general
statement `measurable_momForm_genFibre_cont`, and specialise the translation parameter to
`u = 0` and the ambient measure to the volume measure to get the requested lemma.

The material kept in this file:

* `measurable_momForm_genFibre_cont` — the `(ℓ, d, n, Φ, i)`-general parametric measurability
  with `Continuous Φ` (this is `measurable_momForm_genFibre` with the `ContDiff` hypothesis
  weakened).  The private helpers below reproduce the chain of that proof.
* `aemeasurable_momForm_fibre` — the requested statement: the fibre at `u = 0`,
  `r ↦ momForm ℓ d 0 (fun z ↦ Φ (kcInsN m i (z, r)))`, is a.e. measurable for the volume measure
  on the `m`-body configuration space.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB3.HighMass

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
    (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    Measurable (fun p : E3 × Submission.BoseGases.X n =>
      Φ (Submission.BoseGases.kcInsN n i p)) :=
  hΦ.measurable.comp (Submission.BoseGases.kcInsN n i).measurable

/-- The box mean of the fibre family is strongly measurable in `(u,v)`. -/
private lemma stronglyMeasurable_bsMean_fibre {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
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
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
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
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
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
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
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

/-- **The large-momentum form along an inserted fibre is measurable, for a merely continuous
`(n+1)`-body state.**

For a continuous `(n+1)`-body state `Φ` and an insertion slot `i : Fin (n+1)`, the map

  `q ↦ momForm ℓ d q.1 (fun z => Φ (kcInsN n i (z, q.2)))`

is measurable on `ℝ³ × X n`.  This is `Work.BoseKinLoc.Sector.measurable_momForm_genFibre`
with the smoothness hypothesis on `Φ` weakened to continuity: that proof invokes the
smoothness only through `hΦ.continuous.measurable`. -/
theorem measurable_momForm_genFibre_cont {ℓ d : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    Measurable (fun q : E3 × Submission.BoseGases.X n =>
        Work.BoseKinLoc.momForm ℓ d q.1 (fun z : E3 =>
          Φ (Submission.BoseGases.kcInsN n i (z, q.2)))) := by
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
  exact (hout.const_mul _).measurable

/-- The parametric `momForm` of the inserted fibre of a merely **continuous** `(m+1)`-body state is a.e. measurable: unfold `momForm` and apply `MeasureTheory.StronglyMeasurable.integral_prod_right'` twice (first over `z` for `kinFT`, then over `p`); joint strong measurability comes from joint *continuity* of `((r,p),z) ↦ exp(-I⟪p,z⟫)·Φ (kcInsN m i (z,r))`, so no `ContDiff` hypothesis is needed (unlike `Work.BoseKinLoc.Sector.measurable_momForm_genFibre`). -/
theorem aemeasurable_momForm_fibre {ℓ d : ℝ} {m : ℕ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.momForm ℓ d 0 (fun z : EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN m i (z, r)))) MeasureTheory.volume := by
  have h := measurable_momForm_genFibre_cont (ℓ := ℓ) (d := d) (n := m) hΦ i
  -- the translation parameter is set to `0`, so the family is the composition of the general
  -- one with the measurable inclusion `r ↦ (0, r)`.
  have hcomp : Measurable ((fun q : E3 × Submission.BoseGases.X m =>
      Work.BoseKinLoc.momForm ℓ d q.1 (fun z : E3 =>
        Φ (Submission.BoseGases.kcInsN m i (z, q.2)))) ∘
      (fun r : Submission.BoseGases.X m => ((0 : E3), r))) :=
    h.comp (measurable_const.prodMk measurable_id)
  have heq : ((fun q : E3 × Submission.BoseGases.X m =>
      Work.BoseKinLoc.momForm ℓ d q.1 (fun z : E3 =>
        Φ (Submission.BoseGases.kcInsN m i (z, q.2)))) ∘
      (fun r : Submission.BoseGases.X m => ((0 : E3), r)))
      = (fun r : Submission.BoseGases.X m =>
        Work.BoseKinLoc.momForm ℓ d 0 (fun z : E3 =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))) := by
    funext r; rfl
  rw [← heq]
  exact hcomp.aemeasurable

end Work.BoseFixB3.HighMass
