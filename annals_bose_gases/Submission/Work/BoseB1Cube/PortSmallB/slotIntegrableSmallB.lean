import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseB1Cube.Winchk
import Submission.Work.BoseFixB1B.B1Bfix.cut_slotForm_integrable
import Submission.Work.BoseFixB1B.B1Bfix.sharp_slotForm_integrable
import Submission.Work.BoseFixB1B.B1Bfix.slotAmpDiff_x_integrable
import Submission.Work.BoseFixB1B.B1Bfix.slotAmp_x_integrable
import Submission.Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform
import Submission.Work.BoseFixB1B.cutAmplitude_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.PortSmallB.slotIntegrableSmallB`

The **cube-window (`chiSmallB`)** twin of the four ball-window integrability inputs of the
sharp-fibre convergence chain (`Submission/Work/BoseFixB1B/B1Bfix/{cut_slotForm_integrable,
sharp_slotForm_integrable, slotAmp_x_integrable, slotAmpDiff_x_integrable}.lean`), assembled in a
single statement:

* `∀ δ > 0, ∀ i`, `p ↦ fsKinCoeff c ‖p‖ · slotY … (chiSmallB M L d u) i (cutProd (γ δ) ψ) p`
  is integrable (the smooth approximants),
* `∀ i`, the same for the sharp in-box state `sharpBoxState (dlBox L d u) ψ`,
* the squared slot amplitudes of both states are `x`-integrable over the ambient box `abox (n+1) L`,
* and so is the square of their difference.

Every statement here is `χ`-generic except for the window facts, which for
`χ = chiSmallB M L d u` are supplied by `Submission.Work.BoseB1Cube.Winchk` (regularity
`C³` from `4 ≤ M`, compact support, support inside the sliding box resp. inside `acube L`, sup
bound `kappaS M`) and by `Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform` (the uniform
`(1+‖p‖)⁻³` amplitude decay, the `C³` replacement of the `C^∞` theorem `tBamp_decay`).

The proofs are ports of the four ball-window files with `chiB ↦ chiSmallB`; the generic engine of
`B1Bfix` (`amp_bound`, `tBamp_stronglyMeasurable`, `slotFormL_integrable_of_decay`,
`boxQ_sharp_kcInsN`, `boxQ_kcInsN`, `slotAmpF_sharp_eq`-pattern) is reused verbatim.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

/-! ## The cube-window sharp-state slot identities (port of the `chiB` versions) -/

namespace Work.BoseFixB1B.B1Bfix

open Submission.BoseGases

/-- **The pointwise slot identity for the sharp state.**  Away from the box the two sides are
both killed by the window, and inside the box the indicator `1_B` of the varied coordinate is
`1`, so the indicator of the sharp state collapses onto the outside scalar. -/
private lemma chiSmallB_mul_boxQ_sharp {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {M : ℕ} (hM : 4 ≤ M)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (z : E3) (r : Submission.BoseGases.X n) :
    Submission.BoseGases.chiSmallB M L d u z *
        Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
          (Submission.BoseGases.kcInsN n i (z, r))
      = (if ∀ j : Fin n, r j ∈ Submission.BoseGases.dlBox L d u then (1 : ℝ) else 0) *
        (Submission.BoseGases.chiSmallB M L d u z *
          Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i ψ
            (Submission.BoseGases.kcInsN n i (z, r))) := by
  have hBm : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).isClosed.measurableSet
  have hsh := Work.BoseFixB1B.boxQ_sharp_kcInsN (Work.SmallBoxSliding.boxMass L d u) hBm
    ψ i z r
  have hpsi := boxQ_kcInsN (Work.SmallBoxSliding.boxMass L d u)
    (Submission.BoseGases.dlBox L d u) ψ i z r
  rw [hsh, hpsi]
  by_cases hind : ∀ j : Fin n, r j ∈ Submission.BoseGases.dlBox L d u
  · rw [if_pos hind]
    by_cases hz : z ∈ Submission.BoseGases.dlBox L d u
    · rw [Set.indicator_of_mem hz]; ring
    · have hchi : Submission.BoseGases.chiSmallB M L d u z = 0 := by
        by_contra hne
        exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) (by omega) hL hd hne)
      rw [hchi]; ring
  · rw [if_neg hind]; ring

/-- Complex form of the pointwise slot identity (with the scalar pulled to the front). -/
private lemma chiSmallB_mul_boxQ_sharp_complex {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {M : ℕ} (hM : 4 ≤ M)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (z : E3) (r : Submission.BoseGases.X n) :
    (Submission.BoseGases.chiSmallB M L d u z : ℂ) *
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
          (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)
      = ((if ∀ j : Fin n, r j ∈ Submission.BoseGases.dlBox L d u then (1 : ℝ) else 0 : ℝ) : ℂ) *
        ((Submission.BoseGases.chiSmallB M L d u z : ℂ) *
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i ψ
            (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) := by
  have h := chiSmallB_mul_boxQ_sharp (ψ := ψ) hL hd u hM i z r
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h
  simpa only [Complex.ofReal_mul] using h2

/-! ## 2. The slot amplitude of the sharp state

The windowed `p`-mode amplitude of the sharp state is the outside indicator times the windowed
amplitude of `ψ`: the two integrands coincide pointwise because the window kills the region where
`1_B` differs from `1`. -/

/-- **The slot amplitude of the sharp state.** -/
private lemma chiSmallB_slotAmpF_sharp_eq {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {M : ℕ} (hM : 4 ≤ M)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) (p : E3)
    (x : Submission.BoseGases.X (n + 1)) :
    slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i
        (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x
      = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
            then (1 : ℝ) else 0) : ℝ) : ℂ) *
        slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiSmallB M L d u) i ψ p x := by
  have hpt : ∀ z : E3,
      (Submission.BoseGases.chiSmallB M L d u z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
            (Function.update x i z) : ℂ)
        = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
          ((Submission.BoseGases.chiSmallB M L d u z : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i ψ (Function.update x i z) : ℂ)) := by
    intro z
    rw [update_eq_kcInsN i x z]
    have hc : (Submission.BoseGases.chiSmallB M L d u z : ℂ) *
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
            (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)
        = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
          ((Submission.BoseGases.chiSmallB M L d u z : ℂ) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i ψ
              (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)) := by
      exact chiSmallB_mul_boxQ_sharp_complex (ψ := ψ) hL hd u hM i z
        (fun j : Fin n => x (i.succAbove j))
    calc (Submission.BoseGases.chiSmallB M L d u z : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
              (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)
        = (Submission.BoseGases.chiSmallB M L d u z : ℂ) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
              (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by ring
      _ = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
            ((Submission.BoseGases.chiSmallB M L d u z : ℂ) *
              (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i ψ
                (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by rw [hc]
      _ = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
            ((Submission.BoseGases.chiSmallB M L d u z : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
              (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i ψ
                (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)) := by
          ring
  simp only [slotAmpF, Work.SmallBoxTBWord.tBamp]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_const_mul]

/-! ## 3. Measurability of `p ↦ slotY` for the sharp state -/

/-- **A.e. measurability of `p ↦ slotY …` for the sharp state.**  The amplitude identity of
`slotAmpF_sharp_eq` exhibits the `p`-dependence as that of the *continuous* amplitude of `ψ`
multiplied by an `x`-dependent indicator; joint strong measurability of the integrand and the
Bochner-`integral_prod_right` lemma then give measurability of the `x`-integral. -/
private lemma aemeasurable_slotY_sharp_chiSmallB {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {M : ℕ} (hM : 4 ≤ M)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (i : Fin (n + 1)) :
    AEMeasurable (fun p : E3 => slotY L (Submission.BoseGases.dlBox L d u)
      (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
      (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p) volume := by
  have hBm : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).isClosed.measurableSet
  have hQψ : ContDiff ℝ (⊤ : ENat)
      (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i ψ) := by
    have hA : IsCompact (Submission.BoseGases.dlBox L d u) :=
      Work.SmallBoxTBWord.isCompact_dlBox hL hd u
    have hp := Work.SmallBoxTBWord.boxP_contDiff hA (Work.SmallBoxSliding.boxMass L d u) i hψ
    exact hψ.sub hp
  have hYeq : (fun p : E3 => slotY L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p)
      = fun p : E3 => (L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
            slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiSmallB M L d u) i ψ p x‖ ^ 2 := by
    funext p
    simp only [slotY]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [chiSmallB_slotAmpF_sharp_eq hL hd u hM i p x]
  rw [hYeq]
  have hset : MeasurableSet {q : E3 × Submission.BoseGases.X (n + 1) |
      ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      hBm.preimage ((continuous_apply (i.succAbove j) :
        Continuous fun f : Submission.BoseGases.X (n + 1) => f (i.succAbove j)).comp
        continuous_snd).measurable
  have hmeas : Measurable (fun q : E3 × Submission.BoseGases.X (n + 1) =>
      (((if ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
          then (1 : ℝ) else 0) : ℝ) : ℂ)) := by
    have hind : Measurable (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        (if ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
          then (1 : ℝ) else 0)) := by
      have hEq : (fun q : E3 × Submission.BoseGases.X (n + 1) =>
          (if ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
            then (1 : ℝ) else 0))
          = Set.indicator {q : E3 × Submission.BoseGases.X (n + 1) |
              ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u}
              (fun _ => (1 : ℝ)) := by
        funext q
        rw [Set.indicator_apply]
        simp
      rw [hEq]
      exact measurable_const.indicator hset
    exact Complex.continuous_ofReal.measurable.comp hind
  have hamp : Continuous (fun q : E3 × Submission.BoseGases.X (n + 1) =>
      slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i ψ q.1 q.2) := by
    have hχc : Continuous (Submission.BoseGases.chiSmallB M L d u) :=
      (Work.BoseFixB1S.win.contDiff_three_chiSmallB (ℓ := L) (d := d) hM hL hd u).continuous
    have h := Work.SmallBoxTBWord.continuous_tBamp_pair (N := n + 1) hχc
      (Submission.BoseGases.chiSmallB_hasCompactSupport (M := M) (by omega) hL u) hQψ.continuous i
    simpa only [slotAmpF] using h
  have hF : StronglyMeasurable (fun q : E3 × Submission.BoseGases.X (n + 1) =>
      ‖(((if ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
          then (1 : ℝ) else 0) : ℝ) : ℂ) *
        slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiSmallB M L d u) i ψ q.1 q.2‖ ^ 2) :=
    ((hmeas.mul hamp.measurable).norm.pow_const (2 : ℕ)).stronglyMeasurable
  have hInt : StronglyMeasurable (fun p : E3 =>
      ∫ x : Submission.BoseGases.X (n + 1),
        ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
            then (1 : ℝ) else 0) : ℝ) : ℂ) *
          slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiSmallB M L d u) i ψ p x‖ ^ 2
      ∂(volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    hF.integral_prod_right'
  exact (hInt.aestronglyMeasurable.const_mul ((L ^ 3)⁻¹)).aemeasurable


end Work.BoseFixB1B.B1Bfix

namespace Work.BoseB1Cube.PortSmallB

open Submission.BoseGases

/-- **The squared slot amplitude of any measurable state bounded on the box is integrable** — the
`χ`-generic twin of the private helper of `Submission/Work/BoseFixB1B/B1Bfix/slotAmp_x_integrable.lean`,
obtained from the corpus's `amp_bound` + `tBamp_stronglyMeasurable` and `Integrable.of_bound`. -/
private theorem integrable_sq_slotAmpF_gen {n : ℕ} {a : ℝ} {A : Set E3} {volA : ℝ}
    {χ : E3 → ℝ} (ha : 0 < a) (hAsub : A ⊆ Submission.BoseGases.acube a)
    (hχc : Continuous χ) (hχcs : HasCompactSupport χ)
    (hχsub : tsupport χ ⊆ Submission.BoseGases.acube a)
    {v : Submission.BoseGases.X (n + 1) → ℝ} (hvm : Measurable v) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hvb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |v x| ≤ Cb) (i : Fin (n + 1))
    (p : E3) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖Work.BoseFixB1B.slotAmpF a A volA χ i v p x‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) a)) := by
  obtain ⟨K, -, hK⟩ :=
    Work.BoseFixB1B.B1Bfix.amp_bound ha hAsub hχc hχcs hχsub hvm hCb hvb i p
  have hQm : Measurable (Work.SmallBoxTBWord.boxQ volA A i v) :=
    Work.BoseFixB1B.measurable_boxQ volA i hvm
  have hsm : StronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) =>
      ‖Work.BoseFixB1B.slotAmpF a A volA χ i v p x‖ ^ 2) := by
    have h : StronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) =>
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i v) i x‖ ^ 2) :=
      (Work.BoseFixB1B.B1Bfix.tBamp_stronglyMeasurable hχc
        (Work.SmallBoxTBWord.boxQ volA A i v) hQm i p).norm.pow 2
    simpa only [Work.BoseFixB1B.slotAmpF] using h
  haveI : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) a)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (ne_of_lt (Submission.BoseGases.abox_lt_top (n + 1) a ha.le))
  refine MeasureTheory.Integrable.of_bound hsm.aestronglyMeasurable (K ^ 2) ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) a)]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hK x hx) 2

theorem slotIntegrableSmallB {n : ℕ} {L d c : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    (∀ δ : ℝ, 0 < δ → ∀ i : Fin (n+1),
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.cutProd (γ δ) ψ) p))
    ∧ (∀ i : Fin (n+1),
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p))
    ∧ (∀ (δ : ℝ), 0 < δ → ∀ (i : Fin (n+1)) (p : EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n+1) =>
          ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
              (Work.BoseFixB1B.cutProd (γ δ) ψ) p x‖ ^ 2)
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n+1))).restrict
            (Submission.BoseGases.abox (n+1) L)))
    ∧ (∀ (i : Fin (n+1)) (p : EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n+1) =>
          ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2)
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n+1))).restrict
            (Submission.BoseGases.abox (n+1) L)))
    ∧ (∀ (δ : ℝ), 0 < δ → ∀ (i : Fin (n+1)) (p : EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n+1) =>
          ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
              (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
            - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2)
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n+1))).restrict
            (Submission.BoseGases.abox (n+1) L))) := by
  -- the cube-window side conditions and the box geometry
  have h1M : 1 ≤ M := by omega
  have hAc : Submission.BoseGases.dlBox L d u ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hχc : Continuous (Submission.BoseGases.chiSmallB M L d u) :=
    (Work.BoseFixB1S.win.contDiff_three_chiSmallB (ℓ := L) (d := d) hM hL hd u).continuous
  have hχcs : HasCompactSupport (Submission.BoseGases.chiSmallB M L d u) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport (M := M) h1M hL u
  have hχsub : tsupport (Submission.BoseGases.chiSmallB M L d u)
      ⊆ Submission.BoseGases.acube L :=
    Work.BoseB1Cube.tsupport_chiSmallB_subset_acube (M := M) h1M hL u
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the slot `p`-form of the smooth approximants `Ψ_δ = cutProd (γ δ) ψ`
    intro δ hδ i
    obtain ⟨hγcd, -, -, -, -⟩ := hcut.2 δ hδ
    have hΨcd : ContDiff ℝ (⊤ : ENat) (Work.BoseFixB1B.cutProd (γ δ) ψ) :=
      Work.BoseFixB1B.contDiff_cutProd hγcd hψ
    have hB : IsCompact (Submission.BoseGases.dlBox L d u) :=
      Work.SmallBoxTBWord.isCompact_dlBox hL hd u
    have hΦcd : ContDiff ℝ (⊤ : ENat)
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ)) :=
      Work.SmallBoxTBWord.boxQ_contDiff_of_compact hB _ i hΨcd
    obtain ⟨C, -, hC⟩ := Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform
      (ℓ := L) (d := d) hM hL hd
      (Ψ := Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ)) hΦcd
    have hYm : AEMeasurable (fun p : E3 => Work.BoseFixB1B.slotY L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i
        (Work.BoseFixB1B.cutProd (γ δ) ψ) p) volume := by
      have hcont : Continuous (fun p : E3 => Work.BoseFixB1B.slotY L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.cutProd (γ δ) ψ) p) := by
        rw [show (fun p : E3 => Work.BoseFixB1B.slotY L
              (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiSmallB M L d u) i
              (Work.BoseFixB1B.cutProd (γ δ) ψ) p)
            = fun p : E3 => (L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M L d u) p
                  (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                    (Submission.BoseGases.dlBox L d u) i
                    (Work.BoseFixB1B.cutProd (γ δ) ψ)) i x‖ ^ 2 from rfl]
        exact continuous_const.mul (Work.SmallBoxTBWord.continuous_integral_tBamp_sq hL
          hχc hχcs hΦcd.continuous i)
      exact hcont.aemeasurable
    exact Work.BoseFixB1B.slotFormL_integrable_of_decay (a := L) (c := c) (Cdec := C) hL i hYm
      (fun p x hx => hC u i x hx p)
  · -- (2) the slot `p`-form of the sharp in-box state
    intro i
    have hB : IsCompact (Submission.BoseGases.dlBox L d u) :=
      Work.SmallBoxTBWord.isCompact_dlBox hL hd u
    have hQψ : ContDiff ℝ (⊤ : ENat)
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i ψ) :=
      Work.SmallBoxTBWord.boxQ_contDiff_of_compact hB _ i hψ
    obtain ⟨Cψ, -, hψdec⟩ := Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform
      (ℓ := L) (d := d) hM hL hd
      (Ψ := Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i ψ) hQψ
    refine Work.BoseFixB1B.slotFormL_integrable_of_decay (a := L) hL i
      (Work.BoseFixB1B.B1Bfix.aemeasurable_slotY_sharp_chiSmallB hL hd u hM hψ i)
      (Cdec := Cψ) ?_
    intro p x hx
    rw [Work.BoseFixB1B.B1Bfix.chiSmallB_slotAmpF_sharp_eq hL hd u hM i p x, norm_mul]
    have hind : ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
        then (1 : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1 := by
      by_cases h : ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
      · rw [if_pos h]; norm_num
      · rw [if_neg h]; norm_num
    calc ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
            then (1 : ℝ) else 0) : ℝ) : ℂ)‖ *
          ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
            ψ p x‖
        ≤ 1 * (Cψ / (1 + ‖p‖) ^ 3) := by
          refine mul_le_mul hind ?_ (norm_nonneg _) (by norm_num)
          simpa only [Work.BoseFixB1B.slotAmpF] using hψdec u i x hx p
      _ = Cψ / (1 + ‖p‖) ^ 3 := one_mul _
  · -- (3) the squared slot amplitudes of the smooth approximants are `x`-integrable
    intro δ hδ i p
    obtain ⟨hγcd, -, hγ01, -, -⟩ := hcut.2 δ hδ
    exact integrable_sq_slotAmpF_gen hL hAc hχc hχcs hχsub
      (Work.BoseFixB1B.contDiff_cutProd hγcd hψ).continuous.measurable hCb
      (Work.BoseFixB1B.abs_cutProd_le hγ01 hψb) i p
  · -- (4) the squared slot amplitudes of the sharp state are `x`-integrable
    intro i p
    exact integrable_sq_slotAmpF_gen hL hAc hχc hχcs hχsub
      (Work.BoseFixB1B.sharpBoxState_measurable (Work.SmallBoxSliding.measurableSet_dlBox L d u)
        hψ.continuous.measurable) hCb
      (Work.BoseFixB1B.abs_sharpBoxState_le hCb hψb) i p
  · -- (5) the squared amplitude difference is `x`-integrable
    intro δ hδ i p
    obtain ⟨hγcd, -, hγ01, -, -⟩ := hcut.2 δ hδ
    have hv1m : Measurable (Work.BoseFixB1B.cutProd (γ δ) ψ) :=
      Work.BoseFixB1B.cutFibre_measurable_cutProd hγcd.continuous hψ.continuous
    have hv1b : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
        |Work.BoseFixB1B.cutProd (γ δ) ψ x| ≤ Cb :=
      Work.BoseFixB1B.abs_cutProd_le hγ01 hψb
    have hv0m : Measurable
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) :=
      Work.BoseFixB1B.sharpBoxState_measurable
        (Work.SmallBoxSliding.measurableSet_dlBox L d u) hψ.continuous.measurable
    have hv0b : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
        |Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x| ≤ Cb :=
      Work.BoseFixB1B.abs_sharpBoxState_le hCb hψb
    obtain ⟨K1, -, hK1⟩ :=
      Work.BoseFixB1B.B1Bfix.amp_bound hL hAc hχc hχcs hχsub hv1m hCb hv1b i p
    obtain ⟨K0, -, hK0⟩ :=
      Work.BoseFixB1B.B1Bfix.amp_bound hL hAc hχc hχcs hχsub hv0m hCb hv0b i p
    have hm1 : StronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) =>
        Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.cutProd (γ δ) ψ) p x) := by
      simpa only [Work.BoseFixB1B.slotAmpF] using
        Work.BoseFixB1B.B1Bfix.tBamp_stronglyMeasurable hχc
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ))
          (Work.BoseFixB1B.measurable_boxQ _ i hv1m) i p
    have hm0 : StronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) =>
        Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x) := by
      simpa only [Work.BoseFixB1B.slotAmpF] using
        Work.BoseFixB1B.B1Bfix.tBamp_stronglyMeasurable hχc
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))
          (Work.BoseFixB1B.measurable_boxQ _ i hv0m) i p
    haveI : IsFiniteMeasure
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) L)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.abox_lt_top (n + 1) L hL.le))
    refine MeasureTheory.Integrable.of_bound
      ((hm1.sub hm0).norm.pow 2).aestronglyMeasurable ((K1 + K0) ^ 2) ?_
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) L)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hsub : ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
        - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖
        ≤ K1 + K0 :=
      le_trans (norm_sub_le _ _) (add_le_add (hK1 x hx) (hK0 x hx))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hsub 2


end Work.BoseB1Cube.PortSmallB
