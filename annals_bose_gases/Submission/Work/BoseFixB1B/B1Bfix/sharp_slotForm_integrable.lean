import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.B1Bfix.Basic
import Submission.Work.BoseFixB1B.B1Bfix.FibreAlg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.B1Bfix

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

/-! ## 1. Auxiliary facts

The sharp state `Ψ₀ = sharpBoxState B ψ` differs from `ψ` only by the box indicator.  Along a
single slot the indicator splits into the indicator of the varied coordinate and the indicator of
the *held-fixed* coordinates, and the latter is constant along the slot.  Since the window
`chiB L d u` vanishes outside `B = dlBox L d u`, the two slot functions coincide wherever the
window is alive, up to that constant scalar. -/

/-- The `i`-th update is the insertion of the updated coordinate into the `i`-th slot. -/
lemma update_eq_kcInsN {n : ℕ} (i : Fin (n + 1))
    (x : Submission.BoseGases.X (n + 1)) (z : E3) :
    Function.update x i z
      = Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Submission.BoseGases.kc_insN_apply_same]
  · rw [Function.update_of_ne hj]
    rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    exact (Submission.BoseGases.kc_insN_apply_succ n i z
      (fun j : Fin n => x (i.succAbove j)) j').symm

/-- The slot function of the box mean-free projection of `ψ` at an inserted configuration. -/
lemma boxQ_kcInsN {n : ℕ} (volA : ℝ) (B : Set E3)
    (ψ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1)) (z : E3)
    (r : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.boxQ volA B i ψ (Submission.BoseGases.kcInsN n i (z, r))
      = ψ (Submission.BoseGases.kcInsN n i (z, r))
        - (1 / volA) * ∫ t in B, ψ (Submission.BoseGases.kcInsN n i (t, r)) := by
  rw [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP]
  rw [show (∫ t in B, ψ (Function.update (Submission.BoseGases.kcInsN n i (z, r)) i t))
        = ∫ t in B, ψ (Submission.BoseGases.kcInsN n i (t, r)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
        simp only [Work.SmallBoxBridge.Fourier.update_kcInsN])]

/-- **The pointwise slot identity for the sharp state.**  Away from the box the two sides are
both killed by the window, and inside the box the indicator `1_B` of the varied coordinate is
`1`, so the indicator of the sharp state collapses onto the outside scalar. -/
lemma chiB_mul_boxQ_sharp {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (z : E3) (r : Submission.BoseGases.X n) :
    Submission.BoseGases.chiB L d u z *
        Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
          (Submission.BoseGases.kcInsN n i (z, r))
      = (if ∀ j : Fin n, r j ∈ Submission.BoseGases.dlBox L d u then (1 : ℝ) else 0) *
        (Submission.BoseGases.chiB L d u z *
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
    · have hchi : Submission.BoseGases.chiB L d u z = 0 := by
        by_contra hne
        exact hz (Submission.BoseGases.chiB_support_mem hL hd u z hne)
      rw [hchi]; ring
  · rw [if_neg hind]; ring

/-- Complex form of the pointwise slot identity (with the scalar pulled to the front). -/
lemma chiB_mul_boxQ_sharp_complex {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (z : E3) (r : Submission.BoseGases.X n) :
    (Submission.BoseGases.chiB L d u z : ℂ) *
        (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
          (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)
      = ((if ∀ j : Fin n, r j ∈ Submission.BoseGases.dlBox L d u then (1 : ℝ) else 0 : ℝ) : ℂ) *
        ((Submission.BoseGases.chiB L d u z : ℂ) *
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i ψ
            (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) := by
  have h := chiB_mul_boxQ_sharp (ψ := ψ) hL hd u i z r
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h
  simpa only [Complex.ofReal_mul] using h2

/-! ## 2. The slot amplitude of the sharp state

The windowed `p`-mode amplitude of the sharp state is the outside indicator times the windowed
amplitude of `ψ`: the two integrands coincide pointwise because the window kills the region where
`1_B` differs from `1`. -/

/-- **The slot amplitude of the sharp state.** -/
lemma slotAmpF_sharp_eq {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) (p : E3)
    (x : Submission.BoseGases.X (n + 1)) :
    slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i
        (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x
      = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
            then (1 : ℝ) else 0) : ℝ) : ℂ) *
        slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i ψ p x := by
  have hpt : ∀ z : E3,
      (Submission.BoseGases.chiB L d u z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
            (Function.update x i z) : ℂ)
        = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
          ((Submission.BoseGases.chiB L d u z : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i ψ (Function.update x i z) : ℂ)) := by
    intro z
    rw [update_eq_kcInsN i x z]
    have hc : (Submission.BoseGases.chiB L d u z : ℂ) *
          (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
            (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)
        = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
          ((Submission.BoseGases.chiB L d u z : ℂ) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i ψ
              (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)) := by
      exact chiB_mul_boxQ_sharp_complex (ψ := ψ) hL hd u i z
        (fun j : Fin n => x (i.succAbove j))
    calc (Submission.BoseGases.chiB L d u z : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
              (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)
        = (Submission.BoseGases.chiB L d u z : ℂ) *
            (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ)
              (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by ring
      _ = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
            ((Submission.BoseGases.chiB L d u z : ℂ) *
              (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i ψ
                (Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j))) : ℂ)) *
            Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by rw [hc]
      _ = (((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
            ((Submission.BoseGases.chiB L d u z : ℂ) *
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
lemma aemeasurable_slotY_sharp {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : Submission.BoseGases.X (n + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (i : Fin (n + 1)) :
    AEMeasurable (fun p : E3 => slotY L (Submission.BoseGases.dlBox L d u)
      (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
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
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p)
      = fun p : E3 => (L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
              then (1 : ℝ) else 0) : ℝ) : ℂ) *
            slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.chiB L d u) i ψ p x‖ ^ 2 := by
    funext p
    simp only [slotY]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [slotAmpF_sharp_eq hL hd u i p x]
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
        (Submission.BoseGases.chiB L d u) i ψ q.1 q.2) := by
    have hχc : Continuous (Submission.BoseGases.chiB L d u) :=
      (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous
    have h := Work.SmallBoxTBWord.continuous_tBamp_pair (N := n + 1) hχc
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u) hQψ.continuous i
    simpa only [slotAmpF] using h
  have hF : StronglyMeasurable (fun q : E3 × Submission.BoseGases.X (n + 1) =>
      ‖(((if ∀ j : Fin n, q.2 (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
          then (1 : ℝ) else 0) : ℝ) : ℂ) *
        slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i ψ q.1 q.2‖ ^ 2) :=
    ((hmeas.mul hamp.measurable).norm.pow_const (2 : ℕ)).stronglyMeasurable
  have hInt : StronglyMeasurable (fun p : E3 =>
      ∫ x : Submission.BoseGases.X (n + 1),
        ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
            then (1 : ℝ) else 0) : ℝ) : ℂ) *
          slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.chiB L d u) i ψ p x‖ ^ 2
      ∂(volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    hF.integral_prod_right'
  exact (hInt.aestronglyMeasurable.const_mul ((L ^ 3)⁻¹)).aemeasurable

/-! ## 4. The target -/

/-- **Integrability of the slot `p`-form of the sharp box state.**

The sharp state `Ψ₀ = sharpBoxState (dlBox L d u) ψ = 1_{B(u)^k}·ψ` is *not* continuous, but its
slot-`i` windowed amplitude is (up to the outside indicator `1_{r ∈ B^n}`) the amplitude of the
smooth state `ψ`: by `Work.BoseFixB1B.boxQ_sharp_kcInsN`, the slot function of `Ψ₀` at
`kcInsN n i (y,r)` is `1_{r ∈ B^n}·(1_B(y)·ψ(kcInsN n i (y,r)) − c₀(r))`, and since the window
`chiB L d u` vanishes off `B` (`Work.UBBInputs9.A.tsupport_chiB_subset_dlBox`) the amplitude of
`Ψ₀` equals `1_{r ∈ B^n}` times the amplitude of `ψ` (the two windows cancel because `χ·1_B = χ`),
hence obeys the uniform decay `‖…‖ ≤ C/(1+‖p‖)³` of `Work.SmallBoxTBWord.tBamp_decay` applied to
`Φ = ψ` (or to `boxQ` of it); `Work.BoseFixB1B.slotFormL_integrable_of_decay` then gives the claim.
The hypotheses `hψb`, `hCb` are needed for `boxP ψ` (the mean of `ψ` over the box). -/
theorem sharp_slotForm_integrable {n : ℕ} {L d c : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    ∀ i : Fin (n+1),
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
        Work.BoseFixB1B.slotY L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p) := by
  intro i
  have hQψ : ContDiff ℝ (⊤ : ENat)
      (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i ψ) := by
    have hA : IsCompact (Submission.BoseGases.dlBox L d u) :=
      Work.SmallBoxTBWord.isCompact_dlBox hL hd u
    have hp := Work.SmallBoxTBWord.boxP_contDiff hA (Work.SmallBoxSliding.boxMass L d u) i hψ
    exact hψ.sub hp
  obtain ⟨Cψ, hCψ0, hψdec⟩ :=
    Work.SmallBoxTBWord.tBamp_decay (N := n + 1) hL
      (Work.SmallBoxTBWord.contDiff_chiB hL hd u)
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u) hQψ
  refine Work.BoseFixB1B.slotFormL_integrable_of_decay hL i
    (aemeasurable_slotY_sharp hL hd u hψ i) (Cdec := Cψ) ?_
  intro p x hx
  rw [slotAmpF_sharp_eq hL hd u i p x, norm_mul]
  have hind : ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
      then (1 : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1 := by
    by_cases h : ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  calc ‖(((if ∀ j : Fin n, x (i.succAbove j) ∈ Submission.BoseGases.dlBox L d u
          then (1 : ℝ) else 0) : ℝ) : ℂ)‖ *
        ‖slotAmpF L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i ψ p x‖
      ≤ 1 * (Cψ / (1 + ‖p‖) ^ 3) := by
        refine mul_le_mul hind ?_ (norm_nonneg _) (by norm_num)
        exact hψdec x hx i p
    _ = Cψ / (1 + ‖p‖) ^ 3 := one_mul _

end

end Work.BoseFixB1B.B1Bfix
