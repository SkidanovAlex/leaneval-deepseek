import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.jointMeasurable_chiSmallB_slotWord`

Joint (a.e.-strong) measurability, in the pair `(u, r)`, of the one-particle **cube-windowed**
small-box word `𝒯_{B(u)}` evaluated on the slot-`i` fibre `slotState1 i Φ r` of a smooth
`(n+1)`-particle state, against the product measure `volume.prod (boxMu n ℓ)`.

Here `𝒯_{B(u)}` is `Work.UBBInputs8.tBwordInd` at the sliding box `B(u) = dlBox ℓ d u`, the box
volume `|B(u)| = boxMass ℓ d u` and the **cube** window `chiSmallB M ℓ d u`
(FS `eq:chiBdefinition`).

This is the `chiSmallB`-windowed twin of `Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1`
(the same statement at the ball window `chiB`).  The word is a nest of Bochner integrals (the
moving-box mean over `B(u)`, the `p`-integral of the spectral half, the windowed amplitude and the
ambient box integral), with no decay or integrability available (the state is only smooth and
`fsKinCoeff c` grows); so the route is the *parametric integral* measurability
`MeasureTheory.StronglyMeasurable.integral_prod_right'`, which needs nothing beyond joint strong
measurability of the integrand.  The window is used only through its **joint continuity** in
`(u, x)` (`chiSmallB_pair_continuous` below), so the whole chain of the `chiB`-proof carries over
verbatim.

Contents:
* `sboxW1Sm` — the one-particle word in closed form, at the cube window;
* `cubeWord_fibre_eq` — the `N = 1` collapse of the word on a slot fibre;
* `chiSmallB_pair_continuous` — joint continuity of the cube window;
* the measurability chain (moving-box mean, mean-free projection, gap and kinetic halves);
* `jointMeasurable_chiSmallB_slotWord` — the theorem.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

open Submission.BoseGases
open Work.BSKinetic.SlotSwap

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1.  The one-particle word at the cube window -/

/-- **The one-particle cube-windowed small-box word `𝒯_{B(u)}` on a slot fibre**, in closed form:
the gap term `½ε(1+π⁻²)⁻¹(ℓd)⁻²·‖Q_{B(u)}ψ‖²` plus the spectral half
`(2π)⁻³∫_p [‖p‖−c]₊²·(ℓ³)⁻¹∫_{abox 1 ℓ}‖∫_z χ_{B(u)}(z)e^{−i⟪p,z⟫}Q_{B(u)}ψ(z)‖²` with the
cube window `χ_{B(u)} = chiSmallB M ℓ d u`. -/
def sboxW1Sm (M : ℕ) (ℓ d ε c : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
    Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
        * (∫ x in abox 1 ℓ, (boxQB ℓ d u ψ (x 0)) ^ 2)
  + ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
      ((ℓ ^ 3)⁻¹ * ∫ x in abox 1 ℓ,
        ‖∫ z : ℝ³, (chiSmallB M ℓ d u z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((boxQB ℓ d u ψ z : ℝ) : ℂ)‖ ^ 2)

/-! ## 2.  The `N = 1` collapse of the word -/

/-- The cube-windowed word, restricted to a one-particle fibre, collapses to `sboxW1Sm`.  The
window enters only as the `χ`-argument of `tBamp`, so the pointwise collapse lemmas
`boxQInd_fibre_eq`/`tBamp_fibre_eq` (which hold for an arbitrary window) do all the work. -/
theorem cubeWord_fibre_eq (M : ℕ) (ℓ d ε c : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.UBBInputs8.tBwordInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
        (chiSmallB M ℓ d u) (ℓ * d) ε c (fun x : X 1 => ψ (x 0))
      = sboxW1Sm M ℓ d ε c u ψ := by
  simp only [Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
    Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.cnPlusBoxInd,
    Work.SmallBoxTBWord.tbGapCoeff, Fin.sum_univ_one,
    sboxW1Sm, boxQB, boxMeanB, boxQInd_fibre_eq, tBamp_fibre_eq]

/-! ## 3.  Measurability of the ingredients -/

/-- Joint continuity of the cube window `(u, x) ↦ χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u)`. -/
private lemma chiSmallB_pair_continuous {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} :
    Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
  have h : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
      = fun p : ℝ³ × ℝ³ => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
  rw [h]
  exact ((chiScale_continuous ℓ).comp continuous_snd).mul
    ((chiSmall_continuous hM).comp
      ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst))

/-- Strong measurability of the moving-box fibre mean `(u,r) ↦ |B(u)|⁻¹∫_{B(u)} Φ(kcInsN ·)`. -/
private lemma stronglyMeasurable_boxMeanB {ℓ d : ℝ} (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun q : ℝ³ × X n => boxMeanB ℓ d q.1 (fibψ Φ i q.2)) := by
  classical
  have hnum : StronglyMeasurable (fun q : ℝ³ × X n => ∫ z in dlBox ℓ d q.1, fibψ Φ i q.2 z) := by
    set s : Set ((ℝ³ × X n) × ℝ³) := {w | w.2 ∈ dlBox ℓ d w.1.1} with hs
    have hsm : MeasurableSet s := by
      rw [hs]
      exact (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage
        (by fun_prop : Measurable (fun w : (ℝ³ × X n) × ℝ³ => (w.1.1, w.2)))
    have hg : Measurable (fun w : (ℝ³ × X n) × ℝ³ => Φ (kcInsN n i (w.2, w.1.2))) :=
      hΦ.measurable.comp ((kcInsN_cont i).measurable.comp (by fun_prop))
    have hind : Measurable
        (s.indicator (fun w : (ℝ³ × X n) × ℝ³ => Φ (kcInsN n i (w.2, w.1.2)))) :=
      hg.indicator hsm
    have hint : StronglyMeasurable (fun q : ℝ³ × X n => ∫ z : ℝ³,
        s.indicator (fun w : (ℝ³ × X n) × ℝ³ => Φ (kcInsN n i (w.2, w.1.2))) (q, z)) :=
      hind.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
    have hEq : (fun q : ℝ³ × X n => ∫ z in dlBox ℓ d q.1, fibψ Φ i q.2 z)
        = (fun q : ℝ³ × X n => ∫ z : ℝ³,
            s.indicator (fun w : (ℝ³ × X n) × ℝ³ => Φ (kcInsN n i (w.2, w.1.2))) (q, z)) := by
      funext q
      rw [← MeasureTheory.integral_indicator
        (Work.SmallBoxSliding.measurableSet_dlBox ℓ d q.1)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      have hmem : (q, z) ∈ s ↔ z ∈ dlBox ℓ d q.1 := by simp [hs]
      rw [Set.indicator_apply, Set.indicator_apply, fibψ]
      by_cases h : z ∈ dlBox ℓ d q.1
      · rw [if_pos h, if_pos (hmem.mpr h)]
      · rw [if_neg h, if_neg (fun hc => h (hmem.mp hc))]
    rw [hEq]
    exact hint
  have hmass_inv : StronglyMeasurable
      (fun u : ℝ³ => (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹) := by
    have hb : StronglyMeasurable (Work.SmallBoxSliding.boxMass ℓ d) := by
      have hfun : Work.SmallBoxSliding.boxMass ℓ d
          = fun u : ℝ³ => ∫ z : ℝ³, Work.SmallBoxSliding.boxInd ℓ d u z := rfl
      rw [hfun]
      have hind : Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) := by
        have h2 : Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)
            = {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1}.indicator (fun _ => (1 : ℝ)) := by
          funext p
          obtain ⟨u, z⟩ := p
          simp only [Function.uncurry_apply_pair, Work.SmallBoxSliding.boxInd,
            Set.indicator_apply]
          by_cases h : z ∈ dlBox ℓ d u <;> simp [h]
        rw [h2]
        exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)
      exact hind.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
    exact (measurable_inv.comp hb.measurable).stronglyMeasurable
  have hEq2 : (fun q : ℝ³ × X n => boxMeanB ℓ d q.1 (fibψ Φ i q.2))
      = fun q : ℝ³ × X n => (Work.SmallBoxSliding.boxMass ℓ d q.1)⁻¹
          * ∫ z in dlBox ℓ d q.1, fibψ Φ i q.2 z := by
    funext q; simp only [boxMeanB, one_div]
  rw [hEq2]
  exact (hmass_inv.comp_measurable measurable_fst).mul hnum

/-- Strong measurability of the mean-free box projection `(u,r,z) ↦ Q_{B(u)}ψ_r(z)`. -/
private lemma stronglyMeasurable_boxQB_pair {ℓ d : ℝ} (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun w : (ℝ³ × X n) × ℝ³ =>
      boxQB ℓ d w.1.1 (fibψ Φ i w.1.2) w.2) := by
  classical
  have hsm : MeasurableSet {w : (ℝ³ × X n) × ℝ³ | w.2 ∈ dlBox ℓ d w.1.1} :=
    (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage
      (by fun_prop : Measurable (fun w : (ℝ³ × X n) × ℝ³ => (w.1.1, w.2)))
  have hEqind : (fun w : (ℝ³ × X n) × ℝ³ => (dlBox ℓ d w.1.1).indicator (fun _ => (1 : ℝ)) w.2)
      = ({w : (ℝ³ × X n) × ℝ³ | w.2 ∈ dlBox ℓ d w.1.1}).indicator (fun _ => (1 : ℝ)) := by
    funext w
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : w.2 ∈ dlBox ℓ d w.1.1 <;> simp [h]
  have hind : Measurable
      (fun w : (ℝ³ × X n) × ℝ³ => (dlBox ℓ d w.1.1).indicator (fun _ => (1 : ℝ)) w.2) := by
    rw [hEqind]
    exact measurable_const.indicator hsm
  have hfib : Measurable (fun w : (ℝ³ × X n) × ℝ³ => fibψ Φ i w.1.2 w.2) :=
    hΦ.measurable.comp ((kcInsN_cont i).measurable.comp
      (by fun_prop : Measurable (fun w : (ℝ³ × X n) × ℝ³ => (w.2, w.1.2))))
  have hmean : Measurable (fun w : (ℝ³ × X n) × ℝ³ => boxMeanB ℓ d w.1.1 (fibψ Φ i w.1.2)) :=
    (stronglyMeasurable_boxMeanB n Φ hΦ i).measurable.comp
      (by fun_prop : Measurable (fun w : (ℝ³ × X n) × ℝ³ => (w.1.1, w.1.2)))
  rw [show (fun w : (ℝ³ × X n) × ℝ³ => boxQB ℓ d w.1.1 (fibψ Φ i w.1.2) w.2)
      = fun w : (ℝ³ × X n) × ℝ³ => (dlBox ℓ d w.1.1).indicator (fun _ => (1 : ℝ)) w.2
          * (fibψ Φ i w.1.2 w.2 - boxMeanB ℓ d w.1.1 (fibψ Φ i w.1.2)) from by
        funext w; simp only [boxQB]]
  exact (hind.mul (hfib.sub hmean)).stronglyMeasurable

/-- A.e.-strong measurability of the gap term of the one-particle word. -/
private lemma aestronglyMeasurable_gapTerm {ℓ d : ℝ} (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    AEStronglyMeasurable
      (fun q : ℝ³ × X n => ∫ x in abox 1 ℓ, (boxQB ℓ d q.1 (fibψ Φ i q.2) (x 0)) ^ 2)
      (volume.prod (Work.BSKinetic.boxMu n ℓ)) := by
  classical
  have hQ : StronglyMeasurable
      (fun w : (ℝ³ × X n) × X 1 => (boxQB ℓ d w.1.1 (fibψ Φ i w.1.2) (w.2 0)) ^ 2) :=
    ((stronglyMeasurable_boxQB_pair n Φ hΦ i).comp_measurable
      (by fun_prop : Measurable (fun w : (ℝ³ × X n) × X 1 => (w.1, w.2 0)))).pow 2
  exact (hQ.integral_prod_right'
    (ν := (volume : Measure (X 1)).restrict (abox 1 ℓ))).aestronglyMeasurable

/-- A.e.-strong measurability of the spectral half of the cube-windowed one-particle word: the
nested `z`-, `x`- and `p`-integrals, by three applications of `integral_prod_right'`. -/
private lemma aestronglyMeasurable_kinTerm {M : ℕ} (hM : 1 ≤ M) {ℓ d ε c : ℝ} (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    AEStronglyMeasurable
      (fun q : ℝ³ × X n => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in abox 1 ℓ, ‖∫ z : ℝ³, (chiSmallB M ℓ d q.1 z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
            ((boxQB ℓ d q.1 (fibψ Φ i q.2) z : ℝ) : ℂ)‖ ^ 2))
      (volume.prod (Work.BSKinetic.boxMu n ℓ)) := by
  classical
  have hJ : StronglyMeasurable (fun w : (((ℝ³ × X n) × ℝ³) × X 1) × ℝ³ =>
      (chiSmallB M ℓ d w.1.1.1.1 w.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ w.1.1.2 w.2 : ℂ))) *
        ((boxQB ℓ d w.1.1.1.1 (fibψ Φ i w.1.1.1.2) w.2 : ℝ) : ℂ)) := by
    have h1 : StronglyMeasurable (fun w : (((ℝ³ × X n) × ℝ³) × X 1) × ℝ³ =>
        (chiSmallB M ℓ d w.1.1.1.1 w.2 : ℂ)) :=
      (Complex.continuous_ofReal.comp ((chiSmallB_pair_continuous hM (ℓ := ℓ) (d := d)).comp
        (by fun_prop : Continuous fun w : (((ℝ³ × X n) × ℝ³) × X 1) × ℝ³ =>
          (w.1.1.1.1, w.2)))).stronglyMeasurable
    have h2 : StronglyMeasurable (fun w : (((ℝ³ × X n) × ℝ³) × X 1) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ w.1.1.2 w.2 : ℂ)))) := by
      apply Continuous.stronglyMeasurable
      fun_prop
    have h3 : StronglyMeasurable (fun w : (((ℝ³ × X n) × ℝ³) × X 1) × ℝ³ =>
        ((boxQB ℓ d w.1.1.1.1 (fibψ Φ i w.1.1.1.2) w.2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.measurable.comp
        ((stronglyMeasurable_boxQB_pair n Φ hΦ i).measurable.comp
          (by fun_prop : Measurable fun w : (((ℝ³ × X n) × ℝ³) × X 1) × ℝ³ =>
            ((w.1.1.1.1, w.1.1.1.2), w.2)))).stronglyMeasurable
    exact (h1.mul h2).mul h3
  have hZ := hJ.integral_prod_right' (ν := (volume : Measure ℝ³))
  have hZ2 : StronglyMeasurable (fun W : ((ℝ³ × X n) × ℝ³) × X 1 => ‖∫ z : ℝ³,
      (chiSmallB M ℓ d W.1.1.1 z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ W.1.2 z : ℂ))) *
        ((boxQB ℓ d W.1.1.1 (fibψ Φ i W.1.1.2) z : ℝ) : ℂ)‖ ^ 2) := hZ.norm.pow 2
  have hX : StronglyMeasurable (fun W : (ℝ³ × X n) × ℝ³ => ∫ x in abox 1 ℓ, ‖∫ z : ℝ³,
      (chiSmallB M ℓ d W.1.1 z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ W.2 z : ℂ))) *
        ((boxQB ℓ d W.1.1 (fibψ Φ i W.1.2) z : ℝ) : ℂ)‖ ^ 2) :=
    hZ2.integral_prod_right' (ν := (volume : Measure (X 1)).restrict (abox 1 ℓ))
  have hX2 : StronglyMeasurable (fun W : (ℝ³ × X n) × ℝ³ => (ℓ ^ 3)⁻¹ *
      ∫ x in abox 1 ℓ, ‖∫ z : ℝ³, (chiSmallB M ℓ d W.1.1 z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ W.2 z : ℂ))) *
          ((boxQB ℓ d W.1.1 (fibψ Φ i W.1.2) z : ℝ) : ℂ)‖ ^ 2) :=
    hX.const_mul ((ℓ ^ 3)⁻¹)
  have hcoeff : StronglyMeasurable (fun W : (ℝ³ × X n) × ℝ³ => fsKinCoeff c ‖W.2‖) := by
    have hfs : Continuous fun r : ℝ => fsKinCoeff c r := by
      have hfun : (fun r : ℝ => fsKinCoeff c r) = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
      rw [hfun]
      exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
    exact ((hfs.comp continuous_norm).comp continuous_snd).stronglyMeasurable
  have hX3 : StronglyMeasurable (fun W : (ℝ³ × X n) × ℝ³ => fsKinCoeff c ‖W.2‖ * ((ℓ ^ 3)⁻¹ *
      ∫ x in abox 1 ℓ, ‖∫ z : ℝ³, (chiSmallB M ℓ d W.1.1 z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ W.2 z : ℂ))) *
          ((boxQB ℓ d W.1.1 (fibψ Φ i W.1.2) z : ℝ) : ℂ)‖ ^ 2)) := hcoeff.mul hX2
  have hK : StronglyMeasurable (fun q : ℝ³ × X n => ∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
      ∫ x in abox 1 ℓ, ‖∫ z : ℝ³, (chiSmallB M ℓ d q.1 z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((boxQB ℓ d q.1 (fibψ Φ i q.2) z : ℝ) : ℂ)‖ ^ 2)) :=
    hX3.integral_prod_right' (ν := (volume : Measure ℝ³))
  exact (hK.const_mul ((2 * Real.pi) ^ 3)⁻¹).aestronglyMeasurable

/-! ## 4.  The theorem -/

theorem jointMeasurable_chiSmallB_slotWord {M : ℕ} (hM : 4 ≤ M) {ℓ d ε c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun (u : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n) =>
        Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
          (ℓ * d) ε c (Work.BSKinetic.slotState1 i Φ r)))
      (MeasureTheory.volume.prod (Work.BSKinetic.boxMu n ℓ)) := by
  have hM1 : 1 ≤ M := by omega
  have hΦc : Continuous Φ := hΦ.continuous
  have hEq : Function.uncurry (fun (u : ℝ³) (r : X n) =>
        Work.UBBInputs8.tBwordInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
          (chiSmallB M ℓ d u) (ℓ * d) ε c (Work.BSKinetic.slotState1 i Φ r))
      = fun q : ℝ³ × X n => sboxW1Sm M ℓ d ε c q.1 (fibψ Φ i q.2) := by
    funext q
    obtain ⟨u, r⟩ := q
    simp only [Function.uncurry_apply_pair]
    have hslot : Work.BSKinetic.slotState1 i Φ r = fun x : X 1 => fibψ Φ i r (x 0) := by
      funext x
      simp only [Work.BSKinetic.slotState1, fibψ]
    rw [hslot, cubeWord_fibre_eq M ℓ d ε c u (fibψ Φ i r)]
  rw [hEq]
  have hG := aestronglyMeasurable_gapTerm (ℓ := ℓ) (d := d) n Φ hΦc i
  have hK := aestronglyMeasurable_kinTerm (M := M) hM1 (ℓ := ℓ) (d := d) (ε := ε) (c := c)
    n Φ hΦc i
  have hsum : AEStronglyMeasurable (fun q : ℝ³ × X n =>
      Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
          (∫ x in abox 1 ℓ, (boxQB ℓ d q.1 (fibψ Φ i q.2) (x 0)) ^ 2)
        + ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in abox 1 ℓ, ‖∫ z : ℝ³, (chiSmallB M ℓ d q.1 z : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
                ((boxQB ℓ d q.1 (fibψ Φ i q.2) z : ℝ) : ℂ)‖ ^ 2))
      (volume.prod (Work.BSKinetic.boxMu n ℓ)) :=
    (hG.const_mul _).add hK
  exact hsum

end Work.BoseFixB1B
