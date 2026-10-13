/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TopSlotTwoFts/AHalfInfra`: smoothness, continuity and a.e. strong measurability tools

Infrastructure for the `A`-half of the level-`2` top angular slot
(`Submission/Work/FTS/EllipticEst/TopSlotTwoFts/AHalf.lean`).  Everything here is about the
function

  `A Ψ = fun z θ => z ^ 2 * ∂_z² Ψ z θ`

and the shifted solutions `D_z^j Ψ`:

* `SmoothOpen` of `D_z f`, of `D_z^j f` and of `A Ψ` (needed to apply `SmoothOpen.pth` and get
  continuity of the angular derivatives on the open quadrant);
* continuity of the two integrands `(∂_θ²(D_z^jΨ))² sEta w²` and `(∂_θ²(AΨ))² sEta w²` on the
  open quadrant, hence a.e. strong measurability of their `θ`-slices and of their `z`-parameter
  integrals (`Work.Spaces.aesm_slice_of_continuousOn_Qd`,
  `Work.Spaces.aesm_of_continuousOn_Qd`, `AEStronglyMeasurable.integral_prod_right'`);
* the resulting `IntegrableOn` facts, obtained by dominating with `HkIntegrand α 2 (∂_θ²Ψ)`
  (honest by `EllWeakPos.memB`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The open quadrant. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Qd {z θ : ℝ} : (z, θ) ∈ Qd ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- The `A`-function of the top slot: `A Ψ = z² ∂_z² Ψ`. -/
def Aft (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-! ## Smoothness on the open quadrant -/

theorem smoothOpen_Dz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz f) := hf.pz
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz f) p) Qd :=
    (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder) (s := Qd)).mul h1
  refine h2.congr (fun p _ => ?_)
  rfl

theorem smoothOpen_DzIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j f) := by
  induction j with
  | zero => simpa using hf
  | succ k ih =>
      rw [Work.Spaces.DzIter_succ]
      exact smoothOpen_Dz ih

theorem smoothOpen_Aft {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Aft Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter 2 Ψ) := hΨ.pzIter 2
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 ^ 2 * Function.uncurry (Work.Spaces.pzIter 2 Ψ) p) Qd :=
    ((contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder) (s := Qd)).pow 2).mul h1
  refine h2.congr (fun p _ => ?_)
  rfl

theorem smoothOpen_slices {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z : ℝ} (hz : 0 < z) : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => f z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  exact contDiffOn_iff_forall_nat_le.mp (hf.curry_θ hz) n le_top

/-! ## Continuity of the two integrands on the open quadrant -/

theorem continuousOn_pthIter2_DzIter {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) p.1 p.2)
      Qd :=
  ((smoothOpen_DzIter hΨ j).pth.pth).continuousOn

theorem continuousOn_pthIter2_Aft {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 (Aft Ψ) p.1 p.2) Qd :=
  ((smoothOpen_Aft hΨ).pth.pth).continuousOn

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hnum : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Qd :=
    (continuous_const.continuousOn.add continuous_fst.continuousOn).pow 2
  have hden : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) Qd := continuous_fst.continuousOn.pow 2
  have hne : ∀ p ∈ Qd, p.1 ^ 2 ≠ 0 := fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
  exact hnum.div hden hne

theorem continuousOn_sEta_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
    Qd := by
  obtain ⟨-, -, -, -, hwcont⟩ := Work.FTS.EllipticEst.H2W.SliceEtaFacts
  have hc : ContinuousOn Work.FTS.EllipticEst.sEta (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (hwcont θ hθ).continuousWithinAt
  exact hc.comp continuous_snd.continuousOn (fun p hp => hp.2)

/-- The first integrand: `(∂_θ²(D_z^jΨ))² sEta w²`. -/
theorem continuousOn_F1 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.w p.1) ^ 2) Qd := by
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      ((fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2) p)
        * ((fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) p
            * (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) p)) Qd :=
    ((continuousOn_pthIter2_DzIter hΨ j).pow 2).mul
      (continuousOn_sEta_Qd.mul (continuousOn_w_Qd.pow 2))
  exact h.congr (fun p _ => by ring)

/-- The second integrand: `(∂_θ²(AΨ))² sEta w²`. -/
theorem continuousOn_F2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (Aft Ψ) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.w p.1) ^ 2) Qd := by
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      ((fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 (Aft Ψ) p.1 p.2) ^ 2) p)
        * ((fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) p
            * (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) p)) Qd :=
    ((continuousOn_pthIter2_Aft hΨ).pow 2).mul
      (continuousOn_sEta_Qd.mul (continuousOn_w_Qd.pow 2))
  exact h.congr (fun p _ => by ring)

/-! ## A.e. strong measurability -/

theorem aesm_slice_pthIter2_DzIter {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_F1 hΨ j) hz

theorem aesm_slice_pthIter2_Aft {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_F2 hΨ) hz

theorem aesm_int_pthIter2_DzIter {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_F1 hΨ j)).integral_prod_right'

theorem aesm_int_pthIter2_Aft {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_F2 hΨ)).integral_prod_right'

/-! ## Pointwise domination by the honest level-`2` integrand of `∂_θθΨ` -/

/-- On the open quadrant, `w²(∂_θ²(D_z^jΨ))² sEta = (D_z^j(∂_θ²Ψ)·w/s^{η/2})²`. -/
theorem hk0_pthIter2_DzIter_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2
      = (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [← Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hΨ j hz hθ]
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsq : Real.sin (2 * θ) ^ (Work.Spaces.eta)
      = (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add hs]
    ring_nf
  have hse : Work.FTS.EllipticEst.sEta θ
      = ((Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹) ^ 2 := by
    rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hs.le, hsq, inv_pow]
  rw [hse, div_eq_mul_inv]
  ring

end

end Work.FTS.EllipticEst.TopSlotTwoFts
