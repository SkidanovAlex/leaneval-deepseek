import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.integrableOn_exp_comp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_kj_bound
import Submission.Work.FTS.EllSol.K5cAux.thWeightAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.EllipticEst.Core.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability in `t` of the log-mollification slot of the `D_z`-datum

The target lemma `zmollDDomDomIntegrable` says that for a datum `G` which is `C^∞` on the open
quadrant with honestly slice-integrable `D_z`-weighted square (`SliceHonestOpen`) and honest
`z`-functionals (`FourInts`), the `t`-integrand of the log-radial mollification of the `D_z`-slot,

  `t ↦ sKer δ (log z - t) · ∫_{Iθ} KJ ε θ s · |D_zG (e^t) s|`,

is integrable on `ℝ`, for every `z > 0` and `θ ∈ Iθ`.

The proof has three inputs (all of them purely one-dimensional):

* **the angular slice bound** (`slice_kj_bound`): the inner `θ`-integral is bounded by the
  Cauchy–Schwarz expression `3 (ε sMass)⁻¹ √(π/2) √(dIntS G (e^t)) / w(e^t)`;
* **the substitution** (`integrableOn_exp_comp`): since `dIntS G` is `L¹` on `Iz = [0,∞)`, the
  function `t ↦ √(dIntS G (e^t))` is integrable on every compact interval (here: on the window
  `[log z - δ, log z + δ]` on which the kernel `sKer δ (log z - ·)` lives), and multiplying by
  the continuous weight `1/w(e^t)` preserves that;
* **a.e. strong measurability of the slot** (`kj_dz_joint_aesm`): the uncurried slot integrand is
  a.e. measurable on `volume.prod (volume.restrict Iθ)` (it is continuous on the open strip), so
  by `AEStronglyMeasurable.integral_prod_right'` the inner `θ`-integral is a.e. strongly
  measurable in `t`, and so is the product with the continuous kernel.

The kernel `sKer δ (log z - ·)` is bounded by `(δ sMass)⁻¹` and supported on the compact window,
which makes the majorant integrable (indicator trick). -/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## The three elementary inputs -/

/-- **Joint a.e. strong measurability of the angular slot integrand.**  For `G` smooth on the open
quadrant, the uncurried function `(t,s) ↦ KJ ε θ s · |D_zG (e^t) s|` is a.e. strongly measurable
for the product measure `volume.prod (volume.restrict Iθ)`: on the co-null half-strip
`s ∈ (0, π/2)` it is continuous (since `(e^t, s) ∈ Q0` there and `D_zG` is continuous on `Q0`),
which is `aeStronglyMeasurable_exp`. -/
theorem kj_dz_joint_aesm (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε θ : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun t s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s *
        |Work.Spaces.Dz G (Real.exp t) s|))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (Function.uncurry (fun z s : ℝ =>
      Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G z s|))
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp
        (continuous_const.prodMk continuous_snd)).continuousOn
    · exact (hsm.Dz).continuousOn.abs
  have h := aeStronglyMeasurable_exp (X := fun z s : ℝ =>
      Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G z s|) hcont
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 *
      |Work.Spaces.Dz G (Real.exp p.1) p.2|)
      = Function.uncurry (fun t s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s *
        |Work.Spaces.Dz G (Real.exp t) s|) := rfl
  rw [← hfun]
  exact h

/-- The `D_z`-slot functional `dIntS G y` is nonnegative (it is `w(y)²` times an integral of a
nonnegative function). -/
theorem dIntS_nonneg_fts (G : ℝ → ℝ → ℝ) (y : ℝ) : 0 ≤ Work.EllipticEst.Core.dIntS G y := by
  rw [Work.EllipticEst.Core.dIntS]
  refine mul_nonneg (sq_nonneg _) ?_
  refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
  intro s hs
  exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.EllPkgAux.thEta_nonneg_of_mem_Iθ hs)

/-- **Square roots of `L¹` functions on `Iz` are integrable on compact subintervals.**  For a
nonnegative `L¹` function `F` on `Iz = [0,∞)` and `0 < a ≤ b`, the function `y ↦ √(F y)` is
integrable on `[a,b]`; indeed `√(F y) ≤ 1 + F y` and `1 + F` is integrable there. -/
theorem integrableOn_sqrt_of_integrableOn {F : ℝ → ℝ} (hF : MeasureTheory.IntegrableOn F Iz)
    (hFnn : ∀ y : ℝ, 0 ≤ F y) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Real.sqrt (F y)) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Iz := fun y hy => le_trans ha.le hy.1
  have hF' : MeasureTheory.IntegrableOn F (Set.Icc a b) := hF.mono_set hsub
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hdom : MeasureTheory.IntegrableOn (fun y : ℝ => 1 + F y) (Set.Icc a b) := h1.add hF'
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun y : ℝ => Real.sqrt (F y))
      (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (hF'.aemeasurable.sqrt).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun y _ => ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [Pi.add_apply] using Work.FTS.EllSol.EllPkgAux.sqrt_le_one_add_self (hFnn y)

/-- The `t`-integrand of the `D_z`-slot of the log-mollified datum is integrable on `ℝ`. -/
theorem zmollDDomDomIntegrable (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    MeasureTheory.Integrable (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
      * (∫ s in Work.Spaces.Iθ,
          Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G (Real.exp t) s|)) := by
  -- ## abbreviations
  set A : ℝ → ℝ := fun t : ℝ => ∫ s in Iθ,
      Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |Work.Spaces.Dz G (Real.exp t) s| with hA
  set Ck : ℝ := 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ with hCk
  set φ : ℝ → ℝ := fun t : ℝ =>
      Real.sqrt (Work.EllipticEst.Core.dIntS G (Real.exp t)) /
        Work.Spaces.w (Real.exp t) with hφ
  set maj : ℝ → ℝ := fun t : ℝ => |Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)|
      * (Ck * (Real.sqrt (Real.pi / 2) * φ t)) with hmaj
  -- ## nonnegativity of the slot
  have hAnn : ∀ t : ℝ, 0 ≤ A t := by
    intro t
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun s _ => mul_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε θ s) (abs_nonneg _))
  -- ## the angular slice bound
  have hAbound : ∀ t : ℝ, A t ≤ Ck * (Real.sqrt (Real.pi / 2) * φ t) := by
    intro t
    have h := slice_kj_bound G hsm hhon ε θ hε (Real.exp t) (Real.exp_pos t)
    rw [hA, hCk, hφ]
    exact h
  -- ## integrability of the majorant on the window
  have hφ_int : MeasureTheory.IntegrableOn φ
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) := by
    have hsqrt_all : ∀ a b : ℝ, 0 < a → a ≤ b →
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.sqrt (Work.EllipticEst.Core.dIntS G y)) (Set.Icc a b) :=
      fun a b ha hab => integrableOn_sqrt_of_integrableOn (F := fun y : ℝ =>
        Work.EllipticEst.Core.dIntS G y) hF.2.2.2 (dIntS_nonneg_fts G) ha hab
    have hcomp : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt (Work.EllipticEst.Core.dIntS G (Real.exp t)))
        (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
      integrableOn_exp_comp hsqrt_all _ _
    have hwcont : ContinuousOn (fun t : ℝ => (Work.Spaces.w (Real.exp t))⁻¹)
        (Set.Icc (Real.log z - δ) (Real.log z + δ)) := by
      have hw : Continuous (fun t : ℝ => Work.Spaces.w (Real.exp t)) := by
        have h : Continuous (fun t : ℝ => (1 + Real.exp t) ^ 2 / (Real.exp t) ^ 2) :=
          ((continuous_const.add Real.continuous_exp).pow 2).div
            (Real.continuous_exp.pow 2) (fun t => pow_ne_zero 2 (Real.exp_ne_zero t))
        simpa only [Work.Spaces.w] using h
      exact (hw.inv₀ (fun t =>
        ne_of_gt (Work.FTS.EllSol.EllPkgAux.w_pos (Real.exp_pos t)))).continuousOn
    have h1 := hcomp.mul_continuousOn
      (g' := fun t : ℝ => (Work.Spaces.w (Real.exp t))⁻¹) hwcont isCompact_Icc
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Icc
    rw [hφ]
    simp only [div_eq_mul_inv]
  have hmaj_int : MeasureTheory.Integrable maj := by
    have h2 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Ck * Real.sqrt (Real.pi / 2)) * φ t)
        (Set.Icc (Real.log z - δ) (Real.log z + δ)) := hφ_int.const_mul _
    have h3 := h2.mul_continuousOn
      (g' := fun t : ℝ => |Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)|)
      (((Work.FTS.EllSol.K5cAux.continuous_sKer δ).comp
        (continuous_const.sub continuous_id)).abs).continuousOn isCompact_Icc
    have h4 : MeasureTheory.IntegrableOn maj
        (Set.Icc (Real.log z - δ) (Real.log z + δ)) := by
      refine h3.congr_fun (fun t _ => ?_) measurableSet_Icc
      rw [hmaj]
      ring
    have hsupp : ∀ t : ℝ, t ∉ Set.Icc (Real.log z - δ) (Real.log z + δ) → maj t = 0 := by
      intro t ht
      have hgt : δ ≤ |Real.log z - t| := by
        rw [Set.mem_Icc, not_and_or] at ht
        rcases ht with h | h
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_neg (by linarith)]; linarith
      simp only [hmaj]
      rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ hgt]
      simp
    have hEq : maj = (Set.Icc (Real.log z - δ) (Real.log z + δ)).indicator maj := by
      funext t
      by_cases ht : t ∈ Set.Icc (Real.log z - δ) (Real.log z + δ)
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, hsupp t ht]
    rw [hEq, MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact h4
  -- ## a.e. strong measurability
  have hAmeas : MeasureTheory.AEStronglyMeasurable A MeasureTheory.volume := by
    have h := (kj_dz_joint_aesm G hsm ε θ).integral_prod_right'
    rw [hA]
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    rfl
  have hAE : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * A t)
      MeasureTheory.volume :=
    (((Work.FTS.EllSol.K5cAux.continuous_sKer δ).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable).mul hAmeas
  -- ## the pointwise domination
  have hpt : ∀ t : ℝ,
      ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * A t‖ ≤ maj t := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAnn t), hmaj]
    exact mul_le_mul_of_nonneg_left (hAbound t) (abs_nonneg _)
  -- ## conclusion
  show MeasureTheory.Integrable
    (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * A t)
  exact hmaj_int.mono' hAE (Filter.Eventually.of_forall hpt)

end Work.FTS.EllSol.EllPkgAux.MollDom
