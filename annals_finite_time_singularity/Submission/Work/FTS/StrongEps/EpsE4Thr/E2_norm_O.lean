import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.E2_norm
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hat_HkSq_le_uniform_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSFinal
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.gam_rad_package_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.E2hat_mem_contDiff_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.C0_sq_le_HkSq0_O
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- `√(X+Y) ≤ √X + √Y` for nonnegative `X`, `Y`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X + Y) ≤ Real.sqrt X + Real.sqrt Y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have h2 : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hexp : (Real.sqrt X + Real.sqrt Y) ^ 2
      = X + 2 * (Real.sqrt X * Real.sqrt Y) + Y := by
    rw [add_sq, h1, h2]; ring
  nlinarith [hexp, mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y)]

/-- The uniform `α`- and `n`-independent bound for the projector zero mode
`L₁₂(Transport f)(0)`, in the open class. -/
private theorem C0_bound_O :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hα hα1 n hn f hO hmem5 hl12
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  have hmemd0 : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f) :=
    Work.FTS.OpenPkg.HkMem_mono_open hO.Dth 0 (by omega) hmemdn
  have h := E2O.C0_sq_le_HkSq0_O (α := α) hO hmemd0
  have hmono : Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le n) hmemdn
  have h16 : (16 : ℝ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ 16 * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  have h' : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := h
  linarith

theorem E2_norm_O :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
          ≤ κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  -- ## the constants
  obtain ⟨Cr, hCrpos, hradS⟩ := E2O.radS_slotSum_le_O C0_bound_O
  obtain ⟨Cg, hCgnn, hgamred⟩ := Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le
  obtain ⟨C0c, hC0pos, hE0⟩ := E2hat_HkSq_le_uniform_O 0
  obtain ⟨C1c, hC1pos, hE1⟩ := E2hat_HkSq_le_uniform_O 1
  obtain ⟨C2c, hC2pos, hE2⟩ := E2hat_HkSq_le_uniform_O 2
  obtain ⟨C3c, hC3pos, hE3⟩ := E2hat_HkSq_le_uniform_O 3
  let Cmax : ℝ := max (max C0c C1c) (max C2c C3c)
  have hCmaxdef : Cmax = max (max C0c C1c) (max C2c C3c) := rfl
  have hCmaxnn : 0 ≤ Cmax := by
    rw [hCmaxdef]
    have h : C0c ≤ max (max C0c C1c) (max C2c C3c) :=
      le_trans (le_max_left C0c C1c) (le_max_left _ _)
    linarith [hC0pos]
  refine ⟨Real.sqrt (2 * Cmax + 2 * (Cg * Cr)), Real.sqrt_nonneg _, ?_⟩
  intro α hα hα1 n hn f hf
  -- ## the data of the class
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hl12 : Work.Construction.L12 f 0 = 0 := hf.2.2.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO n (by omega) hmem5
  have hmemdn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hO
      (Work.FTS.OpenPkg.HkMem_mono_open hO (n + 1) (by omega) hmem5)
  -- ## the `E₂`-defect is the sum of its two blocks
  have hE2eq : Work.FTS.CoercivityFix.Transfer.E2 α f
      = Work.FTS.CoercivityFix.E2hat f
        + (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := rfl
  -- ## the radial slot bound and the `Γ·radS` package
  have hslot := hradS α hα hα1 n hn f hO hmem5 hl12
  have hA : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi 0) :=
    E2O.contDiffOn_four_L12f α hα hα1 hO hmem5
  have hgam := E2O.gam_rad_package_O α hα hα1 hn hA hslot.1
  have hmemGR : Work.Spaces.HkMem α n
      (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := hgam.2
  have hcdGR : ContDiffOn ℝ n (Function.uncurry (fun z θ => Work.Spaces.Gam α θ
      * Work.FTS.CoercivityFix.Transfer.radS α f z)) Work.FTS.CoercivityFix.Transfer.E2pkg.Qd :=
    hgam.1
  have hE2hat := E2O.E2hat_mem_contDiff_O α hα (by omega : n ≤ 4) hO hmemn hmemdn
  have hmemE2hat : Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.E2hat f) := hE2hat.1
  have hcdE2hat : ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
      Work.FTS.CoercivityFix.Transfer.E2pkg.Qd := hE2hat.2
  -- ## the split of the `ℋⁿ`-energy
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          + 2 * Work.Spaces.HkIntegrand α n
              (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) z θ := by
    intro z hz θ hθ
    have h := Work.FTS.CoercivityFix.Transfer.E2pkg.hkIntegrand_add_le_of_contDiffOn α n
      hcdE2hat hcdGR z hz θ hθ
    rwa [hE2eq]
  have hsplit : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
      ≤ 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        + 2 * Work.Spaces.HkSq α n
            (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ)
          ≤ 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
                (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
                z θ) := by
      intro z hz
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ)
        (((hmemE2hat.1 z hz).const_mul 2).add ((hmemGR.1 z hz).const_mul 2))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hpt z hz θ hθ))
      have hEq : (∫ a in Work.Spaces.Iθ,
            ((fun x => 2 * Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z x)
              + fun x => 2 * Work.Spaces.HkIntegrand α n
                  (fun z θ => Work.Spaces.Gam α θ
                    * Work.FTS.CoercivityFix.Transfer.radS α f z) z x) a)
          = 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n
                (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
                z θ) := by
        simp only [Pi.add_apply]
        rw [MeasureTheory.integral_add ((hmemE2hat.1 z hz).const_mul 2)
            ((hmemGR.1 z hz).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      exact le_trans hmono (le_of_eq hEq)
    have hmain := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.Transfer.E2 α f) z θ)
      (((hmemE2hat.2).const_mul 2).add ((hmemGR.2).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
    simp only [Pi.add_apply] at hmain
    rw [MeasureTheory.integral_add ((hmemE2hat.2).const_mul 2) ((hmemGR.2).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmain
    exact hmain
  -- ## the two blocks
  have hE2hatLe : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
      ≤ Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hZnn : 0 ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
      have h1 := Work.Spaces.HkSq_nonneg α n f
      have h2 := Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
      linarith
    have hreg : Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f :=
      regQo_mono (by omega) hf.1
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with hn0 | hn1 | hn2 | hn3
    · subst hn0
      refine le_trans (hE0 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C0c C1c) (le_max_left _ _)) hZnn
    · subst hn1
      refine le_trans (hE1 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C0c C1c) (le_max_left _ _)) hZnn
    · subst hn2
      refine le_trans (hE2 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C2c C3c) (le_max_right _ _)) hZnn
    · subst hn3
      refine le_trans (hE3 α hα f hreg) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C2c C3c) (le_max_right _ _)) hZnn
  have hgamLe : Work.Spaces.HkSq α n
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
      ≤ (Cg * Cr) * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ Cg * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
      rw [Work.Spaces.HkSq]
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n
            (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) z θ)
        (hslot.1.const_mul Cg)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz =>
          hgamred α hα hα1 n hn (Work.FTS.CoercivityFix.Transfer.radS α f) z hz))
      rw [MeasureTheory.integral_const_mul] at hmono
      exact hmono
    have h2 : Cg * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cg * (Cr * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hslot.2 hCgnn
    calc Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ Cg * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := h1
      _ ≤ Cg * (Cr * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := h2
      _ = (Cg * Cr) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  -- ## assembly and the square root
  have htotal : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
      ≤ (2 * Cmax + 2 * (Cg * Cr))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ 2 * (Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hE2hatLe (by norm_num)
    have h2 : 2 * Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ 2 * ((Cg * Cr) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hgamLe (by norm_num)
    calc Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        ≤ 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
          + 2 * Work.Spaces.HkSq α n
              (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := hsplit
      _ ≤ 2 * (Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)))
          + 2 * ((Cg * Cr) * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := by linarith
      _ = (2 * Cmax + 2 * (Cg * Cr))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hKnn : 0 ≤ 2 * Cmax + 2 * (Cg * Cr) := by
    have : 0 ≤ 2 * (Cg * Cr) := by
      have := mul_nonneg hCgnn hCrpos.le
      linarith
    linarith
  rw [Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
      ≤ Real.sqrt ((2 * Cmax + 2 * (Cg * Cr))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_le_sqrt htotal
    _ = Real.sqrt (2 * Cmax + 2 * (Cg * Cr))
        * Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
        Real.sqrt_mul hKnn _
    _ ≤ Real.sqrt (2 * Cmax + 2 * (Cg * Cr))
        * (Real.sqrt (Work.Spaces.HkSq α n f)
            + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        mul_le_mul_of_nonneg_left
          (sqrt_add_le_sqrt_add_sqrt (Work.Spaces.HkSq_nonneg α n f)
            (Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * Cmax + 2 * (Cg * Cr))
        * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]

end Work.FTS.StrongEps.EpsE4Thr
