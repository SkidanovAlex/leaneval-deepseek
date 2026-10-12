import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix2.fibreDirI_diff_tendstoB
import Submission.Work.BoseFixB1B.fibreSideConditions_cut
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix2.diffFibre_factsB`

The fibre bookkeeping of the difference state `W_δ = cutProd (γ δ) ψ − 1_{B(u)^{n+1}}ψ` of
`Submission.Work.BoseFixB1B.B1Bfix.DiffVocab` (`DiffFibreFacts`): a.e. measurability of
`Q_{B,i}W_δ`, a uniform bound on the ambient box, smoothness of the windowed slot fibre in the two
parametrisations, and a uniform bound on the fibre Dirichlet energy (`C` may depend on `δ`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.B1Bfix

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Elementary preparations -/

/-- Monotonicity of a set integral from an a.e. hypothesis (junk-safe). -/
private lemma setIntegral_le_of_le_ae'' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f β : α → ℝ} (hs : MeasurableSet s) (hβ : IntegrableOn β s μ)
    (hβ0 : ∀ x ∈ s, 0 ≤ β x) (h : ∀ᵐ x ∂(μ.restrict s), f x ≤ β x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, β x ∂μ := by
  by_cases hf : IntegrableOn f s μ
  · exact integral_mono_ae hf hβ h
  · have hf' : ¬ Integrable f (μ.restrict s) := hf
    rw [integral_undef hf']
    exact integral_nonneg_of_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
      exact hβ0 x hx)

/-- The window kills the box indicator. -/
private lemma chiB_mul_boxInd' {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u z : E3) :
    Submission.BoseGases.chiB L d u z
        * (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1 : ℝ)) z
      = Submission.BoseGases.chiB L d u z := by
  by_cases h : z ∈ Submission.BoseGases.dlBox L d u
  · rw [Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, mul_zero,
      Work.BoseFixB1B.chiB_eq_zero_of_notMem_dlBox hL hd u h]

/-- A global bound on the directional derivatives of the window. -/
private theorem exists_bound_fderiv_chiB' {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)| ≤ C := by
  have hnormk : ∀ k : Fin 3, ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    intro k
    simp [Submission.BoseGases.kcStdBasis]
  have hcont : Continuous (fderiv ℝ (Submission.BoseGases.chiB L d u)) :=
    (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous_fderiv (by simp)
  have hcpt : HasCompactSupport (fderiv ℝ (Submission.BoseGases.chiB L d u)) :=
    (Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u).fderiv ℝ
  obtain ⟨C, hCpos, hCle⟩ := (hcpt.isCompact_range hcont).isBounded.subset_closedBall_lt 0 0
  refine ⟨C, le_of_lt hCpos, fun y k => ?_⟩
  have h1 : ‖fderiv ℝ (Submission.BoseGases.chiB L d u) y (Submission.BoseGases.kcStdBasis k)‖
      ≤ ‖fderiv ℝ (Submission.BoseGases.chiB L d u) y‖ := by
    have hh := ContinuousLinearMap.le_opNorm (fderiv ℝ (Submission.BoseGases.chiB L d u) y)
      (Submission.BoseGases.kcStdBasis k)
    rwa [hnormk k, mul_one] at hh
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have hy := hCle ⟨y, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  exact hy

/-- The slot-`i` fibre of the difference state, in terms of the products of cutoffs. -/
private lemma slotDiffState_kcInsN_eq {n : ℕ} {L d : ℝ} (u : E3) (γ : E3 → ℝ)
    (ψ : Submission.BoseGases.X (n+1) → ℝ) (i : Fin (n+1)) (z : E3)
    (r : Submission.BoseGases.X n) :
    slotDiffState L d u γ ψ (Submission.BoseGases.kcInsN n i (z, r))
      = (Fprod γ (Submission.BoseGases.kcInsN n i (z, r))
          - FprodB (Submission.BoseGases.dlBox L d u) (Submission.BoseGases.kcInsN n i (z, r)))
        * ψ (Submission.BoseGases.kcInsN n i (z, r)) := by
  rw [slotDiffState_apply, cutProd_eq_Fprod, sharpBoxState_eq_FprodB]
  ring

/-- **Smoothness of the windowed slot fibre** of the difference state (in the
`kcInsN n i (·, r)` parametrisation).  The pointwise model replaces the sharp indicator by the
window (`chiB * 1_{dlBox} = chiB`), which removes every singularity. -/
private lemma contDiff_slotFibre {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {γ : E3 → ℝ} (hγ : ContDiff ℝ (⊤ : ENat) γ)
    {ψ : Submission.BoseGases.X (n+1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (i : Fin (n+1)) (r : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ENat) (fun z : E3 => Submission.BoseGases.chiB L d u z
      * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u γ ψ)
          (Submission.BoseGases.kcInsN n i (z, r))) := by
  have hχ : ContDiff ℝ (⊤ : ENat) (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.contDiff_chiB hL hd u
  have hψk : ContDiff ℝ (⊤ : ENat)
      (fun z : E3 => ψ (Submission.BoseGases.kcInsN n i (z, r))) :=
    hψ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)
  have hpt : (fun z : E3 => Submission.BoseGases.chiB L d u z
      * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u γ ψ)
          (Submission.BoseGases.kcInsN n i (z, r)))
      = fun z : E3 =>
          Submission.BoseGases.chiB L d u z * γ z * (∏ j : Fin n, γ (r j))
              * ψ (Submission.BoseGases.kcInsN n i (z, r))
            - Submission.BoseGases.chiB L d u z * FprodBr (Submission.BoseGases.dlBox L d u) r
              * ψ (Submission.BoseGases.kcInsN n i (z, r))
            - Submission.BoseGases.chiB L d u z * (1 / Work.SmallBoxSliding.boxMass L d u)
              * (∫ t in Submission.BoseGases.dlBox L d u,
                  slotDiffState L d u γ ψ (Submission.BoseGases.kcInsN n i (t, r))) := by
    funext z
    rw [Work.BoseFixB1B.boxQ_kcInsN_eq, slotDiffState_kcInsN_eq,
      Fprod_eq_mul_FprodOther, FprodOther_kcInsN_eq, FprodB_kcInsN_eq,
      Submission.BoseGases.kc_insN_apply_same]
    by_cases hz : z ∈ Submission.BoseGases.dlBox L d u
    · rw [Set.indicator_of_mem hz]
      ring
    · rw [Set.indicator_of_notMem hz,
        Work.BoseFixB1B.chiB_eq_zero_of_notMem_dlBox hL hd u hz]
      ring
  rw [hpt]
  have hA : ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
      Submission.BoseGases.chiB L d u z * γ z * (∏ j : Fin n, γ (r j))
        * ψ (Submission.BoseGases.kcInsN n i (z, r))) :=
    ((hχ.mul hγ).mul contDiff_const).mul hψk
  have hB : ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
      Submission.BoseGases.chiB L d u z * FprodBr (Submission.BoseGases.dlBox L d u) r
        * ψ (Submission.BoseGases.kcInsN n i (z, r))) :=
    (hχ.mul contDiff_const).mul hψk
  have hC : ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
      Submission.BoseGases.chiB L d u z * (1 / Work.SmallBoxSliding.boxMass L d u)
        * (∫ t in Submission.BoseGases.dlBox L d u,
            slotDiffState L d u γ ψ (Submission.BoseGases.kcInsN n i (t, r)))) :=
    (hχ.mul contDiff_const).mul contDiff_const
  exact (hA.sub hB).sub hC

/-! ## 2. The fibre facts -/

theorem diffFibre_factsB {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    Work.BoseFixB1B.B1Bfix.DiffFibreFacts L d u ψ K Cb γ := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := chiB_abs_le_boxMargin hL hd u
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_bound_fderiv_chiB' hL hd u
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_fderiv_psi (L := L) hψ
  have hK0 : 0 ≤ K := hcut.1
  have hboxmass0 : 0 ≤ Work.SmallBoxSliding.boxMass L d u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
    positivity
  set Lam : ℝ := max (Submission.BoseGases.chiSup ^ 2 * Cψ)
    (max (C1 * K * Cb) (2 * Cχ * Cb)) with hLam
  have hLam0 : 0 ≤ Lam := by
    rw [hLam]
    exact le_trans (mul_nonneg (pow_nonneg chiSup_pos.le 2) hCψ0) (le_max_left _ _)
  intro δ hδ i
  set R : ℝ := 1 + (n : ℝ)
    + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u with hR
  have hR0 : 0 ≤ R := by
    have h1 : 0 ≤ (∫ w : E3, collarInd L d u δ w) :=
      integral_nonneg (fun w => collarInd_nonneg L d u δ w)
    have h2 : 0 ≤ (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u :=
      div_nonneg h1 hboxmass0
    rw [hR]
    linarith [h2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hC0 : 0 ≤ max (4 * Cb) (3 * (27 * Lam ^ 2) * R ^ 2 * (volume (acube L)).toReal) :=
    le_trans (by linarith : (0 : ℝ) ≤ 4 * Cb)
      (le_max_left (4 * Cb) (3 * (27 * Lam ^ 2) * R ^ 2 * (volume (acube L)).toReal))
  refine ⟨max (4 * Cb) (3 * (27 * Lam ^ 2) * R ^ 2 * (volume (acube L)).toReal),
    hC0, ?_, ?_, ?_, ?_, ?_⟩
  · -- a.e. measurability
    exact (Work.BoseFixB1B.measurable_boxQ (Work.SmallBoxSliding.boxMass L d u) i
      ((Work.BoseFixB1B.cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous
          hψ.continuous).sub
        (Work.BoseFixB1B.cutFibre_measurable_sharpBoxState
          (Work.SmallBoxSliding.measurableSet_dlBox L d u) hψ.continuous.measurable))).aemeasurable
  · -- the bound on the ambient box
    have hb : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
        |slotDiffState L d u (γ δ) ψ x| ≤ 2 * Cb := by
      intro x hx
      have h1 : |Work.BoseFixB1B.cutProd (γ δ) ψ x| ≤ Cb :=
        Work.BoseFixB1B.cutFibre_abs_cutProd_le hL hcut hδ hCb hψb x hx
      have h2 : |Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x| ≤ Cb :=
        Work.BoseFixB1B.cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb x hx
      have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      rw [slotDiffState_apply, abs_sub_le_iff]
      exact ⟨by linarith [h1'.2, h2'.1], by linarith [h2'.2, h1'.1]⟩
    have hres := Work.BoseFixB1B.abs_boxQ_le_two (N := n+1) (ℓ := L)
      (volA := Work.SmallBoxSliding.boxMass L d u) (A := Submission.BoseGases.dlBox L d u)
      (C := 2 * Cb) (i := i) (Φ := slotDiffState L d u (γ δ) ψ)
      hL.le (Work.SmallBoxSliding.dlBox_subset_acube L d u)
      (Work.SmallBoxSliding.boxMass_eq_measureReal L d u) (by linarith : (0:ℝ) ≤ 2 * Cb) hb
    intro x hx
    exact (hres x hx).trans (le_max_of_le_left (by linarith))
  · -- smoothness in the `Function.update` parametrisation
    intro x hx
    have hxr : ∀ z : E3, Function.update x i z
        = Submission.BoseGases.kcInsN n i (z, fun j : Fin n => x (i.succAbove j)) := by
      intro z
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Submission.BoseGases.kc_insN_apply_same]
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        rw [Function.update_of_ne (Fin.succAbove_ne i j'),
          Submission.BoseGases.kc_insN_apply_succ]
    simp only [hxr]
    exact contDiff_slotFibre hL hd u (hcut.2 δ hδ).1 hψ i _
  · -- smoothness in the `kcInsN` parametrisation
    intro r _
    exact contDiff_slotFibre hL hd u (hcut.2 δ hδ).1 hψ i r
  · -- the Dirichlet bound
    intro x hx
    set r : Submission.BoseGases.X n := fun j => x (i.succAbove j) with hr
    have hr_mem : r ∈ Submission.BoseGases.abox n L := by
      rw [Submission.BoseGases.mem_abox_iff]
      intro j
      exact (Submission.BoseGases.mem_abox_iff (n+1) L x).mp hx (i.succAbove j)
    have hxr : ∀ z : E3, Function.update x i z = Submission.BoseGases.kcInsN n i (z, r) := by
      intro z
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Submission.BoseGases.kc_insN_apply_same]
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        rw [Function.update_of_ne (Fin.succAbove_ne i j'),
          Submission.BoseGases.kc_insN_apply_succ]
    simp only [hxr]
    -- the derivative vanishes off the sliding box
    have hsupp : ∀ z : E3, z ∉ Submission.BoseGases.dlBox L d u →
        (∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
      intro z hz
      have hclosed : IsClosed (Submission.BoseGases.dlBox L d u) :=
        (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).isClosed
      obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hz
      have hev : (fun y : E3 => Submission.BoseGases.chiB L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds z hεpos] with y hy
        have hy' : y ∉ Submission.BoseGases.dlBox L d u :=
          fun hmem => hεsub (Metric.mem_ball.mpr hy) hmem
        rw [Work.BoseFixB1B.chiB_eq_zero_of_notMem_dlBox hL hd u hy', zero_mul]
      have hz0 : fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z = 0 :=
        fderiv_eq_zero_of_eventuallyEq_const hev
      rw [hz0]
      simp
    have hEq : (∫ z : E3, ∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∫ z in acube L, ∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB L d u y
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (y, r))) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun z : E3 => ∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB L d u y
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (y, r))) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2)
        (s := acube L)
        (fun z hz => hsupp z (fun hmem => hz (Work.SmallBoxSliding.dlBox_subset_acube L d u hmem)))).symm
    -- the a.e. pointwise bound
    have hpt : ∀ᵐ z ∂(volume.restrict (acube L)),
        (∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ 3 * (27 * Lam ^ 2) * R ^ 2 := by
      have hae : ∀ᵐ y ∂(volume : Measure E3), boxMargin L d u y ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simpa only [not_ne_iff] using Work.BoseFixB1B.cutFibreMass_boxMargin_eq_zero_null L d u
      rw [MeasureTheory.ae_restrict_iff' (acube_measurable L)]
      filter_upwards [hae] with y hym hyac
      have hder := fibre_deriv_sum_sq_le (L := L) (d := d) hL hd u (hcut := hcut) hδ (ψ := ψ) hψ
        hCb hψb hC10 hC1 hCχ hCψ0 hCψ i hyac hr_mem hym
      rw [← hLam] at hder
      refine hder.trans ?_
      have hSle : (∑ j : Fin n, collarInd L d u δ (r j)) ≤ (n : ℝ) := by
        calc ∑ j : Fin n, collarInd L d u δ (r j) ≤ ∑ _j : Fin n, (1 : ℝ) :=
              Finset.sum_le_sum (fun j _ => collarInd_le_one L d u δ (r j))
          _ = (n : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hS0 : 0 ≤ ∑ j : Fin n, collarInd L d u δ (r j) :=
        Finset.sum_nonneg (fun j _ => collarInd_nonneg L d u δ (r j))
      have hV0 : 0 ≤ (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u :=
        div_nonneg (integral_nonneg (fun w => collarInd_nonneg L d u δ w)) hboxmass0
      rw [hR]
      have hG : collarInd L d u δ y + (∑ j : Fin n, collarInd L d u δ (r j))
            + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u
          ≤ 1 + (n : ℝ) + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u := by
        linarith [collarInd_le_one L d u δ y, hSle]
      have hG0 : 0 ≤ collarInd L d u δ y + (∑ j : Fin n, collarInd L d u δ (r j))
            + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u := by
        linarith [collarInd_nonneg L d u δ y, hS0, hV0]
      have hR0' : 0 ≤ 1 + (n : ℝ)
            + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u := by
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hV0]
      have hsq := pow_le_pow_left₀ hG0 hG 2
      have h27 : 0 ≤ 27 * Lam ^ 2 := by positivity
      calc 27 * Lam ^ 2 * (collarInd L d u δ y + (∑ j : Fin n, collarInd L d u δ (r j))
              + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u) ^ 2
          ≤ 27 * Lam ^ 2 * (1 + (n : ℝ)
              + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq h27
        _ ≤ 3 * (27 * Lam ^ 2) * (1 + (n : ℝ)
              + (∫ w : E3, collarInd L d u δ w) / Work.SmallBoxSliding.boxMass L d u) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            linarith [h27]
    -- the integral bound
    have hIconst : IntegrableOn (fun _ : E3 => 3 * (27 * Lam ^ 2) * R ^ 2) (acube L) volume :=
      IntegrableOn.of_bound (acube_lt_top L hL.le)
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : E3 => 3 * (27 * Lam ^ 2) * R ^ 2)
          (volume.restrict (acube L)))
        |3 * (27 * Lam ^ 2) * R ^ 2| (ae_of_all _ (fun _ => by rw [Real.norm_eq_abs]))
    have hle := setIntegral_le_of_le_ae'' (acube_measurable L) hIconst
      (fun _ _ => by positivity) hpt
    have hval : (∫ _ in acube L, 3 * (27 * Lam ^ 2) * R ^ 2)
        = 3 * (27 * Lam ^ 2) * R ^ 2 * (volume (acube L)).toReal := by
      rw [setIntegral_const, Measure.real_def, smul_eq_mul]
      ring
    rw [← hEq, hval] at hle
    exact hle.trans (le_max_right _ _)

end Work.BoseFixB1B.B1Bfix
