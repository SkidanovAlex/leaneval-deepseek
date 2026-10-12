import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.PortSmallB.WinW
import Submission.Work.BoseFixB1B.fibreSideConditions_cut
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.PortSmallB.DiffSmallB` — the fibre bookkeeping at the cube window

The `chiSmallB`-twin of `Work.BoseFixB1B.B1Bfix.DiffFibreFacts`
(`Submission/Work/BoseFixB1B/B1Bfix2/diffFibre_factsB.lean`): a.e. measurability of the box-mean-free
slot projection of the difference state, a uniform bound on the ambient box, `C³`-smoothness of the
cube-windowed slot fibre in the two parametrisations, and a uniform bound on its fibre Dirichlet
energy.  The only changes with respect to the ball-window original are the window
(`chiB L d u ↦ chiSmallB M L d u`, `4 ≤ M`), the sup constant (`chiSup ^ 2 ↦ kappaS M`), and the
regularity (`C^∞ ↦ C³`, forced by `chiSmallB M` being only `C^{M-1}`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.PortSmallB

open Submission.BoseGases
open Work.BoseFixB1B
open Work.BoseFixB1B.B1Bfix

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Smoothness of the windowed slot fibre** of the difference state (in the
`kcInsN n i (·, r)` parametrisation).  The pointwise model replaces the sharp indicator by the
cube window (`chiSmallB * 1_{dlBox} = chiSmallB`), which removes every singularity. -/
lemma contDiff_window_slotFibreW {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {M : ℕ} (hM : 4 ≤ M)
    {γ : E3 → ℝ} (hγ : ContDiff ℝ (⊤ : ENat) γ)
    {ψ : Submission.BoseGases.X (n+1) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (i : Fin (n+1)) (r : Submission.BoseGases.X n) :
    ContDiff ℝ 3 (fun z : E3 => Submission.BoseGases.chiSmallB M L d u z
      * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u γ ψ)
          (Submission.BoseGases.kcInsN n i (z, r))) := by
  have hχ : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M L d u) :=
    Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hL hd u
  have hγ3 : ContDiff ℝ 3 γ := hγ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hψk : ContDiff ℝ 3
      (fun z : E3 => ψ (Submission.BoseGases.kcInsN n i (z, r))) :=
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).comp ((Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r).of_le (WithTop.coe_le_coe.mpr le_top))
  have hpt : (fun z : E3 => Submission.BoseGases.chiSmallB M L d u z
      * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u γ ψ)
          (Submission.BoseGases.kcInsN n i (z, r)))
      = fun z : E3 =>
          Submission.BoseGases.chiSmallB M L d u z * γ z * (∏ j : Fin n, γ (r j))
              * ψ (Submission.BoseGases.kcInsN n i (z, r))
            - Submission.BoseGases.chiSmallB M L d u z * FprodBr (Submission.BoseGases.dlBox L d u) r
              * ψ (Submission.BoseGases.kcInsN n i (z, r))
            - Submission.BoseGases.chiSmallB M L d u z * (1 / Work.SmallBoxSliding.boxMass L d u)
              * (∫ t in Submission.BoseGases.dlBox L d u,
                  slotDiffState L d u γ ψ (Submission.BoseGases.kcInsN n i (t, r))) := by
    funext z
    rw [Work.BoseFixB1B.boxQ_kcInsN_eq, slotDiffState_kcInsN_eqW,
      Fprod_eq_mul_FprodOther, FprodOther_kcInsN_eq, FprodB_kcInsN_eq,
      Submission.BoseGases.kc_insN_apply_same]
    by_cases hz : z ∈ Submission.BoseGases.dlBox L d u
    · rw [Set.indicator_of_mem hz]
      ring
    · rw [Set.indicator_of_notMem hz,
        Work.BoseB1Cube.Winchk.chiSmallB_eq_zero_of_notMem_dlBox (by omega) hL hd hz]
      ring
  rw [hpt]
  have hA : ContDiff ℝ 3 (fun z : E3 =>
      Submission.BoseGases.chiSmallB M L d u z * γ z * (∏ j : Fin n, γ (r j))
        * ψ (Submission.BoseGases.kcInsN n i (z, r))) :=
    ((hχ.mul hγ3).mul contDiff_const).mul hψk
  have hB : ContDiff ℝ 3 (fun z : E3 =>
      Submission.BoseGases.chiSmallB M L d u z * FprodBr (Submission.BoseGases.dlBox L d u) r
        * ψ (Submission.BoseGases.kcInsN n i (z, r))) :=
    (hχ.mul contDiff_const).mul hψk
  have hC : ContDiff ℝ 3 (fun z : E3 =>
      Submission.BoseGases.chiSmallB M L d u z * (1 / Work.SmallBoxSliding.boxMass L d u)
        * (∫ t in Submission.BoseGases.dlBox L d u,
            slotDiffState L d u γ ψ (Submission.BoseGases.kcInsN n i (t, r)))) :=
    (hχ.mul contDiff_const).mul contDiff_const
  exact (hA.sub hB).sub hC

/-! ## 2. The fibre facts at the cube window -/

/-! ## 2. The fibre facts -/

theorem diffFibre_factsSmallB {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    Work.BoseB1Cube.PortSmallB.DiffFibreFactsS L d M u ψ K Cb γ := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := Work.BoseB1Cube.Winchk.chiSmallB_abs_le_boxMargin M (by omega) hL hd u
  obtain ⟨Cχ, hCχ0, hCχ⟩ := Work.BoseB1Cube.PortSmallB.exists_bound_fderiv_chiSmallB_coord hM hL hd u
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_fderiv_psi (L := L) hψ
  have hK0 : 0 ≤ K := hcut.1
  have hboxmass0 : 0 ≤ Work.SmallBoxSliding.boxMass L d u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
    positivity
  set Lam : ℝ := max (Work.BoseB1Cube.Winchk.kappaS M * Cψ)
    (max (C1 * K * Cb) (2 * Cχ * Cb)) with hLam
  have hLam0 : 0 ≤ Lam := by
    rw [hLam]
    exact le_trans (mul_nonneg (Work.BoseB1Cube.Winchk.kappaS_nonneg M) hCψ0) (le_max_left _ _)
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
    exact contDiff_window_slotFibreW hL hd u hM (hcut.2 δ hδ).1 hψ i _
  · -- smoothness in the `kcInsN` parametrisation
    intro r _
    exact contDiff_window_slotFibreW hL hd u hM (hcut.2 δ hδ).1 hψ i r
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
        (∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
      intro z hz
      have hclosed : IsClosed (Submission.BoseGases.dlBox L d u) :=
        (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).isClosed
      obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hz
      have hev : (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds z hεpos] with y hy
        have hy' : y ∉ Submission.BoseGases.dlBox L d u :=
          fun hmem => hεsub (Metric.mem_ball.mpr hy) hmem
        rw [Work.BoseB1Cube.Winchk.chiSmallB_eq_zero_of_notMem_dlBox (by omega) hL hd hy', zero_mul]
      have hz0 : fderiv ℝ (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z = 0 :=
        fderiv_eq_zero_of_eventuallyEq_const hev
      rw [hz0]
      simp
    have hEq : (∫ z : E3, ∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∫ z in acube L, ∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (y, r))) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun z : E3 => ∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
            * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
                (Submission.BoseGases.kcInsN n i (y, r))) z
              (Submission.BoseGases.kcStdBasis k)) ^ 2)
        (s := acube L)
        (fun z hz => hsupp z (fun hmem => hz (Work.SmallBoxSliding.dlBox_subset_acube L d u hmem)))).symm
    -- the a.e. pointwise bound
    have hpt : ∀ᵐ z ∂(volume.restrict (acube L)),
        (∑ k : Fin 3, (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiSmallB M L d u y
          * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i (slotDiffState L d u (γ δ) ψ)
              (Submission.BoseGases.kcInsN n i (y, r))) z
            (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ 3 * (27 * Lam ^ 2) * R ^ 2 := by
      have hae : ∀ᵐ y ∂(volume : Measure E3), boxMargin L d u y ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simpa only [not_ne_iff] using Work.BoseFixB1B.cutFibreMass_boxMargin_eq_zero_null L d u
      rw [MeasureTheory.ae_restrict_iff' (acube_measurable L)]
      filter_upwards [hae] with y hym hyac
      have hder := fibre_deriv_sum_sq_leW (L := L) (d := d) hL hd u hM (hcut := hcut) hδ (ψ := ψ) hψ
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
    have hle := setIntegral_le_of_le_aeW (acube_measurable L) hIconst
      (fun _ _ => by positivity) hpt
    have hval : (∫ _ in acube L, 3 * (27 * Lam ^ 2) * R ^ 2)
        = 3 * (27 * Lam ^ 2) * R ^ 2 * (volume (acube L)).toReal := by
      rw [setIntegral_const, Measure.real_def, smul_eq_mul]
      ring
    rw [← hEq, hval] at hle
    exact hle.trans (le_max_right _ _)


end Work.BoseB1Cube.PortSmallB
