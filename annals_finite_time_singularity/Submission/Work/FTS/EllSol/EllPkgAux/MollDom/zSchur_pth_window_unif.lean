import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zMixedDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.schur_sq_window_le_unif
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aesm_thEta_zSchur_pth_sq
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.win_majorant_integrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.pth_slice_sq_le_majorant
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thSlice_window_aesm_pth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The window estimate for the logarithmic Schur transform of the angular derivative,
uniformly in the radius `z`.**

For a trace-class datum `G` (`TraceClass G`, `FourInts G`) and `0 < δ ≤ 1/2` there is a single
constant `C > 0` — independent of `z` — such that for every `z > 0` the weighted square of
`zSchur δ (fun w => ∂_θG(w,·)) z` against `σ_η = sin(2θ)^{-η}` is integrable on `Iθ` and is
bounded by `C` times the *windowed* angular energy

  `∫_t 1_{|log z - t| ≤ δ} ∫_{Iθ} σ_η(s) (∂_θG(e^t,s))²`.

The proof is the pointwise Cauchy–Schwarz bound `schur_sq_window_le_unif` (whose constant
`2δM² + 1` involves only a global bound `M` of the compactly supported kernel `sKerd δ`),
applied for a.e. angle `s`, followed by Fubini for the (integrable) joint integrand
`J(t,s) = 1_{|log z - t| ≤ δ} (∂_θG(e^t,s))² σ_η(s)`; the integrability of `J` uses the
slice majorant `thSliceMajorant G (e^t)` (`win_majorant_integrable`,
`pth_slice_sq_le_majorant`). -/
theorem zSchur_pth_window_unif (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
        (fun s : ℝ => (Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
          * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ ∧
      (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
          * (Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
        ≤ C * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)) := by
  -- ## the uniform Cauchy–Schwarz bound on the window (constant free of `z`)
  obtain ⟨A, hApos, hAbnd⟩ := schur_sq_window_le_unif δ hδ
  refine ⟨A, hApos, fun z hz => ?_⟩
  -- ## the pointwise angular majorant of the datum `G`
  have hbound_s : ∀ (t s : ℝ), s ∈ Work.Spaces.Iθ →
      (Work.Spaces.pth G (Real.exp t) s) ^ 2 * Work.FTS.EllipticEst.thEta s
        ≤ thSliceMajorant G (Real.exp t) * Work.FTS.EllipticEst.thEta s := by
    intro t s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, thEta_zero]
      simp
    · rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2, thEta_pi_half]
        simp
      · exact mul_le_mul_of_nonneg_right
          (pth_slice_sq_le_majorant G hT (Real.exp t) (Real.exp_pos t) s ⟨h0, h2⟩)
          (Work.FTS.EllipticEst.thEta_nonneg hs)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then thSliceMajorant G (Real.exp t) else 0) MeasureTheory.volume :=
    win_majorant_integrable G hT hF δ z hδ hz
  -- ## the joint integrand on `ℝ × Iθ`
  set J : ℝ × ℝ → ℝ := fun p : ℝ × ℝ =>
    (if |Real.log z - p.1| ≤ δ then (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
      * Work.FTS.EllipticEst.thEta p.2 with hJ
  have hae_Iθ : ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    have h : ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))),
        p ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (μ := (MeasureTheory.volume : Measure ℝ))
        (ν := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
        (s := Set.univ ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2))
        (MeasurableSet.univ.prod (measurableSet_Icc (a := (0 : ℝ)) (b := Real.pi / 2)))).mpr ?_
      filter_upwards with t
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact ⟨trivial, hθ⟩
    exact h.mono (fun p hp => hp.2)
  have hKint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (if |Real.log z - p.1| ≤ δ then thSliceMajorant G (Real.exp p.1) else 0)
        * Work.FTS.EllipticEst.thEta p.2)
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hmaj.mul_prod Work.FTS.EllipticEst.integrableOn_thEta.1
  have hJ_eq : (fun p : ℝ × ℝ => (if |Real.log z - p.1| ≤ δ then
        Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0))
      =ᵐ[((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))] J := by
    rw [hJ]
    filter_upwards with p
    by_cases hp : |Real.log z - p.1| ≤ δ
    · rw [if_pos hp, if_pos hp, mul_comm]
    · rw [if_neg hp, if_neg hp, zero_mul]
  have hJ_aesm : MeasureTheory.AEStronglyMeasurable J
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (thSlice_window_aesm_pth G hT δ z).congr hJ_eq
  have hJint : MeasureTheory.Integrable J
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine hKint.mono' hJ_aesm ?_
    filter_upwards [hae_Iθ] with p hp
    show ‖(if |Real.log z - p.1| ≤ δ
        then (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
        * Work.FTS.EllipticEst.thEta p.2‖
      ≤ (if |Real.log z - p.1| ≤ δ then thSliceMajorant G (Real.exp p.1) else 0)
        * Work.FTS.EllipticEst.thEta p.2
    by_cases hw : |Real.log z - p.1| ≤ δ
    · rw [if_pos hw, if_pos hw,
        Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hp))]
      exact hbound_s p.1 p.2 hp
    · rw [if_neg hw, if_neg hw]
      simp
  -- ## Fubini on the product `ℝ × Iθ`
  have hprod1 : (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ t : ℝ, (∫ s : ℝ, J (t, s) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂MeasureTheory.volume :=
    MeasureTheory.integral_prod J hJint
  have hprod2 : (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ s : ℝ, (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_prod_symm J hJint
  have hslice_s : MeasureTheory.Integrable
      (fun s : ℝ => ∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.integral_prod_right hJint
  -- ## the `t`-slice identity: the right-hand side of the statement
  have hsliceJ : ∀ t : ℝ, (∫ s : ℝ, J (t, s) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
            * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0) := by
    intro t
    by_cases hw : |Real.log z - t| ≤ δ
    · rw [if_pos hw]
      have heq : (fun s : ℝ => J (t, s)) = fun s : ℝ => Work.FTS.EllipticEst.thEta s
          * (Work.Spaces.pth G (Real.exp t) s) ^ 2 := by
        funext s
        show (if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)
            * Work.FTS.EllipticEst.thEta s
          = Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2
        rw [if_pos hw, mul_comm]
      rw [heq]
    · rw [if_neg hw]
      have heq : (fun s : ℝ => J (t, s)) = fun _ : ℝ => (0 : ℝ) := by
        funext s
        show (if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)
            * Work.FTS.EllipticEst.thEta s = 0
        rw [if_neg hw, zero_mul]
      rw [heq, MeasureTheory.integral_zero]
  have hRHS : (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
            * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0) := by
    rw [hprod1]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsliceJ)
  -- ## the `s`-slice identity
  have hJsl : ∀ s : ℝ, (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
      = Work.FTS.EllipticEst.thEta s * (∫ t : ℝ,
          if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0) := by
    intro s
    have heq : (fun t : ℝ => J (t, s)) = fun t : ℝ =>
        (if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)
          * Work.FTS.EllipticEst.thEta s := by
      funext t
      rw [hJ]
    rw [heq, MeasureTheory.integral_mul_const]
    ring
  -- ## continuity of the angular-derivative slice along `t ↦ e^t`
  have hcont_slice : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Continuous (fun t : ℝ => Work.Spaces.pth G (Real.exp t) s) := by
    intro s hs
    have hmap : Continuous (fun t : ℝ => (Real.exp t, s)) :=
      Real.continuous_exp.prodMk continuous_const
    exact (hT.1.pth).continuousOn.comp_continuous hmap (fun t => ⟨Real.exp_pos t, hs⟩)
  -- ## the uniform Cauchy–Schwarz bound for each interior angle
  have hcs : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
        ≤ A * (∫ t : ℝ, if |Real.log z - t| ≤ δ
            then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0) := by
    intro s hs
    have h := hAbnd z hz (fun t : ℝ => Work.Spaces.pth G (Real.exp t) s) (hcont_slice s hs)
    simpa only [zSchur] using h
  -- ## the pointwise bound on `Iθ`
  have hfs_le : ∀ s ∈ Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
      * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
        ≤ A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume) := by
    intro s hs
    rw [hJsl s]
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, thEta_zero]
      simp
    · rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2, thEta_pi_half]
        simp
      · calc Work.FTS.EllipticEst.thEta s * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
            ≤ Work.FTS.EllipticEst.thEta s * (A * (∫ t : ℝ, if |Real.log z - t| ≤ δ
                then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)) :=
              mul_le_mul_of_nonneg_left (hcs s ⟨h0, h2⟩) (Work.FTS.EllipticEst.thEta_nonneg hs)
          _ = A * (Work.FTS.EllipticEst.thEta s * (∫ t : ℝ, if |Real.log z - t| ≤ δ
                then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)) := by ring
  -- ## nonnegativity, integrability of the dominating function, monotonicity
  have hfs_nn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] fun s : ℝ =>
      Work.FTS.EllipticEst.thEta s * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hs) (sq_nonneg _)
  have hgs_int : MeasureTheory.Integrable
      (fun s : ℝ => A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hslice_s.const_mul _
  have hmono := MeasureTheory.integral_mono_of_nonneg hfs_nn hgs_int
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hfs_le)
  have hgs_eq : (∫ s : ℝ, A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = A * (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_const_mul, ← hprod2]
  -- ## integrability of the weighted square (first conjunct of the statement)
  have hLHSint : MeasureTheory.Integrable (fun s : ℝ =>
      (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 * Work.FTS.EllipticEst.thEta s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hgs_int.mono' ?_ ?_
    · exact (aesm_thEta_zSchur_pth_sq G hT δ hδ hz).congr
        (Filter.Eventually.of_forall (fun s => by ring))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))]
      calc (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 * Work.FTS.EllipticEst.thEta s
          = Work.FTS.EllipticEst.thEta s
              * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 := by ring
        _ ≤ A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume) := hfs_le s hs
  refine ⟨hLHSint, ?_⟩
  calc (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
        * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      = ∫ s : ℝ, Work.FTS.EllipticEst.thEta s
          * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := rfl
    _ ≤ ∫ s : ℝ, A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := hmono
    _ = A * (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := hgs_eq
    _ = A * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
            * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)) := by rw [hRHS]

end Work.FTS.EllSol.EllPkgAux.MollDom
