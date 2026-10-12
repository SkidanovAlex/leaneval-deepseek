import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.hp_complex_iteratedFDeriv_norm
import Submission.Work.BoseFixB3.CS.Pieces.hp_kinFT_iteratedDir_basis
import Submission.Work.BoseFixB3.CS.Pieces.hp_norm_pow_coord
import Submission.Work.BoseFixB3.CS.Pieces.hp_shell_integral_le
import Submission.Work.BoseFixB3.HighMassAux.plancherel_L1L2
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-- `L²` high-pass bound at the momentum cut-off `κ`: the `kinFT`-transform of a `C^∞`
compactly supported `u` has `L²` mass over the shell `‖p‖ ≥ κ` bounded by `κ^{-80}` times the
`L²` norm of the order-`40` derivative.

Intended proof: `‖p‖^{80} ≤ 3^{39}·Σ_k |p_k|^{80}` pointwise, so
`∫_{‖p‖≥κ}‖kinFT(u_ℂ) p‖² ≤ κ^{-80}∫_p ‖p‖^{80}‖kinFT(u_ℂ) p‖²
  ≤ 3^{39}κ^{-80}Σ_k ∫_p |p_k|^{80}‖kinFT(u_ℂ) p‖²`, and each summand equals
`(2π)³∫_x ‖(iteratedFDeriv ℝ 40 (u_ℂ) x)(fun _ => kcStdBasis k)‖²` by
`Work.BoseFixB3.CS.Pieces.hp_kinFT_iteratedDir_basis` (the `p`-convention
Fourier-derivative identity) combined with `HighMassAux.plancherel_L1L2`; finally
`(iteratedFDeriv ℝ 40 (u_ℂ) x)(fun _ => kcStdBasis k)` has norm `≤ ‖iteratedFDeriv ℝ 40 u x‖`
(the complexification does not change the operator norms). -/
theorem highpass_shell_l2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E3 → ℝ) (κ : ℝ), 0 < κ →
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      ∫ p in {p : E3 | κ ≤ ‖p‖},
          ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ C * (κ ^ 80)⁻¹ * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2 := by
  refine ⟨3 ^ 40 * (2 * π) ^ 3, by positivity, ?_⟩
  intro u κ hκ hu hcs
  have hpi3pos : (0 : ℝ) < (2 * π) ^ 3 := by positivity
  -- ### 0. The complexified profile `W` and its `C^∞`/compact-support structure
  have hWcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => (u y : ℂ)) := by
    have h := (Complex.ofRealCLM.contDiff).comp hu
    simpa [Function.comp_def] using h
  have hWcs : HasCompactSupport (fun y : E3 => (u y : ℂ)) := by
    have h := hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    simpa [Function.comp_def] using h
  have hW_int : Integrable (fun x : E3 => (u x : ℂ)) :=
    (hu.continuous.integrable_of_hasCompactSupport hcs).ofReal
  have hkin_cont : Continuous
      (fun p : E3 => Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hW_int
  have hG_ae : AEMeasurable
      (fun p : E3 => ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) volume :=
    (hkin_cont.norm.pow 2).aemeasurable
  -- ### 1. The real order-40 derivative: continuity, compact support, integrability
  have hTu_cont : Continuous (iteratedFDeriv ℝ 40 u) :=
    hu.continuous_iteratedFDeriv (m := 40) (WithTop.coe_le_coe.mpr le_top)
  have hTu_cs : HasCompactSupport (iteratedFDeriv ℝ 40 u) := hcs.iteratedFDeriv 40
  have hTu_norm_int : Integrable (fun x : E3 => ‖iteratedFDeriv ℝ 40 u x‖) :=
    hTu_cont.norm.integrable_of_hasCompactSupport (hTu_cs.mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp)))
  have hTu_sq_int : Integrable (fun x : E3 => ‖iteratedFDeriv ℝ 40 u x‖ ^ 2) :=
    (hTu_cont.norm.pow 2).integrable_of_hasCompactSupport (hTu_cs.mono (fun x hx => by
      simp only [Function.mem_support, Pi.pow_apply] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp)))
  have hWder_cont : Continuous (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ))) :=
    hWcd.continuous_iteratedFDeriv (m := 40) (WithTop.coe_le_coe.mpr le_top)
  -- ### 2. Per-coordinate facts
  have hDk_cont : ∀ k : Fin 3, Continuous (fun x : E3 =>
      (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)) := by
    intro k
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 40 => E3) ℂ
      (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)).continuous.comp hWder_cont
    simpa only [Function.comp_def, ContinuousMultilinearMap.apply_apply] using h
  have hDk_int : ∀ k : Fin 3, Integrable (fun x : E3 =>
      (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)) := by
    intro k
    refine Integrable.mono' hTu_norm_int (hDk_cont k).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    exact hp_complex_iteratedFDeriv_norm u k x hu
  have hDk_sq_int : ∀ k : Fin 3, Integrable (fun x : E3 =>
      ‖(iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by
    intro k
    have hcont : Continuous (fun x : E3 =>
        ‖(iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
          (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖ ^ 2) :=
      (hDk_cont k).norm.pow 2
    refine Integrable.mono' hTu_sq_int hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h := hp_complex_iteratedFDeriv_norm u k x hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hDk_mlp2 : ∀ k : Fin 3, MemLp (fun x : E3 =>
      (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)) 2 (volume : Measure E3) := by
    intro k
    refine (memLp_two_iff_integrable_sq_norm (hDk_cont k).aestronglyMeasurable).mpr ?_
    exact hDk_sq_int k
  have hDk_kin_sq_int : ∀ k : Fin 3, Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT
        (fun x : E3 => (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
          (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) := by
    intro k
    have hmlp := Work.BoseKinLoc.Momentum.memLp_kinFT (hDk_int k) (hDk_mlp2 k)
    exact (memLp_two_iff_integrable_sq_norm hmlp.aestronglyMeasurable).mp hmlp
  have hplanch : ∀ k : Fin 3,
      ∫ p : E3, ‖Submission.BoseGases.kinFT
          (fun x : E3 => (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
            (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)) p‖ ^ 2
        = (2 * π) ^ 3 * ∫ x : E3,
            ‖(iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
              (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
    intro k
    have h := Work.BoseFixB3.HighMassAux.plancherel_L1L2
      (u := fun x : E3 => (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
        (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k))
      (memLp_one_iff_integrable.mpr (hDk_int k)) (hDk_mlp2 k)
    have h2 := congrArg (fun t : ℝ => (2 * π) ^ 3 * t) h
    rw [mul_inv_cancel_left₀ (ne_of_gt hpi3pos)] at h2
    exact h2
  have hpt : ∀ k : Fin 3, ∀ p : E3,
      |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        = ‖Submission.BoseGases.kinFT
            (fun x : E3 => (iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
              (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)) p‖ ^ 2 := by
    intro k p
    have h := hp_kinFT_iteratedDir_basis (fun y : E3 => (u y : ℂ)) k 40 p hWcd hWcs
    rw [h]
    ring
  have hInt_k : ∀ k : Fin 3, Integrable (fun p : E3 =>
      |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) := by
    intro k
    refine (hDk_kin_sq_int k).congr (Eventually.of_forall fun p => ?_)
    exact (hpt k p).symm
  have hint_k : ∀ k : Fin 3,
      ∫ p : E3, |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        = (2 * π) ^ 3 * ∫ x : E3,
            ‖(iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
              (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
    intro k
    rw [integral_congr_ae (Eventually.of_forall (hpt k))]
    exact hplanch k
  have hbound_k : ∀ k : Fin 3,
      ∫ x : E3, ‖(iteratedFDeriv ℝ 40 (fun y : E3 => (u y : ℂ)) x)
            (fun _ : Fin 40 => Submission.BoseGases.kcStdBasis k)‖ ^ 2
        ≤ ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2 := by
    intro k
    refine integral_mono (hDk_sq_int k) hTu_sq_int (fun x => ?_)
    have h := hp_complex_iteratedFDeriv_norm u k x hu
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  -- ### 3. The weighted integral is integrable and bounded
  have hInt_rhs : Integrable (fun p : E3 =>
      3 ^ 39 * ∑ k : Fin 3,
        |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) :=
    (integrable_finsetSum Finset.univ (fun k _ => hInt_k k)).const_mul (3 ^ 39)
  have hpt_rhs : ∀ p : E3,
      ‖p‖ ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ 3 ^ 39 * ∑ k : Fin 3,
            |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
    intro p
    have hGnn : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
      sq_nonneg _
    calc ‖p‖ ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ (3 ^ 39 * ∑ k : Fin 3, |p k| ^ 80) *
            ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hp_norm_pow_coord p) hGnn
      _ = 3 ^ 39 * ∑ k : Fin 3,
            |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  have hInt_normpow : Integrable (fun p : E3 =>
      ‖p‖ ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) := by
    have hcont : Continuous (fun p : E3 =>
        ‖p‖ ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) :=
      (continuous_norm.pow 80).mul (hkin_cont.norm.pow 2)
    exact Integrable.mono' hInt_rhs hcont.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) 80) (sq_nonneg _))]
        exact hpt_rhs p)
  -- ### 4. Shell / sum / per-coordinate chain
  have hshell := hp_shell_integral_le
    (fun p : E3 => ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2) κ hκ hG_ae
    (fun p => sq_nonneg _) hInt_normpow
  have hsum1 : ∫ p : E3, ‖p‖ ^ 80 *
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 ^ 39 * ∑ k : Fin 3, ∫ p : E3,
          |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
    calc ∫ p : E3, ‖p‖ ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ ∫ p : E3, 3 ^ 39 * ∑ k : Fin 3,
            |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
          integral_mono hInt_normpow hInt_rhs hpt_rhs
      _ = 3 ^ 39 * ∫ p : E3, ∑ k : Fin 3,
            |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 :=
          integral_const_mul _ _
      _ = 3 ^ 39 * ∑ k : Fin 3, ∫ p : E3,
            |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := by
          rw [integral_finsetSum Finset.univ (fun k _ => hInt_k k)]
  have hsum2 : ∑ k : Fin 3, ∫ p : E3,
        |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 * ((2 * π) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2) := by
    have h3 : ∑ k : Fin 3, ((2 * π) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2)
        = 3 * ((2 * π) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    rw [← h3]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [hint_k k]
    exact mul_le_mul_of_nonneg_left (hbound_k k) hpi3pos.le
  have hmain : ∫ p : E3, ‖p‖ ^ 80 *
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ 3 ^ 40 * (2 * π) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2 := by
    calc ∫ p : E3, ‖p‖ ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
        ≤ 3 ^ 39 * ∑ k : Fin 3, ∫ p : E3,
            |p k| ^ 80 * ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := hsum1
      _ ≤ 3 ^ 39 * (3 * ((2 * π) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum2 (by norm_num)
      _ = 3 ^ 40 * (2 * π) ^ 3 * ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2 := by ring
  calc ∫ p in {p : E3 | κ ≤ ‖p‖},
        ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2
      ≤ (κ ^ 80)⁻¹ * ∫ p : E3, ‖p‖ ^ 80 *
          ‖Submission.BoseGases.kinFT (fun x : E3 => (u x : ℂ)) p‖ ^ 2 := hshell
    _ ≤ (κ ^ 80)⁻¹ * (3 ^ 40 * (2 * π) ^ 3 *
          ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 3 ^ 40 * (2 * π) ^ 3 * (κ ^ 80)⁻¹ *
          ∫ x : E3, ‖iteratedFDeriv ℝ 40 u x‖ ^ 2 := by ring

end Work.BoseFixB3.CS.Pieces
