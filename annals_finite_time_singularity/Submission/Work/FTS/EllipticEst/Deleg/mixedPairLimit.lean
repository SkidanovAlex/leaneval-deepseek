/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedPairLimit` — the `δ ↓ 0` limit of the cut-off chain

Target: `Work.FTS.EllipticEst.Deleg.mixedPairLimit`, i.e. the lemma `Deleg.PairLimit`
(`Deleg/i1Paper_weakMixedDefs.lean`): given `AeData α u G`, `HkMem α 0 (grad u)`, the a.e. mixed
honesty `MixedHon u`, `0 < K`, the a.e. slice rate `SliceRate K u`, and the per-`(n,δ)` inequality

  `kap · Ptr u n δ ≤ Dtr u n δ + Trtr u n δ − 2η · Atr u n δ + Cw · K · Col u n δ`   (`hpair`),

one has, for every `n`, `kap · Pcut u n ≤ Dcut u n + Trcut u n − 2η · Acut u n`.

The proof is the `δ → 0⁺` limit of `hpair`, along the filter `𝓝[>] 0`:
`Ptr/Atr/Dtr/Trtr` converge to `Pcut/Acut/Dcut/Trcut` by the generic dominated-convergence lemma
`Deleg.psiDIntegralLimit`/`Deleg.psiDIntegralLimitAlt` (the bump `psiD δ` tends to `1` pointwise on `(0,π/2)`), and
`Col u n δ → 0` by `Deleg.psiDLayerLimit`.  `le_of_tendsto_of_tendsto` concludes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.Deleg.mixedPairAux2
import Submission.Work.FTS.EllipticEst.Deleg.mixedHdom
import Submission.Work.FTS.EllipticEst.Deleg.psiDIntegralLimitAlt
import Submission.Work.FTS.EllipticEst.Deleg.psiDLayerLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## The five limits -/

theorem tendsto_Ptr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hM : MixedHon u) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Ptr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Pcut u n)) := by
  have hmain := psiDIntegralLimitAlt
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
    (aesm_cut_mul_wt n) (aesm_joint_Vz hA) (integrableOn_slice_of_MixedHon hM)
    (hdom_Vz hA hM n)
  have hval : (∫ z, (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Pcut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Pcut]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Ptr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Atr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Atr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Acut u n)) := by
  have hGz : Filter.Eventually (fun z => Integrable (fun θ =>
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact integrableOn_sig_mul_sq_of_HkMem α hU hz
  have hmain := psiDIntegralLimitAlt
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
    (aesm_cut_mul_wt n) (aesm_joint_Uz hA) hGz (hdom_Uz hA hU n)
  have hval : (∫ z, (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Acut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Acut]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Atr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Dtr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Dtr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Dcut u n)) := by
  have hGz : Filter.Eventually (fun z => Integrable (fun θ =>
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    refine integrableOn_sig_mul_mul_of_HkMem α
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA)
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz ?_
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_joint_AzB hA) hz
  have hmain := psiDIntegralLimitAlt
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
      * Work.Spaces.pthIter 2 u z θ)
    (aesm_cut_mul_wt n) (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_AzB hA)) hGz
    (hdom_AzB hA n)
  have hval : (∫ z, (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ) ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Dcut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Dcut]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Az u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
              * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
                * Work.Spaces.pthIter 2 u z θ) from
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Dtr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
        * (Work.FTS.EllipticEst.AeColl.Az u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
            * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
              * (Work.FTS.EllipticEst.AeColl.Az u z θ)
              * (Work.Spaces.pthIter 2 u z θ)) from
    integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Trtr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Trtr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Trcut u n)) := by
  have hGz : Filter.Eventually (fun z => Integrable (fun θ =>
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    refine integrableOn_sig_mul_mul_of_HkMem α hU
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz ?_
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_joint_UzB hA) hz
  have hmain := psiDIntegralLimitAlt
    (c := fun z => deriv (fun z' => Work.FTS.EllipticEst.cut n z'
      * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
      * Work.Spaces.pthIter 2 u z θ)
    (aesm_trtr_coef n) (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_UzB hA)) hGz
    (hdom_UzB hA hU n)
  have hval : (∫ z, (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
        * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ) ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Trcut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Trcut]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          deriv (fun z' => Work.FTS.EllipticEst.cut n z'
            * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z
          * Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Uz u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
              * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
              * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.Spaces.pthIter 2 u z θ) from
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Trtr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        deriv (fun z' => Work.FTS.EllipticEst.cut n z'
          * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z
        * Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
        * (Work.FTS.EllipticEst.AeColl.Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
            * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
            * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
              * (Work.FTS.EllipticEst.AeColl.Uz u z θ)
              * (Work.Spaces.pthIter 2 u z θ)) from
    integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Col {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hM : MixedHon u) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Col u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hGnn : ∀ z θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → 0 ≤
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 :=
    fun z θ hθ => mul_nonneg
      (le_of_lt (sigθ_pos_of_mem_Ioo hθ)) (sq_nonneg _)
  have hmain := psiDLayerLimit
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
    (aesm_cut_mul_wt n) (aesm_joint_Vz hA) (integrableOn_slice_of_MixedHon hM) hGnn
    (hdom_Vz hA hM n)
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Col]

/-! ## The assembly -/

theorem mixedPairLimit (Cw : ℝ) (hCw : 0 < Cw) :
    Work.FTS.EllipticEst.Deleg.PairLimit Cw := by
  intro α u G hA hU hM K hK _hR hpair n
  have h1 := tendsto_Ptr hA hM n
  have h2 := tendsto_Atr hA hU n
  have h3 := tendsto_Dtr hA n
  have h4 := tendsto_Trtr hA hU n
  have h5 := tendsto_Col hA hM n
  have hL : Tendsto (fun δ : ℝ => kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (kap * Work.FTS.EllipticEst.AeColl.Pcut u n)) :=
    h1.const_mul kap
  have hR : Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Dtr u n δ
        + Work.FTS.EllipticEst.AeColl.Trtr u n δ
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
        + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n + Cw * K * 0)) :=
    (((h3.add h4).sub (h2.const_mul (2 * Work.Spaces.eta))).add (h5.const_mul (Cw * K)))
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ
      ≤ Work.FTS.EllipticEst.AeColl.Dtr u n δ + Work.FTS.EllipticEst.AeColl.Trtr u n δ
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
        + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < Real.pi / 16 by linarith [Real.pi_pos])]
      with δ hδ
    exact hpair n δ hδ.1 (by linarith [hδ.2, Real.pi_pos])
  have hfin := le_of_tendsto_of_tendsto hL hR hev
  simpa using hfin

end

end Work.FTS.EllipticEst.Deleg
