import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.traceVanishingInterp
import Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCore
import Submission.Work.EllipticEst.Core.thetaInterpEndpoints
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Helpers
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux
import Submission.Work.FTS.EllipticEst.Prop.TIProp.Helpers
import Submission.Work.FTS.EllipticEst.Prop.TIProp.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted angular interpolation `thetaInterpCore` from the trace bounds

The hypothesis `hTB` is the one-sided trace bound of `Prop.traceBoundLeft` / `Prop.traceBoundRight`
(carried here as a hypothesis).  The conclusion is the one-dimensional weighted interpolation
inequality of `Core.i0Aux.thetaInterpCore`.

The proof does not use `hTB`.  It reduces the problem to the *trace-vanishing* case
(`Core.i0Aux.traceVanishingInterp`) by subtracting a *surrogate* `ℓ = surrFun ψ F₀ F₁ L`
(`Core.i0Aux.TVRed`) which reproduces the two endpoint traces of `f` and whose weighted energies
are controlled at the scale `L = sScale P E = (P/(16(P+E)))^{1/4}` (`Core.i0Aux.TVRed.Helpers`).
The estimates on the surrogate are `TIProp.surrBounds` (from `TVRed.surrIntegrals` together with
the endpoint value estimates `TVRed.endpointParamLeftW` / `endpointParamRightW`, which also control
the two endpoint traces), and the difference `g = f - ℓ` is handled by the trace-vanishing
inequality, using the derivative identities and weighted-square integrability lemmas of
`Core.i0Aux.TVRed.tvHypAux`.  The intermediate bounds are packaged in `TIProp.bounds`.
-/

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "σ" => Work.FTS.EllipticEst.thEta
theorem thetaInterpCoreOfTraceBounds
    (hTB : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (F₀ L₀ F₁ L₁ : ℝ),
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) →
      Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L₀) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) →
      Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L₁) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      max (F₀ * L₀) 0 + F₀ ^ 2 + max (-(F₁ * L₁)) 0 + F₁ ^ 2
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
                * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
                * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨ψ, Cb, hψ⟩ := Work.EllipticEst.Core.i0Aux.TVRed.bumpExists
  obtain ⟨C_T, hC_Tpos, hC_T⟩ := Work.EllipticEst.Core.i0Aux.traceVanishingInterp
  have hCb1 : (0 : ℝ) < Cb + 1 := by linarith [hψ.C_pos]
  have hCb2 : (0 : ℝ) < (Cb + 1) ^ 2 := pow_pos hCb1 2
  refine ⟨10 ^ 8 * (Cb + 1) ^ 2 * (8 * C_T + 2), ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) hCb2) (by linarith)
  · intro f hf hf0 hf1 hPint hAint hEint
    set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ with hPdef
    set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * σ θ with hAdef
    set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * σ θ with hEdef
    have hPnn : 0 ≤ P := by
      rw [hPdef]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hEnn : 0 ≤ E := by
      rw [hEdef]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    by_cases hPz : P = 0
    · -- ## the degenerate case `P = 0`, where `f` vanishes on the open interval
      have hzero_ae : (fun θ : ℝ => (f θ) ^ 2 * σ θ)
          =ᵐ[volume.restrict Work.Spaces.Iθ] (fun _ => 0) := by
        refine (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae ?_ hPint).mp ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · rw [← hPdef]; exact hPz
      have hfzero : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = 0 := by
        have hiff : (fun θ : ℝ => (f θ) ^ 2 * σ θ)
            =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))] (fun _ => 0) :=
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset
            (t := Work.Spaces.Iθ)
            (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) hzero_ae
        have hfe : f =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))] (fun _ => 0) := by
          filter_upwards [hiff, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ h1 h2
          have h0 : (f θ) ^ 2 = 0 :=
            (mul_eq_zero.mp h1).resolve_right
              (ne_of_gt (Work.FTS.EllipticEst.Prop.TIProp.thEta_pos_Ioo h2))
          have h3 : f θ * f θ = 0 := by rwa [pow_two] at h0
          rcases mul_eq_zero.mp h3 with h | h
          · exact h
          · exact h
        exact MeasureTheory.Measure.eqOn_Ioo_of_ae_eq (μ := volume) hfe hf.continuousOn
          continuous_const.continuousOn
      have hderiv0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv f θ = 0 := by
        intro θ hθ
        have hev : f =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
          exact hfzero y hy
        rw [hev.deriv_eq, deriv_const]
      have hA0 : A = 0 := by
        rw [hAdef]
        have hae : (fun θ : ℝ => (deriv f θ) ^ 2 * σ θ)
            =ᵐ[volume.restrict Work.Spaces.Iθ] (fun _ => 0) := by
          filter_upwards [Work.FTS.EllipticEst.Prop.TIProp.ae_mem_Ioo_Iθ] with θ hθ
          rw [hderiv0 θ hθ]; ring
        rw [MeasureTheory.integral_congr_ae hae]; simp
      rw [hA0, hPz]
      simp
    · -- ## the main case `P > 0`
      have hPpos : 0 < P := lt_of_le_of_ne hPnn (Ne.symm hPz)
      obtain ⟨F₀, F₁, L₀, L₁, M, M', hF0tr, hF1tr, hL0tr, hL1tr, -, -⟩ :=
        Work.EllipticEst.Core.thetaInterpEndpoints f hf hPint hAint hEint
      set L : ℝ := Work.EllipticEst.Core.i0Aux.sScale P E with hLdef
      have hLpos : 0 < L := by
        rw [hLdef]; exact Work.EllipticEst.Core.i0Aux.sScale_pos hPpos hEnn
      have hLhalf : L ≤ 1 / 2 := by
        rw [hLdef]; exact Work.EllipticEst.Core.i0Aux.sScale_le_half hPpos hEnn
      have hLp : L ≤ Real.pi / 4 := by nlinarith [hLhalf, Real.pi_gt_three]
      have hL4 : L ^ 4 = P / (16 * (P + E)) := by
        rw [hLdef]; exact Work.EllipticEst.Core.i0Aux.sScale_pow4 hPpos hEnn
      obtain ⟨hPg, hEg, hAℓ, hgIθ, hg_int1, hg_int2, hintℓ0, hintℓ1⟩ :=
        Work.FTS.EllipticEst.Prop.TIProp.bounds hψ hLpos hLp hPpos hEnn hL4 hf hF0tr hF1tr
          hPint hAint hEint hPdef hEdef
      -- ## the trace-vanishing interpolation applied to `g`
      have hg_cd : ContDiffOn ℝ 2 (fun θ : ℝ => f θ
          - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hf.sub ((Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)).contDiffOn)
      have hg_tr0 : Filter.Tendsto (fun θ : ℝ => f θ
          - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h := hF0tr.sub (Work.EllipticEst.Core.i0Aux.TVRed.surr_tendsto_left (F₀ := F₀)
          (F₁ := F₁) hψ hLpos hLp)
        rwa [sub_self] at h
      have hg_tr1 : Filter.Tendsto (fun θ : ℝ => f θ
          - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have h := hF1tr.sub (Work.EllipticEst.Core.i0Aux.TVRed.surr_tendsto_right (F₀ := F₀)
          (F₁ := F₁) hψ hLpos hLp)
        rwa [sub_self] at h
      have hAg : (∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
          ≤ C_T * ((∫ θ in Work.Spaces.Iθ,
                (fun θ : ℝ => f θ
                  - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Work.Spaces.Iθ,
                  (fun θ : ℝ => f θ
                    - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
                * (∫ θ in Work.Spaces.Iθ,
                    (deriv (deriv (fun θ : ℝ => f θ
                      - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 * σ θ))) :=
        hC_T _ hg_cd hg_tr0 hg_tr1 hgIθ hg_int1 hg_int2
      -- ## splitting `A` against `g` and `ℓ`
      have hApt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f θ) ^ 2 ≤ 2 * (deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2
            + 2 * (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 := by
        intro θ hθ
        have h := Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv_sub hf
          (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth (F₀ := F₀) (F₁ := F₁) hψ
            (ne_of_gt hLpos)) θ hθ
        have h2 : deriv f θ = deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ
            + deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ := by
          rw [show deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ
              = deriv f θ - deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ from h]
          ring
        rw [h2]
        nlinarith [sq_nonneg (deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ
            - deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ)]
      have hAsplit : A ≤ 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ) := by
        rw [hAdef]
        have h1 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * σ θ)
            ≤ ∫ θ in Work.Spaces.Iθ,
                2 * ((deriv (fun θ : ℝ => f θ
                  - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
              + 2 * ((deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
          · exact (hg_int1.const_mul 2).add (hintℓ1.const_mul 2)
          · filter_upwards [Work.FTS.EllipticEst.Prop.TIProp.ae_mem_Ioo_Iθ] with θ hθ
            have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.Prop.TIProp.thEta_nonneg_Ioo hθ
            calc (deriv f θ) ^ 2 * σ θ
                ≤ (2 * (deriv (fun θ : ℝ => f θ
                      - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2
                    + 2 * (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2) * σ θ :=
                  mul_le_mul_of_nonneg_right (hApt θ hθ) hσ
              _ = 2 * ((deriv (fun θ : ℝ => f θ
                      - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
                  + 2 * ((deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ) := by
                  ring
        rw [MeasureTheory.integral_add (hg_int1.const_mul 2) (hintℓ1.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h1
        linarith [h1]
      -- ## the final arithmetic
      have hKpos : (0 : ℝ) < 10 ^ 8 * (Cb + 1) ^ 2 := mul_pos (by norm_num) hCb2
      have hK1 : (1 : ℝ) ≤ 10 ^ 8 * (Cb + 1) ^ 2 := by
        have h2 : (1 : ℝ) ≤ (Cb + 1) ^ 2 := by nlinarith [hψ.C_pos]
        nlinarith
      have hXnn : 0 ≤ Real.sqrt (P * E) := Real.sqrt_nonneg _
      have hEgnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ : ℝ => f θ
            - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 * σ θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
      have hstep1 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => f θ
            - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
          ≤ 10 ^ 8 * (Cb + 1) ^ 2 * P := by
        have h2 : (1 : ℝ) ≤ (Cb + 1) ^ 2 := by nlinarith [hψ.C_pos]
        have h1 : (10 ^ 6 : ℝ) * P ≤ 10 ^ 8 * (Cb + 1) ^ 2 * P := by nlinarith [hPnn, h2]
        linarith [hPg, h1]
      have hstep5 : (∫ θ in Work.Spaces.Iθ,
            (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := by
        have hY : 0 ≤ P + Real.sqrt (P * E) := by linarith [hPnn, hXnn]
        have h2 : (10 ^ 6 : ℝ) * (Cb + 1) ^ 2 ≤ 10 ^ 8 * (Cb + 1) ^ 2 := by
          nlinarith [sq_nonneg (Cb + 1)]
        calc (∫ θ in Work.Spaces.Iθ,
              (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
            ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := hAℓ
          _ ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := by nlinarith [h2, hY]
      have hstep4 : Real.sqrt (P * (P + E)) ≤ P + Real.sqrt (P * E) :=
        Work.EllipticEst.Core.i0Aux.tvc_sqrt_mul_le hPnn hEnn
      have hfacnn : (0 : ℝ)
          ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) :=
        mul_nonneg hKpos.le (by linarith)
      have hKfac : 10 ^ 8 * (Cb + 1) ^ 2 * (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2))
          ≤ (3 * (10 ^ 8 * (Cb + 1) ^ 2)) ^ 2 := by nlinarith [hK1]
      have hstep3 : Real.sqrt ((10 ^ 8 * (Cb + 1) ^ 2 * P)
            * ((2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E)))
          ≤ 3 * (10 ^ 8 * (Cb + 1) ^ 2) * Real.sqrt (P * (P + E)) := by
        rw [show (10 ^ 8 * (Cb + 1) ^ 2 * P)
              * ((2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E))
            = (10 ^ 8 * (Cb + 1) ^ 2 * (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)))
              * (P * (P + E)) by ring,
          Real.sqrt_mul hfacnn]
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact le_trans (Real.sqrt_le_sqrt hKfac) (le_of_eq (Real.sqrt_sq (by positivity)))
      have hstep2 : (∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ : ℝ => f θ
              - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
          ≤ C_T * (10 ^ 8 * (Cb + 1) ^ 2 * P
            + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * Real.sqrt (P * (P + E))) := by
        have h3 : Real.sqrt ((∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => f θ
                  - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ : ℝ => f θ
                  - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 * σ θ))
            ≤ Real.sqrt ((10 ^ 8 * (Cb + 1) ^ 2 * P)
                * ((2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E))) := by
          refine Real.sqrt_le_sqrt (mul_le_mul hstep1 hEg hEgnn ?_)
          exact mul_nonneg hKpos.le hPnn
        have hsum : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => f θ
                - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
              + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => f θ
                    - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
                  * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ : ℝ => f θ
                    - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 * σ θ))
            ≤ 10 ^ 8 * (Cb + 1) ^ 2 * P
              + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * Real.sqrt (P * (P + E)) := by
          linarith [hstep1, h3, hstep3]
        calc (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ : ℝ => f θ
                - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
            ≤ C_T * ((∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => f θ
                    - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
                + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => f θ
                      - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2 * σ θ)
                    * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ : ℝ => f θ
                      - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 * σ θ))) := hAg
          _ ≤ C_T * (10 ^ 8 * (Cb + 1) ^ 2 * P
                + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * Real.sqrt (P * (P + E))) :=
              mul_le_mul_of_nonneg_left hsum hC_Tpos.le
      have hfinal : A ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (8 * C_T + 2) * (P + Real.sqrt (P * E)) := by
        have e3 : 3 * (10 ^ 8 * (Cb + 1) ^ 2) * Real.sqrt (P * (P + E))
            ≤ 3 * (10 ^ 8 * (Cb + 1) ^ 2) * (P + Real.sqrt (P * E)) :=
          mul_le_mul_of_nonneg_left hstep4 (by positivity)
        have e1 : 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ : ℝ => f θ
                - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
            ≤ 2 * C_T * (10 ^ 8 * (Cb + 1) ^ 2 * P
              + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * (P + Real.sqrt (P * E))) := by
          have h1 := mul_le_mul_of_nonneg_left hstep2 (by norm_num : (0 : ℝ) ≤ 2)
          have h2 : 2 * (C_T * (10 ^ 8 * (Cb + 1) ^ 2 * P
                + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * Real.sqrt (P * (P + E))))
              ≤ 2 * C_T * (10 ^ 8 * (Cb + 1) ^ 2 * P
                + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * (P + Real.sqrt (P * E))) := by
            have h4 := mul_le_mul_of_nonneg_left e3 hC_Tpos.le
            linarith
          linarith [h1, h2]
        have e2 : 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
            ≤ 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E))) :=
          mul_le_mul_of_nonneg_left hstep5 (by norm_num)
        calc A ≤ 2 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ : ℝ => f θ
                  - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 * σ θ)
              + 2 * (∫ θ in Work.Spaces.Iθ,
                  (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ) := hAsplit
          _ ≤ 2 * C_T * (10 ^ 8 * (Cb + 1) ^ 2 * P
                + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * (P + Real.sqrt (P * E)))
              + 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E))) := add_le_add e1 e2
          _ ≤ 2 * C_T * (10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E))
                + 3 * (10 ^ 8 * (Cb + 1) ^ 2) * (P + Real.sqrt (P * E)))
              + 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E))) := by
              have h1 : 10 ^ 8 * (Cb + 1) ^ 2 * P
                  ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) :=
                mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hXnn) (by positivity)
              have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * C_T)
              linarith [h2]
          _ = 10 ^ 8 * (Cb + 1) ^ 2 * (8 * C_T + 2) * (P + Real.sqrt (P * E)) := by ring
      exact hfinal

end

end Work.FTS.EllipticEst.Prop
