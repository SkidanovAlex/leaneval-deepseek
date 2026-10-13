import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Cutoff
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Defs
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Bounds
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Integrable
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Aesm
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Const
import Submission.Work.FTS.EllSol.ShiftFT.uTr_niceFlat
import Submission.Work.FTS.EllSol.Trunc.PassAux
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.windowMarginal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem uTr_Atwo (b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
          + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hJ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N ≥ (2 : ℝ),
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
          - 2 * b * Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
          + b ^ 2 * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
            - 2 * b * Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
            + b ^ 2 * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ K * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
              + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + (K / N) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) := by
  obtain ⟨Kd, hKd0, hKd⟩ := Work.FTS.EllSol.Trunc.exists_bound_deriv_tk
  obtain ⟨M, hM0, hM⟩ := Work.FTS.EllSol.Trunc.exists_bound_deriv2_tk
  refine ⟨3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4, ?_, fun N hN => ?_⟩
  · have h2 : (0 : ℝ) ≤ 3 * (Kd * (1 + 2 / 4096)) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ 196608 * M ^ 2 / 4096 ^ 4 := by positivity
    linarith
  · have hN0 : 0 < N := by linarith
    have hI' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
      simpa only [uTrAtwo_L2] using hI
    have hJ' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
      simpa only [uTrAtwo_L1] using hJ
    obtain ⟨hK3, hcc⟩ := uTrAtwo_const N Kd M
      (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2) hN hKd0
      (integral_deriv2_phiTr_sq_le N hM hN0)
    have hI2nn : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_stripIθ (fun p hp =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2))
    have hJnn : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_stripIθ (fun p hp =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2))
    have hAphinn : 0 ≤ ∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2 :=
      MeasureTheory.integral_nonneg (fun t => sq_nonneg _)
    have hDint : MeasureTheory.IntegrableOn (uTrAtwo_D N b u Kd)
        (Set.univ ×ˢ Work.Spaces.Iθ) :=
      uTrAtwo_D_integrable N b u Kd hN0 hu hI' hJ
    have hae : (fun p : ℝ × ℝ => (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2)
        =ᵐ[MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
        (fun p : ℝ × ℝ => (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) := by
      filter_upwards [ae_uTr_L2_eq N b u hu] with p hp
      rw [hp]
    have hle : (fun p : ℝ × ℝ => (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
        uTrAtwo_D N b u Kd := by
      filter_upwards [ae_mem_Ioo_of_Iθ] with p hp
      exact uTrAtwo_W_sq_le_D N b u hb hN0 hu hKd hKd0 p hp
    have hWint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (uTrAtwo_W N b u p) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2)
        (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      MeasureTheory.Integrable.mono' hDint (uTrAtwo_W_aesm N b u hN hu h0 h1) (by
        filter_upwards [hle, ae_restrict_mem measurableSet_stripIθ] with p hp hmem
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
          (Work.FTS.EllSol.FlatFT.wE_nonneg hmem.2))]
        exact hp)
    have hmain := integral_uTrAtwo_D N b u Kd hN0 hu hI' hJ
    have hwin := (Aux2.windowMarginal b N u hu hJ)
    have hWle : (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
        ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2 :=
      hwin.2
    have hint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) := by
      exact hWint.congr hae.symm
    refine ⟨hint, ?_⟩
    calc (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 :=
          MeasureTheory.integral_congr_ae hae
      _ ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, uTrAtwo_D N b u Kd p :=
          MeasureTheory.integral_mono_ae hWint hDint hle
      _ = 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2)
            + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2)
            + 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                    (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)) := hmain
      _ ≤ (3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4)
              * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
                  * Work.FTS.EllSol.FlatFT.wE p.2)
            + ((3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N)
              * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                  * Work.FTS.EllSol.FlatFT.wE p.2) := by
          have h1 : 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2)
              ≤ (3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4)
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2) := by
            nlinarith [hI2nn, hK3]
          have h2 : 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2)
              + 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                    (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
              ≤ ((3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N)
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2) := by
            have hJv : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                * Work.FTS.EllSol.FlatFT.wE p.2 := hJnn
            have hb : 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2)
                + 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2)
                = (3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                    + 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2))
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) := by ring
            have hc : (3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                    + 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2))
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2)
                ≤ ((3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N)
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) :=
              mul_le_mul_of_nonneg_right hcc hJv
            have hd : 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                  * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                      (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
                ≤ 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) := by
              have h4 : (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                  (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
                  ≤ (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) := hWle
              have h5 : 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (4 * N * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                        (uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
                  = 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                        * Work.FTS.EllSol.FlatFT.wE p.2) := by ring
              have h6 : 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                        (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
                  ≤ 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (4 * N * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                        (uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left h4 (by positivity)
              linarith [h5.le, h5.ge, h6]
            linarith [hb.le, hb.ge, hd, hc]
          linarith [h1, h2]

end

end Work.FTS.EllSol.ShiftFT
