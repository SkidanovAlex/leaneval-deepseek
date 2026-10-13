import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Bounds
import Submission.Work.FTS.EllSol.Trunc.PassAux
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


/-- Integrability of the square of the second derivative of `phiTr` (it is continuous and
compactly supported, with support inside `[-8192N, 8192N]`). -/
theorem integrable_deriv2_phiTr_sq (N : ℝ) (hN : 0 < N) :
    Integrable (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2) volume := by
  set A : ℝ := 8192 * N with hAdef
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc (-A) A → (deriv (deriv (phiTr N)) t) ^ 2 = 0 := by
    intro t ht
    have hge : A ≤ |t| := by
      by_contra hcon
      push Not at hcon
      exact ht ⟨by linarith [neg_abs_le t, hcon], by linarith [le_abs_self t, hcon]⟩
    rw [deriv2_phiTr_eq_zero_of_abs_ge hN (by rw [hAdef] at hge; exact hge)]
    ring
  have hcont : Continuous (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2) :=
    (((phiTr_contDiff 2 N).deriv').continuous_deriv_one).pow 2
  have hOn : IntegrableOn (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2) (Set.Icc (-A) A) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hind : Integrable ((Set.Icc (-A) A).indicator
      (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hOn
  refine hind.congr ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (-A) A
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, hsupp t ht]

/-- Integrability of the first summand of `D`. -/
theorem uTrAtwo_D1_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hI : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ => 3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2)) (Set.univ ×ˢ Work.Spaces.Iθ) :=
  hI.const_mul 3

/-- Integrability of the second summand of `D`. -/
theorem uTrAtwo_D2_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ)
    (hJ : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ => 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
      * ((uTrAtwo_L1 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2)) (Set.univ ×ˢ Work.Spaces.Iθ) :=
  hJ.const_mul _

/-- Integrability of the third summand of `D`. -/
theorem uTrAtwo_D3_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hJ : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ => 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
      * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE p.2))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  have hwin := (Aux2.windowMarginal b N u hu hJ).1
  have hBw : Integrable (fun θ : ℝ => 4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N),
      (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hwin.const_mul (4 * N)
  have hprod : Integrable (fun p : ℝ × ℝ => (3 * (deriv (deriv (phiTr N)) p.1) ^ 2)
      * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE p.2)))
      (volume.prod (volume.restrict Work.Spaces.Iθ)) :=
    Integrable.mul_prod ((integrable_deriv2_phiTr_sq N hN).const_mul 3) hBw
  rwa [IntegrableOn, uTrAtwo_prodRestrict_Iθ]

/-- Integrability of the dominating function. -/
theorem uTrAtwo_D_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hJ : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (uTrAtwo_D N b u Kd) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  have hJ' : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    simpa only [uTrAtwo_L1] using hJ
  have h1 := uTrAtwo_D1_integrable N b u hI
  have h2 := uTrAtwo_D2_integrable N b u Kd hJ'
  have h3 := uTrAtwo_D3_integrable N b u hN hu hJ
  change IntegrableOn (fun p : ℝ × ℝ =>
      3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
          * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
              * Work.FTS.EllSol.FlatFT.wE p.2))) (Set.univ ×ˢ Work.Spaces.Iθ)
  exact (h1.add h2).add h3

/-- The value of the integral of the dominating function `D`. -/
theorem integral_uTrAtwo_D (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hJ : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, uTrAtwo_D N b u Kd p)
      = 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2)
        + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
            * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                * Work.FTS.EllSol.FlatFT.wE p.2)
        + 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
            * (4 * N * (∫ θ in Work.Spaces.Iθ,
                (∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
                  * Work.FTS.EllSol.FlatFT.wE θ)) := by
  have hJ' : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    simpa only [uTrAtwo_L1] using hJ
  have h1 := uTrAtwo_D1_integrable N b u hI
  have h2 := uTrAtwo_D2_integrable N b u Kd hJ'
  have h3 := uTrAtwo_D3_integrable N b u hN hu hJ
  have e1 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, 3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2))
      = 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) :=
    MeasureTheory.integral_const_mul 3 _
  have e2 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
      = 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) :=
    MeasureTheory.integral_const_mul _ _
  have e3 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
      * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE p.2)))
      = 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
          * (4 * N * (∫ θ in Work.Spaces.Iθ,
              (∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
                * Work.FTS.EllSol.FlatFT.wE θ)) := by
    rw [Work.FTS.EllSol.Trunc.setIntegral_univ_prod_Iθ_eq_iterated
      (f := fun t θ => 3 * (deriv (deriv (phiTr N)) t) ^ 2
        * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
            * Work.FTS.EllSol.FlatFT.wE θ))) h3]
    have hinner : ∀ t : ℝ, (∫ θ in Work.Spaces.Iθ,
        (3 * (deriv (deriv (phiTr N)) t) ^ 2)
          * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
              * Work.FTS.EllSol.FlatFT.wE θ)))
        = (3 * (deriv (deriv (phiTr N)) t) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, 4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N),
                (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)) :=
      fun t => MeasureTheory.integral_const_mul _ _
    simp only [hinner]
    rw [MeasureTheory.integral_mul_const]
    have h1 : (∫ t in Set.univ, 3 * (deriv (deriv (phiTr N)) t) ^ 2)
        = 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2) :=
      MeasureTheory.integral_const_mul 3 _
    have h2 : (∫ θ in Work.Spaces.Iθ, 4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N),
        (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
        = 4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
            (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [h1, h2]
    try ring
  change (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
      3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
          * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
              * Work.FTS.EllSol.FlatFT.wE p.2))) = _
  have step1 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
              * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
        + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
            * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
                * Work.FTS.EllSol.FlatFT.wE p.2)))
      = (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
            + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
        + ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            3 * (deriv (deriv (phiTr N)) p.1) ^ 2
              * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
                  * Work.FTS.EllSol.FlatFT.wE p.2)) :=
    MeasureTheory.integral_add (h1.add h2) h3
  have step2 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
              * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
      = (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
        + ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
              * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) :=
    MeasureTheory.integral_add h1 h2
  rw [step1, step2, e1, e2, e3]

end

end Work.FTS.EllSol.ShiftFT
