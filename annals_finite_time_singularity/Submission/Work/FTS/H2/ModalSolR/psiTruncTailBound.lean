import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.ModalSolution.psiTrunc_pair_identities
import Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct
import Submission.Work.EllipticEst.ModalSolution.abs_le_of_l2_Icc
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.H2.ModalSolR.tailParseval
import Submission.Work.FTS.H2.ModalSolR.tailFacts
import Submission.Work.FTS.H2.ModalSolR.lzero1FinSumAE
import Submission.Work.FTS.H2.ModalSolR.energyToDeriv
import Submission.Work.FTS.H2.ModalSolR.supBoundOfIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open scoped Real BigOperators
open MeasureTheory Set Filter

noncomputable section

/-- The tail of the truncated mode series is the finite mode combination over
`Finset.Icc (M+1) N`. -/
lemma psitb_tail_diff (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) {M N : ℕ} (hMN : M ≤ N) :
    Work.FTS.PhiStar.Series.psiTrunc α F N z θ - Work.FTS.PhiStar.Series.psiTrunc α F M z θ
      = ∑ m ∈ Finset.Icc (M + 1) N,
          Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsdiff : Finset.range (N + 1) \ Finset.range (M + 1) = Finset.Icc (M + 1) N := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsum := Finset.sum_sdiff hsub
    (f := fun m => Work.FTS.PhiStar.Series.acoeff α m F z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
  rw [hsdiff] at hsum
  simp only [Work.FTS.PhiStar.Series.psiTrunc]
  linarith [hsum]

/-- `cos` is nonnegative on `Iθ = [0, π/2]`. -/
lemma psitb_cos_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- The squared `L²(Iθ, cos θ dθ)` norm of `eFam m` is nonnegative. -/
lemma psitb_eNorm_nonneg (m : ℕ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  rw [Work.Spaces.Iθ]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (sq_nonneg _)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-- The eigenvalue `lam m = 2m(2m+5)` is nonnegative. -/
lemma psitb_lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem psiTruncTailBound (α : ℝ) {F : ℝ → ℝ → ℝ} {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    (hd : d < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z θ : ℝ) (M N : ℕ), θ ∈ Set.Icc c d → M ≤ N →
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
          - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
        ≤ K * Real.sqrt
            ((∑ m ∈ Finset.Icc (M + 1) N,
                (∫ θ' in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                  * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
              + ∑ m ∈ Finset.Icc (M + 1) N,
                  Work.FTS.PhiStar.Gegenbauer.lam m
                    * (∫ θ' in Work.Spaces.Iθ,
                        Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                    * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by
  obtain ⟨K, hKpos, hK⟩ := supBoundOfIntegrals (c := c) (d := d) hcd hc hd
  refine ⟨K * Real.sqrt 7, by positivity, ?_⟩
  intro z θ M N hθ hMN
  set a : ℕ → ℝ := fun m => Work.FTS.PhiStar.Series.acoeff α m F z with ha
  have ha' : ∀ m, a m = Work.FTS.PhiStar.Series.acoeff α m F z := fun m => congrFun ha m
  simp only [← ha']
  set S1 : ℝ := ∑ m ∈ Finset.Icc (M + 1) N,
      (∫ θ' in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ') * (a m) ^ 2 with hS1
  set S2 : ℝ := ∑ m ∈ Finset.Icc (M + 1) N,
      Work.FTS.PhiStar.Gegenbauer.lam m
        * (∫ θ' in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ') * (a m) ^ 2 with hS2
  -- the facts about the tail function
  obtain ⟨hC2raw, hzero, hpi, hI4, hI2, hI3⟩ := tailFacts a (Finset.Icc (M + 1) N)
  obtain ⟨-, hI1⟩ := lzero1FinSumAE a (Finset.Icc (M + 1) N)
  obtain ⟨hP1, hP2⟩ := tailParseval α F z hMN
  -- the weighted tail function
  set v : ℝ → ℝ := fun θ => ∑ m ∈ Finset.Icc (M + 1) N,
      a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ with hv
  have hC2 : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)) := hC2raw
  have hv0 : v 0 = 0 := hzero
  have hvpi : v (Real.pi / 2) = 0 := hpi
  -- the two Parseval identities
  have hP1v : (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2 * Real.cos θ) = S1 := by
    rw [hS1]
    simpa only [← ha', hv] using hP1
  have hP2v : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ)
      = S2 := by
    rw [hS2]
    have hb : Work.FTS.EllipticEst.Lzero1 v
        = fun θ => Work.Elliptic.Lzero (fun _ θ' => v θ') 0 θ :=
      Work.FTS.EllipticEst.Lzero1_eq_Lzero v 0
    rw [hb]
    simpa only [← ha', hv] using hP2
  -- the derivative bound
  have hT : (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ) ≤ 6 * S1 + S2 := by
    have h := energyToDeriv hC2 hv0 hvpi hI1 hI2 hI3 hI4
    linarith [h, hP1v, hP2v]
  -- the sup bound on the interior interval
  have hcont : ContDiffOn ℝ 1 v (Set.Icc 0 (Real.pi / 2)) := hC2.of_le (by norm_num)
  have hAg := hK v hcont hI4 hI2 θ hθ
  rw [hP1v] at hAg
  -- nonnegativity of the two sums
  have hS1nn : 0 ≤ S1 := by
    rw [hS1]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (psitb_eNorm_nonneg m) (sq_nonneg _)
  have hS2nn : 0 ≤ S2 := by
    rw [hS2]
    exact Finset.sum_nonneg fun m _ =>
      mul_nonneg (mul_nonneg (psitb_lam_nonneg m) (psitb_eNorm_nonneg m)) (sq_nonneg _)
  -- identification with the difference of the partial sums
  have hd1 : |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
      - Work.FTS.PhiStar.Series.psiTrunc α F M z θ| = |v θ| := by
    rw [psitb_tail_diff α F z θ hMN]
  rw [hd1]
  -- final chain
  refine hAg.trans ?_
  have hstep : K * Real.sqrt (S1 + (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ))
      ≤ K * Real.sqrt (S1 + (6 * S1 + S2)) := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hKpos.le
    linarith [hT]
  refine hstep.trans ?_
  have harg : S1 + (6 * S1 + S2) ≤ 7 * (S1 + S2) := by linarith
  refine (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) hKpos.le).trans ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7), mul_assoc]

end

end Work.FTS.H2.ModalSolR
