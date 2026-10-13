/-
# `ModalSolR/CoeffBound` — summability and size of the mode coefficients

Under the standing hypotheses on `F` (orthogonality, smoothness, `L²`), the mode coefficients
`a_m(z) = acoeff α m F z = radGreen α m (cmode m F) z` satisfy the uniform-in-`N` bounds

  `Σ_{m ≤ N} eNorm m · a_m(z)² ≤ D z⁻¹`,   `Σ_{m ≤ N} lam m · eNorm m · a_m(z)² ≤ D z⁻¹`

with `D = ‖F‖²_{L²(Q0)}/α²`.  The two inputs are

* `coeffL2_sum_le`: `Σ_{m ≤ N} eNorm m ‖cmode m F‖²_{L²(0,∞)} ≤ ‖F‖²_{L²(Q0)}` (Bessel
  `cmode_bessel` integrated in `z` by Tonelli / Fubini for `ℝ≥0∞`);
* the pointwise Green's-function bound `radGreen_abs_le` (and `a_0 = 0` under `OrthCond F`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-- `eNorm m ≥ 0`. -/
theorem eNorm_nonneg (m : ℕ) : 0 ≤ Work.EllipticEst.ModalSolution.eNorm m :=
  (Work.EllipticEst.ModalSolution.eNorm_pos m).le

/-- **The sum of the coefficient `L²`-masses is bounded by the `L²`-mass of the source.** -/
theorem coeffL2_sum_le {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2 := by
  have hcm : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) (Set.Ioi 0) := fun m =>
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  -- ## the real identity: sum of integrals = integral of the finite sum
  have hsum : (∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      = ∫ z in Set.Ioi 0, ∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun m _ => (MeasureTheory.integral_const_mul _ _).symm)
    · intro m _
      exact (hcm m).const_mul _
  have hnn_sum : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] fun z =>
      ∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 :=
    Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun m _ =>
      mul_nonneg (eNorm_nonneg m) (sq_nonneg _)
  have hint_sum : MeasureTheory.IntegrableOn (fun z =>
      ∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.integrable_finsetSum (Finset.range (N + 1))
      (fun m _ => (hcm m).const_mul _)
  have hofReal : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m
          * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
    rw [hsum, MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_sum hnn_sum]

  -- ## Bessel at each `z`, integrated
  have hbessel : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) :=
    lintegral_mono fun z => Work.EllipticEst.ModalSolution.cmode_bessel F z N
  -- ## Tonelli
  have hcont_g : ContinuousOn (fun p : ℝ × ℝ =>
      ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2)) Work.FTS.EllipticEst.Q0 :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hsm.continuousOn.pow 2).mul (Real.continuous_cos.comp_continuousOn continuousOn_snd))
  have htonelli : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (F z θ ^ 2 * Real.cos θ))
      = ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2) := by
    refine (MeasureTheory.setLIntegral_prod (μ := volume) (ν := volume)
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2))
      (s := Set.Ioi 0) (t := Work.Spaces.Iθ) ?_).symm
    have : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2))
        ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
      rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
      exact hcont_g.aemeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact this
  -- ## bound by the `Q0`-integral of `F²`
  have hbound : (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2))
      ≤ ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
    rw [show (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
        = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 from
      Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (by
      calc F p.1 p.2 ^ 2 * Real.cos p.2 ≤ F p.1 p.2 ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.cos_le_one p.2) (sq_nonneg (F p.1 p.2))
        _ = F p.1 p.2 ^ 2 := mul_one _)
  -- ## the `ofReal` of the source integral
  have hsource : (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2))
      = ENNReal.ofReal (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hL2
      (Filter.Eventually.of_forall fun p => sq_nonneg _)).symm
  -- ## assemble
  have hchain : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m
          * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ENNReal.ofReal (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) := by
    rw [hofReal]
    exact le_trans hbessel (le_trans (le_of_eq htonelli) (le_trans hbound (le_of_eq hsource)))
  exact (ENNReal.ofReal_le_ofReal_iff (MeasureTheory.integral_nonneg
    (fun p => sq_nonneg _))).mp hchain


/-- `lam m ≥ 0`. -/
theorem lam_nonneg' (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]; positivity

/-- **Bounds on the partial sums of the mode coefficients.** -/
theorem coeffSq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, 0 < z → ∀ N : ℕ,
      ((∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) ≤ D * z ^ (-(1 : ℝ))) ∧
      ((∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) ≤ D * z ^ (-(1 : ℝ))) := by
  set S : ℝ := ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2 with hS
  have hS0 : 0 ≤ S := MeasureTheory.integral_nonneg fun p => sq_nonneg _
  have hcm : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 0) := fun m =>
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  refine ⟨S / α ^ 2, by positivity, fun z hz N => ?_⟩
  have hzq : 0 ≤ z ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have hsum := coeffL2_sum_le hsm hL2 N
  -- ## the squared Green's function bound for a single mode
  have hBsq : ∀ m : ℕ, 1 ≤ m →
      (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
        ≤ (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
            * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
    intro m hm
    set C : ℝ := ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 with hC
    set A : ℝ := Work.FTS.PhiStar.Series.acoeff α m F z with hAdef
    have hC0 : 0 ≤ C := by
      rw [hC]; exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
    have hAeq : A = Work.FTS.PhiStar.Radial.radGreen α m
        (Work.FTS.PhiStar.Series.cmode m F) z := by
      rw [hAdef]; rfl
    have hB := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm (hcm m) hz
    have hB' : |A| ≤ Real.sqrt C * z ^ (-(1 / 2) : ℝ)
        / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) := by
      rw [hAeq, hC]
      exact hB
    have hB2 : (Real.sqrt C * z ^ (-(1 / 2) : ℝ)
          / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) ^ 2
        = C * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hC0,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), pow_two, ← Real.rpow_add hz]
      norm_num
      ring
    calc A ^ 2 = |A| ^ 2 := by rw [sq_abs]
      _ = |A| * |A| := by ring
      _ ≤ _ * _ := mul_le_mul hB' hB' (abs_nonneg _) (le_trans (abs_nonneg _) hB')
      _ = (Real.sqrt C * z ^ (-(1 / 2) : ℝ)
          / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) ^ 2 := by ring
      _ = C * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := hB2
  -- ## reduction of a single term to `z⁻¹/α² · eNorm m · ‖cmode m‖²`
  have hred : ∀ m : ℕ, 1 ≤ m →
      (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
          * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
        ≤ z ^ (-(1 : ℝ)) / α ^ 2
            * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
    intro m hm
    have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hD1 : 1 ≤ (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
      nlinarith [hM1, sq_nonneg (4 * (m : ℝ) + 5)]
    have hC0 : 0 ≤ ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 :=
      MeasureTheory.integral_nonneg fun t => sq_nonneg _
    have hD0 : (0 : ℝ) < (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by linarith
    have hden : α ^ 2 * 1 ≤ α ^ 2 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
      nlinarith [hD1, sq_nonneg α, hα]
    have hDne : ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) ≠ 0 := ne_of_gt hD0
    have hgoal : (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
        ≤ z ^ (-(1 : ℝ)) / α ^ 2
          * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
      have hαne : α ^ 2 ≠ 0 := by positivity
      field_simp
      nlinarith [hC0, hzq, hD1, sq_nonneg α, hα,
        mul_nonneg hC0 hzq, mul_nonneg (mul_nonneg hC0 hzq) (le_of_lt hα)]
    exact hgoal
  -- ## the two partial-sum bounds
  constructor
  · have hkey : ∀ m : ℕ,
        Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
          ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
              * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [acoeff_zero_of_orth horth α z]
        have h0 : (0 : ℝ) ≤ z ^ (-(1 : ℝ)) / α ^ 2
            * (Work.EllipticEst.ModalSolution.eNorm 0
              * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode 0 F t) ^ 2) :=
          mul_nonneg (div_nonneg hzq (by positivity))
            (mul_nonneg (eNorm_nonneg 0) (MeasureTheory.integral_nonneg fun t => sq_nonneg _))
        simpa using h0
      · have h1 := hBsq m hm
        have h2 := hred m hm
        have h3 : Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
            ≤ Work.EllipticEst.ModalSolution.eNorm m
              * (z ^ (-(1 : ℝ)) / α ^ 2
                * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) :=
          le_trans (mul_le_mul_of_nonneg_left h1 (eNorm_nonneg m))
            (mul_le_mul_of_nonneg_left h2 (eNorm_nonneg m))
        calc Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
            ≤ Work.EllipticEst.ModalSolution.eNorm m
              * (z ^ (-(1 : ℝ)) / α ^ 2
                * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) := h3
          _ = z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by ring
    refine le_trans (Finset.sum_le_sum fun m _ => hkey m) ?_
    rw [← Finset.mul_sum]
    have hfin := mul_le_mul_of_nonneg_left hsum (div_nonneg hzq (by positivity : (0:ℝ) ≤ α ^ 2))
    rw [hS]
    calc z ^ (-(1 : ℝ)) / α ^ 2 * (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) := hfin
      _ = (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) / α ^ 2 * z ^ (-(1 : ℝ)) := by ring
  · have hkey2 : ∀ m : ℕ,
        Work.FTS.PhiStar.Gegenbauer.lam m * Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
          ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
              * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have hlam0 : Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 := by
          simp only [Work.FTS.PhiStar.Gegenbauer.lam]; norm_num
        rw [hlam0, zero_mul, zero_mul]
        exact mul_nonneg (div_nonneg hzq (by positivity))
          (mul_nonneg (eNorm_nonneg 0) (MeasureTheory.integral_nonneg fun t => sq_nonneg _))
      · have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hD1 : 1 ≤ (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
          nlinarith [hM1, sq_nonneg (4 * (m : ℝ) + 5)]
        have hD0 : (0 : ℝ) < (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by linarith
        have hlam : Work.FTS.PhiStar.Gegenbauer.lam m
            ≤ (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
          rw [Work.FTS.PhiStar.Gegenbauer.lam]
          nlinarith [hM1, sq_nonneg (4 * (m : ℝ) + 5)]
        have h1 := hBsq m hm
        have hE := eNorm_nonneg m
        have hstep1 : Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
            ≤ Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hE) (lam_nonneg' m)
        have hstep2 : Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))))
            ≤ ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_right hlam (by positivity)
        have hX : ∀ Y : ℝ, ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
              * (Y / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) = Y / α ^ 2 := by
          intro Y
          rw [show ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                * (Y / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))
              = Y * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                  / (α ^ 2 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) from by ring]
          exact mul_div_mul_right Y (α ^ 2)
            (by positivity : (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) ≠ 0)
        have hstep3 : ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))))
            = z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
          rw [show ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                * (Work.EllipticEst.ModalSolution.eNorm m
                  * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                      * z ^ (-(1 : ℝ))
                      / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))))
              = Work.EllipticEst.ModalSolution.eNorm m
                * (((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                  * (((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                      * z ^ (-(1 : ℝ)))
                      / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))) from by ring,
            hX ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                * z ^ (-(1 : ℝ)))]
          ring
        have h4 : Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
            ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) :=
          le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))
        calc Work.FTS.PhiStar.Gegenbauer.lam m * Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
            = Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by ring
          _ ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := h4
    refine le_trans (Finset.sum_le_sum fun m _ => hkey2 m) ?_
    rw [← Finset.mul_sum]
    have hfin := mul_le_mul_of_nonneg_left hsum (div_nonneg hzq (by positivity : (0:ℝ) ≤ α ^ 2))
    rw [hS]
    calc z ^ (-(1 : ℝ)) / α ^ 2 * (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) := hfin
      _ = (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) / α ^ 2 * z ^ (-(1 : ℝ)) := by ring

end Work.FTS.H2.ModalSolR
