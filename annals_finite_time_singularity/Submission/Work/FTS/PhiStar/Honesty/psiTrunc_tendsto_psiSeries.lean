/-
# `Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries`

The partial sums of the mode series converge to the `tsum` defining `psiSeries`: at every point
of the open quadrant the mode series is *absolutely* summable, so `psiSeries` is the honest sum
and the partial sums `psiTrunc α F N z θ` converge to it.

**Route.**  Bessel's inequality for the angular Dirichlet basis (`coeffL2_sum_le`) gives

  `∑_{m} eNorm m · ‖cmode m F‖²_{L²(0,∞)} ≤ ∫_{Q0} F²`,

and `eNorm m = (2m+2)(2m+3)/(4m+5) ≥ m`, so the sequence

  `D_m = √m · √(∫_0^∞ (cmode m F t)² dt)`

is in `ℓ²`.  The radial Green's-function bound `radGreen_abs_le` gives

  `|acoeff α m F z| ≤ √(∫ c_m²) z^{-1/2}/(α(4m+5)√m) = D_m z^{-1/2}/(α(4m+5)m)`   (`m ≥ 1`),

and the uniform sup bound `eFam_sup_le` gives `|eFam m θ| ≤ Ce (m+1)`.  Hence each mode term is
dominated by `K · D_m/(m+1)`, and `∑_m D_m/(m+1) < ∞` by AM–GM (`D_m/(m+1) ≤ (D_m² +
1/(m+1)²)/2`).  `Summable.of_norm_bounded` then yields summability of the mode family; the
`m = 0` term is irrelevant (shift by one), and `HasSum.tendsto_sum_nat` converts summability into
convergence of the range-partial sums.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.H2.ModalSolR.LimitFacts
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem psiTrunc_tendsto_psiSeries {α : ℝ} {F : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (horth : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
      (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)) := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  obtain ⟨Ce, hCe, hCeb⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have hcm : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) :=
    fun m => Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  have hcnn : ∀ m : ℕ, 0 ≤ ∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2 :=
    fun m => MeasureTheory.integral_nonneg (fun t => sq_nonneg _)
  -- `B m = ‖cmode m F‖_{L²(0,∞)}`, `D m = √m · B m`
  set B : ℕ → ℝ := fun m => Real.sqrt
    (∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2) with hBdef
  set D : ℕ → ℝ := fun m => Real.sqrt (m : ℝ) * B m with hDdef
  have hBnn : ∀ m : ℕ, 0 ≤ B m := fun m => Real.sqrt_nonneg _
  have hBsq : ∀ m : ℕ, B m ^ 2 = ∫ t in Set.Ioi 0,
      Work.FTS.PhiStar.Series.cmode m F t ^ 2 := fun m => Real.sq_sqrt (hcnn m)
  have hDnn : ∀ m : ℕ, 0 ≤ D m := fun m =>
    mul_nonneg (Real.sqrt_nonneg _) (hBnn m)
  have hDsq : ∀ m : ℕ, D m ^ 2 = (m : ℝ) *
      ∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2 := by
    intro m
    rw [hDdef, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), hBsq m]
  -- ## Bessel: `∑ D m² ≤ ∫_{Q0} F²`
  have hDsum : Summable (fun m : ℕ => D m ^ 2) := by
    have hle : ∀ j : ℕ, (j : ℝ) ≤ Work.EllipticEst.ModalSolution.eNorm j := by
      intro j
      rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (j : ℝ) + 5)]
      nlinarith [hj]
    have hstep : ∀ j : ℕ, (j : ℝ) * ∫ t in Set.Ioi 0,
          Work.FTS.PhiStar.Series.cmode j F t ^ 2
        ≤ Work.EllipticEst.ModalSolution.eNorm j * ∫ t in Set.Ioi 0,
          Work.FTS.PhiStar.Series.cmode j F t ^ 2 :=
      fun j => mul_le_mul_of_nonneg_right (hle j) (hcnn j)
    have hbd : ∀ N : ℕ, ∑ j ∈ Finset.range N, (j : ℝ) * ∫ t in Set.Ioi 0,
        Work.FTS.PhiStar.Series.cmode j F t ^ 2
        ≤ ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2 := by
      intro N
      refine le_trans (Finset.sum_le_sum (fun j _ => hstep j)) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (Nat.le_succ N))
        (fun j _ _ => mul_nonneg (Work.EllipticEst.ModalSolution.eNorm_pos j).le (hcnn j)))
        (Work.FTS.H2.ModalSolR.coeffL2_sum_le hsm hL2 N)
    have hsum := summable_of_sum_range_le
      (f := fun j : ℕ => (j : ℝ) * ∫ t in Set.Ioi 0,
        Work.FTS.PhiStar.Series.cmode j F t ^ 2)
      (fun j => mul_nonneg (Nat.cast_nonneg j) (hcnn j)) hbd
    refine hsum.congr (fun m => ?_)
    rw [hDsq m]
  -- ## the summable majorant `D m / (m+1)`
  have hgeo : Summable (fun m : ℕ => D m / ((m : ℝ) + 1)) := by
    have hone : Summable (fun m : ℕ => (1 / ((m : ℝ) + 1)) ^ 2) := by
      have h2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h3 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
        have h4 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h2
        simpa only [Nat.cast_add, Nat.cast_one] using h4
      refine h3.congr (fun m => ?_)
      rw [div_pow, one_pow]
    have h2 : Summable (fun m : ℕ => (D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) / 2) :=
      (hDsum.add hone).div_const 2
    refine Summable.of_nonneg_of_le (fun m => div_nonneg (hDnn m) (by positivity))
      (fun m => ?_) h2
    have hmain : 2 * (D m / ((m : ℝ) + 1))
        ≤ D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2 := by
      have h := two_mul_le_add_sq (D m) (1 / ((m : ℝ) + 1))
      have hrw : 2 * (D m / ((m : ℝ) + 1)) = 2 * D m * (1 / ((m : ℝ) + 1)) := by ring
      rw [hrw]
      exact h
    have hhalf : (D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) / 2
        = (1 / 2) * (D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) := by ring
    rw [hhalf]
    linarith [hmain]
  -- ## the pointwise bound on the mode terms, `m ≥ 1`
  have hterm : ∀ m : ℕ, 1 ≤ m →
      ‖Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ (Ce * z ^ (-(1 / 2) : ℝ) / α) * (D m / ((m : ℝ) + 1)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hrm0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
    have hsqm : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm0.le
    have hrad := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm (hcm m) hz
    have hE := hCeb m θ hIθ
    have hden : 0 < α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) :=
      mul_pos (mul_pos hα (by linarith)) hrm0
    have hBm0 : 0 ≤ B m * z ^ (-(1 / 2) : ℝ) :=
      mul_nonneg (hBnn m) (Real.rpow_nonneg hz.le (-(1 / 2)))
    have hcoef : 0 ≤ B m * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) :=
      div_nonneg hBm0 hden.le
    have hcore : |Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.Series.cmode m F) z|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤
        (B m * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)))
          * (Ce * ((m : ℝ) + 1)) :=
      mul_le_mul hrad hE (abs_nonneg _) hcoef
    have hkey : ((m : ℝ) + 1) ^ 2 ≤ (m : ℝ) * (4 * (m : ℝ) + 5) := by nlinarith
    have hfac : (B m * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)))
          * (Ce * ((m : ℝ) + 1))
        = (Ce * z ^ (-(1 / 2) : ℝ) / α)
          * (B m * ((m : ℝ) + 1) / ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) := by
      have h1 : Real.sqrt (m : ℝ) ≠ 0 := hrm0.ne'
      have h2 : α ≠ 0 := hα.ne'
      have h3 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
      field_simp
      try ring
    have hDrel : D m = Real.sqrt (m : ℝ) * B m := by rw [hDdef]
    have htail : B m * ((m : ℝ) + 1) / ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))
        ≤ D m / ((m : ℝ) + 1) := by
      have hle : B m * ((m : ℝ) + 1) * ((m : ℝ) + 1)
          ≤ D m * ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) := by
        rw [hDrel]
        calc B m * ((m : ℝ) + 1) * ((m : ℝ) + 1) = B m * (((m : ℝ) + 1) ^ 2) := by ring
          _ ≤ B m * ((m : ℝ) * (4 * (m : ℝ) + 5)) :=
              mul_le_mul_of_nonneg_left hkey (hBnn m)
          _ = B m * ((4 * (m : ℝ) + 5) * (m : ℝ)) := by ring
          _ = B m * ((4 * (m : ℝ) + 5) * (Real.sqrt (m : ℝ)) ^ 2) := by rw [hsqm]
          _ = (Real.sqrt (m : ℝ) * B m) * ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) := by ring
      have hb : 0 < (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) :=
        mul_pos (by linarith) hrm0
      have hd : 0 < (m : ℝ) + 1 := by linarith
      rw [div_le_div_iff₀ hb hd]
      exact hle
    have hKnn : 0 ≤ Ce * z ^ (-(1 / 2) : ℝ) / α :=
      div_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg hz.le (-(1 / 2)))) hα.le
    rw [Real.norm_eq_abs, abs_mul]
    change |Work.FTS.PhiStar.Radial.radGreen α m
        (Work.FTS.PhiStar.Series.cmode m F) z|
      * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ (Ce * z ^ (-(1 / 2) : ℝ) / α) * (D m / ((m : ℝ) + 1))
    refine le_trans hcore ?_
    rw [hfac]
    exact mul_le_mul_of_nonneg_left htail hKnn
  -- ## summability of the shifted mode family, hence of the family itself
  have hKs : Summable (fun n : ℕ => (Ce * z ^ (-(1 / 2) : ℝ) / α)
      * (D (n + 1) / (((n + 1 : ℕ) : ℝ) + 1))) := by
    have hbase : Summable (fun m : ℕ => (Ce * z ^ (-(1 / 2) : ℝ) / α)
        * (D m / ((m : ℝ) + 1))) := hgeo.mul_left _
    exact (summable_nat_add_iff
      (f := fun m : ℕ => (Ce * z ^ (-(1 / 2) : ℝ) / α) * (D m / ((m : ℝ) + 1))) 1).mpr hbase
  have hshift : Summable (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α (n + 1) F z
      * Work.FTS.PhiStar.Gegenbauer.eFam (n + 1) θ) :=
    Summable.of_norm_bounded hKs (fun n => hterm (n + 1) (by omega))
  have hfam : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m F z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := (summable_nat_add_iff 1).mp hshift
  -- ## concluding
  show Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    Filter.atTop (nhds (∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ))
  have hfun : (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = ((fun n : ℕ => ∑ m ∈ Finset.range n,
          Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        ∘ fun N : ℕ => N + 1) := by
    funext N
    rfl
  rw [hfun]
  exact hfam.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

end Work.FTS.PhiStar.Honesty
