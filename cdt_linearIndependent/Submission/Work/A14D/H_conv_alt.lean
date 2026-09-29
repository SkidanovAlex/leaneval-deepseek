import Mathlib
import Submission.Work.A14.defs
import Submission.Work.ALift.ode_hold_A
import Submission.Work.ALift.coef_bound_A
import Submission.Work.C17f.differentiableOn_of_hasSum_powSeries
import Submission.Work.C17f.deriv_hasSum_powSeries

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators

noncomputable section

/-! ## 1. The coefficient bound for `H = a·H_A + b·H_B + c·H_C`

Under the absurd relation the overconvergence of `functionsH` gives, for every `ρ < 1`, a
constant `C` with `‖h_k‖ ≤ C·ρ^{-k}`.  This is the analytic input that makes the series of `H`
converge on the whole unit disc (not merely on `‖q‖ ≤ 9/10`, which is all the continuation
argument of area `ALift` needs). -/

/-- For every `ρ ∈ (0,1)` the coefficients of `H = aH_A + bH_B + cH_C` are bounded by
`C·ρ^{-k}`: the overconvergence statement `functionsH_overconverges`. -/
lemma Hcoef_bound (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ‖Work.ALift.hcoef a b c k‖ ≤ C / ρ ^ k := by
  have hrel' : ((a : ℚ) : ℝ) + ((b : ℚ) : ℝ) * (Submission.CDT.L2chi3Real / 2)
      + ((c : ℚ) : ℝ) * (Submission.CDT.zeta2Real / 4) = 0 := by
    have hh := hRel
    unfold Submission.CDTPlan.ARel at hh
    push_cast
    exact hh
  have hclean := Work.Purge.a_side_clean
  have hB : Submission.CDT.OverconvergesUnit Submission.CDT.eichlerDiffB :=
    hclean.2.2.2.2.2.2.1
  have hC : Submission.CDT.OverconvergesUnit Submission.CDT.eichlerDiffC :=
    hclean.2.2.2.2.2.2.2
  obtain ⟨C, hC0, hCb⟩ :=
    Submission.CDT.functionsH_overconverges (a : ℚ) (b : ℚ) (c : ℚ) hrel' hB hC ρ hρ0 hρ1
  refine ⟨C, hC0, fun k => ?_⟩
  have h1 : Work.ALift.hcoef a b c k
      = ((Submission.CDT.ZagierH_coeff_seq (a : ℚ) (b : ℚ) (c : ℚ) k : ℚ) : ℂ) := by
    unfold Work.ALift.hcoef Submission.CDTPlan.HZ Submission.CDT.ZagierH_coeff_seq
    rw [Submission.CDT.ZagierH_coeff]
  rw [h1, Complex.norm_ratCast]
  exact hCb k

/-- A sequence dominated by `C·ρ^{-k}` with `‖z‖ < ρ` has absolutely summable `z`-series. -/
lemma summable_norm_of_bounded (z : ℂ) {ρ C : ℝ} (hρ : 0 < ρ) (_hC : 0 ≤ C)
    {f : ℕ → ℂ} (hb : ∀ k : ℕ, ‖f k‖ ≤ C / ρ ^ k) (hz : ‖z‖ < ρ) :
    Summable (fun k : ℕ => ‖f k * z ^ k‖) := by
  have ht0 : 0 ≤ ‖z‖ / ρ := div_nonneg (norm_nonneg z) hρ.le
  have ht1 : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hz
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one ht0 ht1).mul_left C)
  calc ‖f k * z ^ k‖ = ‖f k‖ * ‖z‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ (C / ρ ^ k) * ‖z‖ ^ k :=
          mul_le_mul_of_nonneg_right (hb k) (by positivity)
    _ = C * (‖z‖ / ρ) ^ k := by rw [div_pow]; ring

/-- The coefficient series of `H` is absolutely summable everywhere on the open unit disc. -/
lemma summ_H0 (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ)
    (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖Work.ALift.hcoef a b c k * z ^ k‖) := by
  obtain ⟨ρ, hzρ, hρ1⟩ : ∃ ρ : ℝ, ‖z‖ < ρ ∧ ρ < 1 :=
    ⟨(‖z‖ + 1) / 2, by linarith, by linarith⟩
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  obtain ⟨C, hC0, hCb⟩ := Hcoef_bound a b c hRel hρ0 hρ1
  exact summable_norm_of_bounded z hρ0 hC0.le hCb hzρ

/-- The power series of `H` converges on the open unit disc, to the `tsum` defining `Hfun`. -/
lemma hasSum_Hfun (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ)
    (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => Work.ALift.hcoef a b c k * z ^ k) (Hfun a b c z) := by
  have hs : Summable (fun k : ℕ => Work.ALift.hcoef a b c k * z ^ k) :=
    Summable.of_norm (summ_H0 a b c hRel z hz)
  exact hs.hasSum

/-! ## 2. Differentiability and the derivative series on the unit disc -/

lemma diffOn_Hfun (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) :
    DifferentiableOn ℂ (Hfun a b c) (Metric.ball 0 1) :=
  Work.C17f.differentiableOn_of_hasSum_powSeries
    (fun z hz => hasSum_Hfun a b c hRel z hz)

/-- Term-by-term differentiation: the derivative series of `H` is `HU1`. -/
lemma deriv_Hfun (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ)
    (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => ((k : ℂ) + 1) * Work.ALift.hcoef a b c (k + 1) * z ^ k)
      (deriv (Hfun a b c) z) :=
  Work.C17f.deriv_hasSum_powSeries (Work.ALift.hcoef a b c) 1 (Hfun a b c)
    (fun z hz => hasSum_Hfun a b c hRel z hz) z hz

lemma deriv_Hfun_eq (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ)
    (hz : ‖z‖ < 1) :
    deriv (Hfun a b c) z = Work.ALift.HU1 a b c z := by
  have h := deriv_Hfun a b c hRel z hz
  rw [← h.tsum_eq, Work.ALift.HU1]

/-- The second derivative series of `H` is `HU2`. -/
lemma deriv2_Hfun (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ)
    (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => ((k : ℂ) + 1) * ((k : ℂ) + 2) * Work.ALift.hcoef a b c (k + 2) * z ^ k)
      (deriv (deriv (Hfun a b c)) z) := by
  have h := Work.C17f.deriv_hasSum_powSeries
    (fun k : ℕ => ((k : ℂ) + 1) * Work.ALift.hcoef a b c (k + 1))
    1 (deriv (Hfun a b c)) (fun z hz => deriv_Hfun a b c hRel z hz) z hz
  refine h.congr_fun (fun k => ?_)
  push_cast
  ring

lemma deriv2_Hfun_eq (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ)
    (hz : ‖z‖ < 1) :
    deriv (deriv (Hfun a b c)) z = Work.ALift.HU2 a b c z := by
  have h := deriv2_Hfun a b c hRel z hz
  rw [← h.tsum_eq, Work.ALift.HU2]

/-! ## 3. Zagier's operator on the whole unit disc

This is the `‖·‖ ≤ 9/10` statement `Work.ALift.HU_ode` of the continuation area, upgraded to the
whole disc by replacing its `11/10`-coefficient bound by the overconvergence bound on an
arbitrary `ρ < 1`. -/

lemma HU_ode_gen (a b c : ℤ) (hRel : Submission.CDTPlan.ARel a b c) (z : ℂ) (hz : ‖z‖ < 1) :
    Work.ALift.Pd z * Work.ALift.HU2 a b c z + Work.ALift.Qd z * Work.ALift.HU1 a b c z
      + Work.ALift.Rd z * Work.ALift.HU0 a b c z = Work.ALift.rhsA b c z := by
  have hsu0 : Summable (fun k : ℕ => ‖Work.ALift.hcoef a b c k * z ^ k‖) :=
    summ_H0 a b c hRel z hz
  have hsu1 : Summable
      (fun k : ℕ => ‖((k : ℂ) + 1) * Work.ALift.hcoef a b c (k + 1) * z ^ k‖) :=
    (deriv_Hfun a b c hRel z hz).summable.norm
  have hsu2 : Summable
      (fun k : ℕ => ‖((k : ℂ) + 1) * ((k : ℂ) + 2) * Work.ALift.hcoef a b c (k + 2) * z ^ k‖) :=
    (deriv2_Hfun a b c hRel z hz).summable.norm
  have sd1 : Summable (fun k : ℕ => ‖((PowerSeries.coeff k
      (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.HZ a b c)) : ℚ) : ℂ) * z ^ k‖) := by
    refine hsu1.congr (fun k => ?_)
    rw [PowerSeries.coeff_derivative]
    unfold Work.ALift.hcoef
    push_cast
    ring
  have sd2 : Summable (fun k : ℕ => ‖((PowerSeries.coeff k
      (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.HZ a b c))) : ℚ)
        : ℂ) * z ^ k‖) := by
    refine hsu2.congr (fun k => ?_)
    rw [Commons.RingTheory.PowerSeries.coeff_der2]
    unfold Work.ALift.hcoef
    push_cast
    ring
  have sd0 : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Submission.CDTPlan.HZ a b c) : ℚ)
      : ℂ) * z ^ k‖) := by
    refine hsu0.congr (fun k => ?_)
    rfl
  have sP : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Work.ALift.Pdpoly : PowerSeries ℚ)
      : ℚ) : ℂ) * z ^ k‖) := Work.CLift.summable_norm_poly Work.ALift.Pdpoly z
  have sQ : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Work.ALift.Qdpoly : PowerSeries ℚ)
      : ℚ) : ℂ) * z ^ k‖) := Work.CLift.summable_norm_poly Work.ALift.Qdpoly z
  have sR : Summable (fun k : ℕ => ‖((PowerSeries.coeff k (Work.ALift.Rdpoly : PowerSeries ℚ)
      : ℚ) : ℂ) * z ^ k‖) := Work.CLift.summable_norm_poly Work.ALift.Rdpoly z
  have hsP := Work.CLift.evA_mul_hasSum (Work.ALift.Pdpoly : PowerSeries ℚ)
    (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.HZ a b c))) z sP sd2
  have hsQ := Work.CLift.evA_mul_hasSum (Work.ALift.Qdpoly : PowerSeries ℚ)
    (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.HZ a b c)) z sQ sd1
  have hsR := Work.CLift.evA_mul_hasSum (Work.ALift.Rdpoly : PowerSeries ℚ)
    (Submission.CDTPlan.HZ a b c) z sR sd0
  rw [Work.ALift.evA_Pd, Work.ALift.evA_deriv2_H] at hsP
  rw [Work.ALift.evA_Qd, Work.ALift.evA_deriv_H] at hsQ
  rw [Work.ALift.evA_Rd, Work.ALift.evA_H] at hsR
  have hcomb := (hsP.add hsQ).add hsR
  have hevL : Work.CLift.evA (Submission.CDT.HA_odeLHS (Submission.CDTPlan.HZ a b c)) z
      = Work.ALift.Pd z * Work.ALift.HU2 a b c z
        + Work.ALift.Qd z * Work.ALift.HU1 a b c z
        + Work.ALift.Rd z * Work.ALift.HU0 a b c z := by
    rw [Work.CLift.evA]
    refine (hcomb.congr_fun (fun k => ?_)).tsum_eq
    have hc : PowerSeries.coeff k (Submission.CDT.HA_odeLHS (Submission.CDTPlan.HZ a b c))
        = PowerSeries.coeff k ((Work.ALift.Pdpoly : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)
              (PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.HZ a b c))))
          + PowerSeries.coeff k ((Work.ALift.Qdpoly : PowerSeries ℚ)
              * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.HZ a b c))
          + PowerSeries.coeff k ((Work.ALift.Rdpoly : PowerSeries ℚ)
              * Submission.CDTPlan.HZ a b c) := by
      rw [Work.ALift.HA_odeLHS_eq, ← Work.ALift.Pdpoly_coe, ← Work.ALift.Qdpoly_coe,
        ← Work.ALift.Rdpoly_coe, map_add, map_add]
    rw [hc]
    push_cast
    ring
  rw [← hevL, Work.ALift.HZ_odeLHS a b c, Work.ALift.evA_rhs b c z hz]

/-! ## 4. The target -/

/-- The `x`-side series `H = a·H_A + b·H_B + c·H_C`, viewed through the power-series sum
`Hfun a b c z = Σ_k h_k z^k`, converges on the unit disc and satisfies Zagier's order-two
operator `LZ y = PZ·y'' + PZ'·y' + RZ·y` there with inhomogeneity `rhsZ b c z = b + c/(1-z)`. -/
theorem H_conv_alt (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) :
    DifferentiableOn ℂ (Hfun a b c) (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, LZ (Hfun a b c) z = rhsZ b c z := by
  refine ⟨diffOn_Hfun a b c h, fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hd1 := deriv_Hfun_eq a b c h z hz
  have hd2 := deriv2_Hfun_eq a b c h z hz
  have hode := HU_ode_gen a b c h z hz
  simp only [LZ]
  rw [hd2, hd1]
  have hRd : RZ z = Work.ALift.Rd z := by unfold RZ Work.ALift.Rd; ring
  have hPZ : PZ z = Work.ALift.Pd z := rfl
  have hPZ' : PZ' z = Work.ALift.Qd z := rfl
  have hrhs : rhsZ b c z = Work.ALift.rhsA b c z := rfl
  have hH0 : Hfun a b c z = Work.ALift.HU0 a b c z := rfl
  rw [hRd, hPZ, hPZ', hrhs, hH0]
  exact hode

end

end Work.A14D
