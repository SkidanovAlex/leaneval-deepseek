import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.EllExist.Honesty.G1Aux
import Submission.Work.FTS.EllExist.Honesty.G1_endpoint_bound
import Submission.Work.FTS.EllExist.Honesty.G1_energy_identity
import Submission.Work.FTS.EllExist.Honesty.G1_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

-- ROUTE (the `z → 0` half of the weighted `L²`-honesty of the `z^{s⁻}` Green term of `radGreen`).
-- Let `a := (2*(m:ℝ)+5)/α > 0` (from `hα`), `A z := ∫ t in (0:ℝ)..z, c t * t^(a-1)`,
-- `Φ := Work.FTS.EllExist.Honesty.G1 α m c` (so `Φ z = z^(-a) * A z`), and
-- `M0 := ∫ z in Ioo 0 1, c z^2/z^4` — a NONNEGATIVE real number, finite because `c z^2/z^4 ≥ 0` is
-- integrable by `h0`.
--
-- (1) For `z > 0`: `z * deriv Φ z = -a * Φ z + c z`  (product rule; `A' = c z * z^{a-1}` and
--     `z^(-a) * z^(a-1) = 1/z`, via `Real.rpow_add` with `0 < z`).
-- (2) Energy identity.  `u z := Φ z^2 / z^3` satisfies `u' z = ((-2a-3)*Φ z^2 + 2*c z*Φ z)/z^4`, so the
--     FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) on `[x,y] ⊆ (0,1)` gives
--       `(3+2a) * ∫ z in x..y, Φ z^2/z^4 = 2 * ∫ z in x..y, c z * Φ z / z^4 + Φ x^2/x^3 - Φ y^2/y^3`.
-- (3) ENDPOINT (this is the delicate step).  The pointwise Cauchy–Schwarz bound
--     `|Φ z| ≤ z^(3/2) * √(M0/(2a+3))` only gives `Φ z^2/z^4 = O(1/z)`, which is NOT integrable, so it cannot
--     be used directly; but it is exactly enough for the endpoint term.  Equivalently (avoiding a
--     substitution): the `x`-dependent AM-GM `2*|X*Y| ≤ λ*X^2 + Y^2/λ` with `X = |c u|*u^{-1}`, `Y = u^a`
--     and `λ := x^(a-1/2) > 0` gives, using `∫ u in (0)..x, c u^2/u^2 ≤ x^2 * M0`,
--       `|A x| ≤ x^(a+3/2) * C0`,  `C0 := M0/2 + 1/(2*(2a+1))`,
--     hence `Φ x^2/x^3 ≤ CΦ := C0^2` for every `x ∈ (0,1]`.
-- (4) AM-GM `2*|c z * Φ z|/z^4 ≤ η*c z^2/z^4 + η^{-1}*Φ z^2/z^4` with `η := 2/(3+2a)` (`3+2a > 0`),
--     combined with `∫ z in x..y, c z^2/z^4 ≤ M0` (monotonicity of the integral, `(x,y) ⊆ (0,1)`),
--     yields `∫ z in x..y, Φ z^2/z^4 ≤ M := 2*(η*M0 + CΦ)/(3+2a)` uniformly for all `0 < x < y < 1`.
-- (5) Continuity of `Φ` on `(0,1)`: product of `z ↦ z^(-a)` (continuous on `Ioi 0`) and the primitive `A`
--     (`MeasureTheory.continuousOn_primitive_interval`, or the FTC for primitives); integrability of
--     `t ↦ c t * t^(a-1)` on `[0,1]` follows from `h0` and the AM-GM bound
--     `2*|c t| * t^(a-1) ≤ c t^2/t^4 + t^(2a+2)` (both summands are integrable on `(0,1)`).
--
-- PROOF (as formalised): the three ingredients are the auxiliary file `G1Aux` (`a`, `A`, `M0`, `C0`,
-- `CΦ = C0²`, `η`, `M = 2(η M0 + CΦ)/(3+2a)`, `G1f_integrableOn`, `G1A_algebra: G1A_hasDerivAt`,
-- `G1_two_mul_abs_mul_le_mul`, `G1_csq_mono`) together with the three proved lemmas
-- `G1_endpoint_bound` (3), `G1_energy_identity` (2) and `G1_continuousOn` (5); the remaining step (4)
-- is the AM–GM comparison of interval integrals carried out below.
theorem G1_est (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x y : ℝ, 0 < x → x < y → y < 1 →
        (∫ z in x..y, Work.FTS.EllExist.Honesty.G1 α m c z ^ 2 / z ^ 4) ≤ M) ∧
      ContinuousOn (fun z => Work.FTS.EllExist.Honesty.G1 α m c z) (Set.Ioo 0 1) := by
  refine ⟨⟨G1M α m c, G1M_nonneg hα m c, ?_⟩, G1_continuousOn hα m hc h0⟩
  intro x y hx hxy hy1
  have hη : 0 < G1eta α m := G1eta_pos hα m
  have hIn : ∀ z ∈ Set.Icc x y, (0 : ℝ) < z := fun z hz => lt_of_lt_of_le hx hz.1
  have hsub : Set.Icc x y ⊆ Set.Ioo (0 : ℝ) 1 := fun z hz =>
    ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy1⟩
  have hΦc : ContinuousOn (G1 α m c) (Set.Icc x y) :=
    (G1_continuousOn hα m hc h0).mono hsub
  have hcc : ContinuousOn c (Set.Icc x y) :=
    hc.mono (fun z hz => lt_of_lt_of_le hx hz.1)
  have hpow : ContinuousOn (fun z : ℝ => z ^ 4) (Set.Icc x y) := continuousOn_id.pow 4
  have hz4ne : ∀ z ∈ Set.Icc x y, z ^ 4 ≠ 0 := fun z hz => pow_ne_zero 4 (ne_of_gt (hIn z hz))
  -- pointwise AM–GM
  have hpt : ∀ z ∈ Set.Icc x y,
      2 * |c z * G1 α m c z / z ^ 4|
        ≤ G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4) := by
    intro z hz
    have h := G1_two_mul_abs_mul_le_mul (l := G1eta α m) (X := c z / z ^ 2)
      (Y := G1 α m c z / z ^ 2) hη
    have e1 : (c z / z ^ 2) * (G1 α m c z / z ^ 2) = c z * G1 α m c z / z ^ 4 := by
      rw [div_mul_div_comm, show z ^ 2 * z ^ 2 = z ^ 4 from by ring]
    have e2 : G1eta α m * (c z / z ^ 2) ^ 2 + (G1 α m c z / z ^ 2) ^ 2 / G1eta α m
        = G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4) := by
      rw [div_pow, div_pow, div_eq_mul_inv]
      field_simp
    rwa [e1, e2] at h
  -- continuity / interval integrability of the two comparison functions
  have hcont1 : ContinuousOn (fun z : ℝ => 2 * |c z * G1 α m c z / z ^ 4|) (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy.le]
    exact continuousOn_const.mul (ContinuousOn.abs (ContinuousOn.div (hcc.mul hΦc) hpow hz4ne))
  have hcont2 : ContinuousOn
      (fun z : ℝ => G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4))
      (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy.le]
    exact ContinuousOn.add (continuousOn_const.mul (ContinuousOn.div (hcc.pow 2) hpow hz4ne))
      (continuousOn_const.mul (ContinuousOn.div (hΦc.pow 2) hpow hz4ne))
  have hI1 : IntervalIntegrable (fun z : ℝ => 2 * |c z * G1 α m c z / z ^ 4|) volume x y :=
    ContinuousOn.intervalIntegrable hcont1
  have hI2 : IntervalIntegrable
      (fun z : ℝ => G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4))
      volume x y := ContinuousOn.intervalIntegrable hcont2
  have hIc : IntervalIntegrable (fun z : ℝ => c z ^ 2 / z ^ 4) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy.le]
    exact ContinuousOn.div (hcc.pow 2) hpow hz4ne
  have hIg : IntervalIntegrable (fun z : ℝ => G1 α m c z ^ 2 / z ^ 4) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy.le]
    exact ContinuousOn.div (hΦc.pow 2) hpow hz4ne
  -- linearity
  have hlin : (∫ z in x..y,
        G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4))
      = G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4)
        + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    rw [intervalIntegral.integral_add (hIc.const_mul (G1eta α m)) (hIg.const_mul (G1eta α m)⁻¹),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the AM–GM step
  have hmono_int := intervalIntegral.integral_mono_on hxy.le hI1 hI2 hpt
  have h2I2 : 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
      ≤ ∫ z in x..y, 2 * |c z * G1 α m c z / z ^ 4| := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun z : ℝ => c z * G1 α m c z / z ^ 4) hxy.le
    have hle : (∫ z in x..y, c z * G1 α m c z / z ^ 4)
        ≤ ∫ z in x..y, |c z * G1 α m c z / z ^ 4| := le_trans (le_abs_self _) habs
    have hmul : 2 * (∫ z in x..y, |c z * G1 α m c z / z ^ 4|)
        = ∫ z in x..y, 2 * |c z * G1 α m c z / z ^ 4| := by
      rw [intervalIntegral.integral_const_mul]
    linarith
  have hA : 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
      ≤ G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4)
        + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) :=
    le_trans h2I2 (le_trans hmono_int (le_of_eq hlin))
  have hcsq := G1_csq_mono h0 x y hx hxy hy1
  have hB : G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4) ≤ G1eta α m * G1M0 c :=
    mul_le_mul_of_nonneg_left hcsq (le_of_lt hη)
  have hei := G1_energy_identity hα m hc h0 x y hx hxy hy1
  have hend := G1_endpoint_bound hα m hc h0 x hx (hxy.trans hy1)
  have hy0 : (0 : ℝ) < y := lt_trans hx hxy
  have hyend : 0 ≤ G1 α m c y ^ 2 / y ^ 3 :=
    div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hy0) 3)
  have h3 : (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      ≤ G1eta α m * G1M0 c + G1CPhi α m c
        + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    calc (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
          + G1 α m c x ^ 2 / x ^ 3 - G1 α m c y ^ 2 / y ^ 3 := hei
      _ ≤ 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4) + G1CPhi α m c := by
          linarith [hend, hyend]
      _ ≤ (G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4)
            + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)) + G1CPhi α m c := by
          linarith [hA]
      _ ≤ (G1eta α m * G1M0 c
            + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)) + G1CPhi α m c := by
          linarith [hB]
      _ = G1eta α m * G1M0 c + G1CPhi α m c
            + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by ring
  have heta : 3 + 2 * G1a α m - (G1eta α m)⁻¹ = (G1eta α m)⁻¹ := by
    rw [G1eta, inv_div]; ring
  have hcoef : (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
        - (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      = (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    rw [← sub_mul, heta]
  have key : (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      ≤ G1eta α m * G1M0 c + G1CPhi α m c := by linarith [h3, hcoef]
  have hM : G1M α m c = G1eta α m * (G1eta α m * G1M0 c + G1CPhi α m c) := by
    rw [G1M, G1eta]
    have h3a : 3 + 2 * G1a α m ≠ 0 := by
      have := G1a_pos hα m; intro hc0; linarith [hc0]
    field_simp
  rw [hM]
  calc (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      = G1eta α m * ((G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη), one_mul]
    _ ≤ G1eta α m * (G1eta α m * G1M0 c + G1CPhi α m c) :=
        mul_le_mul_of_nonneg_left key (le_of_lt hη)

end Work.FTS.EllExist.Honesty
