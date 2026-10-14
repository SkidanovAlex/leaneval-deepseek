import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.bt_prod_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The far-window bound `∫_{farSet} (∂^m (u/cos θ))² sin(2θ)^{2k-γ} ≤ C · FarR`

Route: substitute `x = π/2 - θ ∈ [0, π/8]`, write `v(π/2 - x) = (U/x)·(x/sin x)` with
`U x = u(π/2 - x)` and `x/sin x` a bounded smooth factor, bound the `m`-th derivative by Leibniz
plus Cauchy–Schwarz, use the weighted Hardy division `∫ x^{2j-γ}((U/x)^{(j)})² ≤ 2∫x^{2j-γ}
(U^{(j+1)})²` with a constant uniform in `γ ≥ 1`, and compare the resulting weights with the
slots of `FarR`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## `Real.rpow`-form restatements of the power lemmas

`x ^ y` (an `HPow` application) and `Real.rpow x y` are definitionally but not *syntactically*
the same term, so `rw` needs the following restatements. -/

theorem rpow_neg_r {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : Real.rpow x (-y) = (Real.rpow x y)⁻¹ :=
  Real.rpow_neg hx y

theorem rpow_add_r {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    Real.rpow x (y + z) = Real.rpow x y * Real.rpow x z := Real.rpow_add hx y z

theorem mul_rpow_r {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) :
    Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z := Real.mul_rpow hx hy

theorem div_rpow_r {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) :
    Real.rpow (x / y) z = Real.rpow x z / Real.rpow y z := Real.div_rpow hx hy z

theorem rpow_le_rpow_r {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    Real.rpow x z ≤ Real.rpow y z := Real.rpow_le_rpow hx hxy hz

theorem rpow_le_rpow_of_exponent_ge_r {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) {y z : ℝ}
    (hz : z ≤ y) : Real.rpow x y ≤ Real.rpow x z := Real.rpow_le_rpow_of_exponent_ge h0 h1 hz

theorem rpow_le_rpow_of_exponent_le_r {x : ℝ} (h1 : 1 ≤ x) {y z : ℝ} (hyz : y ≤ z) :
    Real.rpow x y ≤ Real.rpow x z := Real.rpow_le_rpow_of_exponent_le h1 hyz

theorem rpow_le_one_r {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) {y : ℝ} (hy : 0 ≤ y) :
    Real.rpow x y ≤ 1 := Real.rpow_le_one h0 h1 hy

theorem rpow_natCast_r (x : ℝ) (n : ℕ) : Real.rpow x (n : ℝ) = x ^ n := Real.rpow_natCast x n

theorem rpow_pos_r {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < Real.rpow x y := Real.rpow_pos_of_pos hx y

/-! ## Weighted Hardy division with a `γ`-uniform constant -/

/-- **Weighted Hardy division, integral form, with constant `2` uniform in `γ ≥ 1`.**

For `f` of class `C^{j+2}` on `(0,x₁]` with `f → 0` at `0⁺` and `∫ x^{2j-γ}(f^{(j+1)})² < ∞`,
`∫_0^{x₁} x^{2j-γ}((f/x)^{(j)})² ≤ 2∫_0^{x₁} x^{2j-γ}(f^{(j+1)})²`.

(The truncation bound `HardyFin.hardyA_trunc_bound_fin` gives the sub-interval estimate with the
explicit constant `6/(1+γ)² ≤ 3/2 < 2` for `γ ≥ 1`, which the truncation machinery
`Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc` upgrades to `(0,x₁)`.) -/
theorem hardyDiv_int {j : ℕ} (hj : 1 ≤ j) {γ : ℝ} (hγ : 1 ≤ γ) {x₁ : ℝ} (hx₁ : 0 < x₁)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (j + 2) f (Set.Ioc 0 x₁))
    (h0 : Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hw : IntegrableOn
      (fun x : ℝ => x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    (∫ x in (0 : ℝ)..x₁, x ^ (2 * (j : ℝ) - γ) *
        (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2)
      ≤ 2 * (∫ x in (0 : ℝ)..x₁, x ^ (2 * (j : ℝ) - γ) *
          (iteratedDeriv (j + 1) f x) ^ 2) := by
  have hγ' : -1 < γ := by linarith
  have hf' : ContDiffOn ℝ (((j + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioc 0 x₁) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hf
  set u : ℝ → ℝ := fun x => x ^ (2 * (j : ℝ) - γ) *
      (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2 with hu
  set ua : ℝ → ℝ := fun x => |u x| with hua
  set Btot : ℝ := ∫ x in (0 : ℝ)..x₁,
      x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2 with hBtot
  have hgm : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) := by
    have h1 : ContDiffOn ℝ (((j + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      hf'.mono Set.Ioo_subset_Ioc_self
    have h2 : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      h1.of_le (by exact_mod_cast (show j ≤ j + 2 by omega))
    have hid : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) :=
      contDiffOn_id
    have hdiv := h2.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rwa [hfun] at hdiv
  have hvcont : ContinuousOn (fun x : ℝ => iteratedDeriv j (fun y : ℝ => f y / y) x)
      (Set.Ioo 0 x₁) :=
    Work.FTS.EllipticEst.remov.HardyFin.continuousOn_iteratedDeriv_Ioo_fin' hgm le_rfl
  have hucont : ContinuousOn u (Set.Ioo 0 x₁) := by
    rw [hu]
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hvcont.pow 2)
  have huacont : ContinuousOn ua (Set.Ioo 0 x₁) := by
    rw [hua]
    exact hucont.abs
  have hBnn : 0 ≤ Btot := by
    rw [hBtot]
    exact intervalIntegral.integral_nonneg hx₁.le
      (fun t ht => mul_nonneg (Real.rpow_nonneg ht.1 _) (sq_nonneg _))
  have htrunc0 :=
    Work.FTS.EllipticEst.remov.HardyFin.hardyA_trunc_bound_fin j γ x₁ hx₁ hγ' (j + 2) le_rfl
      f hf' h0 hw
  have htrunc : ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x, ua t) ≤ 2 * Btot := by
    intro y x hy hyx hxx₁
    have heq : (∫ t in y..x, ua t) = ∫ t in y..x, u t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      rw [hua]
      exact abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt ht0) _) (sq_nonneg _))
    rw [heq]
    have h6 := htrunc0 y x hy hyx hxx₁
    have h3 : (3 : ℝ) ≤ (1 + γ) ^ 2 := by nlinarith
    have hle : 6 * Btot / (1 + γ) ^ 2 ≤ 2 * Btot := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hua_bound : (∫ t in (0 : ℝ)..x₁, ua t) ≤ 2 * Btot :=
    (Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc hx₁ (fun t => abs_nonneg _) huacont htrunc).2
  have heqfinal : (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t
    intro ht
    rw [Set.uIoc_of_le hx₁.le] at ht
    rw [hua]
    exact (abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _) (sq_nonneg _))).symm
  rw [heqfinal]
  exact hua_bound

/-- `Real.rpow`-form of `hardyDiv_int`. -/
theorem hardyDiv_int_r {j : ℕ} (hj : 1 ≤ j) {γ : ℝ} (hγ : 1 ≤ γ) {x₁ : ℝ} (hx₁ : 0 < x₁)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (j + 2) f (Set.Ioc 0 x₁))
    (h0 : Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hw : IntegrableOn
      (fun x : ℝ => Real.rpow x (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    (∫ x in (0 : ℝ)..x₁, Real.rpow x (2 * (j : ℝ) - γ) *
        (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2)
      ≤ 2 * (∫ x in (0 : ℝ)..x₁, Real.rpow x (2 * (j : ℝ) - γ) *
          (iteratedDeriv (j + 1) f x) ^ 2) :=
  hardyDiv_int hj hγ hx₁ hf h0 hw

/-! ## Pointwise Leibniz bound for `v = (U/x)·(x/sin x)` -/

/-- `x / sin x` is smooth at points where `sin x ≠ 0`. -/
theorem contDiffAt_secH {m : ℕ} {x : ℝ} (hsin : Real.sin x ≠ 0) :
    ContDiffAt ℝ m secH x :=
  contDiffAt_id.div Real.contDiff_sin.contDiffAt hsin

/-- `y ↦ u (π/2 - y) / y` is `C^m` at interior points of the reflected window. -/
theorem contDiffAt_divX {m : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ m u (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xEnd) :
    ContDiffAt ℝ m (fun y : ℝ => shiftU u y / y) x :=
  ((contDiffOn_shiftU hu).contDiffAt (isOpen_Ioo.mem_nhds hx)).div contDiffAt_id
    (ne_of_gt hx.1)

/-- **Pointwise Leibniz bound** for the reflected `v = u / cos θ`. -/
theorem shiftV_deriv_sq_le {u : ℝ → ℝ} {m : ℕ} {K : ℝ}
    (hK : ∀ i ≤ m, ∀ y ∈ Set.Ioc 0 xEnd, |iteratedDeriv i secH y| ≤ K)
    (hu : ContDiffOn ℝ m u (Set.Ioo 0 (Real.pi / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 xEnd) :
    (iteratedDeriv m (shiftV u) x) ^ 2
      ≤ ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
        * ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2 := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
      (by linarith [hx.2, xEnd_lt_pi_half, Real.pi_pos]))
  have hev : (fun y : ℝ => shiftU u y / y) * secH =ᶠ[nhds x] shiftV u := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    simp only [Pi.mul_apply, secH, shiftV, shiftU]
    field_simp
  rw [Filter.EventuallyEq.iteratedDeriv_eq m hev.symm]
  rw [iteratedDeriv_mul (contDiffAt_divX hu hx) (contDiffAt_secH hsin)]
  set F : ℕ → ℝ := fun i => iteratedDeriv i (fun y : ℝ => shiftU u y / y) x with hF
  have hchoose : ∀ i ≤ m, (m.choose i : ℝ) ≤ (2 : ℝ) ^ m := by
    intro i hi
    have hnat : m.choose i ≤ 2 ^ m := by
      calc m.choose i ≤ ∑ j ∈ Finset.range (m + 1), m.choose j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _)
              (by simpa [Finset.mem_range] using Nat.lt_succ_of_le hi)
        _ = 2 ^ m := Nat.sum_range_choose m
    calc (m.choose i : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 : ℝ) ^ m := by push_cast; ring
  have hterm : ∀ i ∈ Finset.range (m + 1),
      |(m.choose i : ℝ) * F i * iteratedDeriv (m - i) secH x| ≤ (2 : ℝ) ^ m * K * |F i| := by
    intro i hi
    have hi' : i ≤ m := by simpa [Finset.mem_range] using hi
    have h2 : |iteratedDeriv (m - i) secH x| ≤ K :=
      hK (m - i) (by omega) x ⟨hx.1, le_of_lt hx.2⟩
    have h1 := hchoose i hi'
    have hmul : (m.choose i : ℝ) * |iteratedDeriv (m - i) secH x| ≤ (2 : ℝ) ^ m * K :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |(m.choose i : ℝ) * F i * iteratedDeriv (m - i) secH x|
        = ((m.choose i : ℝ) * |iteratedDeriv (m - i) secH x|) * |F i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
          ring
      _ ≤ ((2 : ℝ) ^ m * K) * |F i| := mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
      _ = (2 : ℝ) ^ m * K * |F i| := by ring
  have hsum : |∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * F i * iteratedDeriv (m - i) secH x|
      ≤ (2 : ℝ) ^ m * K * ∑ i ∈ Finset.range (m + 1), |F i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsq1 : ((∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * F i * iteratedDeriv (m - i) secH x)) ^ 2
      ≤ ((2 : ℝ) ^ m * K * ∑ i ∈ Finset.range (m + 1), |F i|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hsum 2
  have hcs : (∑ i ∈ Finset.range (m + 1), |F i|) ^ 2
      ≤ ((m + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (m + 1), |F i| ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := fun i => |F i|)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hsq2 : ((∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * F i * iteratedDeriv (m - i) secH x)) ^ 2
      ≤ ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
        * ∑ i ∈ Finset.range (m + 1), |F i| ^ 2 := by
    calc ((∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * F i * iteratedDeriv (m - i) secH x)) ^ 2
        ≤ ((2 : ℝ) ^ m * K * ∑ i ∈ Finset.range (m + 1), |F i|) ^ 2 := hsq1
      _ = ((2 : ℝ) ^ m * K) ^ 2 * (∑ i ∈ Finset.range (m + 1), |F i|) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ m * K) ^ 2
            * (((m + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (m + 1), |F i| ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
            * ∑ i ∈ Finset.range (m + 1), |F i| ^ 2 := by ring
  refine hsq2.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq_abs]

/-! ## Weight comparisons against `sin (2x)` -/

/-- **Weight comparison** for nonnegative exponents: `x^{e+2} ≤ sin(2x)^e` on `(0,π/8]`. -/
theorem rpow_x_le_sin_rpow {e : ℝ} (he : 0 ≤ e) {x : ℝ} (hx : x ∈ Set.Ioc 0 xEnd) :
    x ^ (e + 2) ≤ Real.rpow (Real.sin (2 * x)) e := by
  have hx0 : 0 < x := hx.1
  have hsin0 : 0 < Real.sin (2 * x) := sin_two_pos_Ioc hx
  have hsin1 : Real.sin (2 * x) ≤ 1 := Real.sin_le_one _
  have hxle : x ≤ (Real.pi / 4) * Real.sin (2 * x) := by
    have h0 : 0 ≤ 2 * x := by linarith
    have h1 : 2 * x ≤ Real.pi / 2 := by
      have := hx.2; rw [xEnd] at this; linarith [Real.pi_pos]
    have hm := Real.mul_le_sin h0 h1
    have hrew : (Real.pi / 4) * (2 / Real.pi * (2 * x)) = x := by field_simp; ring
    calc x = (Real.pi / 4) * (2 / Real.pi * (2 * x)) := hrew.symm
      _ ≤ (Real.pi / 4) * Real.sin (2 * x) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
  calc x ^ (e + 2) ≤ ((Real.pi / 4) * Real.sin (2 * x)) ^ (e + 2) :=
        Real.rpow_le_rpow (le_of_lt hx0) hxle (by linarith)
    _ = (Real.pi / 4) ^ (e + 2) * Real.rpow (Real.sin (2 * x)) (e + 2) :=
        Real.mul_rpow (by positivity) (le_of_lt hsin0)
    _ ≤ 1 * Real.rpow (Real.sin (2 * x)) (e + 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hsin0) _)
        refine Real.rpow_le_one (by positivity) ?_ (by linarith)
        rw [div_le_one (by positivity)]
        linarith [Real.pi_lt_four]
    _ = Real.rpow (Real.sin (2 * x)) (e + 2) := one_mul _
    _ ≤ Real.rpow (Real.sin (2 * x)) e :=
        Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1 (by linarith)


/-- Weight comparison for the `η`-slot: `x^{2-γ} ≤ 2^η sin(2x)^{-η}`. -/
theorem rpow_x_le_sin_rpow_eta {γ : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 5 / 4) {x : ℝ}
    (hx : x ∈ Set.Ioc 0 xEnd) :
    x ^ (2 - γ) ≤ (2 : ℝ) ^ Work.Spaces.eta
      * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := le_trans hx.2 xEnd_le_one
  have hsin0 : 0 < Real.sin (2 * x) := sin_two_pos_Ioc hx
  have hsinle : Real.sin (2 * x) ≤ 2 * x := le_of_lt (Real.sin_lt (by linarith))
  -- step 1: `x^{2-γ} ≤ x^{-η}`
  have hstep1 : Real.rpow x (2 - γ) ≤ Real.rpow x (-(Work.Spaces.eta)) :=
    rpow_le_rpow_of_exponent_ge_r hx0 hx1 (by linarith [hγ2, Work.Spaces.eta_pos])
  -- step 2: `x^{-η} ≤ 2^η σ^{-η}`
  have hratio : Real.rpow (Real.sin (2 * x) / x) Work.Spaces.eta
      ≤ Real.rpow (2 : ℝ) Work.Spaces.eta := by
    refine rpow_le_rpow_r (div_nonneg (le_of_lt hsin0) (le_of_lt hx0)) ?_
      (le_of_lt Work.Spaces.eta_pos)
    rw [div_le_iff₀ hx0]
    linarith
  have hdiv : Real.rpow (Real.sin (2 * x) / x) Work.Spaces.eta
      = Real.rpow (Real.sin (2 * x)) Work.Spaces.eta / Real.rpow x Work.Spaces.eta :=
    div_rpow_r (le_of_lt hsin0) (le_of_lt hx0) Work.Spaces.eta
  rw [hdiv, div_eq_mul_inv] at hratio
  have hstep2 : Real.rpow x (-(Work.Spaces.eta)) ≤ (2 : ℝ) ^ Work.Spaces.eta
      * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)) := by
    rw [rpow_neg_r (le_of_lt hx0) Work.Spaces.eta,
      rpow_neg_r (le_of_lt hsin0) Work.Spaces.eta]
    rw [le_mul_inv_iff₀ (rpow_pos_r hsin0 Work.Spaces.eta), mul_comm]
    exact hratio
  exact hstep1.trans hstep2

/-- **The top weight against the `i`-th power weight**: `sin(2x)^{2k-γ} ≤ 2^{2k} x^{2i-γ}`. -/
theorem sin_rpow_le_two_pow_mul {k i : ℕ} {γ : ℝ} (hk : 1 ≤ k) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ 5 / 4) (hik : i ≤ k) {x : ℝ} (hx : x ∈ Set.Ioc 0 xEnd) :
    Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ (2 : ℝ) ^ (2 * k) * Real.rpow x (2 * (i : ℝ) - γ) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := le_trans hx.2 xEnd_le_one
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : (0 : ℝ) ≤ 2 * (k : ℝ) - γ := by linarith
  have h1 : Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ Real.rpow (2 * x) (2 * (k : ℝ) - γ) :=
    rpow_le_rpow_r (le_of_lt (sin_two_pos_Ioc hx))
      (le_of_lt (Real.sin_lt (by linarith))) hexp
  rw [mul_rpow_r (by norm_num) (le_of_lt hx0) (2 * (k : ℝ) - γ)] at h1
  have h2 : Real.rpow (2 : ℝ) (2 * (k : ℝ) - γ) ≤ (2 : ℝ) ^ (2 * k) := by
    have h1' : Real.rpow (2 : ℝ) (2 * (k : ℝ) - γ) ≤ Real.rpow (2 : ℝ) (2 * (k : ℝ)) :=
      rpow_le_rpow_of_exponent_le_r (x := (2 : ℝ)) (y := 2 * (k : ℝ) - γ)
        (z := 2 * (k : ℝ)) (by norm_num) (by linarith)
    have h2' : Real.rpow (2 : ℝ) (2 * (k : ℝ)) = (2 : ℝ) ^ (2 * k) := by
      rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring]
      exact rpow_natCast_r 2 (2 * k)
    linarith
  have h3 : Real.rpow x (2 * (k : ℝ) - γ) ≤ Real.rpow x (2 * (i : ℝ) - γ) :=
    rpow_le_rpow_of_exponent_ge_r hx0 hx1 (by
      have : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
      linarith)
  calc Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ Real.rpow (2 : ℝ) (2 * (k : ℝ) - γ) * Real.rpow x (2 * (k : ℝ) - γ) := h1
    _ ≤ (2 : ℝ) ^ (2 * k) * Real.rpow x (2 * (i : ℝ) - γ) :=
        mul_le_mul h2 h3 (Real.rpow_nonneg (le_of_lt hx0) _) (by positivity)

/-! ## Integrability transfers -/

/-- A.e. strong measurability on `(0,xEnd]` from continuity on `(0,xEnd)`. -/
theorem aestronglyMeasurable_Ioc_of_continuousOn {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Ioo 0 xEnd)) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 xEnd)) := by
  have h1 : AEStronglyMeasurable f (volume.restrict (Set.Ioo 0 xEnd)) :=
    hc.aestronglyMeasurable measurableSet_Ioo
  rwa [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := xEnd))] at h1

/-- Domination of a nonnegative function by a constant multiple of an integrable one. -/
theorem integrableOn_of_le_const_mul {f g : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : IntegrableOn g (Set.Ioc 0 xEnd))
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 xEnd)))
    (h0 : ∀ x ∈ Set.Ioc 0 xEnd, 0 ≤ f x)
    (h : ∀ x ∈ Set.Ioc 0 xEnd, f x ≤ C * g x) :
    IntegrableOn f (Set.Ioc 0 xEnd) := by
  refine (hg.const_mul C).mono' hf ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 x hx)]
  exact h x hx

/-- Monotonicity of the integral over `(0,xEnd]`. -/
theorem integral_Ioc_mono {f g : ℝ → ℝ} (hf : ∀ x ∈ Set.Ioc 0 xEnd, 0 ≤ f x)
    (hg : IntegrableOn g (Set.Ioc 0 xEnd)) (h : ∀ x ∈ Set.Ioc 0 xEnd, f x ≤ g x) :
    (∫ x in Set.Ioc 0 xEnd, f x) ≤ ∫ x in Set.Ioc 0 xEnd, g x := by
  refine integral_mono_of_nonneg ?_ hg ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx; exact hf x hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx; exact h x hx


/-- `fun y ↦ u (π/2 - y) / y` is `C^N` on `(0,xEnd)` when `u` is `C^{N+1}`. -/
theorem contDiffOn_divX {N : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (N + 1) u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ N (fun y : ℝ => shiftU u y / y) (Set.Ioo 0 xEnd) := by
  have h1 : ContDiffOn ℝ (N + 1) (shiftU u) (Set.Ioo 0 xEnd) := contDiffOn_shiftU hu
  have h2 : ContDiffOn ℝ N (shiftU u) (Set.Ioo 0 xEnd) := h1.of_le (by exact_mod_cast (by omega))
  have hid : ContDiffOn ℝ N (fun y : ℝ => y) (Set.Ioo 0 xEnd) := contDiffOn_id
  have hdiv := h2.div hid (fun x hx => ne_of_gt hx.1)
  have hfun : (shiftU u / fun y : ℝ => y) = fun y : ℝ => shiftU u y / y := by
    funext y; rw [Pi.div_apply]
  rwa [hfun] at hdiv

/-- Continuity of the `i`-th divided derivative on `(0,xEnd)`. -/
theorem continuousOn_divXDeriv {N : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (N + 1) u (Set.Ioo 0 (Real.pi / 2))) {i : ℕ} (hi : i ≤ N) :
    ContinuousOn (iteratedDeriv i (fun y : ℝ => shiftU u y / y)) (Set.Ioo 0 xEnd) :=
  Work.FTS.EllipticEst.remov.HardyFin.continuousOn_iteratedDeriv_Ioo_fin' (contDiffOn_divX hu) hi

/-! ## Integrability of the reflected slots -/

theorem rpow_zero_r (x : ℝ) : Real.rpow x 0 = 1 := Real.rpow_zero x

theorem rpow_two_r (x : ℝ) : Real.rpow x 2 = x ^ 2 := Real.rpow_natCast x 2

theorem continuousOn_sin_rpow {p : ℝ} :
    ContinuousOn (fun x : ℝ => Real.rpow (Real.sin (2 * x)) p) (Set.Ioo 0 xEnd) := by
  have hsin : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 xEnd) :=
    Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id)
  refine hsin.rpow_const (fun x hx => Or.inl ?_)
  exact ne_of_gt (sin_two_pos_Ioc ⟨hx.1, le_of_lt hx.2⟩)

theorem continuousOn_shiftU_iteratedDeriv {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {j : ℕ} (hj : j ≤ k + 2) :
    ContinuousOn (iteratedDeriv j (shiftU u)) (Set.Ioo 0 xEnd) :=
  Work.FTS.EllipticEst.remov.HardyFin.continuousOn_iteratedDeriv_Ioo_fin'
    (contDiffOn_shiftU h.huC) hj

theorem integrableOn_shiftU_sq {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g) :
    IntegrableOn (fun x : ℝ => (shiftU u x) ^ 2) (Set.Ioc 0 xEnd) := by
  have hs := integrableOn_shift_slot_Ioc 0 0 u (by simpa using h.hH6)
  refine hs.congr ?_
  filter_upwards with x
  rw [iteratedDeriv_zero, rpow_zero_r, mul_one]

theorem integrableOn_sin2u_sq {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g) :
    IntegrableOn (fun x : ℝ => (iteratedDeriv 2 (shiftU u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta))) (Set.Ioc 0 xEnd) := by
  refine integrableOn_shift_slot_Ioc 2 (-(Work.Spaces.eta)) u ?_
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  exact h.hH4

/-- Integrability of `x^{2i-γ}(U^{(i+1)})²` for `1 ≤ i ≤ k`. -/
theorem integrableOn_xWeight_deriv {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    IntegrableOn
      (fun x : ℝ => Real.rpow x (2 * (i : ℝ) - γ) * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2)
      (Set.Ioc 0 xEnd) := by
  have hγ0 : (0 : ℝ) ≤ γ := by linarith [h.hγ1]
  have hcont : ContinuousOn (iteratedDeriv (i + 1) (shiftU u)) (Set.Ioo 0 xEnd) :=
    continuousOn_shiftU_iteratedDeriv h (by omega)
  have haesm : AEStronglyMeasurable
      (fun x : ℝ => Real.rpow x (2 * (i : ℝ) - γ) * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2)
      (volume.restrict (Set.Ioc 0 xEnd)) :=
    aestronglyMeasurable_Ioc_of_continuousOn
      ((continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hcont.pow 2))
  have h0 : ∀ x ∈ Set.Ioc 0 xEnd,
      0 ≤ Real.rpow x (2 * (i : ℝ) - γ) * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2 :=
    fun x hx => mul_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _) (sq_nonneg _)
  rcases eq_or_lt_of_le hi1 with h1 | h2
  · subst h1
    have hslot := integrableOn_sin2u_sq h
    refine integrableOn_of_le_const_mul (C := (2 : ℝ) ^ Work.Spaces.eta)
      (by positivity) hslot haesm h0 ?_
    intro x hx
    have hcmp : Real.rpow x (2 * ((1 : ℕ) : ℝ) - γ) ≤ (2 : ℝ) ^ Work.Spaces.eta
        * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)) := by
      simpa using rpow_x_le_sin_rpow_eta h.hγ1 h.hγ2 hx
    calc Real.rpow x (2 * ((1 : ℕ) : ℝ) - γ) * (iteratedDeriv (1 + 1) (shiftU u) x) ^ 2
        ≤ ((2 : ℝ) ^ Work.Spaces.eta
            * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)))
            * (iteratedDeriv (1 + 1) (shiftU u) x) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (2 : ℝ) ^ Work.Spaces.eta
            * ((iteratedDeriv (1 + 1) (shiftU u) x) ^ 2
              * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta))) := by ring
  · have hi2 : 2 ≤ i := h2
    have hslot := integrableOn_shift_slot_Ioc (i + 1) (2 * ((i + 1 : ℕ) : ℝ) - 4 - γ) u
      (h.hH3 (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    have he : (0 : ℝ) ≤ 2 * ((i : ℕ) : ℝ) - 2 - γ := by
      have hi2' : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
      linarith [h.hγ2]
    refine integrableOn_of_le_const_mul (C := 1) zero_le_one hslot haesm h0 ?_
    intro x hx
    have hexp : 2 * ((i + 1 : ℕ) : ℝ) - 4 - γ = 2 * (i : ℝ) - 2 - γ := by push_cast; ring
    rw [hexp]
    have hcmp : Real.rpow x (2 * (i : ℝ) - γ)
        ≤ Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ) := by
      have hh := rpow_x_le_sin_rpow (e := 2 * (i : ℝ) - 2 - γ) he hx
      rwa [show 2 * (i : ℝ) - 2 - γ + 2 = 2 * (i : ℝ) - γ by ring] at hh
    calc Real.rpow x (2 * (i : ℝ) - γ) * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2
        ≤ Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ)
            * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = 1 * ((iteratedDeriv (i + 1) (shiftU u) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ)) := by ring

/-- Integrability of `x^{2i-γ}((U/x)^{(i)})²` for `1 ≤ i ≤ k` (Hardy division). -/
theorem integrableOn_xDivX {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    IntegrableOn (fun x : ℝ =>
        Real.rpow x (2 * (i : ℝ) - γ) * (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2)
      (Set.Ioc 0 xEnd) := by
  obtain ⟨C, _hC, hmain⟩ := hardyDiv_fin i γ (by linarith [h.hγ1]) xEnd xEnd_pos
  have hfd : ContDiffOn ℝ (i + 2) (shiftU u) (Set.Ioc 0 xEnd) :=
    (contDiffOn_shiftU_Ioc (N := k + 2) h.huC).of_le
      (by exact_mod_cast (by omega : i + 2 ≤ k + 2))
  have hw : IntegrableOn (fun x : ℝ => x ^ (2 * (i : ℝ) - γ)
      * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2) (Set.Ioc 0 xEnd) :=
    integrableOn_xWeight_deriv h hi1 hik
  exact (hmain (shiftU u) hfd (tendsto_shiftU h.hucont h.hupi) hw).1

/-- The `i`-th reflected divided derivative against the top weight is integrable. -/
theorem integrableOn_sinWeight_xDivX {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ}
    (h : FarHyp k γ u g) {i : ℕ} (hik : i ≤ k) :
    IntegrableOn (fun x : ℝ =>
        (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) (Set.Ioc 0 xEnd) := by
  have hγ0 : (0 : ℝ) ≤ γ := by linarith [h.hγ1]
  have hk1 : 1 ≤ k := by omega
  have hk2 : (2 : ℕ) ≤ k := hk
  rcases Nat.eq_zero_or_pos i with h0 | hi1
  · subst h0
    have haesm : AEStronglyMeasurable
        (fun x : ℝ => (iteratedDeriv 0 (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (volume.restrict (Set.Ioc 0 xEnd)) := by
      refine aestronglyMeasurable_Ioc_of_continuousOn ?_
      have h1 : ContinuousOn (fun x : ℝ => shiftU u x / x) (Set.Ioo 0 xEnd) :=
        (contDiffOn_shiftU h.huC).continuousOn.div continuousOn_id (fun x hx => ne_of_gt hx.1)
      exact (h1.pow 2).mul (continuousOn_sin_rpow (p := 2 * (k : ℝ) - γ))
    have h0' : ∀ x ∈ Set.Ioc 0 xEnd,
        0 ≤ (iteratedDeriv 0 (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      fun x hx => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
    refine integrableOn_of_le_const_mul (C := (2 : ℝ) ^ (2 * k))
      (by positivity) (integrableOn_shiftU_sq h) haesm h0' ?_
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := le_trans hx.2 xEnd_le_one
    have hs := sin_rpow_le_two_pow_mul (k := k) (i := k) (γ := γ) hk1 hγ0 h.hγ2
      (le_refl k) hx
    have hsplit : Real.rpow x (2 * (k : ℝ) - γ)
        = Real.rpow x (2 * (k : ℝ) - γ - 2) * Real.rpow x 2 := by
      rw [← rpow_add_r hx0 (2 * (k : ℝ) - γ - 2) 2]
      ring_nf
    have hx2 : Real.rpow x (2 * (k : ℝ) - γ - 2) ≤ 1 := by
      refine rpow_le_one_r (le_of_lt hx0) hx1 ?_
      have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith [h.hγ2]
    have hkey : Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (2 : ℝ) ^ (2 * k) * Real.rpow x 2 := by
      rw [hsplit] at hs
      calc Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
          ≤ (2 : ℝ) ^ (2 * k) * (Real.rpow x (2 * (k : ℝ) - γ - 2) * Real.rpow x 2) := hs
        _ ≤ (2 : ℝ) ^ (2 * k) * (1 * Real.rpow x 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg (le_of_lt hx0) 2)
        _ = (2 : ℝ) ^ (2 * k) * Real.rpow x 2 := by ring
    calc (iteratedDeriv 0 (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        = (shiftU u x / x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) := by
          rw [iteratedDeriv_zero]
      _ ≤ (shiftU u x / x) ^ 2 * ((2 : ℝ) ^ (2 * k) * Real.rpow x 2) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = (2 : ℝ) ^ (2 * k) * (shiftU u x) ^ 2 := by
          have hxne : x ≠ 0 := ne_of_gt hx0
          have hcancel : (shiftU u x / x) ^ 2 * Real.rpow x 2 = (shiftU u x) ^ 2 := by
            rw [rpow_two_r x, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hxne)]
          rw [show (shiftU u x / x) ^ 2 * ((2 : ℝ) ^ (2 * k) * Real.rpow x 2)
              = (2 : ℝ) ^ (2 * k) * ((shiftU u x / x) ^ 2 * Real.rpow x 2) from by ring,
            hcancel]
  · have haesm : AEStronglyMeasurable
        (fun x : ℝ => (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        (volume.restrict (Set.Ioc 0 xEnd)) := by
      refine aestronglyMeasurable_Ioc_of_continuousOn ?_
      have h1 : ContinuousOn (iteratedDeriv i (fun y : ℝ => shiftU u y / y)) (Set.Ioo 0 xEnd) :=
        continuousOn_divXDeriv (N := k + 1) h.huC (by omega)
      exact (h1.pow 2).mul (continuousOn_sin_rpow (p := 2 * (k : ℝ) - γ))
    have h0' : ∀ x ∈ Set.Ioc 0 xEnd,
        0 ≤ (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      fun x hx => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
    refine integrableOn_of_le_const_mul (C := (2 : ℝ) ^ (2 * k))
      (by positivity) (integrableOn_xDivX h hi1 hik) haesm h0' ?_
    intro x hx
    have hs := sin_rpow_le_two_pow_mul (k := k) (i := i) (γ := γ) hk1 hγ0 h.hγ2 hik hx
    calc (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
            * ((2 : ℝ) ^ (2 * k) * Real.rpow x (2 * (i : ℝ) - γ)) :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ = (2 : ℝ) ^ (2 * k) * (Real.rpow x (2 * (i : ℝ) - γ)
            * (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2) := by ring

/-! ## Slot bounds against `FarR` -/

theorem farSet_slot_le_FarR {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {j : ℕ} (hj3 : 3 ≤ j) (hjk : j ≤ k + 1) :
    (∫ θ in farSet, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) ≤ FarR k γ u g := by
  have hmem : j ∈ Finset.Icc 3 (k + 1) := Finset.mem_Icc.mpr ⟨hj3, hjk⟩
  have hInt := h.hH3 j hmem
  have hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (iteratedDeriv j u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) := fun θ hθ =>
    mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)
  have h1 := farIntegral_le_Iθ hInt hnn
  have hsum : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
      ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j' u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.single_le_sum
      (f := fun j' => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j' u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ))
      (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ))) hmem
  have h2' : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg hθ))
  have h4 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h5 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have h6 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  simp only [FarR]
  linarith

theorem farSet_eta_le_FarR {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g) :
    (∫ θ in farSet, (iteratedDeriv 2 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) ≤ FarR k γ u g := by
  have hder : iteratedDeriv 2 u = deriv (deriv u) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  have hInt : IntegrableOn (fun θ : ℝ => (iteratedDeriv 2 u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    rw [hder]; exact h.hH4
  have hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (iteratedDeriv 2 u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  have h1 := farIntegral_le_Iθ hInt hnn
  have h2' : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg hθ))
  have h3' : (0 : ℝ) ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j' u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)))
  have h5 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have h6 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hEq : (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
      = ∫ θ in Work.Spaces.Iθ, (iteratedDeriv 2 u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by rw [hder]
  simp only [FarR]
  linarith

theorem farSet_u2_le_FarR {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g) :
    (∫ θ in farSet, (u θ) ^ 2) ≤ FarR k γ u g := by
  have h1 := farIntegral_le_Iθ h.hH6 (fun θ _ => sq_nonneg _)
  have h2' : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg hθ))
  have h3' : (0 : ℝ) ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j' u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)))
  have h4 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have h5 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  simp only [FarR]
  linarith

/-! ## The per-derivative bound and the assembly -/

/-- Pointwise domination of the `i = 0` term: `(U/x)² sin(2x)^{2k-γ} ≤ 2^{2k}U²`. -/
theorem xDivX0_le {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ2 : γ ≤ 5 / 4)
    {u : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioc 0 xEnd) :
    (shiftU u x / x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ (2 : ℝ) ^ (2 * k) * (shiftU u x) ^ 2 := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := le_trans hx.2 xEnd_le_one
  have hk1 : 1 ≤ k := by omega
  have hs := sin_rpow_le_two_pow_mul (k := k) (i := k) (γ := γ) hk1 hγ0 hγ2 (le_refl k) hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hsplit : Real.rpow x (2 * (k : ℝ) - γ)
      = Real.rpow x (2 * (k : ℝ) - γ - 2) * Real.rpow x 2 := by
    rw [← rpow_add_r hx0 (2 * (k : ℝ) - γ - 2) 2]
    ring_nf
  have hx2 : Real.rpow x (2 * (k : ℝ) - γ - 2) ≤ 1 := by
    refine rpow_le_one_r (le_of_lt hx0) hx1 ?_
    have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [hγ2]
  have hkey : Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ (2 : ℝ) ^ (2 * k) * Real.rpow x 2 := by
    rw [hsplit] at hs
    calc Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (2 : ℝ) ^ (2 * k) * (Real.rpow x (2 * (k : ℝ) - γ - 2) * Real.rpow x 2) := hs
      _ ≤ (2 : ℝ) ^ (2 * k) * (1 * Real.rpow x 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hx2 (Real.rpow_nonneg (le_of_lt hx0) 2)
      _ = (2 : ℝ) ^ (2 * k) * Real.rpow x 2 := by ring
  have hcancel : (shiftU u x / x) ^ 2 * Real.rpow x 2 = (shiftU u x) ^ 2 := by
    rw [rpow_two_r x, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hxne)]
  calc (shiftU u x / x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ (shiftU u x / x) ^ 2 * ((2 : ℝ) ^ (2 * k) * Real.rpow x 2) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = (2 : ℝ) ^ (2 * k) * (shiftU u x) ^ 2 := by
        rw [show (shiftU u x / x) ^ 2 * ((2 : ℝ) ^ (2 * k) * Real.rpow x 2)
            = (2 : ℝ) ^ (2 * k) * ((shiftU u x / x) ^ 2 * Real.rpow x 2) from by ring,
          hcancel]

/-- Pointwise domination for `i ≥ 1`: `(W_i)² sin(2x)^{2k-γ} ≤ 2^{2k} x^{2i-γ}(W_i)²`. -/
theorem xDivX_le {k : ℕ} (hk : 1 ≤ k) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ2 : γ ≤ 5 / 4)
    {u : ℝ → ℝ} {i : ℕ} (hik : i ≤ k) {x : ℝ} (hx : x ∈ Set.Ioc 0 xEnd) :
    (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ (2 : ℝ) ^ (2 * k) * (Real.rpow x (2 * (i : ℝ) - γ)
          * (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2) := by
  have hs := sin_rpow_le_two_pow_mul hk hγ0 hγ2 hik hx
  calc (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
      ≤ (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
          * ((2 : ℝ) ^ (2 * k) * Real.rpow x (2 * (i : ℝ) - γ)) :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (2 : ℝ) ^ (2 * k) * (Real.rpow x (2 * (i : ℝ) - γ)
          * (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2) := by ring

/-- **The `i`-th reflected divided derivative against the top weight.** -/
theorem xTerm_le {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {i : ℕ} (hik : i ≤ k) :
    (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ (2 : ℝ) ^ (2 * k + 3) * FarR k γ u g := by
  have hγ0 : (0 : ℝ) ≤ γ := by linarith [h.hγ1]
  have hγ1 : (1 : ℝ) ≤ γ := h.hγ1
  have hk1 : 1 ≤ k := by omega
  have hFarR : (0 : ℝ) ≤ FarR k γ u g := FarR_nonneg hk h
  have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
  rcases Nat.eq_zero_or_pos i with h0 | hi1
  · subst h0
    rw [show (fun x : ℝ => (iteratedDeriv 0 (fun y : ℝ => shiftU u y / y) x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        = (fun x : ℝ => (shiftU u x / x) ^ 2
          * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) from by
      funext x; rw [iteratedDeriv_zero]]
    have hstep1 : (∫ x in (0 : ℝ)..xEnd, (shiftU u x / x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ (2 : ℝ) ^ (2 * k) * (∫ x in (0 : ℝ)..xEnd, (shiftU u x) ^ 2) := by
      rw [intervalIntegral.integral_of_le xEnd_pos.le,
        intervalIntegral.integral_of_le xEnd_pos.le, ← MeasureTheory.integral_const_mul]
      refine integral_Ioc_mono ?_ ((integrableOn_shiftU_sq h).const_mul _) ?_
      · intro x hx
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
      · intro x hx
        exact xDivX0_le hk hγ0 h.hγ2 hx
    have hstep2 : (∫ x in (0 : ℝ)..xEnd, (shiftU u x) ^ 2) ≤ FarR k γ u g := by
      have hh : (∫ θ in farSet, (u θ) ^ 2) = (∫ x in (0 : ℝ)..xEnd, (shiftU u x) ^ 2) := by
        have hh' := integral_farSet_slot_eq 0 0 u
        simpa [iteratedDeriv_zero, rpow_zero_r] using hh'
      rw [← hh]
      exact farSet_u2_le_FarR hk h
    have harith : (2 : ℝ) ^ (2 * k) * FarR k γ u g
        ≤ (2 : ℝ) ^ (2 * k + 3) * FarR k γ u g := by
      have hle : (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (2 * k + 3) := by
        rw [pow_add]
        nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (2 * k) by positivity]
      exact mul_le_mul_of_nonneg_right hle hFarR
    exact (hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (le_of_lt h2k))).trans harith
  · -- `i ≥ 1`
    have hA : (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ (2 : ℝ) ^ (2 * k) * (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
            * (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2) := by
      rw [intervalIntegral.integral_of_le xEnd_pos.le,
        intervalIntegral.integral_of_le xEnd_pos.le, ← MeasureTheory.integral_const_mul]
      refine integral_Ioc_mono ?_ ((integrableOn_xDivX h hi1 hik).const_mul _) ?_
      · intro x hx
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
      · intro x hx
        exact xDivX_le hk1 hγ0 h.hγ2 hik hx
    have hB : (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
        * (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2)
        ≤ 2 * (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
            * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2) :=
      hardyDiv_int_r hi1 hγ1 xEnd_pos
        ((contDiffOn_shiftU_Ioc (N := k + 2) h.huC).of_le
          (by exact_mod_cast (by omega : i + 2 ≤ k + 2)))
        (tendsto_shiftU h.hucont h.hupi) (integrableOn_xWeight_deriv h hi1 hik)
    have hB' : (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
        * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2) ≤ 4 * FarR k γ u g := by
      have hi1' : 1 ≤ i := by omega
      rcases eq_or_lt_of_le hi1' with h1 | h2
      · subst h1
        have hstep : (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * ((1 : ℕ) : ℝ) - γ)
              * (iteratedDeriv (1 + 1) (shiftU u) x) ^ 2)
            ≤ (2 : ℝ) ^ Work.Spaces.eta * (∫ x in (0 : ℝ)..xEnd,
                (iteratedDeriv 2 (shiftU u) x) ^ 2
                  * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta))) := by
          rw [intervalIntegral.integral_of_le xEnd_pos.le,
            intervalIntegral.integral_of_le xEnd_pos.le, ← MeasureTheory.integral_const_mul]
          refine integral_Ioc_mono ?_ ((integrableOn_sin2u_sq h).const_mul _) ?_
          · intro x hx
            exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _) (sq_nonneg _)
          · intro x hx
            have hcmp : Real.rpow x (2 * ((1 : ℕ) : ℝ) - γ)
                ≤ (2 : ℝ) ^ Work.Spaces.eta
                  * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)) := by
              simpa using rpow_x_le_sin_rpow_eta h.hγ1 h.hγ2 hx
            calc Real.rpow x (2 * ((1 : ℕ) : ℝ) - γ) * (iteratedDeriv 2 (shiftU u) x) ^ 2
                ≤ ((2 : ℝ) ^ Work.Spaces.eta
                    * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)))
                    * (iteratedDeriv 2 (shiftU u) x) ^ 2 :=
                  mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
              _ = (2 : ℝ) ^ Work.Spaces.eta
                    * ((iteratedDeriv 2 (shiftU u) x) ^ 2
                      * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta))) := by ring
        have hη : (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv 2 (shiftU u) x) ^ 2
              * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta))) ≤ FarR k γ u g := by
          have hh : (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv 2 (shiftU u) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta)))
              = ∫ θ in farSet, (iteratedDeriv 2 u θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
            (integral_farSet_slot_eq 2 (-(Work.Spaces.eta)) u).symm
          rw [hh]
          exact farSet_eta_le_FarR hk h
        have heta : (2 : ℝ) ^ Work.Spaces.eta ≤ 4 := by
          have h1' : Real.rpow (2 : ℝ) Work.Spaces.eta ≤ 4 := by
            have h2' : Real.rpow (2 : ℝ) Work.Spaces.eta ≤ Real.rpow (2 : ℝ) 2 :=
              rpow_le_rpow_of_exponent_le_r (x := (2 : ℝ)) (y := Work.Spaces.eta) (z := 2)
                (by norm_num) (by linarith [Work.Spaces.eta_lt_one])
            rwa [rpow_two_r, show (2 : ℝ) ^ 2 = 4 by norm_num] at h2'
          exact h1'
        calc (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * ((1 : ℕ) : ℝ) - γ)
              * (iteratedDeriv (1 + 1) (shiftU u) x) ^ 2)
            ≤ (2 : ℝ) ^ Work.Spaces.eta * (∫ x in (0 : ℝ)..xEnd,
                (iteratedDeriv 2 (shiftU u) x) ^ 2
                  * Real.rpow (Real.sin (2 * x)) (-(Work.Spaces.eta))) := hstep
          _ ≤ (2 : ℝ) ^ Work.Spaces.eta * FarR k γ u g :=
              mul_le_mul_of_nonneg_left hη (by positivity)
          _ ≤ 4 * FarR k γ u g := by nlinarith [hFarR, heta]
      · have hi2 : 2 ≤ i := h2
        have he : (0 : ℝ) ≤ 2 * (i : ℝ) - 2 - γ := by
          have hi2' : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
          linarith [h.hγ2]
        have hstep : (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
              * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2)
            ≤ (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv (i + 1) (shiftU u) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ)) := by
          rw [intervalIntegral.integral_of_le xEnd_pos.le,
            intervalIntegral.integral_of_le xEnd_pos.le]
          refine integral_Ioc_mono ?_ ?_ ?_
          · intro x hx
            exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx.1) _) (sq_nonneg _)
          · exact integrableOn_shift_slot_Ioc (i + 1) (2 * (i : ℝ) - 2 - γ) u
              (by
                convert h.hH3 (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) using 2
                push_cast; ring)
          · intro x hx
            have hcmp : Real.rpow x (2 * (i : ℝ) - γ)
                ≤ Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ) := by
              have hh := rpow_x_le_sin_rpow (e := 2 * (i : ℝ) - 2 - γ) he hx
              rwa [show 2 * (i : ℝ) - 2 - γ + 2 = 2 * (i : ℝ) - γ by ring] at hh
            calc Real.rpow x (2 * (i : ℝ) - γ) * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2
                ≤ Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ)
                    * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2 :=
                  mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
              _ = (iteratedDeriv (i + 1) (shiftU u) x) ^ 2
                    * Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ) := by ring
        have hsub : (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv (i + 1) (shiftU u) x) ^ 2
              * Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ))
            = ∫ θ in farSet, (iteratedDeriv (i + 1) u θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (i : ℝ) - 2 - γ) := by
          exact (integral_farSet_slot_eq (i + 1) (2 * (i : ℝ) - 2 - γ) u).symm
        have hslot : (∫ θ in farSet, (iteratedDeriv (i + 1) u θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (i : ℝ) - 2 - γ)) ≤ FarR k γ u g := by
          rw [show 2 * (i : ℝ) - 2 - γ = 2 * ((i + 1 : ℕ) : ℝ) - 4 - γ by push_cast; ring]
          exact farSet_slot_le_FarR hk h (by omega) (by omega)
        calc (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
              * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2)
            ≤ (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv (i + 1) (shiftU u) x) ^ 2
                * Real.rpow (Real.sin (2 * x)) (2 * (i : ℝ) - 2 - γ)) := hstep
          _ = _ := hsub
          _ ≤ FarR k γ u g := hslot
          _ ≤ 4 * FarR k γ u g := by nlinarith [hFarR]
    have harith : (2 : ℝ) ^ (2 * k) * (2 * (4 * FarR k γ u g))
        ≤ (2 : ℝ) ^ (2 * k + 3) * FarR k γ u g := by
      rw [pow_add]
      have h8 : (2 : ℝ) ^ 3 = 8 := by norm_num
      nlinarith [hFarR]
    have hB'' : 2 * (∫ x in (0 : ℝ)..xEnd, Real.rpow x (2 * (i : ℝ) - γ)
        * (iteratedDeriv (i + 1) (shiftU u) x) ^ 2) ≤ 2 * (4 * FarR k γ u g) :=
      mul_le_mul_of_nonneg_left hB' (by norm_num)
    exact (hA.trans (mul_le_mul_of_nonneg_left (hB.trans hB'') (le_of_lt h2k))).trans harith

/-- **The reflected `m`-th derivative bound.** -/
theorem xLHS_le {k : ℕ} (hk : 2 ≤ k) {γ : ℝ} {u g : ℝ → ℝ} (h : FarHyp k γ u g)
    {m : ℕ} (hm : m ≤ k) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ i ≤ m, ∀ y ∈ Set.Ioc 0 xEnd, |iteratedDeriv i secH y| ≤ K) :
    (∫ θ in farSet, (iteratedDeriv m (vF u) θ) ^ 2 * qW k γ θ)
      ≤ ((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
          * (2 : ℝ) ^ (2 * k + 3) * FarR k γ u g := by
  have hFarR : (0 : ℝ) ≤ FarR k γ u g := FarR_nonneg hk h
  have huC : ContDiffOn ℝ m u (Set.Ioo 0 (Real.pi / 2)) :=
    h.huC.of_le (by exact_mod_cast (by omega : m ≤ k + 2))
  rw [farSet_LHS_eq]
  set A : ℝ := ((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set G : ℝ → ℝ := fun x => A * ∑ i ∈ Finset.range (m + 1),
      ((iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) with hG
  have hGint : IntegrableOn G (Set.Ioc 0 xEnd) := by
    rw [hG]
    exact (MeasureTheory.integrable_finsetSum (Finset.range (m + 1))
      (fun i hi => integrableOn_sinWeight_xDivX hk h
        (le_trans (by simpa [Finset.mem_range] using hi) hm))).const_mul A
  have hpoint : ∀ᵐ x ∂(volume.restrict (Set.Ioc 0 xEnd)),
      (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ G x := by
    have hsub : ∀ᵐ x ∂(volume.restrict (Set.Ioc 0 xEnd)), x ∈ Set.Ioo 0 xEnd := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := xEnd))]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => hx)
    filter_upwards [hsub] with x hx
    have hw_nn : 0 ≤ Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, le_of_lt hx.2⟩) _
    have h1 := shiftV_deriv_sq_le (u := u) (m := m) (K := K) hK huC hx
    calc (iteratedDeriv m (shiftV u) x) ^ 2 * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)
        ≤ (((2 : ℝ) ^ m * K) ^ 2 * ((m + 1 : ℕ) : ℝ)
            * ∑ i ∈ Finset.range (m + 1),
                (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2)
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ) :=
          mul_le_mul_of_nonneg_right h1 hw_nn
      _ = G x := by
          simp only [hG, hA]
          rw [← Finset.sum_mul]
          ring
  have hstep1 : (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv m (shiftV u) x) ^ 2
      * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) ≤ ∫ x in (0 : ℝ)..xEnd, G x := by
    rw [intervalIntegral.integral_of_le xEnd_pos.le, intervalIntegral.integral_of_le xEnd_pos.le]
    refine integral_mono_of_nonneg ?_ hGint hpoint
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Ioc ⟨hx.1, hx.2⟩) _)
  have hsplit : (∫ x in Set.Ioc 0 xEnd, G x) = A * ∑ i ∈ Finset.range (m + 1),
      (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := by
    rw [hG, MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum (Finset.range (m + 1))
      (fun i hi => integrableOn_sinWeight_xDivX hk h
        (le_trans (by simpa [Finset.mem_range] using hi) hm))
  have hsum : ∑ i ∈ Finset.range (m + 1),
      (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g) := by
    calc ∑ i ∈ Finset.range (m + 1),
          (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
        ≤ ∑ i ∈ Finset.range (m + 1), ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [← intervalIntegral.integral_of_le xEnd_pos.le]
          exact xTerm_le hk h (le_trans (by simpa [Finset.mem_range] using hi) hm)
      _ = ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hAb : A ≤ ((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) := by
    rw [hA]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) hK0
    · exact_mod_cast (by omega : m + 1 ≤ k + 1)
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m + 1 ≤ k + 1)
  calc (∫ x in (0 : ℝ)..xEnd, (iteratedDeriv m (shiftV u) x) ^ 2
        * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ))
      ≤ ∫ x in (0 : ℝ)..xEnd, G x := hstep1
    _ = ∫ x in Set.Ioc 0 xEnd, G x := by rw [intervalIntegral.integral_of_le xEnd_pos.le]
    _ = A * ∑ i ∈ Finset.range (m + 1),
          (∫ x in Set.Ioc 0 xEnd, (iteratedDeriv i (fun y : ℝ => shiftU u y / y) x) ^ 2
            * Real.rpow (Real.sin (2 * x)) (2 * (k : ℝ) - γ)) := hsplit
    _ ≤ A * (((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g)) :=
        mul_le_mul_of_nonneg_left hsum hA0
    _ ≤ (((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ))
          * (((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * k + 3) * FarR k γ u g)) := by
        refine mul_le_mul hAb ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hm1 (by positivity)
    _ = ((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
          * (2 : ℝ) ^ (2 * k + 3) * FarR k γ u g := by ring

/-- **The far-window bound for `∂^m v`, `v = u/cos θ`** (the target of this file). -/
theorem far_vBound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.TopCoreB.FarHyp k γ u g →
      ∀ m : ℕ, m ≤ k →
        (∫ θ in Work.FTS.EllipticEst.remov.TopCoreB.farSet,
            (iteratedDeriv m (Work.FTS.EllipticEst.remov.TopCoreB.vF u) θ) ^ 2
              * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
          ≤ C * Work.FTS.EllipticEst.remov.TopCoreB.FarR k γ u g := by
  obtain ⟨K, hKpos, hKb⟩ := sinDivDerivBounds k
  refine ⟨((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
      * (2 : ℝ) ^ (2 * k + 3) + 1, by positivity, ?_⟩
  intro γ u g hF m hm
  have hK : ∀ i ≤ m, ∀ y ∈ Set.Ioc 0 xEnd, |iteratedDeriv i secH y| ≤ K :=
    fun i hi y hy => hKb i (le_trans hi hm) y hy
  have hbound := xLHS_le hk hF hm (le_of_lt hKpos) hK
  have hC : (0 : ℝ) < ((2 : ℝ) ^ k * K) ^ 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
      * (2 : ℝ) ^ (2 * k + 3) + 1 := by positivity
  nlinarith [hbound, FarR_nonneg hk hF, hC]

end Work.FTS.EllipticEst.remov.TopCoreB
