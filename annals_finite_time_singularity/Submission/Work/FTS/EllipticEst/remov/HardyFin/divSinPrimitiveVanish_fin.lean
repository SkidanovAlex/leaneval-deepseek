import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllipticEst.remov.HardyFin.Basic
import Submission.Work.FTS.H2.DivQ.divSinPrimitiveVanish
import Submission.Work.FTS.H2.DivQ.hardyIter_tendsto_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Filter Set
open scoped Topology

/-- Finite-order version of the private base case `Work.FTS.H2.DivQ.van_baseCase` of
`Submission/Work/FTS/H2/DivQ/divSinPrimitiveVanish.lean`: the `C^∞` hypothesis is replaced by
`ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)`, and the order `N` is assumed `≥ k + 1`.  The smoothness is
used only at `iteratedDeriv (k+1) f`, through `continuousOn_iteratedDeriv_Icc_fin` and
`intervalIntegral_iteratedDeriv_succ_fin`. -/
private lemma van_baseCase_fin (k : ℕ) (hk : 1 ≤ k) {γ x₁ : ℝ} (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {N : ℕ} (hN : k + 1 ≤ N) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hB : IntegrableOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    Filter.Tendsto (fun x : ℝ => x ^ k * iteratedDeriv k f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the tail of the weighted integral is small for small `δ`
  have hΨ : Filter.Tendsto
      (fun δ : ℝ => ∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2)
      (nhds 0) (nhds 0) := Work.FTS.H2.DivQ.hardyIter_tendsto_zero hx₁ hB
  have hEv₁ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 4 :=
    Filter.Tendsto.eventually_lt (hΨ.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (by linarith)
  have hEv₂ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have hEv₃ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < x₁ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx₁)
  obtain ⟨δ, hδpos, hδx, hδsmall⟩ := (hEv₂.and (hEv₃.and hEv₁)).exists
  -- the two decay inputs at the level of `x`
  have hq : 0 < ((2 * k : ℕ) : ℝ) + (γ - 2 * (k : ℝ)) + 1 := by
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  have hA : Filter.Tendsto
      (fun x : ℝ => (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := Work.FTS.H2.DivQ.van_powMul_rpow_integral (2 * k) (γ - 2 * (k : ℝ))
      (by omega) hq hδpos
    have h := h0.const_mul (1 / 2 : ℝ)
    refine Filter.Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring
  have hA' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))) < ε / 2 :=
    Filter.Tendsto.eventually_lt hA tendsto_const_nhds (by linarith)
  have hC : Filter.Tendsto (fun x : ℝ => x ^ k * |iteratedDeriv k f δ|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h := (hid.pow k).mul_const |iteratedDeriv k f δ|
    simpa [zero_pow (by omega : k ≠ 0)] using h
  have hC' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ k * |iteratedDeriv k f δ| < ε / 4 :=
    Filter.Tendsto.eventually_lt hC tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hA', hC'] with x hx hxA hxC
  have hxk : 0 < x ^ k := pow_pos hx.1 k
  have hxδ : x ≤ δ := hx.2.le
  -- fundamental theorem of calculus
  have hFTC : iteratedDeriv k f x
      = iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s := by
    have h := intervalIntegral_iteratedDeriv_succ_fin hf (j := k) hN hx.1 hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (k + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (k + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv k f x|
      ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by
    have h := abs_add_le (iteratedDeriv k f δ) (-(∫ s in x..δ, iteratedDeriv (k + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s|
        ≤ |iteratedDeriv k f δ| + |∫ s in x..δ, iteratedDeriv (k + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using h
      _ ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by linarith [hI]
  -- the weighted AM–GM bound
  have hcontG : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Icc x δ) :=
    continuousOn_iteratedDeriv_Icc_fin hf (j := k + 1) hN hx.1 hδx
  have hamgm := Work.FTS.H2.DivQ.van_amgm_integral (iteratedDeriv (k + 1) f)
    (e := γ - 2 * (k : ℝ)) (a := x ^ k) hxk hx.1 hxδ hcontG
  simp only [show -(γ - 2 * (k : ℝ)) = 2 * (k : ℝ) - γ from by ring] at hamgm
  -- the bound on the last term of the displayed estimate
  have hTle : (1 / 2) * (∫ s in x..δ,
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      ≤ (1 / 2) * (∫ y in Set.Ioc 0 δ,
        y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [intervalIntegral.integral_of_le hxδ]
    exact Work.FTS.H2.DivQ.van_setIntegral_mono_Ioc hx.1
      (hB.mono_set (Set.Ioc_subset_Ioc le_rfl hδx.le))
      fun y hy => mul_nonneg (Real.rpow_nonneg (le_of_lt hy.1) _) (sq_nonneg _)
  -- assemble
  have hstep : x ^ k * |iteratedDeriv k f x|
      ≤ x ^ k * |iteratedDeriv k f δ|
        + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
        + (1 / 2) * (∫ s in x..δ,
            s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
    have h1 : x ^ k * |iteratedDeriv k f x|
        ≤ x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|) :=
      mul_le_mul_of_nonneg_left hFx (le_of_lt hxk)
    have h2 : x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|)
        ≤ x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxk)
      linarith [hamgm]
    have h3 : x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)))
        = x ^ k * |iteratedDeriv k f δ|
          + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
          + (1 / 2) * (∫ s in x..δ,
              s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
      have hkk : x ^ (2 * k) = x ^ k * x ^ k := by
        rw [show 2 * k = k + k by omega, pow_add]
      rw [hkk]
      have hxne : x ^ k ≠ 0 := ne_of_gt hxk
      field_simp
      ring
    linarith [h1, h2, le_of_eq h3]
  have hTsmall : (1 / 2) * (∫ y in Set.Ioc 0 δ,
      y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 8 := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (le_of_lt hxk)]
  linarith [hstep, hxA, hxC, hTle, hTsmall]

/-- Finite-order version of the private induction step `Work.FTS.H2.DivQ.van_step` of
`Submission/Work/FTS/H2/DivQ/divSinPrimitiveVanish.lean`: the `C^∞` hypothesis is replaced by
`ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)`, and the order `N` is assumed `≥ j + 1`.  The smoothness is
used only at `iteratedDeriv (j+1) f`. -/
private lemma van_step_fin (j : ℕ) (hj : 1 ≤ j) {N : ℕ} (hjN : j + 1 ≤ N) {f : ℝ → ℝ}
    {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (h : Filter.Tendsto (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hjn : ((j : ℝ) ≠ 0) := by positivity
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the limit hypothesis, in interval form
  have hεj : (0 : ℝ) < ε * (j : ℝ) / 2 := by positivity
  have hev := Metric.tendsto_nhds.mp h (ε * (j : ℝ) / 2) hεj
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (x₁ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδlt₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδx : δ < x₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the tail bound against the model integral `∫_x^δ t^{-(j+1)}`
  have htail : ∀ x : ℝ, 0 < x → x ≤ δ →
      x ^ j * (∫ s in x..δ, |iteratedDeriv (j + 1) f s|) ≤ ε / 2 := by
    intro x hxpos hxδ
    have hxj : 0 < x ^ j := pow_pos hxpos j
    -- pointwise bound from the limit hypothesis
    have hbd : ∀ t ∈ Set.Icc x δ,
        |iteratedDeriv (j + 1) f t| ≤ (ε * (j : ℝ) / 2) * (t : ℝ) ^ (-((j : ℝ) + 1)) := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hxpos ht.1
      have htδ₀ : t ∈ Set.Ioo (0 : ℝ) δ₀ := ⟨htpos, lt_of_le_of_lt ht.2 hδlt₀⟩
      have h1 := hδ₀ htδ₀
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : |iteratedDeriv (j + 1) f t| * (t : ℝ) ^ (j + 1) < ε * (j : ℝ) / 2 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt htpos) (j + 1)),
          mul_comm ((t : ℝ) ^ (j + 1))] at h1
        exact h1
      have h3 := mul_lt_mul_of_pos_right h2 (inv_pos.mpr (pow_pos htpos (j + 1)))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos htpos (j + 1))), mul_one] at h3
      have hbase : (t : ℝ) ^ ((j : ℝ) + 1) = (t : ℝ) ^ (j + 1) := by
        have hcast : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, Real.rpow_natCast]
      have hpow : (t : ℝ) ^ (-((j : ℝ) + 1)) = ((t : ℝ) ^ (j + 1))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt htpos) ((j : ℝ) + 1), hbase]
      rw [hpow]
      exact h3.le
    have hint1 : IntervalIntegrable (fun s : ℝ => |iteratedDeriv (j + 1) f s|) volume x δ :=
      ((continuousOn_iteratedDeriv_Icc_fin hf (j := j + 1) hjN hxpos hδx).abs).intervalIntegrable_of_Icc
        (μ := volume) hxδ
    have hcontw : ContinuousOn (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        (Set.Icc x δ) :=
      continuousOn_const.mul (continuousOn_id.rpow_const fun s hs =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hxpos hs.1)))
    have hint2 : IntervalIntegrable (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        volume x δ := hcontw.intervalIntegrable_of_Icc (μ := volume) hxδ
    have hmono := intervalIntegral.integral_mono_on hxδ hint1 hint2 hbd
    rw [intervalIntegral.integral_const_mul] at hmono
    -- evaluate the model integral
    have hnozero : (0 : ℝ) ∉ Set.uIcc x δ := by
      rw [Set.uIcc_of_le hxδ]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hxpos)
    have hne : -((j : ℝ) + 1) ≠ -1 := by
      intro hc
      exact hjn (by linarith)
    have hval : (∫ s in x..δ, s ^ (-((j : ℝ) + 1)))
        = ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) / (j : ℝ) := by
      rw [integral_rpow (Or.inr ⟨hne, hnozero⟩)]
      have hr : (-((j : ℝ) + 1) + 1) = -(j : ℝ) := by ring
      rw [hr]
      ring
    rw [hval] at hmono
    -- multiply by `x ^ j`
    have hxd : x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt hxpos) (j : ℝ), Real.rpow_neg (le_of_lt hδpos) (j : ℝ),
        Real.rpow_natCast, Real.rpow_natCast]
      have hδj : 0 < δ ^ j := pow_pos hδpos j
      have hxinv : x ^ j * (x ^ j)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxj)
      have hnonneg : 0 ≤ x ^ j * (δ ^ j)⁻¹ := mul_nonneg hxj.le (inv_nonneg.mpr hδj.le)
      nlinarith [hxinv, hnonneg]
    have hstep1 : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
        / (j : ℝ))) ≤ ε / 2 := by
      have hrw : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
          / (j : ℝ))) = (ε / 2) * (x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))) := by
        field_simp
      rw [hrw]
      nlinarith [hxd, hε]
    exact (mul_le_mul_of_nonneg_left hmono hxj.le).trans hstep1
  -- eventually the `δ`-term is small
  have hfin : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ j * |iteratedDeriv j f δ| < ε / 2 := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hh := (hid.pow j).mul_const |iteratedDeriv j f δ|
    have hh' : Filter.Tendsto (fun x : ℝ => x ^ j * |iteratedDeriv j f δ|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [zero_pow (by omega : j ≠ 0)] using hh
    exact Filter.Tendsto.eventually_lt hh' tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hfin] with x hx hxfin
  have hxpos : 0 < x := hx.1
  have hxδ : x ≤ δ := hx.2.le
  have hxj : 0 < x ^ j := pow_pos hxpos j
  have hFTC : iteratedDeriv j f x
      = iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s := by
    have hh := intervalIntegral_iteratedDeriv_succ_fin hf (j := j) hjN hxpos hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (j + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (j + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv j f x|
      ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by
    have hh := abs_add_le (iteratedDeriv j f δ) (-(∫ s in x..δ, iteratedDeriv (j + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s|
        ≤ |iteratedDeriv j f δ| + |∫ s in x..δ, iteratedDeriv (j + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using hh
      _ ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by linarith [hI]
  have htail' := htail x hxpos hxδ
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hxj.le]
  linarith [mul_le_mul_of_nonneg_left hFx hxj.le, htail', hxfin]

/-- Finite-order version of `Work.FTS.H2.DivQ.divSinPrimitiveVanish`
(`Submission/Work/FTS/H2/DivQ/divSinPrimitiveVanish.lean`), where the `C^∞` hypothesis
`ContDiffOn ℝ (⊤ : ℕ∞) f (Ioc 0 x₁)` is replaced by `ContDiffOn ℝ ((N:ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`
for a *finite* order `N`, assumed `≥ k+1`.

Adaptation instructions: the original file's proof goes through verbatim. Only two of its
ingredients need finite-order replacements (available in
`Submission/Work/FTS/EllipticEst/remov/HardyFin/Basic.lean`, namespace
`Work.FTS.EllipticEst.remov.HardyFin`):

* `Work.FTS.H2.DivQ.continuousOn_iteratedDeriv_Icc`  ⟶ `continuousOn_iteratedDeriv_Icc_fin`
  (`hf : ContDiffOn ℝ ((N:ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`, `{j} (hj : j ≤ N)`, `ha : 0 < a`,
   `hb : b < x₁`);
* `Work.FTS.H2.DivQ.intervalIntegral_iteratedDeriv_succ` ⟶ `intervalIntegral_iteratedDeriv_succ_fin`
  (same conventions, with `(hj : j + 1 ≤ N)`).

Reusable verbatim (no smoothness hypothesis): `Work.FTS.H2.DivQ.van_powMul_rpow_integral`,
`Work.FTS.H2.DivQ.van_amgm_integral`, `Work.FTS.H2.DivQ.van_setIntegral_mono_Ioc`,
`Work.FTS.H2.DivQ.hardyIter_tendsto_zero`, `Work.FTS.H2.DivQ.two_mul_le_mul_sq_add_div_sq`.
The two private lemmas `van_baseCase` and `van_step` of the original file are to be copied with
`ContDiffOn ℝ (⊤ : ℕ∞) f (Ioc 0 x₁)` replaced by `ContDiffOn ℝ ((N:ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`
together with the extra `hN : k + 1 ≤ N` (in `van_baseCase`) and `hjN : j + 1 ≤ N` (in `van_step`),
and each call of the two ⊤-lemmas replaced by its `_fin` counterpart. In `van_baseCase` the
smoothness is used at `iteratedDeriv (k+1) f` only; in `van_step` at `iteratedDeriv (j+1) f`.
The hypothesis `hN`/`hjN` should be derived from `1 ≤ j` and `j ≤ k` when the lemmas are called
from the main downward induction (`key`), so that the main induction needs no changes. -/
theorem divSinPrimitiveVanish_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (N : ℕ) (hN : k + 1 ≤ N) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro f hf hB j hj1 hjk
  have key : ∀ n : ℕ, ∀ j : ℕ, k - j ≤ n → 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro n
    induction n with
    | zero =>
      intro j hle hj1 hjk
      have hjk' : j = k := by omega
      subst j
      exact van_baseCase_fin k hj1 hx₁ hγ hN hf hB
    | succ n ih =>
      intro j hle hj1 hjk
      rcases Nat.lt_or_ge (k - j) (n + 1) with hlt | hge
      · exact ih j (Nat.lt_succ_iff.mp hlt) hj1 hjk
      · exact van_step_fin j hj1 (by omega) hx₁ hf (ih (j + 1) (by omega) (by omega) (by omega))
  exact key k j (Nat.sub_le k j) hj1 hjk

end Work.FTS.EllipticEst.remov.HardyFin
