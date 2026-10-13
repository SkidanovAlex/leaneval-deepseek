/-
# `radPsi_contDiffOn` — smoothness of the outer rescaled Green's piece

`radPsi α m c z = ∫_{u > 1} c (z u) u^{-p-1} du` with `p = radP α m = 2m/α`.  We show that it is
`C^22` on `(0,∞)` whenever `c` is `C^22` there with all derivatives bounded by `K ≥ 0`.

The proof does *not* differentiate under the integral sign in the original form: the `k`-th
`z`-derivative of the integrand is `c^{(k)}(zu)·u^{k-p-1}`, integrable only for `k < p`, and `p`
can be arbitrarily small.  Instead the change of variables `t = z u` (lemma
`integral_Ioi_one_rpow`) rewrites

  `radPsi α m c z = z^p · ∫_{Ioi z} c t · t^{-p-1} dt`      (`z > 0`),

i.e. `z^p` times the *tail integral* `T k z = ∫_{Ioi z} k` of `k t = c t · t^{-p-1}`.

* For `p > 0` (i.e. `m ≥ 1`) the function `k` is integrable on every tail `Ioi a`, `a > 0`
  (`|k t| ≤ K t^{-p-1}`), and `T k` is differentiable with `deriv (T k) = -k`
  (`hasDerivAt_tailIntegral`).  As `-k` is again `C^22`, `T k` is `C^23`
  (`contDiffOn_succ_of_hasDerivAt_eq`, `contDiffOn_tailIntegral`), and multiplying by the
  `C^∞` factor `z^p` leaves a `C^22` function.
* For `m = 0` (`p = 0`) the critical exponent `-1` makes integrability on a tail a genuine
  question.  By `integrableOn_Ioi_dichotomy` either every tail `Ioi z` carries an integrable `k`,
  in which case the previous argument applies, or none does, in which case the Lebesgue integral
  of a non-integrable function is `0` and `radPsi α 0 c` vanishes identically.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped ContDiff Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- **Derivative-to-smoothness upgrade.**  If `f` has derivative `g` at every point of an open set
and `g` is `C^n` there, then `f` is `C^{n+1}` there. -/
theorem contDiffOn_succ_of_hasDerivAt_eq {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {n : ℕ}
    (hf : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ContDiffOn ℝ (n : ℕ∞ω) g s) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) f s := by
  have hsucc : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by norm_num
  rw [hsucc, contDiffOn_succ_iff_deriv_of_isOpen hs]
  exact ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt,
    fun h => absurd h (by norm_num),
    hg.congr (fun x hx => (hf x hx).deriv)⟩

/-- **Derivative of a tail integral.**  If `k` is continuous on `(0,∞)` and integrable on every
tail `Ioi a` with `a > 0`, then `z ↦ ∫_{Ioi z} k` is differentiable at every `x > 0` with
derivative `-k x`. -/
theorem hasDerivAt_tailIntegral {k : ℝ → ℝ} (hk : ContinuousOn k (Ioi 0))
    (hint : ∀ a ∈ Ioi (0 : ℝ), IntegrableOn k (Ioi a) volume) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => ∫ y in Ioi z, k y) (-(k x)) x := by
  obtain ⟨a, ha0, hax⟩ : ∃ a : ℝ, 0 < a ∧ a < x := ⟨x / 2, by linarith, by linarith⟩
  have hIa : IntegrableOn k (Ioi a) volume := hint a ha0
  have hsub : uIcc a x ⊆ Ioi (0 : ℝ) := by
    intro y hy
    have hy' : y ∈ Icc a x := by simpa [uIcc_of_le (le_of_lt hax)] using hy
    exact lt_of_lt_of_le ha0 hy'.1
  have hInt : IntervalIntegrable k volume a x := hk.mono hsub |>.intervalIntegrable
  have hsm : StronglyMeasurableAtFilter k (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun y hy => hk.continuousAt (isOpen_Ioi.mem_nhds hy)) x hx
  have hcx : ContinuousAt k x := hk.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hFTC : HasDerivAt (fun u => ∫ y in a..u, k y) (k x) x :=
    intervalIntegral.integral_hasDerivAt_right hInt hsm hcx
  refine (hFTC.const_sub (∫ y in Ioi a, k y)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hax] with u hu
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hIa (le_of_lt hu)
  linarith [hsplit]

/-- **Smoothness of a tail integral.**  The tail integral of a `C^n` function which is integrable
on every tail `Ioi a` with `a > 0` is `C^{n+1}` on `(0,∞)`. -/
theorem contDiffOn_tailIntegral {k : ℝ → ℝ} {n : ℕ} (hk : ContDiffOn ℝ (n : ℕ∞ω) k (Ioi 0))
    (hint : ∀ a ∈ Ioi (0 : ℝ), IntegrableOn k (Ioi a) volume) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (fun z => ∫ y in Ioi z, k y) (Ioi 0) :=
  contDiffOn_succ_of_hasDerivAt_eq isOpen_Ioi
    (fun x hx => hasDerivAt_tailIntegral hk.continuousOn hint hx) hk.neg

/-- Integrability of `k` on a *bounded* interval `(a,b]` when `|k y| ≤ K/y`. -/
theorem integrableOn_Ioc_of_abs_le_div {k : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hk : ContinuousOn k (Ioi 0)) (hbound : ∀ y, 0 < y → |k y| ≤ K / y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntegrableOn k (Ioc a b) volume := by
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ (K / a) ?_
  · exact (hk.mono fun y hy => lt_of_lt_of_le ha (le_of_lt hy.1)).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha (le_of_lt hy.1)
    calc ‖k y‖ = |k y| := Real.norm_eq_abs _
      _ ≤ K / y := hbound y hy0
      _ ≤ K / a := div_le_div_of_nonneg_left hK ha (le_of_lt hy.1)

/-- **Dichotomy for tails.**  For a continuous `k` on `(0,∞)` with `|k y| ≤ K/y`, either `k` is
integrable on every tail `Ioi z` (`z > 0`) or on none of them. -/
theorem integrableOn_Ioi_dichotomy {k : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hk : ContinuousOn k (Ioi 0)) (hbound : ∀ y, 0 < y → |k y| ≤ K / y) :
    (∀ z, 0 < z → IntegrableOn k (Ioi z) volume) ∨
      (∀ z, 0 < z → ¬IntegrableOn k (Ioi z) volume) := by
  by_cases h1 : IntegrableOn k (Ioi (1 : ℝ)) volume
  · left
    intro z hz
    rcases le_or_gt 1 z with hle | hlt
    · exact h1.mono_set (Ioi_subset_Ioi hle)
    · rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
      exact (integrableOn_Ioc_of_abs_le_div hK hk hbound hz (le_of_lt hlt)).union h1
  · right
    intro z hz hzint
    refine h1 ?_
    rcases le_or_gt z 1 with hle | hlt
    · exact hzint.mono_set (Ioi_subset_Ioi hle)
    · rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hlt)]
      exact (integrableOn_Ioc_of_abs_le_div hK hk hbound zero_lt_one (le_of_lt hlt)).union hzint

/-- **The rescaled identity.**  For `z > 0`, `Ψ z = z^p · ∫_{Ioi z} c t t^{-p-1} dt`, where
`p = radP α m`. -/
theorem radPsi_eq_rpow_mul_tail (α : ℝ) (m : ℕ) (c : ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    radPsi α m c z = z ^ (radP α m) * ∫ t in Ioi z, c t * t ^ (-(radP α m) - 1) := by
  have hid := integral_Ioi_one_rpow c (-(radP α m) - 1) (z := z) hz
  have hexp : -(-(radP α m) - 1 + 1) = radP α m := by ring
  rw [hexp] at hid
  simpa only [radPsi] using hid

/-- The `m = 0` instance of the rescaled identity. -/
theorem radPsi_zero_eq {α : ℝ} {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    radPsi α 0 c z = ∫ t in Ioi z, c t * t⁻¹ := by
  have hid := integral_Ioi_one_rpow c (-(radP α 0) - 1) (z := z) hz
  have h1 : radP α 0 = 0 := by simp [radP]
  have h2 : -(-(radP α 0) - 1 + 1) = 0 := by rw [h1]; norm_num
  rw [h2, Real.rpow_zero, one_mul] at hid
  have h3 : -(radP α 0) - 1 = -1 := by rw [h1]; norm_num
  simpa only [radPsi, h3, Real.rpow_neg_one] using hid

/-- Integrability of `y ↦ c y · y^{-p-1}` on a tail, for `p > 0`, from a bound `|c| ≤ K`. -/
theorem integrableOn_Ioi_mul_rpow {c : ℝ → ℝ} {K p a : ℝ}
    (hkcont : ContinuousOn (fun y : ℝ => c y * y ^ (-p - 1)) (Ioi 0))
    (hc0 : ∀ y, 0 < y → |c y| ≤ K) (hp : 0 < p) (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => c y * y ^ (-p - 1)) (Ioi a) volume := by
  have hlt : -p - 1 < -1 := by linarith
  have hg : IntegrableOn (fun y : ℝ => K * y ^ (-p - 1)) (Ioi a) volume :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt hlt ha) K
  refine Integrable.mono' hg ?_ ?_
  · exact (hkcont.mono fun y hy => lt_trans ha hy).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := lt_trans ha hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
    exact mul_le_mul_of_nonneg_right (hc0 y hy0) (le_of_lt (Real.rpow_pos_of_pos hy0 _))

theorem radPsi_contDiffOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv 22 c K) :
    ContDiffOn ℝ 22 (Work.FTS.PhiStar.RadialWAux.radPsi α m c) (Set.Ioi 0) := by
  have hc0 : ∀ y, 0 < y → |c y| ≤ K := by
    intro y hy
    have h := hb 0 (by norm_num) y hy
    simpa using h
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: the critical exponent `-1`
    subst hm
    have hk22 : ContDiffOn ℝ (22 : ℕ∞ω) (fun y : ℝ => c y * y⁻¹) (Ioi 0) := by
      refine hc.mul ?_
      have h : ContDiffOn ℝ (22 : ℕ∞ω) (fun y : ℝ => y ^ (-1 : ℝ)) (Ioi 0) :=
        contDiffOn_id.rpow_const_of_ne (p := (-1 : ℝ)) (fun x hx => ne_of_gt hx)
      exact h.congr (fun y _ => by rw [Real.rpow_neg_one])
    have hcont : ContinuousOn (fun y : ℝ => c y * y⁻¹) (Ioi 0) := hk22.continuousOn
    have hbnd : ∀ y, 0 < y → |c y * y⁻¹| ≤ K / y := by
      intro y hy
      have h := div_le_div_of_nonneg_right (hc0 y hy) (le_of_lt hy)
      rw [abs_mul, abs_inv, abs_of_pos hy]
      simpa [div_eq_mul_inv] using h
    rcases integrableOn_Ioi_dichotomy hK hcont hbnd with hall | hnone
    · refine ((contDiffOn_tailIntegral (n := 22) hk22 hall).of_le (by norm_num)).congr
        (fun z hz => radPsi_zero_eq hz)
    · refine (contDiffOn_const (c := (0 : ℝ)) (s := Ioi (0 : ℝ))).congr (fun z hz => ?_)
      rw [radPsi_zero_eq hz]
      exact integral_undef (hnone z hz)
  · -- `m ≥ 1`: the exponent is strictly positive
    have hp : 0 < radP α m := radP_pos hα (Nat.succ_le_of_lt hm)
    have hk22 : ContDiffOn ℝ (22 : ℕ∞ω)
        (fun y : ℝ => c y * y ^ (-(radP α m) - 1)) (Ioi 0) :=
      hc.mul (contDiffOn_id.rpow_const_of_ne (p := -(radP α m) - 1)
        (fun x hx => ne_of_gt hx))
    have hcont : ContinuousOn (fun y : ℝ => c y * y ^ (-(radP α m) - 1)) (Ioi 0) :=
      hk22.continuousOn
    have hint : ∀ a ∈ Ioi (0 : ℝ),
        IntegrableOn (fun y : ℝ => c y * y ^ (-(radP α m) - 1)) (Ioi a) volume :=
      fun a ha => integrableOn_Ioi_mul_rpow hcont hc0 hp ha
    have hT : ContDiffOn ℝ (((22 + 1 : ℕ) : ℕ∞ω))
        (fun z : ℝ => ∫ y in Ioi z, c y * y ^ (-(radP α m) - 1)) (Ioi 0) :=
      contDiffOn_tailIntegral hk22 hint
    have hzp : ContDiffOn ℝ (((22 + 1 : ℕ) : ℕ∞ω))
        (fun z : ℝ => z ^ (radP α m)) (Ioi 0) :=
      contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)
    refine ((hzp.mul hT).of_le (by norm_num)).congr (fun z hz => ?_)
    exact radPsi_eq_rpow_mul_tail α m c hz

end Work.FTS.PhiStar.RadialWAux
