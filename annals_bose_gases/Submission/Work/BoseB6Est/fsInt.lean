import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseB6Est.GFun
import Submission.Work.BoseB6Est.tailIntegralBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — shared integrability and crude pointwise data for the `I₁` estimate

This module collects the *region-independent* data used by the four region
estimates (`reg_small`, `reg_mid`, `reg_far`, `tailIntegralBound`) of FS's
`lem:BogIntegral`:

* the crude kernel bounds `β ≤ 26.2`, `|β − 8π| ≤ 26.2` on the support;
* the crude pointwise bound `|G| ≤ 26.2 + 26.2²/(2r²)` for the kernel bracket and
  the corresponding bounds for the model bracket `G₀ = lhyRad (8π)`;
* measurability and integrability of `r ↦ r²(G − G₀)` on `(0,∞)`;
* the logarithmic integral `∫_{(1,T]} r⁻¹ = log T` in the form
  `∫_{(a,T]} r⁻¹ ≤ log T` for `1 ≤ a`.

Everything here is independent of the parameter regime; the estimates themselves
are in the sibling modules.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

local notation "ℝ³" => Fin 3 → ℝ

/-! ## 1. The crude kernel bounds -/

/-- `β r ≤ 26.2` for `r > 0` (from `|β − 8π| ≤ η r`, `η T ≤ 1` and the
cutoff). -/
theorem FsKernel.beta_le_B0 (K : FsKernel) (hηT : K.η * K.T ≤ 1) {r : ℝ} (hr : 0 < r) :
    K.β r ≤ 26.2 := by
  by_cases h : r ≤ K.T
  · have h1 : K.β r - 8 * Real.pi ≤ K.η * r := (abs_le.mp (K.close r hr.le h)).2
    have h2 : K.η * r ≤ K.η * K.T := mul_le_mul_of_nonneg_left h K.ηnn
    have h3 : K.β r ≤ 8 * Real.pi + 1 := by linarith
    nlinarith [Real.pi_lt_d2]
  · rw [K.support r (not_le.mp h)]; norm_num

/-- `|β r − 8π| ≤ 26.2` for `r > 0`. -/
theorem FsKernel.abs_beta_sub_le (K : FsKernel) (hηT : K.η * K.T ≤ 1) {r : ℝ} (hr : 0 < r) :
    |K.β r - 8 * Real.pi| ≤ 26.2 := by
  have h0 : 0 ≤ K.β r := K.nonneg r
  have h1 : K.β r ≤ 26.2 := K.beta_le_B0 hηT hr
  have h2 : (8 * Real.pi : ℝ) ≤ 26.2 := by nlinarith [Real.pi_lt_d2]
  rw [abs_le]
  exact ⟨by linarith, by linarith [Real.pi_pos]⟩

/-! ## 2. Crude pointwise bounds for the two radial integrands -/

/-- **The crude pointwise bound** `|G| ≤ 26.2 + 26.2²/(2r²)` for `r > 0`. -/
theorem fsGR_abs_le (K : FsKernel) (hηT : K.η * K.T ≤ 1) {εT c1 c2 : ℝ}
    (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1) {r : ℝ} (hr : 0 < r) :
    |fsGR K εT c1 c2 r| ≤ 26.2 + 26.2 ^ 2 / (2 * r ^ 2) := by
  set τ := Work.BoseB6.fsTau εT c1 c2 r with hτdef
  set b := K.β r with hbdef
  have hb0 : 0 ≤ b := K.nonneg r
  have hτ0 : 0 ≤ τ := fsTau_nonneg hε0 hε1 hr.le
  have hden : b ≤ (τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2) := by
    have := Real.sqrt_nonneg ((τ + b) ^ 2 - b ^ 2); linarith
  have hbs : b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) ≤ b := by
    rcases lt_or_eq_of_le hb0 with hb | hb
    · rw [div_le_iff₀ (lt_of_lt_of_le hb hden)]
      nlinarith [hden, hb]
    · have hb' : b = 0 := hb.symm
      simp [hb']
  have hkey : (τ + b) - Real.sqrt ((τ + b) ^ 2 - b ^ 2)
      = b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) :=
    sq_sub_sqrt_eq_div hb0 (by linarith)
  have hG : fsGR K εT c1 c2 r
      = b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) - b ^ 2 / (2 * r ^ 2) := by
    rw [fsGR, ← hτdef, ← hbdef, hkey]
  rw [hG]
  have hX0 : 0 ≤ b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) :=
    div_nonneg (sq_nonneg b) (by linarith)
  have hY0 : 0 ≤ b ^ 2 / (2 * r ^ 2) := by positivity
  have h1 : |b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) - b ^ 2 / (2 * r ^ 2)|
      ≤ b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) + b ^ 2 / (2 * r ^ 2) := by
    rw [abs_sub_le_iff]; exact ⟨by linarith, by linarith⟩
  have hB0 : b ≤ 26.2 := K.beta_le_B0 hηT hr
  have hb2 : b ^ 2 ≤ 26.2 ^ 2 := by nlinarith [hb0]
  have hr2 : 0 < 2 * r ^ 2 := by positivity
  calc |b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) - b ^ 2 / (2 * r ^ 2)|
      ≤ b ^ 2 / ((τ + b) + Real.sqrt ((τ + b) ^ 2 - b ^ 2)) + b ^ 2 / (2 * r ^ 2) := h1
    _ ≤ b + b ^ 2 / (2 * r ^ 2) := by linarith
    _ ≤ 26.2 + 26.2 ^ 2 / (2 * r ^ 2) :=
        add_le_add hB0 (div_le_div_of_nonneg_right hb2 hr2.le)

/-- `G₀(r) < 0` for `r > 0`. -/
theorem fsG0R_neg {r : ℝ} (hr : 0 < r) : fsG0R r < 0 := by
  rw [fsG0R_eq_lhyRad]; exact lhyRadBounds.1 r hr

/-- `|G₀(r)| ≤ 8π + (8π)²/(2r²)` for `r > 0`. -/
theorem fsG0R_abs_le {r : ℝ} (hr : 0 < r) :
    |fsG0R r| ≤ 8 * Real.pi + (8 * Real.pi) ^ 2 / (2 * r ^ 2) := by
  rw [fsG0R_eq_lhyRad]; exact lhyRadBounds.2.2.1 r hr

/-- `−G₀(r) ≤ (8π)³/(2r⁴)` for `r > 0`. -/
theorem fsG0R_le_tail {r : ℝ} (hr : 0 < r) :
    -fsG0R r ≤ (8 * Real.pi) ^ 3 / (2 * r ^ 4) := by
  rw [fsG0R_eq_lhyRad]; exact lhyRadBounds.2.1 r hr

/-! ## 3. Measurability and integrability -/

theorem measurable_fsGR (K : FsKernel) (εT c1 c2 : ℝ) :
    Measurable (fun r : ℝ => fsGR K εT c1 c2 r) := by
  unfold fsGR
  have hβ : Measurable (fun r : ℝ => K.β r) := K.meas
  have hτ : Measurable (fun r : ℝ => Work.BoseB6.fsTau εT c1 c2 r) := by
    unfold Work.BoseB6.fsTau; fun_prop
  have hα : Measurable (fun r : ℝ => Work.BoseB6.fsTau εT c1 c2 r + K.β r) := hτ.add hβ
  have hrad : Measurable (fun r : ℝ =>
      (Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2) :=
    (hα.pow_const 2).sub (hβ.pow_const 2)
  have hsq : Measurable (fun r : ℝ =>
      Real.sqrt ((Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2)) :=
    Real.continuous_sqrt.measurable.comp hrad
  have hdiv : Measurable (fun r : ℝ => (K.β r) ^ 2 / (2 * r ^ 2)) :=
    (hβ.pow_const 2).div (measurable_const.mul (measurable_id.pow_const 2))
  exact (hα.sub hsq).sub hdiv

/-- `r ↦ r² G(r)` is integrable on `(0,∞)`. -/
theorem integrableOn_r2_fsGR (K : FsKernel) {εT c1 c2 : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hηT : K.η * K.T ≤ 1) :
    IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioi 0) := by
  have hmeas : Measurable (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) :=
    (measurable_id.pow_const 2).mul (measurable_fsGR K εT c1 c2)
  have hbnd : ∀ r ∈ Set.Ioc (0:ℝ) K.T,
      ‖r ^ 2 * fsGR K εT c1 c2 r‖ ≤ 26.2 * K.T ^ 2 + 26.2 ^ 2 / 2 := by
    intro r hr
    have hr0 : 0 < r := hr.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
    have h1 := fsGR_abs_le (K := K) (εT := εT) (c1 := c1) (c2 := c2) hηT hε0 hε1 hr0
    have hr2 : r ^ 2 ≤ K.T ^ 2 := by nlinarith [hr.2, hr.1, K.Tnn]
    have h2 : 0 ≤ r ^ 2 := by positivity
    calc r ^ 2 * |fsGR K εT c1 c2 r|
        ≤ r ^ 2 * (26.2 + 26.2 ^ 2 / (2 * r ^ 2)) := mul_le_mul_of_nonneg_left h1 h2
      _ = 26.2 * r ^ 2 + 26.2 ^ 2 / 2 := by field_simp
      _ ≤ 26.2 * K.T ^ 2 + 26.2 ^ 2 / 2 := by nlinarith
  have h1 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioc 0 K.T) := by
    refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioc 0 K.T)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
      (26.2 * K.T ^ 2 + 26.2 ^ 2 / 2) ?_
    · exact hmeas.aestronglyMeasurable.restrict
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun r hr => hbnd r hr)
  have h2 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioi K.T) := by
    refine (MeasureTheory.integrableOn_congr_fun
      (f := fun _ : ℝ => (0:ℝ)) (g := fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r)
      (fun r hr => ?_) measurableSet_Ioi).mp MeasureTheory.integrableOn_zero
    have hz : fsGR K εT c1 c2 r = 0 := tail_fsGR_eq_zero K hε0 hε1 (Set.mem_Ioi.mp hr)
    show (0:ℝ) = r ^ 2 * fsGR K εT c1 c2 r
    rw [hz, mul_zero]
  have hun := h1.union h2
  rwa [show Set.Ioc (0:ℝ) K.T ∪ Set.Ioi K.T = Set.Ioi 0 from ?_] at hun
  ext r
  constructor
  · intro h
    rcases h with h | h
    · exact h.1
    · exact lt_of_le_of_lt K.Tnn h
  · intro hr
    by_cases h2 : r ≤ K.T
    · exact Or.inl ⟨hr, h2⟩
    · exact Or.inr (not_le.mp h2)

/-- `r ↦ r² G₀(r)` is integrable on `(0,∞)`. -/
theorem integrableOn_r2_fsG0R :
    IntegrableOn (fun r : ℝ => r ^ 2 * fsG0R r) (Set.Ioi 0) := by
  have h := lhyRadBounds.2.2.2.2
  have hfun : (fun r : ℝ => r ^ 2 * fsG0R r)
      = (fun r : ℝ => r ^ 2 * Work.BoseB6.lhyRad (8 * Real.pi) r) := by
    funext r; rw [fsG0R_eq_lhyRad]
  rw [hfun]; exact h

/-! ## 4. The logarithmic integral -/

/-- `∫_{a}^{T} r⁻¹ ≤ log T` for `1 ≤ a` and `1 ≤ T`. -/
lemma integral_Ioc_inv_le_log {a T : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T) :
    ∫ r in Set.Ioc a T, (1 / r : ℝ) ≤ Real.log T := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  rcases le_total a T with h | h
  · rw [← intervalIntegral.integral_of_le h]
    have h0 : (0 : ℝ) ∉ Set.uIcc a T := by
      rw [Set.uIcc_of_le h]
      exact fun hx => absurd hx.1 (not_le.mpr (by linarith : (0:ℝ) < a))
    rw [show (fun r : ℝ => 1 / r) = fun r => r⁻¹ by funext r; rw [one_div]]
    rw [integral_inv h0, Real.log_div (ne_of_gt hT0) (ne_of_gt ha0)]
    linarith [Real.log_nonneg ha]
  · have hempty : Set.Ioc a T = ∅ := by
      ext r
      constructor
      · intro hr; exact absurd hr.2 (not_le.mpr (lt_of_le_of_lt h hr.1))
      · intro hr; exact absurd hr (Set.notMem_empty r)
    rw [hempty, MeasureTheory.setIntegral_empty]
    exact Real.log_nonneg hT

end Work.BoseB6Est
