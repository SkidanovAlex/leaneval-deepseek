import Mathlib
import Submission.Commons.Analysis.Abel.volterra_double_integral

/-!
# The right-edge Abel singularity

The Volterra/Abel layer of the odd-dimensional Ulam construction uses the kernel
`(√(v - t))⁻¹ * (√(x - v))⁻¹` on the triangle `0 ≤ t ≤ v ≤ x`.  The singularities live on the
*diagonal* `v = t` and on the *right edge* `v = x`.  The commons already has the corresponding
*left-edge* theory (`(√(t - a))⁻¹ * (√(v - t))⁻¹`, singular on the left edge `t = a` and on the
diagonal): `Commons.Analysis.Abel.integrableOn_weight_triangle` and
`Commons.Analysis.Abel.integrableOn_invSqrt_triangle` are stated for the left edge, while the
requested `Analysis/Abel/integrableOn_invSqrt_triangle_right` — the right-edge kernel that
`abel_self_convolution` / `abel_inversion` actually need — is still missing.

This file closes the **one-dimensional half** of that gap: the right-edge singular weight
`(√(b - x))⁻¹` is interval-integrable on `[a, b]` and its integral is `2 √(b - a)`, exactly the
mirror images of the left-edge lemmas `intervalIntegrable_invSqrt_sub` / `integral_invSqrt_sub`
already in the commons.  Every subsequent step of the Abel layer (in particular the
`abel_self_convolution` hypothesis
`IntegrableOn (fun p => (√(p₂-p₁))⁻¹ * (√(b-p₂))⁻¹ * g p₁) (uIoc 0 b ×ˢ uIoc 0 b)`)
is an assembly of this weight with the existing left-edge/2-D machinery.

Both remaining pieces are proved below:

* `integrableOn_weight_triangle_right` -- the 2-D right-edge weight is integrable on the square.
  The proof mirrors `Commons.Analysis.Abel.integrableOn_weight_triangle` with the weights swapped
  (`MeasureTheory.integrable_prod_iff`), and the fibre bound uses the elementary midpoint split at
  `m := (x+b)/2` instead of a beta integral: for `v <= m` one has
  `(sqrt(v-x))⁻¹ (sqrt(b-v))⁻¹ <= (sqrt(b-m))⁻¹ (sqrt(v-x))⁻¹` and for `v >= m`
  `(sqrt(v-x))⁻¹ (sqrt(b-v))⁻¹ <= (sqrt(m-x))⁻¹ (sqrt(b-v))⁻¹`; since `b-m = m-x = (b-x)/2` the
  fibre integral is `<= 2√2 + 2√2·√(b-a)·(√(b-x))⁻¹`, which is bounded by the explicit integrable
  function `4 + 4√(b-a)(√(b-x))⁻¹` -- integrable exactly by the new one-dimensional right-edge
  lemma above.
* `integrableOn_invSqrt_triangle_right` -- the E-valued version with a continuous factor `K`,
  by the same `Measurable`/`Integrable.mono'` argument as the commons' left-edge
  `Commons.Analysis.Abel.integrableOn_invSqrt_triangle`.

A historical note on the routes that were available:

* mirror `Commons.Analysis.Abel.integrableOn_weight_triangle` with the two weights swapped
  (`(√(p₂-p₁))⁻¹` and `(√(b-p₂))⁻¹` instead of `(√(p₁-a))⁻¹` and `(√(p₂-p₁))⁻¹`), using
  `MeasureTheory.integrable_prod_iff` and, for the fibre bound, the elementary split at the
  midpoint `m := (x+b)/2`:
  `(√(v-x))⁻¹ (√(b-v))⁻¹ ≤ (√(b-m))⁻¹ (√(v-x))⁻¹` for `v ≤ m` and
  `(√(v-x))⁻¹ (√(b-v))⁻¹ ≤ (√(m-x))⁻¹ (√(b-v))⁻¹` for `v ≥ m`; since `b - m = m - x = (b-x)/2`,
  the fibre integral is bounded by `2 + 2 = 4` uniformly, so the outer integrability is
  immediate from `Integrable.const`);
* alternatively, transport the *already proved* left-edge 2-D lemma along the measure-preserving
  involution `p ↦ (a+b-p.2, a+b-p.1)` of `ℝ²` (its Jacobian has determinant `-1`, and it swaps
  the two edges while fixing the diagonal), then use `MeasurePreserving.integrable_comp`.

The E-valued version `integrableOn_invSqrt_triangle_right` is then the same
`Integrable.mono'` argument as ` Commons.Analysis.Abel.integrableOn_invSqrt_triangle`, with the
sup bound of the continuous factor `K` on the compact square.
-/

open MeasureTheory Filter
open scoped Interval

namespace Commons.Analysis.Abel

/-- The right-edge Abel singularity `(√(b - x))⁻¹` is interval-integrable on `[a, b]`
(the mirror image of `intervalIntegrable_invSqrt_sub`). -/
lemma intervalIntegrable_invSqrt_sub_right {a b : ℝ} (hab : a < b) :
    IntervalIntegrable (fun x => (Real.sqrt (b - x))⁻¹) volume a b := by
  let g : ℝ → ℝ := fun x => -2 * Real.sqrt (b - x)
  have hcont : ContinuousOn g (Set.uIcc a b) := by dsimp [g]; fun_prop
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt g ((Real.sqrt (b - x))⁻¹) x := by
    intro x hx
    have hxne : b - x ≠ 0 := by linarith [hx.2]
    have hsqrt := Real.hasDerivAt_sqrt hxne
    have hlin : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (b - y))
        (1 / (2 * Real.sqrt (b - x)) * (-1)) x :=
      HasDerivAt.comp (x := x) (h := fun y : ℝ => b - y) (h₂ := Real.sqrt)
        (h' := -1) (h₂' := 1 / (2 * Real.sqrt (b - x))) hsqrt hlin
    have hg : HasDerivAt g (-2 * (1 / (2 * Real.sqrt (b - x)) * (-1))) x := by
      dsimp [g]; exact hcomp.const_mul (-2)
    have hsqrtne : Real.sqrt (b - x) ≠ 0 := (Real.sqrt_pos_of_pos (by linarith [hx.2])).ne'
    have hval : -2 * (1 / (2 * Real.sqrt (b - x)) * (-1)) = (Real.sqrt (b - x))⁻¹ := by
      field_simp [hsqrtne]
    exact hg.congr_deriv hval
  have hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ (Real.sqrt (b - x))⁻¹ := fun x _ =>
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hderiv' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt g ((Real.sqrt (b - x))⁻¹) x := by
    intro x hx
    exact hderiv x (by simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] using hx)
  have hpos' : ∀ x ∈ Set.Ioo (min a b) (max a b), 0 ≤ (Real.sqrt (b - x))⁻¹ := by
    intro x hx
    exact hpos x (by simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] using hx)
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont hderiv' hpos'

/-- The value of the right-edge Abel integral (the mirror image of `integral_invSqrt_sub`). -/
lemma integral_invSqrt_sub_right {a b : ℝ} (hab : a < b) :
    ∫ x in a..b, (Real.sqrt (b - x))⁻¹ = 2 * Real.sqrt (b - a) := by
  let g : ℝ → ℝ := fun x => -2 * Real.sqrt (b - x)
  let g' : ℝ → ℝ := fun x => (Real.sqrt (b - x))⁻¹
  have hcont : ContinuousOn g (Set.Icc a b) := by dsimp [g]; fun_prop
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hxne : b - x ≠ 0 := by linarith [hx.2]
    have hsqrt := Real.hasDerivAt_sqrt hxne
    have hlin : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (b - y))
        (1 / (2 * Real.sqrt (b - x)) * (-1)) x :=
      HasDerivAt.comp (x := x) (h := fun y : ℝ => b - y) (h₂ := Real.sqrt)
        (h' := -1) (h₂' := 1 / (2 * Real.sqrt (b - x))) hsqrt hlin
    have hg : HasDerivAt g (-2 * (1 / (2 * Real.sqrt (b - x)) * (-1))) x := by
      dsimp [g]; exact hcomp.const_mul (-2)
    have hsqrtne : Real.sqrt (b - x) ≠ 0 := (Real.sqrt_pos_of_pos (by linarith [hx.2])).ne'
    have hval : -2 * (1 / (2 * Real.sqrt (b - x)) * (-1)) = g' x := by
      dsimp [g']; field_simp [hsqrtne]
    exact hg.congr_deriv hval
  have hint : IntervalIntegrable g' volume a b := by
    simpa [g'] using intervalIntegrable_invSqrt_sub_right hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hab) hcont hderiv hint
  dsimp [g] at h
  rw [h, show b - b = (0 : ℝ) by ring, Real.sqrt_zero]
  ring

/-- The right-edge analogue of
`intervalIntegrable_indicator_ge_const_mul_invSqrt_sub`: a constant times the right-edge
singularity, supported on `(-∞, b]`. -/
lemma intervalIntegrable_indicator_le_const_mul_invSqrt_sub_right
    {a b C : ℝ} (hab : a < b) :
    IntervalIntegrable (fun y => if y ≤ b then C * (Real.sqrt (b - y))⁻¹ else 0) volume a b := by
  have hbase : IntervalIntegrable (fun y => C * (Real.sqrt (b - y))⁻¹) volume a b :=
    (intervalIntegrable_invSqrt_sub_right hab).const_mul C
  have hcongr : Set.EqOn (fun y => C * (Real.sqrt (b - y))⁻¹)
      (fun y => if y ≤ b then C * (Real.sqrt (b - y))⁻¹ else 0) (Set.uIoc a b) := by
    intro y hy
    have hyb : y ≤ b := by
      rw [Set.uIoc_of_le (le_of_lt hab)] at hy
      exact hy.2
    simp [hyb]
  exact hbase.congr hcongr

lemma integrableOn_weight_triangle_right {a b : ℝ} (hab : a < b) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (b - p.2))⁻¹ else 0)
      (Set.uIoc a b ×ˢ Set.uIoc a b) := by
  let S : Set ℝ := Set.uIoc a b
  let μ : Measure ℝ := volume.restrict S
  let g : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (b - p.2))⁻¹ else 0
  have h_ae_Ioo : ∀ᵐ x ∂μ, x ∈ Set.Ioo a b := by
    rw [ae_iff]
    change (volume.restrict S) {x | x ∉ Set.Ioo a b} = 0
    dsimp [S]
    rw [Set.uIoc_of_le (le_of_lt hab)]
    rw [Measure.restrict_apply (s := Set.Ioc a b) (t := {x | x ∉ Set.Ioo a b})
      (ht := measurableSet_Ioo.compl)]
    have h_inter : {x : ℝ | x ∉ Set.Ioo a b} ∩ Set.Ioc a b = {b} := by
      ext x
      constructor
      · intro hx
        have hxIoc : x ∈ Set.Ioc a b := hx.2
        have hxnot : x ∉ Set.Ioo a b := hx.1
        by_cases hxb : x = b
        · exact hxb
        · exact False.elim (hxnot ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxb⟩)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨by simp, ⟨hab, le_rfl⟩⟩
    rw [h_inter]
    simp [measure_singleton]
  have hsqrt2m : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.2 - p.1)) :=
    Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst)
  have hsqrtRm : Measurable (fun p : ℝ × ℝ => Real.sqrt (b - p.2)) :=
    Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_snd)
  have hg_measurable : Measurable g := by
    dsimp only [g]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      ((Measurable.inv hsqrt2m).mul (Measurable.inv hsqrtRm)) measurable_const
  have hg_meas : AEStronglyMeasurable g (μ.prod μ) := hg_measurable.aestronglyMeasurable
  have hsec_meas : ∀ x : ℝ, AEStronglyMeasurable (fun y => g (x, y)) μ := fun x =>
    (hg_measurable.comp (by fun_prop : Measurable (fun y : ℝ => (x, y)))).aestronglyMeasurable
  -- fibrewise integrability with an explicit majorant
  have h_fib : ∀ᵐ x ∂μ, Integrable (fun y => g (x, y)) μ := by
    filter_upwards [h_ae_Ioo] with x hx
    set m : ℝ := (x + b) / 2 with hm
    have hxm : x < m := by dsimp only [m]; linarith [hx.2]
    have hmb : m < b := by dsimp only [m]; linarith [hx.2]
    have hxb : x < b := hx.2
    have hbm_pos : 0 < b - m := by linarith
    have hmx_pos : 0 < m - x := by linarith
    let F1 : ℝ → ℝ := fun y => if x ≤ y then (Real.sqrt (b - m))⁻¹ * (Real.sqrt (y - x))⁻¹ else 0
    let F2 : ℝ → ℝ := fun y => (Real.sqrt (m - x))⁻¹ * (Real.sqrt (b - y))⁻¹
    have hF1_int : Integrable F1 μ := by
      have hint : IntervalIntegrable F1 volume a b := by
        simpa only [F1] using intervalIntegrable_indicator_ge_const_mul_invSqrt_sub
          (a := a) (b := b) (x := x) (C := (Real.sqrt (b - m))⁻¹) hx.1 hxb
      have hintOn : IntegrableOn F1 (Set.Ioc a b) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp hint
      dsimp only [μ, S]
      rw [Set.uIoc_of_le (le_of_lt hab)]
      simpa only [F1, MeasureTheory.IntegrableOn] using hintOn
    have hF2_int : Integrable F2 μ := by
      have hint : IntervalIntegrable F2 volume a b := by
        simpa only [F2] using
          (intervalIntegrable_invSqrt_sub_right hab).const_mul ((Real.sqrt (m - x))⁻¹)
      have hintOn : IntegrableOn F2 (Set.Ioc a b) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp hint
      dsimp only [μ, S]
      rw [Set.uIoc_of_le (le_of_lt hab)]
      simpa only [F2, MeasureTheory.IntegrableOn] using hintOn
    refine Integrable.mono' (hF1_int.add hF2_int) (hsec_meas x) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
    have hyS : y ∈ Set.Ioc a b := by
      have h : S = Set.Ioc a b := Set.uIoc_of_le (le_of_lt hab)
      rw [h] at hy
      exact hy
    have hyb : y ≤ b := hyS.2
    have hF1nn : 0 ≤ F1 y := by
      dsimp only [F1]
      by_cases h : x ≤ y
      · rw [if_pos h]
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      · rw [if_neg h]
    have hF2nn : 0 ≤ F2 y := by
      dsimp only [F2]
      exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    by_cases hxy : x ≤ y
    · have hval : g (x, y) = (Real.sqrt (y - x))⁻¹ * (Real.sqrt (b - y))⁻¹ := by
        dsimp only [g]; rw [if_pos hxy]
      rw [hval]
      have h1 : 0 ≤ (Real.sqrt (y - x))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h2 : 0 ≤ (Real.sqrt (b - y))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
      by_cases hym : y ≤ m
      · have hbnd : (Real.sqrt (b - y))⁻¹ ≤ (Real.sqrt (b - m))⁻¹ := by
          apply inv_anti₀ (Real.sqrt_pos_of_pos hbm_pos)
          exact Real.sqrt_le_sqrt (by linarith)
        have hF1v : F1 y = (Real.sqrt (b - m))⁻¹ * (Real.sqrt (y - x))⁻¹ := by
          dsimp only [F1]; rw [if_pos hxy]
        change (Real.sqrt (y - x))⁻¹ * (Real.sqrt (b - y))⁻¹ ≤ F1 y + F2 y
        rw [hF1v]
        have hstep := mul_le_mul_of_nonneg_left hbnd h1
        exact le_trans (by simpa [mul_comm] using hstep) (le_add_of_nonneg_right hF2nn)
      · have hym' : m ≤ y := (not_le.mp hym).le
        have hbnd : (Real.sqrt (y - x))⁻¹ ≤ (Real.sqrt (m - x))⁻¹ := by
          apply inv_anti₀ (Real.sqrt_pos_of_pos hmx_pos)
          exact Real.sqrt_le_sqrt (by linarith)
        have hF2v : F2 y = (Real.sqrt (m - x))⁻¹ * (Real.sqrt (b - y))⁻¹ := rfl
        change (Real.sqrt (y - x))⁻¹ * (Real.sqrt (b - y))⁻¹ ≤ F1 y + F2 y
        rw [hF2v]
        exact le_trans (mul_le_mul_of_nonneg_right hbnd h2) (le_add_of_nonneg_left hF1nn)
    · have hval : g (x, y) = 0 := by dsimp only [g]; rw [if_neg hxy]
      rw [hval, norm_zero]
      exact add_nonneg hF1nn hF2nn
  -- outer integrability: bound the fibre norm-integral by an explicit integrable function
  have h_int_x : Integrable (fun x : ℝ => ∫ y : ℝ, ‖g (x, y)‖ ∂μ) μ := by
    set Γ : ℝ := 4 * Real.sqrt (b - a) with hΓ
    have hB_int : Integrable (fun x : ℝ => 4 + Γ * (Real.sqrt (b - x))⁻¹) μ := by
      have hint : IntervalIntegrable (fun x : ℝ => Γ * (Real.sqrt (b - x))⁻¹) volume a b :=
        (intervalIntegrable_invSqrt_sub_right hab).const_mul Γ
      have hintOn : IntegrableOn (fun x : ℝ => Γ * (Real.sqrt (b - x))⁻¹) (Set.Ioc a b) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp hint
      have hconstOn : IntegrableOn (fun _ : ℝ => (4 : ℝ)) (Set.Ioc a b) :=
        integrableOn_const (by simp)
      have hsum := hconstOn.add hintOn
      dsimp only [μ, S]
      rw [Set.uIoc_of_le (le_of_lt hab)]
      have hsum' : Integrable (fun x : ℝ => (4 : ℝ) + Γ * (Real.sqrt (b - x))⁻¹)
          (volume.restrict (Set.Ioc a b)) := hsum
      exact hsum'
    refine Integrable.mono' hB_int ?_ ?_
    · exact (hg_measurable.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · filter_upwards [h_ae_Ioo, h_fib] with x hx hfib
      set m : ℝ := (x + b) / 2 with hm
      have hxm : x < m := by dsimp only [m]; linarith [hx.2]
      have hmb : m < b := by dsimp only [m]; linarith [hx.2]
      have hxb : x < b := hx.2
      have hbm_pos : 0 < b - m := by linarith
      have hmx_pos : 0 < m - x := by linarith
      have hbm_eq : b - m = m - x := by dsimp only [m]; ring
      have hbx_split : b - x = 2 * (m - x) := by dsimp only [m]; ring
      let F1 : ℝ → ℝ := fun y => if x ≤ y then (Real.sqrt (b - m))⁻¹ * (Real.sqrt (y - x))⁻¹ else 0
      let F2 : ℝ → ℝ := fun y => (Real.sqrt (m - x))⁻¹ * (Real.sqrt (b - y))⁻¹
      have hF1_int : Integrable F1 μ := by
        have hint : IntervalIntegrable F1 volume a b := by
          simpa only [F1] using intervalIntegrable_indicator_ge_const_mul_invSqrt_sub
            (a := a) (b := b) (x := x) (C := (Real.sqrt (b - m))⁻¹) hx.1 hxb
        have hintOn : IntegrableOn F1 (Set.Ioc a b) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp hint
        dsimp only [μ, S]
        rw [Set.uIoc_of_le (le_of_lt hab)]
        simpa only [F1, MeasureTheory.IntegrableOn] using hintOn
      have hF2_int : Integrable F2 μ := by
        have hint : IntervalIntegrable F2 volume a b := by
          simpa only [F2] using
            (intervalIntegrable_invSqrt_sub_right hab).const_mul ((Real.sqrt (m - x))⁻¹)
        have hintOn : IntegrableOn F2 (Set.Ioc a b) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hab)).mp hint
        dsimp only [μ, S]
        rw [Set.uIoc_of_le (le_of_lt hab)]
        simpa only [F2, MeasureTheory.IntegrableOn] using hintOn
      -- pointwise domination
      have hpt : ∀ᵐ y ∂μ, ‖g (x, y)‖ ≤ F1 y + F2 y := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
        have hyS : y ∈ Set.Ioc a b := by
          have h : S = Set.Ioc a b := Set.uIoc_of_le (le_of_lt hab)
          rw [h] at hy
          exact hy
        have hF1nn : 0 ≤ F1 y := by
          dsimp only [F1]
          by_cases h : x ≤ y
          · rw [if_pos h]
            exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
              (inv_nonneg.mpr (Real.sqrt_nonneg _))
          · rw [if_neg h]
        have hF2nn : 0 ≤ F2 y := by
          dsimp only [F2]
          exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
            (inv_nonneg.mpr (Real.sqrt_nonneg _))
        by_cases hxy : x ≤ y
        · have hval : g (x, y) = (Real.sqrt (y - x))⁻¹ * (Real.sqrt (b - y))⁻¹ := by
            dsimp only [g]; rw [if_pos hxy]
          rw [hval]
          have h1 : 0 ≤ (Real.sqrt (y - x))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
          have h2 : 0 ≤ (Real.sqrt (b - y))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
          rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
          by_cases hym : y ≤ m
          · have hbnd : (Real.sqrt (b - y))⁻¹ ≤ (Real.sqrt (b - m))⁻¹ := by
              apply inv_anti₀ (Real.sqrt_pos_of_pos hbm_pos)
              exact Real.sqrt_le_sqrt (by linarith)
            have hF1v : F1 y = (Real.sqrt (b - m))⁻¹ * (Real.sqrt (y - x))⁻¹ := by
              dsimp only [F1]; rw [if_pos hxy]
            change (Real.sqrt (y - x))⁻¹ * (Real.sqrt (b - y))⁻¹ ≤ F1 y + F2 y
            rw [hF1v]
            have hstep := mul_le_mul_of_nonneg_left hbnd h1
            exact le_trans (by simpa [mul_comm] using hstep) (le_add_of_nonneg_right hF2nn)
          · have hym' : m ≤ y := (not_le.mp hym).le
            have hbnd : (Real.sqrt (y - x))⁻¹ ≤ (Real.sqrt (m - x))⁻¹ := by
              apply inv_anti₀ (Real.sqrt_pos_of_pos hmx_pos)
              exact Real.sqrt_le_sqrt (by linarith)
            have hF2v : F2 y = (Real.sqrt (m - x))⁻¹ * (Real.sqrt (b - y))⁻¹ := rfl
            change (Real.sqrt (y - x))⁻¹ * (Real.sqrt (b - y))⁻¹ ≤ F1 y + F2 y
            rw [hF2v]
            exact le_trans (mul_le_mul_of_nonneg_right hbnd h2) (le_add_of_nonneg_left hF1nn)
        · have hval : g (x, y) = 0 := by dsimp only [g]; rw [if_neg hxy]
          rw [hval, norm_zero]
          exact add_nonneg hF1nn hF2nn
      -- the two 1-D values
      have hconv1 : (∫ y : ℝ, F1 y ∂μ) = ∫ y in a..b, F1 y := by
        dsimp only [μ, S]
        rw [Set.uIoc_of_le (le_of_lt hab), ← intervalIntegral.integral_of_le (le_of_lt hab)]
      have hconv2 : (∫ y : ℝ, F2 y ∂μ) = ∫ y in a..b, F2 y := by
        dsimp only [μ, S]
        rw [Set.uIoc_of_le (le_of_lt hab), ← intervalIntegral.integral_of_le (le_of_lt hab)]
      have hF1val : (∫ y : ℝ, F1 y ∂μ) = (Real.sqrt (b - m))⁻¹ * (2 * Real.sqrt (b - x)) := by
        rw [hconv1]
        have hind : (∫ y in a..b, F1 y)
            = ∫ y in a..b, Set.indicator {y : ℝ | x ≤ y}
                (fun y => (Real.sqrt (b - m))⁻¹ * (Real.sqrt (y - x))⁻¹) y := by
          apply intervalIntegral.integral_congr
          intro y _
          dsimp only [F1]
          by_cases h : x ≤ y <;> simp [Set.indicator_apply, Set.mem_Ici, h]
        rw [hind, intervalIntegral_indicator_ge (a := a) (b := b) (c := x) hx.1 (le_of_lt hxb)]
        rw [intervalIntegral.integral_const_mul, integral_invSqrt_sub hxb]
      have hF2val : (∫ y : ℝ, F2 y ∂μ) = (Real.sqrt (m - x))⁻¹ * (2 * Real.sqrt (b - a)) := by
        rw [hconv2, intervalIntegral.integral_const_mul, integral_invSqrt_sub_right hab]
      -- combine
      have hmono : (∫ y : ℝ, ‖g (x, y)‖ ∂μ)
          ≤ ∫ y : ℝ, (F1 y + F2 y) ∂μ :=
        integral_mono_ae hfib.norm (hF1_int.add hF2_int) hpt
      have hsum : (∫ y : ℝ, (F1 y + F2 y) ∂μ)
          = (Real.sqrt (b - m))⁻¹ * (2 * Real.sqrt (b - x))
            + (Real.sqrt (m - x))⁻¹ * (2 * Real.sqrt (b - a)) := by
        rw [integral_add hF1_int hF2_int, hF1val, hF2val]
      -- the numerical bound
      have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← pow_two]; exact Real.sq_sqrt (by norm_num)
      have hbm_ne : Real.sqrt (b - m) ≠ 0 := (Real.sqrt_pos_of_pos hbm_pos).ne'
      have hmx_ne : Real.sqrt (m - x) ≠ 0 := (Real.sqrt_pos_of_pos hmx_pos).ne'
      have hterm1 : (Real.sqrt (b - m))⁻¹ * (2 * Real.sqrt (b - x)) = 2 * Real.sqrt 2 := by
        rw [hbx_split, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hbm_eq]
        field_simp [hmx_ne]
      have hterm2 : (Real.sqrt (m - x))⁻¹ * (2 * Real.sqrt (b - a)) ≤ Γ * (Real.sqrt (b - x))⁻¹ := by
        have hkey : (Real.sqrt (m - x))⁻¹ = Real.sqrt 2 * (Real.sqrt (b - x))⁻¹ := by
          rw [hbx_split, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp [(Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)).ne', hmx_ne]
        have hle : 2 * Real.sqrt 2 ≤ 4 := by nlinarith [Real.sqrt_nonneg 2, hsqrt2sq]
        calc (Real.sqrt (m - x))⁻¹ * (2 * Real.sqrt (b - a))
            = 2 * Real.sqrt 2 * Real.sqrt (b - a) * (Real.sqrt (b - x))⁻¹ := by
              rw [hkey]; ring
          _ ≤ 4 * Real.sqrt (b - a) * (Real.sqrt (b - x))⁻¹ := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
              · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
          _ = Γ * (Real.sqrt (b - x))⁻¹ := by rw [hΓ]
      have h24 : 2 * Real.sqrt 2 ≤ 4 := by nlinarith [Real.sqrt_nonneg 2, hsqrt2sq]
      have hnn : 0 ≤ ∫ y : ℝ, ‖g (x, y)‖ ∂μ :=
        integral_nonneg (fun y => norm_nonneg _)
      have hfinal : (Real.sqrt (b - m))⁻¹ * (2 * Real.sqrt (b - x))
          + (Real.sqrt (m - x))⁻¹ * (2 * Real.sqrt (b - a))
          ≤ 4 + Γ * (Real.sqrt (b - x))⁻¹ := by
        rw [hterm1]; linarith [hterm2, h24]
      rw [Real.norm_of_nonneg hnn]
      calc (∫ y : ℝ, ‖g (x, y)‖ ∂μ)
          ≤ ∫ y : ℝ, (F1 y + F2 y) ∂μ := hmono
        _ = (Real.sqrt (b - m))⁻¹ * (2 * Real.sqrt (b - x))
            + (Real.sqrt (m - x))⁻¹ * (2 * Real.sqrt (b - a)) := hsum
        _ ≤ 4 + Γ * (Real.sqrt (b - x))⁻¹ := hfinal

  have h_prod : Integrable g (μ.prod μ) :=
    (MeasureTheory.integrable_prod_iff (μ := μ) (ν := μ) hg_meas).2 ⟨h_fib, h_int_x⟩
  have h_on : IntegrableOn g (S ×ˢ S) := by
    change Integrable g ((volume.prod volume).restrict (S ×ˢ S))
    rw [← MeasureTheory.Measure.prod_restrict]
    exact h_prod
  simpa only [g, S] using h_on

/-- The right-edge Abel triangle kernel with a continuous factor is integrable: the mirror of
`integrableOn_invSqrt_triangle` for the right-edge singularity `(√(b - p.2))⁻¹`. -/
lemma integrableOn_invSqrt_triangle_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        if p.1 ≤ p.2 then
          (Real.sqrt (p.2 - p.1))⁻¹ • (Real.sqrt (b - p.2))⁻¹ • K p.1 p.2
        else 0)
      (Set.uIoc a b ×ˢ Set.uIoc a b) := by
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc a b
  let t : Set (ℝ × ℝ) := Set.uIoc a b ×ˢ Set.uIoc a b
  have hK_cont_norm : ContinuousOn (fun p : ℝ × ℝ => ‖K p.1 p.2‖) S := hK_cont.norm
  have hS_compact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hK_cont_norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  have hC_bound : ∀ p ∈ S, ‖K p.1 p.2‖ ≤ C := fun p hp =>
    le_trans (by simpa using hC0 p hp) (le_max_left _ _)
  have hweight := integrableOn_weight_triangle_right hab
  have hweightC : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        C * ((Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (b - p.2))⁻¹) else 0) t := by
    simpa [t, MeasureTheory.IntegrableOn, mul_assoc] using hweight.const_mul C
  let w1 : ℝ × ℝ → ℝ := fun p => (Real.sqrt (p.2 - p.1))⁻¹
  let w2 : ℝ × ℝ → ℝ := fun p => (Real.sqrt (b - p.2))⁻¹
  let Kcurry : ℝ × ℝ → E := fun p => K p.1 p.2
  let H : ℝ × ℝ → E := fun p => (w1 p * w2 p) • Kcurry p
  let F : ℝ × ℝ → E := fun p => if p.1 ≤ p.2 then H p else 0
  have ht_meas : MeasurableSet t := measurableSet_uIoc.prod measurableSet_uIoc
  have hts : t ⊆ S := by
    intro p hp
    have hp' : p.1 ∈ Set.Ioc a b ∧ p.2 ∈ Set.Ioc a b := by
      simpa [t, Set.uIoc_of_le (le_of_lt hab)] using hp
    exact ⟨⟨le_of_lt hp'.1.1, hp'.1.2⟩, ⟨le_of_lt hp'.2.1, hp'.2.2⟩⟩
  have hK_ae : AEStronglyMeasurable Kcurry (volume.restrict t) := by
    dsimp only [Kcurry]
    exact hK_cont.aestronglyMeasurable_of_subset_isCompact hS_compact ht_meas hts
  have hw1_meas : Measurable w1 := by
    dsimp only [w1]
    exact Measurable.inv (Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst))
  have hw2_meas : Measurable w2 := by
    dsimp only [w2]
    exact Measurable.inv (Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_snd))
  have hw_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => w1 p * w2 p) (volume.restrict t) :=
    (hw1_meas.mul hw2_meas).aestronglyMeasurable
  have hH_ae : AEStronglyMeasurable H (volume.restrict t) := by
    dsimp only [H]
    exact hw_ae.smul hK_ae
  have hcond_meas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hF_ae : AEStronglyMeasurable F (volume.restrict t) := by
    dsimp only [F]
    exact hH_ae.indicator hcond_meas
  have hle_ae : ∀ᵐ p ∂(volume.restrict t), ‖F p‖ ≤
      (if p.1 ≤ p.2 then C * (w1 p * w2 p) else 0) := by
    filter_upwards [ae_restrict_mem ht_meas] with p hp
    by_cases hle : p.1 ≤ p.2
    · have hpS : p ∈ S := hts hp
      have hK_norm : ‖Kcurry p‖ ≤ C := by simpa [Kcurry] using hC_bound p hpS
      have hw_nonneg : 0 ≤ w1 p * w2 p := by
        dsimp only [w1, w2]
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      dsimp only [F, H]
      rw [if_pos hle, if_pos hle]
      calc ‖(w1 p * w2 p) • Kcurry p‖ = |w1 p * w2 p| * ‖Kcurry p‖ := norm_smul _ _
        _ = (w1 p * w2 p) * ‖Kcurry p‖ := by rw [abs_of_nonneg hw_nonneg]
        _ ≤ (w1 p * w2 p) * C := mul_le_mul_of_nonneg_left hK_norm hw_nonneg
        _ = C * (w1 p * w2 p) := mul_comm _ _
    · dsimp only [F, H]
      rw [if_neg hle, if_neg hle, norm_zero]
  have hF_int_restrict : Integrable F (volume.restrict t) :=
    MeasureTheory.Integrable.mono' hweightC hF_ae hle_ae
  simpa only [F, H, w1, w2, Kcurry, t, MeasureTheory.IntegrableOn, smul_smul] using hF_int_restrict

end Commons.Analysis.Abel
