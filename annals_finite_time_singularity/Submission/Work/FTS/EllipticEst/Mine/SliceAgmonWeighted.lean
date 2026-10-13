import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Mine.Support.slice_local_interp
import Submission.Work.FTS.EllipticEst.Mine.Support.deriv_sq_le_local_avg
import Submission.Work.FTS.EllipticEst.Mine.Support.integrableOn_of_mul_thEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

/-! ## Elementary facts about the angular weight `thEta θ = sin(2θ)^{-η}` -/

lemma thEta_zero : thEta 0 = 0 := by
  rw [thEta, mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by have := Work.Spaces.eta_pos; linarith)

lemma thEta_pi_half : thEta (Real.pi / 2) = 0 := by
  rw [thEta, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by have := Work.Spaces.eta_pos; linarith)

lemma one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ thEta θ := by
  have hpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hneg : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hpos hle hneg
  simpa [thEta, Real.rpow_zero] using h

lemma intervalIntegral_eq_setIntegral_Iθ (f : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) = ∫ θ in Work.Spaces.Iθ, f θ := by
  rw [intervalIntegral.integral_of_le (by positivity),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

lemma intervalIntegrable_thEta {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) :
    IntervalIntegrable (fun θ : ℝ => thEta θ) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact integrableOn_thEta.1.mono_set (fun x hx =>
    ⟨le_trans ha (le_of_lt hx.1), le_trans hx.2 hb⟩)

lemma intervalIntegral_thEta_le {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) :
    (∫ θ in a..b, thEta θ) ≤ 10000 := by
  have hcomp : (∫ θ in a..b, thEta θ) ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), thEta θ :=
    intervalIntegral.integral_mono_interval ha hab hb
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        exact thEta_nonneg ⟨le_of_lt hx.1, hx.2⟩)
      (intervalIntegrable_thEta (by positivity) le_rfl le_rfl)
  rw [intervalIntegral_eq_setIntegral_Iθ thEta] at hcomp
  linarith [hcomp, integrableOn_thEta.2]

/-! ## Two elementary comparison lemmas -/

/-- If `(g')² ≤ K` on the open interval `(0, π/2)`, then for `[a,b] ⊆ Iθ`
`∫_a^b (g')² w ≤ K ∫_a^b w` (the endpoints `0`, `π/2` are harmless because `w = 0` there). -/
lemma piece_le {g : ℝ → ℝ} {K a b : ℝ} (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ)
    (hab : a ≤ b)
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv g θ) ^ 2 ≤ K)
    (hL : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume a b) :
    (∫ θ in a..b, (deriv g θ) ^ 2 * thEta θ) ≤ K * (∫ θ in a..b, thEta θ) := by
  have hW : IntervalIntegrable (fun θ : ℝ => thEta θ) volume a b :=
    intervalIntegrable_thEta hab ha.1 hb.2
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab hL (hW.const_mul K) ?_
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_trans ha.1 hθ.1, le_trans hθ.2 hb.2⟩
  by_cases h0 : θ = 0
  · subst h0
    simp [thEta_zero]
  by_cases hπ : θ = Real.pi / 2
  · subst hπ
    simp [thEta_pi_half]
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθI.1 (Ne.symm h0), lt_of_le_of_ne hθI.2 hπ⟩
    exact mul_le_mul_of_nonneg_right (hpt θ hθ') (thEta_nonneg hθI)

/-- For a nonnegative `f` that is integrable on `Iθ` together with `f · thEta`, the unweighted
interval integral over `[a,b] ⊆ Iθ` is at most the weighted integral over the whole `Iθ`. -/
lemma intervalIntegral_le_weighted {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ) (hab : a ≤ b)
    (hfn : ∀ θ : ℝ, 0 ≤ f θ)
    (hf : IntegrableOn f Work.Spaces.Iθ)
    (hfw : IntegrableOn (fun θ => f θ * thEta θ) Work.Spaces.Iθ) :
    (∫ y in a..b, f y) ≤ ∫ θ in Work.Spaces.Iθ, f θ * thEta θ := by
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha.1 (le_of_lt hx.1), le_trans hx.2 hb.2⟩
  have hfa : IntegrableOn f (Set.Ioc a b) := hf.mono_set hsub
  have hfwa : IntegrableOn (fun θ => f θ * thEta θ) (Set.Ioc a b) := hfw.mono_set hsub
  -- almost every `θ ∈ (a,b]` lies in the open interval `(0, π/2)`
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]
    simpa using MeasureTheory.measure_singleton (Real.pi / 2)
  have hmem_ae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc a b)), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with x hx hmem
    exact ⟨lt_of_le_of_lt ha.1 hmem.1, lt_of_le_of_ne (le_trans hmem.2 hb.2) hx⟩
  have h1 : (∫ y in a..b, f y) ≤ ∫ y in a..b, f y * thEta y := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ _
      exact hfn θ
    · exact hfwa
    · filter_upwards [hmem_ae] with θ hθ
      calc f θ = f θ * 1 := by ring
        _ ≤ f θ * thEta θ := mul_le_mul_of_nonneg_left (one_le_thEta hθ) (hfn θ)
  have h2 : (∫ y in a..b, f y * thEta y)
      ≤ ∫ y in (0 : ℝ)..(Real.pi / 2), f y * thEta y := by
    refine intervalIntegral.integral_mono_interval ha.1 hab hb.2 ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (hfn x) (thEta_nonneg ⟨le_of_lt hx.1, hx.2⟩)
    · rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity)]
      exact hfw.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  rw [intervalIntegral_eq_setIntegral_Iθ (fun y => f y * thEta y)] at h2
  linarith

/-! ## The assembly -/

/-- **Assembly of the weighted slice Agmon inequality.**  Assuming the one-dimensional inputs
(the local interpolation inequality `hS1`, the averaging bound `hS2` and the two removals of the
weight `hInt0`, `hInt2`), the weighted `L²`-bound for the first angular derivative holds with the
explicit constant `10 ^ 8`. -/
lemma assembly {g : ℝ → ℝ} {x₁ x₂ : ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hx₁ : 0 ≤ x₁) (hx₁₂ : x₁ < x₂) (hx₂ : x₂ ≤ Real.pi / 2)
    (hL : x₂ - x₁ = Real.pi / 4)
    (hLint : IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hGint : IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hFint : IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hInt2 : IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2) Work.Spaces.Iθ)
    (hInt0 : IntegrableOn (fun θ : ℝ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hS1 : (∫ y in x₁..x₂, (deriv g y) ^ 2)
        ≤ (64 / (x₂ - x₁) ^ 2) * (∫ y in x₁..x₂, (g y) ^ 2)
          + (x₂ - x₁) ^ 2 * (∫ y in x₁..x₂, (deriv (deriv g) y) ^ 2))
    (hS2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv g θ) ^ 2
        ≤ (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
          + 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)) :
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * thEta θ)
      ≤ 10 ^ 8 * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)) := by
  have hpi := Real.pi_pos
  have hx₁I : x₁ ∈ Work.Spaces.Iθ := ⟨hx₁, by linarith⟩
  have hx₂I : x₂ ∈ Work.Spaces.Iθ := ⟨le_trans hx₁ hx₁₂.le, hx₂⟩
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := Work.Spaces.zero_mem_Iθ
  have hpI : (Real.pi / 2) ∈ Work.Spaces.Iθ := Work.Spaces.pi_half_mem_Iθ
  have hLpos : 0 < x₂ - x₁ := by linarith
  -- nonnegativity of the two energy integrals
  have hF0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
  have hG0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
  -- step 1: comparisons of the unweighted pieces with the weighted ones
  have hJg : (∫ y in x₁..x₂, (g y) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ :=
    intervalIntegral_le_weighted hx₁I hx₂I hx₁₂.le (fun θ => sq_nonneg _) hInt0 hFint
  have hJ2g : (∫ y in x₁..x₂, (deriv (deriv g) y) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ :=
    intervalIntegral_le_weighted hx₁I hx₂I hx₁₂.le (fun θ => sq_nonneg _) hInt2 hGint
  have hI2g : (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ :=
    intervalIntegral_le_weighted h0I hpI (by positivity) (fun θ => sq_nonneg _) hInt2 hGint
  -- step 2: the uniform pointwise bound `K`, and its nonnegativity
  have hJnn : 0 ≤ ∫ y in x₁..x₂, (deriv g y) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hx₁₂.le (fun y => sq_nonneg _)
  have hJ2nn : 0 ≤ (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall (by positivity) (fun y => sq_nonneg _)
  set K : ℝ := (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
    + 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 2 / (x₂ - x₁) := div_nonneg (by norm_num) hLpos.le
    have h2 : 0 ≤ 2 * (Real.pi / 2 - 0) := by have := Real.pi_pos; nlinarith
    nlinarith [hJnn, hJ2nn]
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv g θ) ^ 2 ≤ K := by
    intro θ hθ
    rw [hKdef]
    exact hS2 θ hθ
  -- step 3: the numeric bound on `K`
  have hJbound : (∫ y in x₁..x₂, (deriv g y) ^ 2)
      ≤ (64 / (x₂ - x₁) ^ 2) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (x₂ - x₁) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) :=
    le_trans hS1
      (add_le_add (mul_le_mul_of_nonneg_left hJg (div_nonneg (by norm_num) (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left hJ2g (sq_nonneg _)))
  have hcoef1 : 128 / (x₂ - x₁) ^ 3 ≤ 304 := by
    have hcube : (27 : ℝ) < Real.pi ^ 3 := by
      have h := pow_lt_pow_left₀ Real.pi_gt_three (by norm_num : (0:ℝ) ≤ 3)
        (by norm_num : (3:ℕ) ≠ 0)
      norm_num at h
      exact h
    have hrew : (128 : ℝ) / (x₂ - x₁) ^ 3 = 8192 / Real.pi ^ 3 := by
      rw [hL, show (Real.pi / 4) ^ 3 = Real.pi ^ 3 / 64 by ring, div_div_eq_mul_div]
      norm_num
    rw [hrew, div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 3)]
    nlinarith [hcube]
  have hcoef2 : 2 * (x₂ - x₁) + Real.pi ≤ 6 := by
    rw [hL]; linarith [Real.pi_le_four]
  have hA0 : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
      ≤ (2 / (x₂ - x₁)) * ((64 / (x₂ - x₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (x₂ - x₁) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)) :=
    mul_le_mul_of_nonneg_left hJbound (div_nonneg (by norm_num) hLpos.le)
  have hrew : (2 / (x₂ - x₁)) * ((64 / (x₂ - x₁) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
      + (x₂ - x₁) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ))
      = (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (2 * (x₂ - x₁)) * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    have hne : x₂ - x₁ ≠ 0 := ne_of_gt hLpos
    field_simp
    ring
  have hA : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
      ≤ (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (2 * (x₂ - x₁)) * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) :=
    le_trans hA0 (le_of_eq hrew)
  have hB : 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)
      ≤ Real.pi * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    have h2pi : 2 * (Real.pi / 2 - 0) = (Real.pi : ℝ) := by ring
    rw [h2pi]
    exact mul_le_mul_of_nonneg_left hI2g Real.pi_pos.le
  have htot : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
      + 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)
      ≤ (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (2 * (x₂ - x₁) + Real.pi)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    linarith [hA, hB]
  have hfin : (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
      + (2 * (x₂ - x₁) + Real.pi)
        * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)
      ≤ 304 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + 6 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    have h1 := mul_le_mul_of_nonneg_right hcoef1 hF0
    have h2 := mul_le_mul_of_nonneg_right hcoef2 hG0
    linarith
  have hKb : K ≤ 304 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
      + 6 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    rw [hKdef]
    linarith [htot, hfin]
  -- step 4: split the weighted integral of `(g')²` into three pieces
  have hf : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity)]
    exact hLint.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hf01 : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume 0 x₁ := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁]
    exact hLint.mono_set (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 (le_trans hx₁₂.le hx₂)⟩)
  have hf12 : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume x₁ x₂ := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁₂.le]
    exact hLint.mono_set (fun x hx => ⟨le_trans hx₁ (le_of_lt hx.1), le_trans hx.2 hx₂⟩)
  have hf2h : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume x₂ (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₂]
    exact hLint.mono_set (fun x hx => ⟨le_trans hx₁ (le_trans hx₁₂.le (le_of_lt hx.1)), hx.2⟩)
  have hf02 : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume 0 x₂ := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (le_trans hx₁ hx₁₂.le)]
    exact hLint.mono_set (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hx₂⟩)
  have hp1 : (∫ θ in (0 : ℝ)..x₁, (deriv g θ) ^ 2 * thEta θ) ≤ K * 10000 :=
    le_trans (piece_le h0I hx₁I hx₁ hpt hf01)
      (mul_le_mul_of_nonneg_left
        (intervalIntegral_thEta_le hx₁ le_rfl (le_trans hx₁₂.le hx₂)) hKnn)
  have hp2 : (∫ θ in x₁..x₂, (deriv g θ) ^ 2 * thEta θ) ≤ K * 10000 :=
    le_trans (piece_le hx₁I hx₂I hx₁₂.le hpt hf12)
      (mul_le_mul_of_nonneg_left (intervalIntegral_thEta_le hx₁₂.le hx₁ hx₂) hKnn)
  have hp3 : (∫ θ in x₂..(Real.pi / 2), (deriv g θ) ^ 2 * thEta θ) ≤ K * 10000 :=
    le_trans (piece_le hx₂I hpI hx₂ hpt hf2h)
      (mul_le_mul_of_nonneg_left
        (intervalIntegral_thEta_le hx₂ (le_trans hx₁ hx₁₂.le) le_rfl) hKnn)
  have hsum : (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv g θ) ^ 2 * thEta θ) ≤ 30000 * K := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals hf01 hf12
    have e2 := intervalIntegral.integral_add_adjacent_intervals hf02 hf2h
    rw [← e2, ← e1]
    linarith [hp1, hp2, hp3]
  -- step 5: conclude
  have hsum' : (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * thEta θ) ≤ 30000 * K := by
    rw [← intervalIntegral_eq_setIntegral_Iθ (fun θ => (deriv g θ) ^ 2 * thEta θ)]
    exact hsum
  have hfinal : 30000 * K ≤ 10 ^ 8 * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)
      + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)) := by
    have h := mul_le_mul_of_nonneg_left hKb (by norm_num : (0:ℝ) ≤ 30000)
    nlinarith [h, hF0, hG0]
  linarith [hsum', hfinal]

theorem SliceAgmonWeighted : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ),
    ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro g hg hGint hFint
  by_cases hLint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ
  · -- the honest case: the hypotheses supply the two energy bounds of `assembly`
    have hder1 : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
      hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hcont2' : ContinuousOn (deriv (deriv g)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hder1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn
    have hcont2 : ContinuousOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      hcont2'.pow 2
    have hcont0 : ContinuousOn (fun θ : ℝ => (g θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
      hg.continuousOn.pow 2
    have hInt2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2)
        Work.Spaces.Iθ :=
      (Support.integrableOn_of_mul_thEta hcont2 (fun θ _ => sq_nonneg _) hGint).1
    have hInt0 : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2) Work.Spaces.Iθ :=
      (Support.integrableOn_of_mul_thEta hcont0 (fun θ _ => sq_nonneg _) hFint).1
    have hInt2int : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) volume
        (0 : ℝ) (Real.pi / 2) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity)]
      exact hInt2.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
    have hInt2intJ : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) volume
        (Real.pi / 8) (3 * Real.pi / 8) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos])]
      exact hInt2.mono_set (fun x hx =>
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    refine assembly (x₁ := Real.pi / 8) (x₂ := 3 * Real.pi / 8) hg (by positivity)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by ring)
      hLint hGint hFint hInt2 hInt0 ?_ ?_
    · exact Support.slice_local_interp (p := 0) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hg hInt2intJ
    · exact Support.deriv_sq_le_local_avg (p := 0) (r := Real.pi / 2)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        hg hInt2int
  · -- otherwise the left-hand side is the junk value `0`
    rw [MeasureTheory.integral_undef hLint]
    refine mul_nonneg (by norm_num) (add_nonneg ?_ ?_)
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))

end Work.FTS.EllipticEst.Mine
