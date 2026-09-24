import Mathlib
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.Gfun_sq_integral_ge_diag
import Submission.Work.GM.Affine.assembly_aux

/-!
# `Work.GM.Affine.Gfun_sq_ge_center` (GM §9: the honest affine sum at a rational center)

GM's expansion (§9, equation (9.8)) produces the honest affine sum

`Gfun C₀ T M₂ f u = Σ_{m₂ ∈ R2 M₂} Σ_{m₂' ∈ R2 M₂} Σ_{|j| ≤ ⌊2C₀M₂⌋} f̃((m₂u + j)/m₂')`,
`f̃ = smoothed psiSmooth T f`,

and needs a *lower* bound for `∫ (Gfun)²` in terms of `(∫ f̃)²/L` when `f̃` is supported in an
interval `[u₀, u₀+L]` of length `L` with `M₂ L ≤ 1/2` and the *center* `u₀` is rational with
`m₂ u₀ ∈ ℤ` for every `m₂ ∈ R2 M₂`.

The point is that for each pair `(m₂, m₂') ∈ R2 M₂ × R2 M₂` the integer
`j(m₂,m₂') = m₂'u₀ - m₂u₀` realises

`f̃((m₂u + j(m₂,m₂'))/m₂') = f̃(u₀ + (m₂/m₂')(u - u₀))`,

a dilate of `f̃` by the factor `m₂/m₂' ∈ [1/2, 2]`.  Hence all the `|R2 M₂|²` "centred" terms are
supported in `[u₀, u₀+2L]` and each has integral `(m₂'/m₂) ∫f̃ ≥ (1/2)∫f̃`, so their sum `Ψ`
satisfies `∫Ψ ≥ (|R2 M₂|²/2) ∫f̃`.  Since `∫Ψ ≤ ∫Gfun`, Cauchy–Schwarz on the interval of length
`2L` gives `(∫Ψ)² ≤ 2L ∫Ψ² ≤ 2L ∫(Gfun)²`, and `|R2 M₂| ≥ M₂/2` yields

`(1/128) M₂⁴ (∫f̃)²/L ≤ ∫ (Gfun)²`.
-/

open Complex MeasureTheory Finset Filter
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-- `ψ = psiSmooth` is supported in the open ball of radius `1/4` (it is the normalised
`ContDiffBump` with `rOut = 1/4`). -/
lemma psiSmooth_abs_lt_quarter {x : ℝ} (hx : psiSmooth x ≠ 0) : |x| < 1 / 4 := by
  have hmem : x ∈ Function.support (psiBump.normed volume) := by
    rw [Function.mem_support]; exact hx
  rw [ContDiffBump.support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  exact hmem

lemma psiSmooth_eq_zero_of_quarter_le_abs {x : ℝ} (hx : 1 / 4 ≤ |x|) : psiSmooth x = 0 := by
  by_contra h
  have := psiSmooth_abs_lt_quarter h
  linarith

/-- `smoothed psiSmooth T f` vanishes strictly to the left of `1/C₀ - 1/(4T)` when `f` is
supported in `[1/C₀, C₀]`. -/
lemma smoothed_eq_zero_of_lt_left {C₀ T u : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hsupp : SuppHyp C₀ f)
    (h : u < 1 / C₀ - 1 / (4 * T)) : smoothed psiSmooth T f u = 0 := by
  rw [smoothed]
  have hzero : ∀ u' : ℝ, psiSmooth (T * (u - u')) * f u' = 0 := by
    intro u'
    by_cases hf : f u' = 0
    · rw [hf, mul_zero]
    · have h1 : 1 / C₀ ≤ u' := (hsupp u' hf).1
      have h2 : 1 / (4 * T) ≤ u' - u := by linarith
      have hpos : 0 < 1 / (4 * T) := by positivity
      have h3 : 1 / 4 ≤ |T * (u - u')| := by
        have h4 : u - u' < 0 := by linarith
        rw [abs_mul, abs_of_pos hT, abs_of_neg h4]
        have h5 : T * (1 / (4 * T)) ≤ T * (u' - u) := mul_le_mul_of_nonneg_left h2 hT.le
        have h6 : T * (1 / (4 * T)) = 1 / 4 := by field_simp
        rw [h6] at h5
        linarith
      rw [psiSmooth_eq_zero_of_quarter_le_abs h3, zero_mul]
  rw [show (fun u' : ℝ => psiSmooth (T * (u - u')) * f u') = fun _ => 0 from funext hzero]
  rw [MeasureTheory.integral_zero, mul_zero]

/-- `smoothed psiSmooth T f` vanishes strictly to the right of `C₀ + 1/(4T)`. -/
lemma smoothed_eq_zero_of_gt_right {C₀ T u : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hsupp : SuppHyp C₀ f)
    (h : C₀ + 1 / (4 * T) < u) : smoothed psiSmooth T f u = 0 := by
  rw [smoothed]
  have hzero : ∀ u' : ℝ, psiSmooth (T * (u - u')) * f u' = 0 := by
    intro u'
    by_cases hf : f u' = 0
    · rw [hf, mul_zero]
    · have h1 : u' ≤ C₀ := (hsupp u' hf).2
      have h2 : 1 / (4 * T) ≤ u - u' := by linarith
      have hpos : 0 < 1 / (4 * T) := by positivity
      have h3 : 1 / 4 ≤ |T * (u - u')| := by
        have h4 : 0 < u - u' := by linarith
        rw [abs_mul, abs_of_pos hT, abs_of_pos h4]
        have h5 : T * (1 / (4 * T)) ≤ T * (u - u') := mul_le_mul_of_nonneg_left h2 hT.le
        have h6 : T * (1 / (4 * T)) = 1 / 4 := by field_simp
        rw [h6] at h5
        linarith
      rw [psiSmooth_eq_zero_of_quarter_le_abs h3, zero_mul]
  rw [show (fun u' : ℝ => psiSmooth (T * (u - u')) * f u') = fun _ => 0 from funext hzero]
  rw [MeasureTheory.integral_zero, mul_zero]

/-- The sharp support bound for the smoothing: `f̃` vanishes off
`[1/C₀ - 1/(4T), C₀ + 1/(4T)]` when `f` is supported in `[1/C₀, C₀]`. -/
lemma smoothed_supp_sharp {C₀ T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hsupp : SuppHyp C₀ f) :
    ∀ u, smoothed psiSmooth T f u ≠ 0 → u ∈ Set.Icc (1 / C₀ - 1 / (4 * T)) (C₀ + 1 / (4 * T)) := by
  intro u hu
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    push_neg at h
    exact hu (smoothed_eq_zero_of_lt_left hT hsupp h)
  · by_contra h
    push_neg at h
    exact hu (smoothed_eq_zero_of_gt_right hT hsupp h)

/-- If `f ≥ 0` is continuous and not identically zero, the smoothing `f̃` is strictly positive on
an interval of length `1/(8T)`, namely `[x₀ - 1/(16T), x₀ + 1/(16T)]`. -/
lemma smoothed_pos_interval {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ u, 0 ≤ f u) (hne : ∃ u, 0 < f u) :
    ∃ x₀ : ℝ, ∀ u, |u - x₀| ≤ 1 / (16 * T) → 0 < smoothed psiSmooth T f u := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hεf⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - x₀| < ε → 0 < f y := by
    have hmem : Set.Ioi (0:ℝ) ∈ nhds (f x₀) := IsOpen.mem_nhds isOpen_Ioi hx₀
    have hEv : ∀ᶠ y in nhds x₀, 0 < f y := hf.continuousAt hmem
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp hEv
    exact ⟨ε, hε, fun y hy => hε' (by rwa [Real.dist_eq])⟩
  refine ⟨x₀, fun u hu => ?_⟩
  set η : ℝ := min ε (1 / (32 * T)) with hηdef
  have hηpos : 0 < η := lt_min hε (by positivity)
  rw [smoothed]
  apply mul_pos hT
  have hcont : Continuous (fun y : ℝ => psiSmooth (T * (u - y)) * f y) :=
    ((psiSmooth_contDiff.continuous).comp
      (continuous_const.mul (continuous_const.sub continuous_id))).mul hf
  have hcspsi : HasCompactSupport psiSmooth :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/4)) (1/4)) isCompact_Icc
      (fun x hx => by
        have h := psiSmooth_abs_lt_quarter hx
        rw [Set.mem_Icc]; constructor <;> linarith [neg_abs_le x, le_abs_self x])
  have hcs1 : HasCompactSupport (fun y : ℝ => psiSmooth (T * (u - y))) := by
    have h := hasCompactSupport_affine (f := psiSmooth) hcspsi (c := -T) (d := 1) (e := T*u)
      (by linarith : -T ≠ 0) one_ne_zero
    have hfe : (fun y : ℝ => psiSmooth ((-T * y + T * u) / 1))
        = fun y => psiSmooth (T * (u - y)) := by
      funext y; rw [div_one]; congr 1; ring
    rwa [hfe] at h
  have hint : Integrable (fun y : ℝ => psiSmooth (T * (u - y)) * f y) :=
    hcont.integrable_of_hasCompactSupport (hcs1.mul_right (f' := f))
  have hnn' : 0 ≤ᵐ[volume] fun y : ℝ => psiSmooth (T * (u - y)) * f y :=
    Filter.Eventually.of_forall fun y => mul_nonneg (psiSmooth_nonneg _) (hnn y)
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnn' hint]
  have hIoo : Set.Ioo (x₀ - η) (x₀ + η) ⊆
      Function.support (fun y : ℝ => psiSmooth (T * (u - y)) * f y) := by
    intro y hy
    have hy1 : |y - x₀| < η := by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
    have hfy : 0 < f y := hεf y (lt_of_lt_of_le hy1 (min_le_left _ _))
    have hpsi : 0 < psiSmooth (T * (u - y)) := by
      have h1 : |T * (u - y)| ≤ 1/8 := by
        have hsub : |u - y| ≤ |u - x₀| + |x₀ - y| := by
          calc |u - y| = |(u - x₀) + (x₀ - y)| := by ring_nf
            _ ≤ |u - x₀| + |x₀ - y| := abs_add_le _ _
        have h3 : |x₀ - y| < η := by rwa [abs_sub_comm] at hy1
        have hu' : T * |u - x₀| ≤ 1/16 := by
          have := mul_le_mul_of_nonneg_left hu hT.le
          rwa [show T * (1/(16*T)) = 1/16 by field_simp] at this
        have hy' : T * |x₀ - y| ≤ 1/32 := by
          have h3' : |x₀ - y| ≤ 1/(32*T) := le_trans h3.le (min_le_right _ _)
          have := mul_le_mul_of_nonneg_left h3' hT.le
          rwa [show T * (1/(32*T)) = 1/32 by field_simp] at this
        rw [abs_mul, abs_of_pos hT]
        nlinarith [hsub, hu', hy', hT]
      exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (psiSmooth_ge_one (by
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; linarith))
    exact ne_of_gt (mul_pos hpsi hfy)
  refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hIoo)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- `R2 M₂ = {m ∈ ℤ : M₂ < m ≤ 2M₂}` has at least `M₂/2` elements when `M₂ ≥ 1`. -/
lemma R2_card_ge {M₂ : ℝ} (hM₂ : 1 ≤ M₂) : M₂ / 2 ≤ ((R2 M₂).card : ℝ) := by
  have h1 : (1:ℤ) ≤ ⌊M₂⌋ := by
    rw [Int.le_floor]; exact_mod_cast hM₂
  have heq : R2 M₂ = Finset.Icc (⌊M₂⌋ + 1) ⌊2 * M₂⌋ := by
    ext m
    rw [R2, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1', h2'⟩, h3'⟩
      exact ⟨by have : ⌊M₂⌋ < m := Int.floor_lt.mpr h3'; omega, h2'⟩
    · rintro ⟨h1', h2'⟩
      refine ⟨⟨by omega, h2'⟩, ?_⟩
      exact lt_of_lt_of_le (Int.lt_floor_add_one M₂) (by exact_mod_cast h1')
  have hDnn : (0:ℤ) ≤ ⌊2 * M₂⌋ - ⌊M₂⌋ := by
    have := Int.floor_mono (show M₂ ≤ 2 * M₂ by linarith)
    omega
  rw [heq, Int.card_Icc]
  have hcast : ((⌊2 * M₂⌋ + 1 - (⌊M₂⌋ + 1)).toNat : ℝ)
      = ((⌊2 * M₂⌋ - ⌊M₂⌋ : ℤ) : ℝ) := by
    rw [show ⌊2 * M₂⌋ + 1 - (⌊M₂⌋ + 1) = ⌊2 * M₂⌋ - ⌊M₂⌋ by ring]
    exact_mod_cast Int.toNat_of_nonneg hDnn
  rw [hcast]
  have hA : (⌊M₂⌋ : ℝ) ≤ ((⌊2 * M₂⌋ - ⌊M₂⌋ : ℤ) : ℝ) := by
    have h2' : (2 * ⌊M₂⌋ : ℤ) ≤ ⌊2 * M₂⌋ := by
      rw [Int.le_floor]; push_cast; linarith [Int.floor_le M₂]
    have h3' : ((2 * ⌊M₂⌋ : ℤ) : ℝ) ≤ ((⌊2 * M₂⌋) : ℝ) := by exact_mod_cast h2'
    push_cast at h3' ⊢
    linarith
  have hB : M₂ / 2 ≤ (⌊M₂⌋ : ℝ) := by
    by_cases h₂ : M₂ ≤ 2
    · have h3' : (1:ℝ) ≤ (⌊M₂⌋ : ℝ) := by exact_mod_cast h1
      linarith
    · push_neg at h₂
      have := Int.lt_floor_add_one M₂
      linarith
  linarith

/-- Cauchy–Schwarz in the form `(∫ h)² ≤ (b - a) * ∫ h²` for a continuous nonnegative `h` whose
support is contained in `[a,b]`. -/
lemma sq_integral_le_width {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ u, 0 ≤ h u)
    {a b : ℝ} (hab : a < b) (hsupp : ∀ u, h u ≠ 0 → u ∈ Set.Icc a b) :
    (∫ u, h u) ^ 2 ≤ (b - a) * ∫ u, (h u) ^ 2 := by
  have hcs : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a b) isCompact_Icc hsupp
  have hint : Integrable h := hh.integrable_of_hasCompactSupport hcs
  have hcs2 : HasCompactSupport (fun u : ℝ => (h u)^2) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a b) isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact hsupp u (fun h0 => hu (by rw [h0]; norm_num))
  have hint2 : Integrable (fun u : ℝ => (h u)^2) := (hh.pow 2).integrable_of_hasCompactSupport hcs2
  set I : ℝ → ℝ := Set.indicator (Set.Icc a b) (1 : ℝ → ℝ) with hI
  have hIndint : Integrable I := by
    rw [hI, MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    refine MeasureTheory.integrableOn_const ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  set A : ℝ := b - a with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set B : ℝ := ∫ u, h u with hB
  set C : ℝ := ∫ u, (h u)^2 with hC
  set t : ℝ := B / A with ht
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg hnn
  have hpt : ∀ u : ℝ, 2 * t * h u ≤ t^2 * I u + (h u)^2 := by
    intro u
    by_cases hu : u ∈ Set.Icc a b
    · rw [hI, Set.indicator_of_mem hu, Pi.one_apply]
      nlinarith [sq_nonneg (t - h u)]
    · have h0 : h u = 0 := by by_contra hc; exact hu (hsupp u hc)
      rw [hI, Set.indicator_of_notMem hu, h0]
      norm_num
  have hIndval : ∫ u, I u = A := by
    rw [hI, MeasureTheory.integral_indicator_one measurableSet_Icc,
      Real.volume_real_Icc_of_le hab.le, hA]
  have hInt : 2 * t * B ≤ t^2 * A + C := by
    have h1 : ∫ u, 2 * t * h u = 2 * t * B := by
      rw [hB, MeasureTheory.integral_const_mul]
    have h2 : ∫ u, (t^2 * I u + (h u)^2) = t^2 * A + C := by
      rw [MeasureTheory.integral_add (hIndint.const_mul _) hint2, MeasureTheory.integral_const_mul,
        hIndval, hC]
    calc 2 * t * B = ∫ u, 2 * t * h u := h1.symm
      _ ≤ ∫ u, (t^2 * I u + (h u)^2) :=
          MeasureTheory.integral_mono (hint.const_mul (2*t)) ((hIndint.const_mul _).add hint2)
            (fun u => hpt u)
      _ = t^2 * A + C := h2
  have e1 : (2 : ℝ) * t * B = 2 * B^2 / A := by rw [ht]; field_simp
  have e2 : t^2 * A = B^2 / A := by rw [ht]; field_simp
  rw [e1, e2] at hInt
  have hfin : B^2 ≤ A * C := by
    have h2 := mul_le_mul_of_nonneg_right hInt hApos.le
    have e3 : (2 * B^2 / A) * A = 2 * B^2 := by field_simp
    have e4 : (B^2 / A + C) * A = B^2 + C * A := by field_simp
    rw [e3, e4] at h2
    linarith
  calc (∫ u, h u)^2 = B^2 := by rw [hB]
    _ ≤ A * C := hfin
    _ = (b - a) * ∫ u, (h u)^2 := by rw [hA, hC]

/-- The change of variables for a single affine term. -/
lemma integral_affine_eq {f : ℝ → ℝ} {c d e : ℝ} (hc : c ≠ 0) (hd : 0 < d) :
    ∫ u, f ((c*u+e)/d) = (d/|c|) * ∫ u, f u := by
  have h1 : ∀ u : ℝ, f ((c*u+e)/d) = (fun v => f v) ((c/d) * (u + e/c)) := by
    intro u; congr 1; field_simp
  calc ∫ u, f ((c*u+e)/d)
      = ∫ u, (fun v => f v) ((c/d) * (u + e/c)) := by simp only [h1]
    _ = ∫ y, (fun v => f v) ((c/d) * y) := by
        rw [MeasureTheory.integral_add_right_eq_self (fun u => (fun v => f v) ((c/d) * u)) (e/c)]
    _ = |(c/d)⁻¹| • ∫ v, f v := by
        simpa using MeasureTheory.Measure.integral_comp_mul_left (fun v : ℝ => f v) (c/d)
    _ = (d/|c|) * ∫ v, f v := by
        rw [inv_div, abs_div, abs_of_pos hd]
        simp only [smul_eq_mul]

theorem Gfun_sq_ge_center {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ {T M₂ : ℝ}, 0 < T → 1 ≤ M₂ →
      ∀ {f : ℝ → ℝ}, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      ∀ {u₀ L : ℝ}, (∀ m₂ ∈ R2 M₂, ∃ k : ℤ, (m₂ : ℝ) * u₀ = (k : ℝ)) → 0 < L →
      (∀ u, smoothed psiSmooth T f u ≠ 0 → u ∈ Set.Icc u₀ (u₀ + L)) → M₂ * L ≤ 1 / 2 →
      c * M₂ ^ 4 * (∫ u, smoothed psiSmooth T f u) ^ 2 / L
        ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := by
  refine ⟨1/128, by norm_num, ?_⟩
  intro T M₂ hT hM₂ f hf hfnn hsupp u₀ L hrat hL hsuppL hML
  have hM₂pos : (0:ℝ) < M₂ := lt_of_lt_of_le zero_lt_one hM₂
  have hC₀pos : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set F : ℝ → ℝ := smoothed psiSmooth T f with hFdef
  have hFnn : ∀ u, 0 ≤ F u := fun u => by
    rw [hFdef]; exact smoothed_psiSmooth_nonneg hT hfnn u
  have hfcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  obtain ⟨hFcont, hFcs, -⟩ := smoothed_psiSmooth_fourier hT hf hfcs
  set V : ℝ := ∫ u, F u with hVdef
  have hVnn : 0 ≤ V := by rw [hVdef]; exact integral_nonneg hFnn
  change (1/128 : ℝ) * M₂ ^ 4 * V ^ 2 / L ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2
  by_cases hV0 : V = 0
  · have hzero : (1/128 : ℝ) * M₂ ^ 4 * V ^ 2 / L = 0 := by rw [hV0]; ring
    rw [hzero]
    exact integral_nonneg (fun u => sq_nonneg (Gfun C₀ T M₂ f u))
  · have hVpos : 0 < V := lt_of_le_of_ne hVnn (Ne.symm hV0)
    -- `f` is not identically zero
    have hfne : ∃ u, 0 < f u := by
      by_contra hcon
      push_neg at hcon
      have hfz : ∀ u, f u = 0 := fun u => le_antisymm (hcon u) (hfnn u)
      have hFz : F = fun _ => (0:ℝ) := by
        funext u
        rw [hFdef, smoothed]
        simp [hfz]
      have hVz : V = 0 := by rw [hVdef, hFz, MeasureTheory.integral_zero]
      exact hV0 hVz
    -- positivity of the smoothing on an interval of length `1/(8T)`
    obtain ⟨x₁, hx₁⟩ := smoothed_pos_interval hT hf hfnn hfne
    have hx₁ne : smoothed psiSmooth T f x₁ ≠ 0 :=
      ne_of_gt (hx₁ x₁ (by rw [sub_self, abs_zero]; positivity))
    have hx₁supp : x₁ ∈ Set.Icc (1/C₀ - 1/(4*T)) (C₀ + 1/(4*T)) :=
      smoothed_supp_sharp hT hsupp x₁ hx₁ne
    have hx₁mem : x₁ ∈ Set.Icc u₀ (u₀ + L) := hsuppL x₁ hx₁ne
    have hlen : 1/(8*T) ≤ L := by
      have hsub : Set.Icc (x₁ - 1/(16*T)) (x₁ + 1/(16*T)) ⊆ Set.Icc u₀ (u₀ + L) := by
        intro u hu
        rw [Set.mem_Icc] at hu ⊢
        have habs : |u - x₁| ≤ 1/(16*T) := by
          rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
        exact hsuppL u (ne_of_gt (hx₁ u habs))
      have hle1 : x₁ - 1/(16*T) ≤ x₁ + 1/(16*T) := by
        have : (0:ℝ) < 1/(16*T) := by positivity
        linarith
      have hle2 : u₀ ≤ u₀ + L := by linarith
      have hfin : volume (Set.Icc u₀ (u₀ + L)) ≠ ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      have hreal := MeasureTheory.measureReal_mono hsub hfin
      have hval1 : (x₁ + 1/(16*T)) - (x₁ - 1/(16*T)) = 1/(8*T) := by ring
      have hval2 : (u₀ + L) - u₀ = L := by ring
      rw [Real.volume_real_Icc_of_le hle1, Real.volume_real_Icc_of_le hle2, hval1, hval2] at hreal
      exact hreal
    have hLhalf : L ≤ 1/2 := by
      have h1 : L ≤ (1/2)/M₂ := by
        rw [le_div_iff₀ hM₂pos]
        linarith [hML]
      have h2 : (1/2)/M₂ ≤ 1/2 := by
        rw [div_le_iff₀ hM₂pos]; linarith
      linarith
    have hT14 : 1/4 ≤ T := by
      have h3 : 1/(8*T) ≤ 1/2 := le_trans hlen hLhalf
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*T)] at h3
      linarith
    have hu₀abs : |u₀| ≤ 2*C₀ := by
      have h4T : 1/(4*T) ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < 4*T)]
        linarith
      rw [abs_le]
      constructor
      · have h1 : u₀ ≥ x₁ - L := by linarith [hx₁mem.2]
        have h2 : 1/C₀ - 1/(4*T) ≤ x₁ := hx₁supp.1
        have h5 : (0:ℝ) ≤ 1/C₀ := by positivity
        linarith
      · have h1 : u₀ ≤ C₀ + 1/(4*T) := by linarith [hx₁mem.1, hx₁supp.2]
        linarith
    -- the integers realising `m₂ u₀ ∈ ℤ`
    have hrat' : ∀ m₂ : ℤ, ∃ k : ℤ, m₂ ∈ R2 M₂ → (m₂:ℝ) * u₀ = (k:ℝ) := by
      intro m₂
      by_cases h : m₂ ∈ R2 M₂
      · obtain ⟨k, hk⟩ := hrat m₂ h
        exact ⟨k, fun _ => hk⟩
      · exact ⟨0, fun hh => absurd hh h⟩
    choose kk hkk using hrat'
    set Ψ : ℝ → ℝ := fun u => ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
        F (((m₂:ℝ)*u + ((kk m₂' - kk m₂ : ℤ) : ℝ))/(m₂':ℝ)) with hΨdef
    -- each centred term really is one of the terms of `Gfun`
    have hGge : ∀ u, Ψ u ≤ Gfun C₀ T M₂ f u := by
      intro u
      rw [hΨdef, Gfun]
      refine Finset.sum_le_sum fun m₂ hm₂ => Finset.sum_le_sum fun m₂' hm₂' => ?_
      have hjmem : (kk m₂' - kk m₂ : ℤ) ∈ Finset.Icc (-⌊2*C₀*M₂⌋) ⌊2*C₀*M₂⌋ := by
        have h2'mem : M₂ < (m₂':ℝ) := (Finset.mem_filter.mp hm₂').2
        have h2'le : (m₂':ℝ) ≤ 2*M₂ := R2_le hm₂'
        have hm₂mem : M₂ < (m₂:ℝ) := (Finset.mem_filter.mp hm₂).2
        have h2le : (m₂:ℝ) ≤ 2*M₂ := R2_le hm₂
        have hk1 : ((kk m₂ : ℤ) : ℝ) = (m₂:ℝ)*u₀ := (hkk m₂ hm₂).symm
        have hk2 : ((kk m₂' : ℤ) : ℝ) = (m₂':ℝ)*u₀ := (hkk m₂' hm₂').symm
        have hjval : ((kk m₂' - kk m₂ : ℤ) : ℝ) = ((m₂':ℝ) - (m₂:ℝ))*u₀ := by
          push_cast [hk1, hk2]; ring
        have hjabs : |((kk m₂' - kk m₂ : ℤ) : ℝ)| ≤ 2*C₀*M₂ := by
          rw [hjval, abs_mul]
          have hdiff : |(m₂':ℝ) - (m₂:ℝ)| ≤ M₂ := by
            rw [abs_le]; constructor <;> linarith
          calc |(m₂':ℝ) - (m₂:ℝ)| * |u₀| ≤ M₂ * (2*C₀) :=
                mul_le_mul hdiff hu₀abs (abs_nonneg _) (by linarith)
            _ = 2*C₀*M₂ := by ring
        rw [Finset.mem_Icc]
        constructor
        · have hx : (-(kk m₂' - kk m₂) : ℤ) ≤ ⌊2*C₀*M₂⌋ := by
            refine Int.le_floor.mpr ?_
            push_cast
            linarith [hjabs, neg_abs_le ((kk m₂' - kk m₂ : ℤ) : ℝ)]
          omega
        · refine Int.le_floor.mpr ?_
          linarith [hjabs, le_abs_self ((kk m₂' - kk m₂ : ℤ) : ℝ)]
      exact Finset.single_le_sum (f := fun j : ℤ => F (((m₂:ℝ)*u + (j:ℝ))/(m₂':ℝ)))
        (fun j _ => hFnn _) hjmem
    -- the support of `Ψ`
    have hΨsupp : ∀ u, Ψ u ≠ 0 → u ∈ Set.Icc u₀ (u₀ + 2*L) := by
      intro u hu
      by_contra hcon
      rw [Set.mem_Icc, not_and_or] at hcon
      apply hu
      rw [hΨdef]
      refine Finset.sum_eq_zero fun m₂ hm₂ => Finset.sum_eq_zero fun m₂' hm₂' => ?_
      have hm₂mem : M₂ < (m₂:ℝ) := (Finset.mem_filter.mp hm₂).2
      have h2'le : (m₂':ℝ) ≤ 2*M₂ := R2_le hm₂'
      have h2'pos : 0 < (m₂':ℝ) := R2_pos hM₂pos hm₂'
      have hmr : (1/2 : ℝ) < (m₂:ℝ)/(m₂':ℝ) := by
        rw [lt_div_iff₀ h2'pos]; nlinarith
      have hmrpos : 0 < (m₂:ℝ)/(m₂':ℝ) := by positivity
      have hk1 : ((kk m₂ : ℤ) : ℝ) = (m₂:ℝ)*u₀ := (hkk m₂ hm₂).symm
      have hk2 : ((kk m₂' : ℤ) : ℝ) = (m₂':ℝ)*u₀ := (hkk m₂' hm₂').symm
      have harg : ((m₂:ℝ)*u + ((kk m₂' - kk m₂ : ℤ) : ℝ))/(m₂':ℝ)
          = u₀ + (m₂:ℝ)/(m₂':ℝ) * (u - u₀) := by
        have hjk : ((kk m₂' - kk m₂ : ℤ) : ℝ) = ((m₂':ℝ) - (m₂:ℝ))*u₀ := by
          push_cast [hk1, hk2]; ring
        rw [hjk]
        field_simp
        ring
      rw [harg]
      by_contra hne
      have hmem := hsuppL _ hne
      rw [Set.mem_Icc] at hmem
      rcases hcon with hlt | hgt
      · have hneg : (m₂:ℝ)/(m₂':ℝ) * (u - u₀) < 0 :=
          mul_neg_of_pos_of_neg hmrpos (by linarith)
        linarith [hmem.1]
      · have hbig : u₀ + L < u₀ + (m₂:ℝ)/(m₂':ℝ) * (u - u₀) := by
          have h1 : (1/2:ℝ) * (2*L) < (m₂:ℝ)/(m₂':ℝ) * (u - u₀) := by
            nlinarith [hmr, hgt, hL]
          linarith
        linarith [hmem.2]
    have hΨcont : Continuous Ψ := by
      rw [hΨdef]
      refine continuous_finsetSum _ fun m₂ hm₂ => continuous_finsetSum _ fun m₂' hm₂' => ?_
      exact hFcont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _)
    have hΨnn : ∀ u, 0 ≤ Ψ u := by
      intro u
      rw [hΨdef]
      exact Finset.sum_nonneg fun m₂ hm₂ => Finset.sum_nonneg fun m₂' hm₂' => hFnn _
    have hterm_int : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂,
        Integrable (fun u : ℝ => F (((m₂:ℝ)*u + ((kk m₂' - kk m₂ : ℤ) : ℝ))/(m₂':ℝ))) :=
      fun m₂ hm₂ m₂' hm₂' => integrable_affine hFcont hFcs
        (ne_of_gt (R2_pos hM₂pos hm₂)) (ne_of_gt (R2_pos hM₂pos hm₂'))
    have hterm_val : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂,
        (∫ u, F (((m₂:ℝ)*u + ((kk m₂' - kk m₂ : ℤ) : ℝ))/(m₂':ℝ)))
          = ((m₂':ℝ)/(m₂:ℝ)) * V := by
      intro m₂ hm₂ m₂' hm₂'
      have h := integral_affine_eq (f := F) (c := (m₂:ℝ)) (d := (m₂':ℝ))
        (e := ((kk m₂' - kk m₂ : ℤ) : ℝ)) (ne_of_gt (R2_pos hM₂pos hm₂)) (R2_pos hM₂pos hm₂')
      rw [h, abs_of_pos (R2_pos hM₂pos hm₂)]
    have hΨint : ∫ u, Ψ u = (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ((m₂':ℝ)/(m₂:ℝ))) * V := by
      rw [hΨdef]
      rw [MeasureTheory.integral_finsetSum _ (fun m₂ hm₂ =>
        integrable_finsetSum _ (fun m₂' hm₂' => hterm_int m₂ hm₂ m₂' hm₂'))]
      have hinner : ∀ m₂ ∈ R2 M₂,
          (∫ u, ∑ m₂' ∈ R2 M₂, F (((m₂:ℝ)*u + ((kk m₂' - kk m₂ : ℤ) : ℝ))/(m₂':ℝ)))
            = ∑ m₂' ∈ R2 M₂, ((m₂':ℝ)/(m₂:ℝ)) * V := by
        intro m₂ hm₂
        rw [MeasureTheory.integral_finsetSum _ (fun m₂' hm₂' => hterm_int m₂ hm₂ m₂' hm₂')]
        exact Finset.sum_congr rfl fun m₂' hm₂' => hterm_val m₂ hm₂ m₂' hm₂'
      rw [Finset.sum_congr rfl hinner]
      simp only [Finset.sum_mul]
    have hcoef : ((R2 M₂).card : ℝ)^2 * (1/2)
        ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ((m₂':ℝ)/(m₂:ℝ)) := by
      calc ((R2 M₂).card : ℝ)^2 * (1/2)
          = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, (1/2 : ℝ) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ((m₂':ℝ)/(m₂:ℝ)) := by
            apply Finset.sum_le_sum; intro m₂ hm₂
            apply Finset.sum_le_sum; intro m₂' hm₂'
            have h2pos : 0 < (m₂:ℝ) := R2_pos hM₂pos hm₂
            rw [le_div_iff₀ h2pos]
            have h1 : (m₂:ℝ) ≤ 2*M₂ := R2_le hm₂
            have h2 : M₂ < (m₂':ℝ) := (Finset.mem_filter.mp hm₂').2
            linarith
    have hΨlow : M₂^2/8 * V ≤ ∫ u, Ψ u := by
      rw [hΨint]
      have hcard := R2_card_ge hM₂
      have hkey : M₂^2/8 ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ((m₂':ℝ)/(m₂:ℝ)) := by
        nlinarith [hcoef, hcard]
      exact mul_le_mul_of_nonneg_right hkey hVpos.le
    have hCS := sq_integral_le_width hΨcont hΨnn (a := u₀) (b := u₀ + 2*L)
      (by linarith : u₀ < u₀ + 2*L) hΨsupp
    have hCS' : (∫ u, Ψ u)^2 ≤ (2*L) * ∫ u, (Ψ u)^2 := by
      rw [show (u₀ + 2*L) - u₀ = 2*L by ring] at hCS
      exact hCS
    -- integrability of `Gfun^2`
    have hGunfold : ∀ u : ℝ, Gfun C₀ T M₂ f u
        = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2*C₀*M₂⌋) ⌊2*C₀*M₂⌋,
            F (((m₂:ℝ)*u + (j:ℝ))/(m₂':ℝ)) := by
      intro u; rw [Gfun]
    have hGcont : Continuous (fun u => Gfun C₀ T M₂ f u) := by
      rw [show (fun u : ℝ => Gfun C₀ T M₂ f u) = fun u =>
          ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2*C₀*M₂⌋) ⌊2*C₀*M₂⌋,
            F (((m₂:ℝ)*u + (j:ℝ))/(m₂':ℝ)) from funext hGunfold]
      refine continuous_finsetSum _ fun m₂ hm₂ => continuous_finsetSum _ fun m₂' hm₂' =>
        continuous_finsetSum _ fun j hj => ?_
      exact hFcont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _)
    have hGcs : HasCompactSupport (fun u => Gfun C₀ T M₂ f u) := by
      have hfun : (fun u : ℝ => Gfun C₀ T M₂ f u)
          = fun u : ℝ => ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
              ∑ j ∈ Finset.Icc (-⌊2*C₀*M₂⌋) ⌊2*C₀*M₂⌋,
                F (((m₂:ℝ)*u + (j:ℝ))/(m₂':ℝ)) := funext hGunfold
      rw [hfun]
      have hfun2 : (fun u : ℝ => ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
              ∑ j ∈ Finset.Icc (-⌊2*C₀*M₂⌋) ⌊2*C₀*M₂⌋,
                F (((m₂:ℝ)*u + (j:ℝ))/(m₂':ℝ)))
          = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, (∑ j ∈ Finset.Icc (-⌊2*C₀*M₂⌋) ⌊2*C₀*M₂⌋,
              fun u : ℝ => F (((m₂:ℝ)*u + (j:ℝ))/(m₂':ℝ))) := by
        funext u
        simp only [Finset.sum_apply]
      rw [hfun2]
      refine HasCompactSupport.finset_sum fun m₂ hm₂ => HasCompactSupport.finset_sum
        fun m₂' hm₂' => HasCompactSupport.finset_sum fun j hj => ?_
      exact hasCompactSupport_affine hFcs (ne_of_gt (R2_pos hM₂pos hm₂))
        (ne_of_gt (R2_pos hM₂pos hm₂'))
    have hGint : Integrable (fun u => (Gfun C₀ T M₂ f u)^2) :=
      (hGcont.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hGcs)
    have hmono : ∫ u, (Ψ u)^2 ≤ ∫ u, (Gfun C₀ T M₂ f u)^2 :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
        hGint (Filter.Eventually.of_forall fun u => pow_le_pow_left₀ (hΨnn u) (hGge u) 2)
    have h2Lpos : (0:ℝ) < 2*L := by linarith
    have hkey : (1/64 : ℝ) * M₂^4 * V^2 ≤ (∫ u, Ψ u)^2 := by
      have h1 : (M₂^2/8*V)^2 ≤ (∫ u, Ψ u)^2 :=
        pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ M₂^2/8*V) hΨlow 2
      have h2 : (M₂^2/8*V)^2 = (1/64 : ℝ) * M₂^4 * V^2 := by ring_nf
      linarith [h1, h2]
    rw [div_le_iff₀ hL]
    have h1 : (∫ u, Ψ u)^2 ≤ (2*L) * ∫ u, (Gfun C₀ T M₂ f u)^2 :=
      le_trans hCS' (mul_le_mul_of_nonneg_left hmono h2Lpos.le)
    nlinarith [h1, hkey, hL]
end

end Work.GM.Affine
