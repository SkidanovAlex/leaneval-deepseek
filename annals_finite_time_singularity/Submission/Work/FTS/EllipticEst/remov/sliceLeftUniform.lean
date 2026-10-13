import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_left_le
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The *uniform* left-half slice estimate for `(u / cos)''`

For every `γ ∈ [1, 3/2]`, every `u` of class `C³` on `(0, π/2)` continuous on `[0, π/2]`
with `u 0 = u (π/2) = 0`, whose second, first and zeroth derivatives against the weights
`sin(2θ)^{-η}`, `1`, `1` are `θ`-integrable on `Iθ = [0, π/2]`, the second derivative of
the quotient `v = u / cos θ` is square integrable on the left half `[0, π/4]` against the
weight `sin(2θ)^{2-γ}`, and

  `∫_{[0,π/4]} (v'')² sin(2θ)^{2-γ} ≤ C (∫_{Iθ} (u'')² sin(2θ)^{-η} + ∫_{Iθ} (u')² + ∫_{Iθ} u²)`

with a **single constant `C = 2000` independent of `γ`** (and of `u`, `g`); this is the
uniform-in-`γ` form of `Work.FTS.EllipticEst.remov.slice_left_le`, where `γ` is quantified
*inside* the existential.  The pointwise core is the quotient-rule identity

  `(u/cos)'' = u''/cos + 2 u' sin/cos² + u (1 + sin²)/cos³`

(`deriv_deriv_div_cos` below) together with the elementary arithmetic estimate
`quarter_arith`; on `[0, π/4]` one has `1/2 ≤ cos θ ≤ 1`, `sin²θ ≤ 1`, `sin(2θ)^{-η} ≥ 1`
and `sin(2θ)^{2-γ} ≤ 1`.  No use is made of the equation `L₀u = g` or of the boundary
conditions, so the three integrability hypotheses on `Iθ` are only used to dominate the
right-hand side.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## Elementary real arithmetic -/

/-- Cauchy–Schwarz for three terms: `(x+y+z)² ≤ 3(x²+y²+z²)`. -/
private lemma sq_three (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z)]

/-- Arithmetic core of the pointwise bound: if `c ∈ [1/2, 1]`, `s² ≤ 1`, `se ≥ 1`,
`w ∈ [0,1]` and `a c³ = U₂ c² + 2 U₁ s c + U₀ (1 + s²)`, then
`a² w ≤ 2000 (U₂² se + U₁² + U₀²)`. -/
private lemma quarter_arith {c s w se a U2 U1 U0 : ℝ}
    (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 1) (hs : s ^ 2 ≤ 1) (hse : 1 ≤ se)
    (_hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (ha : a * c ^ 3 = U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) :
    a ^ 2 * w ≤ 2000 * (U2 ^ 2 * se + U1 ^ 2 + U0 ^ 2) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc1
  have hc2sq : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc2
  have hc4le : c ^ 4 ≤ 1 := pow_le_one₀ hc0.le hc2
  have hc6 : (1 : ℝ) / 64 ≤ c ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hc1 6
    norm_num at h
    linarith
  have hsc : s ^ 2 * c ^ 2 ≤ 1 := by
    calc s ^ 2 * c ^ 2 ≤ 1 * 1 := mul_le_mul hs hc2sq (sq_nonneg c) (by norm_num)
      _ = 1 := by ring
  have h1s2 : (1 + s ^ 2) ^ 2 ≤ 4 := by
    have h : (1 + s ^ 2) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    norm_num at h
    exact h
  have hN : (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2
      ≤ 3 * (U2 ^ 2 + 4 * U1 ^ 2 + 4 * U0 ^ 2) := by
    have h0 := sq_three (U2 * c ^ 2) (2 * U1 * s * c) (U0 * (1 + s ^ 2))
    have e1 : (U2 * c ^ 2) ^ 2 ≤ U2 ^ 2 := by nlinarith [hc4le, sq_nonneg U2]
    have e2 : (2 * U1 * s * c) ^ 2 ≤ 4 * U1 ^ 2 := by nlinarith [hsc, sq_nonneg U1]
    have e3 : (U0 * (1 + s ^ 2)) ^ 2 ≤ 4 * U0 ^ 2 := by nlinarith [h1s2, sq_nonneg U0]
    nlinarith [h0, e1, e2, e3]
  have ha2 : a ^ 2 * c ^ 6 = (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := by
    have h : (a * c ^ 3) ^ 2 = (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := by
      rw [ha]
    nlinarith [h]
  have ha_le : a ^ 2 ≤ 64 * (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := by
    have h : a ^ 2 * ((1 : ℝ) / 64) ≤ a ^ 2 * c ^ 6 :=
      mul_le_mul_of_nonneg_left hc6 (sq_nonneg a)
    nlinarith [h, ha2]
  calc a ^ 2 * w ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left hw1 (sq_nonneg a)
    _ = a ^ 2 := by ring
    _ ≤ 64 * (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := ha_le
    _ ≤ 64 * (3 * (U2 ^ 2 + 4 * U1 ^ 2 + 4 * U0 ^ 2)) := by
        have h := mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 64)
        linarith
    _ ≤ 2000 * (U2 ^ 2 * se + U1 ^ 2 + U0 ^ 2) := by
        nlinarith [hse, sq_nonneg U2, sq_nonneg U1, sq_nonneg U0]

/-- `cos θ ≥ 1/2` on `[0, π/4]`. -/
private lemma cos_ge_half {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (1 : ℝ) / 2 ≤ Real.cos θ := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 3) hθ.1
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos, hθ.2])
  rwa [Real.cos_pi_div_three] at h

/-! ## The derivative identities for `u / cos` -/

/-- First derivative of `u / cos`: `(u/cos)' = u'/cos + u sin/cos²`. -/
private lemma deriv_div_cos (u : ℝ → ℝ) (h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun s => u s / Real.cos s) θ
      = deriv u θ / Real.cos θ + u θ * Real.sin θ / (Real.cos θ) ^ 2 := by
  have hdu : DifferentiableAt ℝ u θ :=
    (h3.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [deriv_fun_div hdu Real.differentiableAt_cos hcos, Real.deriv_cos]
  field_simp
  ring

/-- Second derivative of `u / cos`:
`(u/cos)'' = u''/cos + 2 u' sin/cos² + u (1 + sin²)/cos³`. -/
private lemma deriv_deriv_div_cos (u : ℝ → ℝ) (h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
      = deriv (deriv u) θ / Real.cos θ + 2 * deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
        + u θ * (1 + (Real.sin θ) ^ 2) / (Real.cos θ) ^ 3 := by
  have hdu : DifferentiableAt ℝ u θ :=
    (h3.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have h2 : ContDiffOn ℝ 2 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    h3.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv u) θ :=
    (h2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hev : (fun t : ℝ => deriv (fun s => u s / Real.cos s) t) =ᶠ[nhds θ]
      (fun t => deriv u t / Real.cos t + u t * Real.sin t / (Real.cos t) ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact deriv_div_cos u h3 ht
  rw [hev.deriv_eq]
  have h1' : HasDerivAt (fun t => deriv u t / Real.cos t)
      (deriv (deriv u) θ / Real.cos θ + deriv u θ * Real.sin θ / (Real.cos θ) ^ 2) θ := by
    have h := hdd.hasDerivAt.div (Real.hasDerivAt_cos θ) hcos
    convert h using 1
    field_simp
    ring
  have h2' : HasDerivAt (fun t => u t * Real.sin t / (Real.cos t) ^ 2)
      (deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
        + u θ * (1 + (Real.sin θ) ^ 2) / (Real.cos θ) ^ 3) θ := by
    have hA : HasDerivAt (fun t => u t * Real.sin t)
        (deriv u θ * Real.sin θ + u θ * Real.cos θ) θ :=
      hdu.hasDerivAt.mul (Real.hasDerivAt_sin θ)
    have hB : HasDerivAt (fun t : ℝ => (Real.cos t) ^ 2) (2 * Real.cos θ * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow 2
      convert h using 1
      ring
    have h := hA.div hB (pow_ne_zero 2 hcos)
    convert h using 1
    rw [← Real.sin_sq_add_cos_sq θ]
    field_simp
    ring
  have hsum : HasDerivAt (fun t => deriv u t / Real.cos t + u t * Real.sin t / (Real.cos t) ^ 2)
      (deriv (deriv u) θ / Real.cos θ + deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
        + (deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
            + u θ * (1 + (Real.sin θ) ^ 2) / (Real.cos θ) ^ 3)) θ :=
    h1'.add h2'
  rw [hsum.deriv]
  ring

/-! ## The pointwise bound on `[0, π/4]` -/

/-- Pointwise domination on `[0, π/4]`: the integrand of the left slice is bounded by
`2000` times the sum of the three energy densities. -/
private lemma sec_second_deriv_le (u : ℝ → ℝ) (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
  intro θ hθ
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases eq_or_lt_of_le hθ.1 with h0 | hpos
  · rw [← h0]
    have hz : Real.rpow (Real.sin (2 * 0)) (2 - γ) = 0 := by
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
    rw [hz, mul_zero]
    have hsE : 0 ≤ sEta (0 : ℝ) := by
      rw [sEta]
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      exact Real.rpow_nonneg le_rfl _
    have h1 : 0 ≤ (deriv (deriv u) 0) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (deriv u 0) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (u 0) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 hsE]
  · have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, by linarith [hθ.2, hpi]⟩
    have hid := deriv_deriv_div_cos u h3 hθIoo
    have hc1 : (1 : ℝ) / 2 ≤ Real.cos θ := cos_ge_half hθ
    have hc2 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hs : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hsin2nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, hpi])
    have hse : 1 ≤ sEta θ := by
      rw [sEta]
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, hpi])
      · exact Real.sin_le_one _
      · have := Work.Spaces.eta_pos
        linarith
    have hw0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin2nn _
    have hw1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
      Real.rpow_le_one hsin2nn (Real.sin_le_one _) (by linarith)
    have ha : deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ * (Real.cos θ) ^ 3
        = deriv (deriv u) θ * (Real.cos θ) ^ 2 + 2 * deriv u θ * Real.sin θ * Real.cos θ
          + u θ * (1 + (Real.sin θ) ^ 2) := by
      rw [hid]
      have hcne : Real.cos θ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hc1)
      field_simp
    exact quarter_arith hc1 hc2 hs hse hw0 hw1 ha

/-! ## Two measure theory helpers -/

/-- If `G` is a.e. strongly measurable on `s`, nonnegative there, and dominated there by an
integrable `H`, then `G` is integrable on `s`. -/
private lemma integrableOn_of_le {G H : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hH : MeasureTheory.IntegrableOn H s) (hG0 : ∀ x ∈ s, 0 ≤ G x)
    (hG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict s))
    (hle : ∀ x ∈ s, G x ≤ H x) : MeasureTheory.IntegrableOn G s := by
  refine MeasureTheory.Integrable.mono' hH hG ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) hs] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hG0 x hx)]
  exact hle x hx

/-- Integral comparison across an inclusion of sets, for a nonnegative majorant. -/
private lemma setIntegral_le_of_pointwise {G H : ℝ → ℝ} {s t : Set ℝ} (hst : s ⊆ t)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hG : MeasureTheory.IntegrableOn G s)
    (hH : MeasureTheory.IntegrableOn H t) (hle : ∀ x ∈ s, G x ≤ H x)
    (hH0 : ∀ x ∈ t, 0 ≤ H x) : ∫ x in s, G x ≤ ∫ x in t, H x := by
  have h1 : ∫ x in s, G x ≤ ∫ x in s, H x :=
    MeasureTheory.setIntegral_mono_on hG (hH.mono_set hst) hs hle
  have h2 : ∫ x in s, H x ≤ ∫ x in t, H x := by
    refine MeasureTheory.setIntegral_mono_set hH ?_
      (Filter.Eventually.of_forall (fun x hx => hst hx))
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) ht] with x hx
    exact hH0 x hx
  linarith

/-! ## The slice estimate -/

theorem sliceLeftUniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ =>
            (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 4)) ∧
        (∫ θ in Set.Icc 0 (Real.pi / 4),
            (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  refine ⟨2000, by norm_num, ?_⟩
  intro γ u g hγ1 hγ2 h3 hcont hu0 hpi hL hInt2 hInt1 hInt0
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hpt := sec_second_deriv_le u γ hγ1 hγ2 h3
  have hHIθ : MeasureTheory.IntegrableOn
      (fun θ => 2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2))
      Work.Spaces.Iθ := ((hInt2.add hInt1).add hInt0).const_mul 2000
  have hHIcc : MeasureTheory.IntegrableOn
      (fun θ => 2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2))
      (Set.Icc 0 (Real.pi / 4)) := hHIθ.mono_set hsub
  have hH0 : ∀ x ∈ Work.Spaces.Iθ,
      0 ≤ 2000 * ((deriv (deriv u) x) ^ 2 * sEta x + (deriv u x) ^ 2 + (u x) ^ 2) := by
    intro x hx
    have hsx : 0 ≤ sEta x := by
      rw [sEta]
      exact Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
          (by linarith [hx.2, Real.pi_pos])) _
    have h1 : 0 ≤ (deriv (deriv u) x) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (deriv u x) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (u x) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 hsx]
  have hG0 : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      0 ≤ (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2 *
        Real.rpow (Real.sin (2 * x)) (2 - γ) := by
    intro x hx
    refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos])
  have hGmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 4))) := by
    have h1 : Measurable
        (fun θ : ℝ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) :=
      measurable_deriv (fun t => deriv (fun s => u s / Real.cos s) t)
    have h2 : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun x => Or.inr (by linarith))
    exact ((h1.aestronglyMeasurable.pow 2).mul h2.measurable.aestronglyMeasurable)
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 4)) :=
    integrableOn_of_le measurableSet_Icc hHIcc hG0 hGmeas (fun x hx => hpt x hx)
  constructor
  · exact hGint
  · calc (∫ θ in Set.Icc 0 (Real.pi / 4),
          (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2) :=
          setIntegral_le_of_pointwise hsub measurableSet_Icc measurableSet_Icc hGint hHIθ
            (fun x hx => hpt x hx) hH0
      _ = 2000 * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          have hsplit1 : (∫ a in Work.Spaces.Iθ,
                (deriv (deriv u) a) ^ 2 * sEta a + (deriv u a) ^ 2)
              = (∫ a in Work.Spaces.Iθ, (deriv (deriv u) a) ^ 2 * sEta a)
                + (∫ a in Work.Spaces.Iθ, (deriv u a) ^ 2) :=
            MeasureTheory.integral_add hInt2 hInt1
          have hsplit2 : (∫ a in Work.Spaces.Iθ,
                ((deriv (deriv u) a) ^ 2 * sEta a + (deriv u a) ^ 2) + (u a) ^ 2)
              = (∫ a in Work.Spaces.Iθ, (deriv (deriv u) a) ^ 2 * sEta a + (deriv u a) ^ 2)
                + (∫ a in Work.Spaces.Iθ, (u a) ^ 2) :=
            MeasureTheory.integral_add (hInt2.add hInt1) hInt0
          rw [hsplit2, hsplit1]

end Work.FTS.EllipticEst.remov
