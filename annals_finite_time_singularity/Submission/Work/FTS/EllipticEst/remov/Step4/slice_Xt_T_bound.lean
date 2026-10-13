import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities
import Submission.Work.FTS.EllipticEst.remov.slice_Q_pointwise
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.Step4

set_option autoImplicit false

/-
# Step 4 (Elgindi §H2, tex 931-953): the weighted bound for `(tan θ·u)''·T`

With `v = u / cos θ`, `X = (tan θ·u)''`, `σ = sin(2θ)^{2-γ}` and
`T := sin θ·v'' - 4 cos θ·v' + 5 sin θ·v` (the right-hand side of the differentiated equation),
this proves `∫ X·T·σ ≤ 4 ∫(v'')²σ + 7 ∫(v')²σ + 7 ∫v²σ`, together with the integrability of
`X·T·σ`.

Route: `slice_v_identities` gives on `(0, π/2)` that
`X = sin θ·v'' + 2 cos θ·v' - sin θ·v`, so `X·T` is the product of the two linear forms
`(sinθ, 2cosθ, -sinθ)·(v'',v',v)` and `(sinθ, -4cosθ, 5sinθ)·(v'',v',v)`, and
`Work.FTS.EllipticEst.remov.slice_Q_pointwise` gives pointwise
`X·T ≤ 4 sin²θ(v'')² + 7(v')² + 7v² ≤ 4(v'')² + 7(v')² + 7v²`.
For integrability use the absolute-value domination
`|X·T| ≤ (X² + T²)/2 ≤ 3(v'')² + 30(v')² + 39v²` (from `(a+b+c)² ≤ 3(a²+b²+c²)`), then
`Integrable.mono'`.  As usual the pointwise identities hold on `(0, π/2)`, which equals
`Iθ = [0, π/2]` up to the null set `{0, π/2}`.
-/

/-! ### The null set `{0, π/2}` -/

/-- `[0, π/2]` and `(0, π/2)` agree up to a null set. -/
private lemma sliceXTB_ae_eq_Icc_Ioo :
    (Set.Icc 0 (Real.pi / 2) : Set ℝ) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · have hsub : Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) ⊆
        ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        by_contra hne
        exact hx.2 ⟨h, lt_of_le_of_ne hx.1.2 hne⟩
    have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
      (Set.Finite.insert (0 : ℝ) (Set.finite_singleton (Real.pi / 2))).measure_zero _
    exact MeasureTheory.measure_mono_null hsub hnull
  · have h0 : Set.Ioo 0 (Real.pi / 2) \ Set.Icc 0 (Real.pi / 2) = ∅ :=
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self
    rw [h0, MeasureTheory.measure_empty]

/-- Consequently `volume.restrict Iθ = volume.restrict (0, π/2)`. -/
private lemma sliceXTB_restrict_Iθ_eq_Ioo :
    (volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  simpa [Work.Spaces.Iθ] using
    MeasureTheory.Measure.restrict_congr_set sliceXTB_ae_eq_Icc_Ioo

/-! ### Elementary pointwise bounds for the two linear forms

`X = s a + 2 t b - s c` and `T = s a - 4 t b + 5 s c` with `s = sin θ`, `t = cos θ` and
`s² + t² = 1`: Cauchy–Schwarz for three terms gives `X² ≤ 3(a² + 4b² + c²)` and
`T² ≤ 3(a² + 16b² + 25c²)`, whence `|X·T| ≤ (X² + T²)/2 ≤ 3a² + 30b² + 39c²`. -/

private lemma Xsq_le (θ a b c : ℝ) :
    (Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c) ^ 2
      ≤ 3 * (a ^ 2 + 4 * b ^ 2 + c ^ 2) := by
  have h := Real.sin_sq_add_cos_sq θ
  have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  nlinarith [sq_nonneg (Real.sin θ * a - 2 * Real.cos θ * b),
             sq_nonneg (2 * Real.cos θ * b + Real.sin θ * c),
             sq_nonneg (Real.sin θ * c + Real.sin θ * a)]

private lemma Tsq_le (θ a b c : ℝ) :
    (Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c) ^ 2
      ≤ 3 * (a ^ 2 + 16 * b ^ 2 + 25 * c ^ 2) := by
  have h := Real.sin_sq_add_cos_sq θ
  have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  nlinarith [sq_nonneg (Real.sin θ * a + 4 * Real.cos θ * b),
             sq_nonneg (4 * Real.cos θ * b + 5 * Real.sin θ * c),
             sq_nonneg (5 * Real.sin θ * c - Real.sin θ * a)]

private lemma abs_XT_le (θ a b c : ℝ) :
    |(Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c)
      * (Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c)|
      ≤ 3 * a ^ 2 + 30 * b ^ 2 + 39 * c ^ 2 := by
  set A := Real.sin θ * a + 2 * Real.cos θ * b - Real.sin θ * c with hA
  set B := Real.sin θ * a - 4 * Real.cos θ * b + 5 * Real.sin θ * c with hB
  have h2 : |A * B| ≤ (A ^ 2 + B ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
  have h3a : A ^ 2 ≤ 3 * (a ^ 2 + 4 * b ^ 2 + c ^ 2) := by
    rw [hA]; exact Xsq_le θ a b c
  have h3b : B ^ 2 ≤ 3 * (a ^ 2 + 16 * b ^ 2 + 25 * c ^ 2) := by
    rw [hB]; exact Tsq_le θ a b c
  linarith

/-! ### Splitting a sum of three weighted integrals -/

private lemma integral_three {μ : Measure ℝ} {F G H : ℝ → ℝ}
    (hF : Integrable F μ) (hG : Integrable G μ) (hH : Integrable H μ) (c d e : ℝ) :
    ∫ θ, (c * F θ + d * G θ + e * H θ) ∂μ
      = c * (∫ θ, F θ ∂μ) + d * (∫ θ, G θ ∂μ) + e * (∫ θ, H θ ∂μ) := by
  rw [integral_add (f := fun θ => c * F θ + d * G θ) (g := fun θ => e * H θ)
        ((hF.const_mul c).add (hG.const_mul d)) (hH.const_mul e),
      integral_add (f := fun θ => c * F θ) (g := fun θ => d * G θ)
        (hF.const_mul c) (hG.const_mul d),
      integral_const_mul, integral_const_mul, integral_const_mul]

private lemma setIntegral_three (s : Set ℝ) {F G H : ℝ → ℝ}
    (hF : IntegrableOn F s) (hG : IntegrableOn G s) (hH : IntegrableOn H s) (c d e : ℝ) :
    ∫ θ in s, c * F θ + d * G θ + e * H θ
      = c * (∫ θ in s, F θ) + d * (∫ θ in s, G θ) + e * (∫ θ in s, H θ) :=
  integral_three (μ := volume.restrict s) hF hG hH c d e

/-! ### The main statement -/

theorem slice_Xt_T_bound (γ : ℝ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hV2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY3 : MeasureTheory.IntegrableOn (fun θ =>
        (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        deriv (deriv (fun t => Real.tan t * u t)) θ *
        (Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
          + 5 * Real.sin θ * (u θ / Real.cos θ)) *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun t => Real.tan t * u t)) θ *
          (Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
            - 4 * Real.cos θ * deriv (fun t => u t / Real.cos t) θ
            + 5 * Real.sin θ * (u θ / Real.cos θ)) *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 4 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 7 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 7 * (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  classical
  -- the open interval and the null-set identification
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
  have hsopen : IsOpen s := by rw [hs_def]; exact isOpen_Ioo
  have hsmeas : MeasurableSet s := hsopen.measurableSet
  have hrestrict : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict s := by
    rw [hs_def]; exact sliceXTB_restrict_Iθ_eq_Ioo
  -- abbreviations for `v`, `v'`, `v''`, `X`, `T`, `σ`
  let v0 : ℝ → ℝ := fun θ => u θ / Real.cos θ
  let v1 : ℝ → ℝ := deriv v0
  let v2 : ℝ → ℝ := deriv v1
  let X : ℝ → ℝ := deriv (deriv (fun t => Real.tan t * u t))
  let T : ℝ → ℝ := fun θ => Real.sin θ * v2 θ - 4 * Real.cos θ * v1 θ + 5 * Real.sin θ * v0 θ
  let σ : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)
  change MeasureTheory.IntegrableOn (fun θ => X θ * T θ * σ θ) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, X θ * T θ * σ θ)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, (v2 θ) ^ 2 * σ θ)
          + 7 * (∫ θ in Work.Spaces.Iθ, (v1 θ) ^ 2 * σ θ)
          + 7 * (∫ θ in Work.Spaces.Iθ, (v0 θ) ^ 2 * σ θ)
  -- the three weighted square integrability hypotheses, on `s`
  have hV2s : Integrable (fun θ => (v2 θ) ^ 2 * σ θ) (volume.restrict s) := by
    rw [← hrestrict]; exact hV2
  have hY2s : Integrable (fun θ => (v1 θ) ^ 2 * σ θ) (volume.restrict s) := by
    rw [← hrestrict]; exact hY2
  have hY3s : Integrable (fun θ => (v0 θ) ^ 2 * σ θ) (volume.restrict s) := by
    rw [← hrestrict]; exact hY3
  -- elementary facts on `s`
  have hcos_ne : ∀ θ ∈ s, Real.cos θ ≠ 0 := by
    intro θ hθ
    rw [hs_def] at hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩)
  have hsinpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    rw [hs_def] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ0 : ∀ θ ∈ s, 0 ≤ σ θ := fun θ hθ =>
    Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _
  -- regularity
  have htu : ContDiffOn ℝ 3 (fun t => Real.tan t * u t) s := by
    intro θ hθ
    exact ((Real.contDiffAt_tan.mpr (hcos_ne θ hθ)).mul
      (hu.contDiffAt (hsopen.mem_nhds hθ))).contDiffWithinAt
  have hv0C : ContDiffOn ℝ 3 v0 s := hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hv1C : ContDiffOn ℝ 2 v1 s := hv0C.deriv_of_isOpen hsopen (by norm_num)
  have hv2C : ContDiffOn ℝ 1 v2 s := hv1C.deriv_of_isOpen hsopen (by norm_num)
  have hXC : ContDiffOn ℝ 1 X s := by
    have h1 : ContDiffOn ℝ 2 (deriv (fun t => Real.tan t * u t)) s :=
      htu.deriv_of_isOpen hsopen (by norm_num)
    exact h1.deriv_of_isOpen hsopen (by norm_num)
  -- a.e. strong measurability of the pieces
  have hm0 : AEStronglyMeasurable v0 (volume.restrict s) :=
    hv0C.continuousOn.aestronglyMeasurable hsmeas
  have hm1 : AEStronglyMeasurable v1 (volume.restrict s) :=
    hv1C.continuousOn.aestronglyMeasurable hsmeas
  have hm2 : AEStronglyMeasurable v2 (volume.restrict s) :=
    hv2C.continuousOn.aestronglyMeasurable hsmeas
  have hmX : AEStronglyMeasurable X (volume.restrict s) :=
    hXC.continuousOn.aestronglyMeasurable hsmeas
  have hmsin : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ) (volume.restrict s) :=
    Real.continuous_sin.continuousOn.aestronglyMeasurable hsmeas
  have hmcos : AEStronglyMeasurable (fun θ : ℝ => Real.cos θ) (volume.restrict s) :=
    Real.continuous_cos.continuousOn.aestronglyMeasurable hsmeas
  have hmT : AEStronglyMeasurable T (volume.restrict s) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ * v2 θ) (volume.restrict s) :=
      hmsin.mul hm2
    have h2 : AEStronglyMeasurable (fun θ : ℝ => 4 * Real.cos θ * v1 θ) (volume.restrict s) :=
      (hmcos.const_mul 4).mul hm1
    have h3 : AEStronglyMeasurable (fun θ : ℝ => 5 * Real.sin θ * v0 θ) (volume.restrict s) :=
      (hmsin.const_mul 5).mul hm0
    exact (h1.sub h2).add h3
  have hmσ : AEStronglyMeasurable σ (volume.restrict s) := by
    refine (ContinuousOn.rpow_const ?_ ?_).aestronglyMeasurable hsmeas
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      exact Or.inl (ne_of_gt (hsinpos θ hθ))
  -- the pointwise identity for `X`
  have hXeq : ∀ θ ∈ s, X θ = Real.sin θ * v2 θ + 2 * Real.cos θ * v1 θ - Real.sin θ * v0 θ :=
    fun θ hθ => (slice_v_identities u hu θ (by rw [hs_def] at hθ; exact hθ)).2.2.1
  -- `X·T ≤ 4 (v'')² + 7 (v')² + 7 v²`
  have hQT : ∀ θ ∈ s, X θ * T θ ≤ 4 * (v2 θ) ^ 2 + 7 * (v1 θ) ^ 2 + 7 * (v0 θ) ^ 2 := by
    intro θ hθ
    have hX := hXeq θ hθ
    have hT : T θ = Real.sin θ * v2 θ - 4 * Real.cos θ * v1 θ + 5 * Real.sin θ * v0 θ := rfl
    have hQ := slice_Q_pointwise θ (v2 θ) (v1 θ) (v0 θ)
    rw [hX, hT]
    nlinarith [hQ, Real.sin_sq_le_one θ, sq_nonneg (v2 θ)]
  -- `|X·T| ≤ 3 (v'')² + 30 (v')² + 39 v²`
  have hXT : ∀ θ ∈ s, |X θ * T θ| ≤ 3 * (v2 θ) ^ 2 + 30 * (v1 θ) ^ 2 + 39 * (v0 θ) ^ 2 := by
    intro θ hθ
    have hX := hXeq θ hθ
    have hT : T θ = Real.sin θ * v2 θ - 4 * Real.cos θ * v1 θ + 5 * Real.sin θ * v0 θ := rfl
    rw [hX, hT]
    exact abs_XT_le θ (v2 θ) (v1 θ) (v0 θ)
  -- integrability of `X·T·σ`
  have hdom : Integrable (fun θ => 3 * ((v2 θ) ^ 2 * σ θ) + 30 * ((v1 θ) ^ 2 * σ θ)
      + 39 * ((v0 θ) ^ 2 * σ θ)) (volume.restrict s) :=
    ((hV2s.const_mul 3).add (hY2s.const_mul 30)).add (hY3s.const_mul 39)
  have hmain : Integrable (fun θ => X θ * T θ * σ θ) (volume.restrict s) := by
    refine Integrable.mono' hdom ((hmX.mul hmT).mul hmσ) ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    have hσ := hσ0 θ hθ
    have h1 := mul_le_mul_of_nonneg_right (hXT θ hθ) hσ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ]
    calc |X θ * T θ| * σ θ
        ≤ (3 * (v2 θ) ^ 2 + 30 * (v1 θ) ^ 2 + 39 * (v0 θ) ^ 2) * σ θ := h1
      _ = 3 * ((v2 θ) ^ 2 * σ θ) + 30 * ((v1 θ) ^ 2 * σ θ) + 39 * ((v0 θ) ^ 2 * σ θ) := by
          ring
  -- the integral comparison
  have hgint : Integrable (fun θ => 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ)
      + 7 * ((v0 θ) ^ 2 * σ θ)) (volume.restrict s) :=
    ((hV2s.const_mul 4).add (hY2s.const_mul 7)).add (hY3s.const_mul 7)
  have hmono : (∫ θ in s, X θ * T θ * σ θ)
      ≤ ∫ θ in s, 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ)
          + 7 * ((v0 θ) ^ 2 * σ θ) := by
    refine setIntegral_mono_ae_restrict hmain hgint ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    have hσ := hσ0 θ hθ
    have h1 := mul_le_mul_of_nonneg_right (hQT θ hθ) hσ
    calc X θ * T θ * σ θ = (X θ * T θ) * σ θ := by ring
      _ ≤ (4 * (v2 θ) ^ 2 + 7 * (v1 θ) ^ 2 + 7 * (v0 θ) ^ 2) * σ θ := h1
      _ = 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ) + 7 * ((v0 θ) ^ 2 * σ θ) := by
          ring
  have hsplit : (∫ θ in s, 4 * ((v2 θ) ^ 2 * σ θ) + 7 * ((v1 θ) ^ 2 * σ θ)
        + 7 * ((v0 θ) ^ 2 * σ θ))
      = 4 * (∫ θ in s, (v2 θ) ^ 2 * σ θ) + 7 * (∫ θ in s, (v1 θ) ^ 2 * σ θ)
        + 7 * (∫ θ in s, (v0 θ) ^ 2 * σ θ) :=
    setIntegral_three s hV2s hY2s hY3s 4 7 7
  refine ⟨?_, ?_⟩
  · rw [MeasureTheory.IntegrableOn, hrestrict]
    exact hmain
  · rw [hrestrict]
    exact le_trans hmono (le_of_eq hsplit)

end Work.FTS.EllipticEst.remov.Step4
