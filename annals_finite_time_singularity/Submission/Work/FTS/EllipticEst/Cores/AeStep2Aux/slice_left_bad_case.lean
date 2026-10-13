import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux.hasDerivAt_J
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux.deriv_limit_of_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux
set_option autoImplicit false

theorem slice_left_bad_case {f : ℝ → ℝ} {d b : ℝ} (hd : 0 < d) (hd2 : d ≤ Real.pi / 2)
    (hb : 0 < b) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 d))
    (h0 : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hPhi : ∀ θ ∈ Set.Ioo 0 d, Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f θ ≤ -b)
    (hint : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f) (Set.Ioo 0 d)) : False := by
  -- ===== Step 1: setup =====
  set θ₁ : ℝ := d / 2 with hθ₁
  set θ₂ : ℝ := d / 4 with hθ₂
  have hθ₂pos : 0 < θ₂ := by rw [hθ₂]; linarith
  have hθ₁pos : 0 < θ₁ := by rw [hθ₁]; linarith
  have hθ₂θ₁ : θ₂ < θ₁ := by rw [hθ₂, hθ₁]; linarith
  have hθ₁d : θ₁ < d := by rw [hθ₁]; linarith
  have hθ₂d : θ₂ < d := by rw [hθ₂]; linarith
  have hsubd : Set.Ioo 0 θ₂ ⊆ Set.Ioo 0 d := fun x hx => ⟨hx.1, lt_trans hx.2 hθ₂d⟩
  have hsinpos : ∀ θ ∈ Set.Ioo 0 d, 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, hd2])
  have hsigpos : ∀ θ ∈ Set.Ioo 0 d, 0 < sig θ := fun θ hθ =>
    sig_pos ⟨hθ.1, lt_of_lt_of_le hθ.2 hd2⟩
  -- ===== Step 2: J and its derivative =====
  let J : ℝ → ℝ := fun θ => (f θ) ^ 2 / Real.sin (2 * θ)
  have hJd : ∀ θ ∈ Set.Ioo 0 d,
      HasDerivAt J (2 * Phi f θ / (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)) θ := by
    intro θ hθ
    have hmem : Set.Ioo 0 d ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hfd : DifferentiableOn ℝ f (Set.Ioo 0 d) := hf.differentiableOn (by simp)
    have hd1 : HasDerivAt f (deriv f θ) θ := (hfd.differentiableAt hmem).hasDerivAt
    have hdf : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 d) :=
      hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    have hd2 : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
      ((hdf.differentiableOn (by simp)).differentiableAt hmem).hasDerivAt
    exact SliceLeftAux.hasDerivAt_J (hsinpos θ hθ) hd1 hd2
  -- ===== Step 3: the pointwise bound deriv J ≤ -2 b sin^(eta-1) =====
  have hJb : ∀ θ ∈ Set.Ioo 0 d, deriv J θ ≤ -2 * b * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
    intro θ hθ
    rw [(hJd θ hθ).deriv]
    have hs := hsinpos θ hθ
    have hs1 : 0 < (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := Real.rpow_pos_of_pos hs _
    have h1 : 2 * Phi f θ ≤ 2 * (-b) := by linarith [hPhi θ hθ]
    have h2 : 2 * Phi f θ / (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
        ≤ 2 * (-b) / (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hs1)
    have h3 : 2 * (-b) / (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
        = -2 * b * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
      rw [show (Work.Spaces.eta - 1 : ℝ) = -(1 - Work.Spaces.eta) by ring,
        Real.rpow_neg (le_of_lt hs)]
      rw [div_eq_mul_inv]
      ring
    rw [h3] at h2
    exact h2
  have hJb' : ∀ θ ∈ Set.Ioo 0 d, deriv J θ + 2 * b ≤ 0 := by
    intro θ hθ
    have h1 := hJb θ hθ
    have hs := hsinpos θ hθ
    have hge : (1:ℝ) ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
      have hη : Work.Spaces.eta - 1 ≤ 0 := by rw [Work.Spaces.eta]; norm_num
      have h := Real.rpow_le_rpow_of_nonpos hs (Real.sin_le_one (2 * θ)) hη
      rwa [Real.one_rpow] at h
    nlinarith [h1, hge, hb]
  -- ===== Step 4: J is bounded below on (0,θ₂) =====
  have hJlow : ∀ θ ∈ Set.Ioo 0 θ₂, 2 * b * (θ₁ - θ₂) ≤ J θ := by
    intro θ hθ
    have hle : θ ≤ θ₁ := le_of_lt (lt_trans hθ.2 hθ₂θ₁)
    have hsub : Set.Icc θ θ₁ ⊆ Set.Ioo 0 d := fun t ht =>
      ⟨lt_of_lt_of_le hθ.1 ht.1, lt_of_le_of_lt ht.2 hθ₁d⟩
    have hJcont : ContinuousOn (fun t : ℝ => (f t) ^ 2 / Real.sin (2 * t)) (Set.Icc θ θ₁) := by
      have hnum : ContinuousOn (fun t : ℝ => (f t) ^ 2) (Set.Icc θ θ₁) :=
        (hf.continuousOn.mono hsub).pow 2
      have hden : ContinuousOn (fun t : ℝ => Real.sin (2 * t)) (Set.Icc θ θ₁) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      exact hnum.div hden (fun t ht => ne_of_gt (hsinpos t (hsub ht)))
    have hcont : ContinuousOn (J + fun t : ℝ => 2 * b * t) (Set.Icc θ θ₁) :=
      hJcont.add (continuousOn_const.mul continuousOn_id)
    have hdiff : DifferentiableOn ℝ (J + fun t : ℝ => 2 * b * t) (interior (Set.Icc θ θ₁)) := by
      rw [interior_Icc]
      intro x hx
      have hxd : x ∈ Set.Ioo 0 d := ⟨lt_trans hθ.1 hx.1, lt_trans hx.2 hθ₁d⟩
      exact ((hJd x hxd).differentiableAt.add
        ((differentiableAt_const (c := 2 * b)).mul differentiableAt_id)).differentiableWithinAt
    have hderiv : ∀ x ∈ interior (Set.Icc θ θ₁), deriv (J + fun t : ℝ => 2 * b * t) x ≤ 0 := by
      intro x hx
      rw [interior_Icc] at hx
      have hxd : x ∈ Set.Ioo 0 d := ⟨lt_trans hθ.1 hx.1, lt_trans hx.2 hθ₁d⟩
      have hlin : HasDerivAt (fun t : ℝ => 2 * b * t) (2 * b) x := by
        simpa using (hasDerivAt_id x).const_mul (2 * b)
      have hsum : HasDerivAt (J + fun t : ℝ => 2 * b * t)
          (2 * Phi f x / (Real.sin (2 * x)) ^ (1 - Work.Spaces.eta) + 2 * b) x :=
        (hJd x hxd).add hlin
      rw [hsum.deriv, ← (hJd x hxd).deriv]
      exact hJb' x hxd
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc θ θ₁) hcont hdiff hderiv
    have h1 : (J + fun t : ℝ => 2 * b * t) θ₁ ≤ (J + fun t : ℝ => 2 * b * t) θ :=
      hanti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    have hJ1 : 0 ≤ J θ₁ := by
      have hs := hsinpos θ₁ ⟨hθ₁pos, hθ₁d⟩
      exact div_nonneg (sq_nonneg _) (le_of_lt hs)
    simp only [Pi.add_apply] at h1
    have hd : θ₁ - θ₂ ≤ θ₁ - θ := by linarith [hθ.2]
    have hstep : 2 * b * (θ₁ - θ₂) ≤ 2 * b * (θ₁ - θ) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    linarith [h1, hJ1, hstep]
  -- ===== Step 5: f² ≥ c₀ sin(2θ) on (0,θ₂) =====
  have hf2low : ∀ θ ∈ Set.Ioo 0 θ₂, 2 * b * (θ₁ - θ₂) * Real.sin (2 * θ) ≤ (f θ) ^ 2 := by
    intro θ hθ
    have hθd : θ ∈ Set.Ioo 0 d := hsubd ⟨hθ.1, hθ.2⟩
    have hs := hsinpos θ hθd
    have hlow := hJlow θ hθ
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
    have heq : J θ * Real.sin (2 * θ) = (f θ) ^ 2 := by
      change (f θ) ^ 2 / Real.sin (2 * θ) * Real.sin (2 * θ) = (f θ) ^ 2
      rw [div_mul_cancel₀ _ hsne]
    nlinarith [hlow, hs, heq]
  -- ===== Step 6: |f''| ≤ |Γ| / sqrt c₀ on (0,θ₂) =====
  have hf''b : ∀ θ ∈ Set.Ioo 0 θ₂,
      |deriv (deriv f) θ| ≤ |sliceIntegrand f θ| / Real.sqrt (2 * b * (θ₁ - θ₂)) := by
    intro θ hθ
    have hθd : θ ∈ Set.Ioo 0 d := hsubd ⟨hθ.1, hθ.2⟩
    have hs := hsinpos θ hθd
    have hc₀pos : 0 < 2 * b * (θ₁ - θ₂) := by
      have h : 0 < θ₁ - θ₂ := by linarith
      exact mul_pos (by positivity) h
    have hfl := hf2low θ hθ
    have hfne : f θ ≠ 0 := by
      intro hf0
      have hzero : (f θ) ^ 2 = 0 := by simp [hf0]
      have hpos : 0 < 2 * b * (θ₁ - θ₂) * Real.sin (2 * θ) := by positivity
      linarith [hfl, hzero]
    have hfab : Real.sqrt (2 * b * (θ₁ - θ₂)) * Real.sqrt (Real.sin (2 * θ)) ≤ |f θ| := by
      have h1 : Real.sqrt (2 * b * (θ₁ - θ₂) * Real.sin (2 * θ)) ≤ Real.sqrt ((f θ) ^ 2) :=
        Real.sqrt_le_sqrt hfl
      rw [Real.sqrt_mul (le_of_lt hc₀pos), Real.sqrt_sq_eq_abs] at h1
      exact h1
    have hsig_sqrt : sig θ * Real.sqrt (Real.sin (2 * θ))
        = (Real.sin (2 * θ)) ^ ((1:ℝ) / 2 - Work.Spaces.eta) := by
      rw [show sig θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl, Real.sqrt_eq_rpow,
        ← Real.rpow_add hs]
      congr 1
      ring
    have hpow1 : (1:ℝ) ≤ (Real.sin (2 * θ)) ^ ((1:ℝ) / 2 - Work.Spaces.eta) := by
      have hη : (1:ℝ) / 2 - Work.Spaces.eta ≤ 0 := by rw [Work.Spaces.eta]; norm_num
      have h := Real.rpow_le_rpow_of_nonpos hs (Real.sin_le_one (2 * θ)) hη
      rwa [Real.one_rpow] at h
    have hmain : Real.sqrt (2 * b * (θ₁ - θ₂)) ≤ sig θ * |f θ| := by
      have h1 : sig θ * (Real.sqrt (2 * b * (θ₁ - θ₂)) * Real.sqrt (Real.sin (2 * θ)))
          ≤ sig θ * |f θ| :=
        mul_le_mul_of_nonneg_left hfab (le_of_lt (hsigpos θ hθd))
      have h2 : sig θ * (Real.sqrt (2 * b * (θ₁ - θ₂)) * Real.sqrt (Real.sin (2 * θ)))
          = Real.sqrt (2 * b * (θ₁ - θ₂)) * (Real.sin (2 * θ)) ^ ((1:ℝ) / 2 - Work.Spaces.eta) := by
        rw [← hsig_sqrt]; ring
      rw [h2] at h1
      have h3 : Real.sqrt (2 * b * (θ₁ - θ₂)) * 1
          ≤ Real.sqrt (2 * b * (θ₁ - θ₂)) * (Real.sin (2 * θ)) ^ ((1:ℝ) / 2 - Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_left hpow1 (Real.sqrt_nonneg _)
      linarith [h1, h3]
    have hΓeq : |sliceIntegrand f θ| = sig θ * |f θ| * |deriv (deriv f) θ| := by
      rw [show sliceIntegrand f θ = sig θ * (f θ * deriv (deriv f) θ) from rfl, abs_mul, abs_mul]
      rw [abs_of_pos (hsigpos θ hθd)]
      ring
    have h1 : |sliceIntegrand f θ| / (sig θ * |f θ|)
        ≤ |sliceIntegrand f θ| / Real.sqrt (2 * b * (θ₁ - θ₂)) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr hc₀pos) hmain
    have h2 : |deriv (deriv f) θ| = |sliceIntegrand f θ| / (sig θ * |f θ|) := by
      have hne : sig θ * |f θ| ≠ 0 :=
        ne_of_gt (mul_pos (hsigpos θ hθd) (abs_pos.mpr hfne))
      rw [hΓeq, eq_div_iff hne]
      ring
    rw [h2]
    exact h1
  -- ===== Step 7: f'' ∈ L¹(0,θ₂) and the delegated limit lemma =====
  have hf''int : MeasureTheory.IntegrableOn (fun x : ℝ => deriv (deriv f) x) (Set.Ioo 0 θ₂) := by
    have hc₀pos : 0 < 2 * b * (θ₁ - θ₂) := by
      have h : 0 < θ₁ - θ₂ := by linarith
      exact mul_pos (by positivity) h
    have hΓint : MeasureTheory.IntegrableOn (fun θ => |sliceIntegrand f θ|) (Set.Ioo 0 θ₂) :=
      (hint.mono_set hsubd).abs
    have hg : MeasureTheory.Integrable
        (fun θ => |sliceIntegrand f θ| / Real.sqrt (2 * b * (θ₁ - θ₂)))
        (volume.restrict (Set.Ioo 0 θ₂)) := by
      have h := hΓint.const_mul ((Real.sqrt (2 * b * (θ₁ - θ₂)))⁻¹)
      simpa only [div_eq_mul_inv, mul_comm] using h
    have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 θ₂) := by
      have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 d) :=
        hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      have h2 : ContDiffOn ℝ 0 (deriv (deriv f)) (Set.Ioo 0 d) :=
        h1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
      exact h2.continuousOn.mono hsubd
    show MeasureTheory.Integrable (fun x : ℝ => deriv (deriv f) x) (volume.restrict (Set.Ioo 0 θ₂))
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · exact hcont2.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs]
      exact hf''b θ hθ
  have hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 θ₂) := hf.mono hsubd
  obtain ⟨L, -, hL2⟩ := SliceLeftAux.deriv_limit_of_integrableOn hθ₂pos hcd hf''int h0
  -- ===== Step 8: the final contradiction =====
  rw [Metric.tendsto_nhdsWithin_nhds] at hL2
  obtain ⟨δ, hδpos, hδ⟩ := hL2 1 (by norm_num)
  set c₀ : ℝ := 2 * b * (θ₁ - θ₂) with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    have h : 0 < θ₁ - θ₂ := by linarith
    exact mul_pos (by positivity) h
  set Cn : ℝ := Real.pi / 4 * (|L| + 1) ^ 2 + 1 with hCn
  have hCnpos : 0 < Cn := by
    rw [hCn]
    have h : (0:ℝ) ≤ Real.pi / 4 * (|L| + 1) ^ 2 := by positivity
    linarith
  have hJbd : ∀ θ ∈ Set.Ioo 0 (min δ θ₂), J θ ≤ Cn * θ := by
    intro θ hθ
    have hθδ : θ < δ := lt_of_lt_of_le hθ.2 (min_le_left _ _)
    have hθθ₂ : θ < θ₂ := lt_of_lt_of_le hθ.2 (min_le_right _ _)
    have hθd : θ ∈ Set.Ioo 0 d := ⟨hθ.1, lt_trans hθθ₂ hθ₂d⟩
    have hfl : |f θ - L * θ| ≤ θ := by
      have h1 := hδ hθ.1 (by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hθ.1]; exact hθδ)
      rw [dist_zero_right, Real.norm_eq_abs] at h1
      rw [abs_div, abs_of_pos hθ.1, div_lt_one hθ.1] at h1
      exact le_of_lt h1
    have habs : |f θ| ≤ (|L| + 1) * θ := by
      calc |f θ| = |(f θ - L * θ) + L * θ| := by ring_nf
        _ ≤ |f θ - L * θ| + |L * θ| := abs_add_le _ _
        _ ≤ θ + |L| * θ := by
              gcongr
              rw [abs_mul, abs_of_pos hθ.1]
        _ = (|L| + 1) * θ := by ring
    have hsq : (f θ) ^ 2 ≤ ((|L| + 1) * θ) ^ 2 := by
      have hnn : (0:ℝ) ≤ (|L| + 1) * θ := by
        have h1 : (0:ℝ) ≤ |L| + 1 := by positivity
        exact mul_nonneg h1 (le_of_lt hθ.1)
      rw [sq_le_sq, abs_of_nonneg hnn]
      exact habs
    have hsinlb : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
      have h2 : 2 * θ ≤ Real.pi / 2 := by
        rw [hθ₂] at hθθ₂; linarith
      have h1 := Real.mul_le_sin (by linarith [hθ.1]) h2
      have h3 : 2 / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
      linarith [h1, h3.le]
    have h1 : J θ ≤ ((|L| + 1) * θ) ^ 2 / ((4 / Real.pi) * θ) := by
      rw [show J θ = (f θ) ^ 2 / Real.sin (2 * θ) from rfl]
      have hden : 0 < (4 / Real.pi) * θ := by
        have hπ : (0:ℝ) < 4 / Real.pi := by positivity
        exact mul_pos hπ hθ.1
      exact div_le_div₀ (sq_nonneg _) hsq hden hsinlb
    have h2 : ((|L| + 1) * θ) ^ 2 / ((4 / Real.pi) * θ) = Real.pi / 4 * (|L| + 1) ^ 2 * θ := by
      have hden : (4 / Real.pi) * θ ≠ 0 := by
        have hπ : (0:ℝ) < 4 / Real.pi := by positivity
        exact ne_of_gt (mul_pos hπ hθ.1)
      rw [div_eq_iff hden]
      field_simp
    have h3 : Real.pi / 4 * (|L| + 1) ^ 2 * θ ≤ Cn * θ := by
      have h4 : Real.pi / 4 * (|L| + 1) ^ 2 ≤ Cn := by rw [hCn]; linarith
      exact mul_le_mul_of_nonneg_right h4 (le_of_lt hθ.1)
    linarith [h1, h2.le, h3]
  set θ₀ : ℝ := min δ (min θ₂ (c₀ / Cn)) / 2 with hθ₀
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀]
    have hmin : 0 < min δ (min θ₂ (c₀ / Cn)) :=
      lt_min hδpos (lt_min hθ₂pos (by positivity))
    linarith
  have hθ₀δ : θ₀ < δ := by
    rw [hθ₀]; have := min_le_left δ (min θ₂ (c₀ / Cn)); linarith
  have hθ₀θ₂ : θ₀ < θ₂ := by
    rw [hθ₀]
    have := le_trans (min_le_right δ (min θ₂ (c₀ / Cn))) (min_le_left θ₂ (c₀ / Cn))
    linarith
  have hθ₀c : Cn * θ₀ ≤ c₀ / 2 := by
    rw [hθ₀]
    have h1 : min δ (min θ₂ (c₀ / Cn)) ≤ c₀ / Cn :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : Cn * (min δ (min θ₂ (c₀ / Cn)) / 2) ≤ Cn * ((c₀ / Cn) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hCnpos)
    have h3 : Cn * ((c₀ / Cn) / 2) = c₀ / 2 := by field_simp
    linarith [h2, h3.le]
  have h1 : c₀ ≤ J θ₀ := by
    have h := hJlow θ₀ ⟨hθ₀pos, hθ₀θ₂⟩
    rw [hc₀]; exact h
  have h2 : J θ₀ ≤ Cn * θ₀ := hJbd θ₀ ⟨hθ₀pos, lt_min hθ₀δ hθ₀θ₂⟩
  linarith [h1, h2, hθ₀c, hc₀pos]

end Work.FTS.EllipticEst.Cores.AeStep2Aux
