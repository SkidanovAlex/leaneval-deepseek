import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinIdentDefs
import Submission.Work.Elliptic.SliceBddBounds
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.DivSinIntegrable_u1
import Submission.Work.Elliptic.DivSinIntegrable_u2
import Submission.Work.Elliptic.DivSinIntegrable_u0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- Pointwise identity: the derivative of the antiderivative `DivSinB` is the difference of the
two integrands of `DivSinIdentityB`. -/
theorem DivSinB_hasDerivAt (γ : ℝ) (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (Work.Elliptic.DivSinB γ h) (Work.Elliptic.Dfun γ h θ) θ := by
  obtain ⟨j, rfl⟩ : ∃ j, θ = j := ⟨θ, rfl⟩
  have hsmU : ContDiffOn ℝ ⊤ h (Set.Ioo 0 (Real.pi / 2)) :=
    hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  have hsinU : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 :=
    fun x hx => ne_of_gt (sin_two_pos hx)
  have hgU : ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ⊤ (fun x => h x / Real.sin (2 * x)) _
    exact hsmU.div hsinU hne
  have huS : HasDerivAt (SinQ h) (deriv (SinQ h) θ) θ :=
    ((hgU.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt
  have hderU : ContDiffOn ℝ ⊤ (deriv (SinQ h)) (Set.Ioo 0 (Real.pi / 2)) :=
    hgU.deriv_of_isOpen isOpen_Ioo le_top
  have huD : HasDerivAt (deriv (SinQ h)) (deriv (deriv (SinQ h)) θ) θ :=
    ((hderU.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt
  have hspos0 : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hsu : Real.sin (2 * θ) * SinQ h θ = h θ := by
    rw [SinQ, mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hspos0)
  have hrel : deriv (deriv h) θ
      = Real.sin (2 * θ) * deriv (deriv (SinQ h)) θ + 4 * Real.cos (2 * θ) * deriv (SinQ h) θ
        - 4 * Real.sin (2 * θ) * SinQ h θ := by
    have hh2 := SliceBdd_second_deriv_rel h hh θ hθ
    rw [← hsu] at hh2
    linarith [hh2]
  have hs := hasDerivAt_sin_two θ
  have hc := hasDerivAt_cos_two θ
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h3 := hs.rpow_const (p := 3 - γ) (Or.inl (ne_of_gt hspos))
  have hu2 : HasDerivAt (fun θ => (deriv (SinQ h) θ) ^ 2)
      ((2 : ℝ) * (deriv (SinQ h) θ) ^ (2 - 1) * deriv (deriv (SinQ h)) θ) θ := huD.pow 2
  have hA : HasDerivAt (fun θ => (4 * Real.cos (2 * θ)) * (deriv (SinQ h) θ) ^ 2)
      ((4 * (-2 * Real.sin (2 * θ))) * (deriv (SinQ h) θ) ^ 2
        + (4 * Real.cos (2 * θ)) * ((2 : ℝ) * (deriv (SinQ h) θ) ^ (2 - 1)
            * deriv (deriv (SinQ h)) θ)) θ := (hc.const_mul 4).mul hu2
  have hB : HasDerivAt (fun θ => (8 * Real.sin (2 * θ)) * (deriv (SinQ h) θ * SinQ h θ))
      ((8 * (2 * Real.cos (2 * θ))) * (deriv (SinQ h) θ * SinQ h θ)
        + (8 * Real.sin (2 * θ)) * (deriv (deriv (SinQ h)) θ * SinQ h θ
            + deriv (SinQ h) θ * deriv (SinQ h) θ)) θ := (hs.const_mul 8).mul (huD.mul huS)
  have hu2' : HasDerivAt (fun θ => (SinQ h θ) ^ 2)
      ((2 : ℝ) * (SinQ h θ) ^ (2 - 1) * deriv (SinQ h) θ) θ := huS.pow 2
  have hC : HasDerivAt (fun θ => (8 * (2 - γ) * Real.cos (2 * θ)) * (SinQ h θ) ^ 2)
      ((8 * (2 - γ) * (-2 * Real.sin (2 * θ))) * (SinQ h θ) ^ 2
        + (8 * (2 - γ) * Real.cos (2 * θ)) * ((2 : ℝ) * (SinQ h θ) ^ (2 - 1)
            * deriv (SinQ h) θ)) θ := (hc.const_mul (8 * (2 - γ))).mul hu2'
  have hF1 : HasDerivAt (DivSinF1 γ h)
      (4 * ((-2 * Real.sin (2 * θ)) * (deriv (SinQ h) θ) ^ 2 + Real.cos (2 * θ)
            * (2 * deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ))
        - 8 * (2 * Real.cos (2 * θ) * deriv (SinQ h) θ * SinQ h θ
            + Real.sin (2 * θ) * (deriv (deriv (SinQ h)) θ * SinQ h θ
                + deriv (SinQ h) θ * deriv (SinQ h) θ))
        + 8 * (2 - γ) * ((-2 * Real.sin (2 * θ)) * (SinQ h θ) ^ 2 + Real.cos (2 * θ)
            * (2 * SinQ h θ * deriv (SinQ h) θ))) θ := by
    have := (hA.sub hB).add hC
    convert this using 1
    · ext x; simp only [DivSinF1, Pi.sub_apply, Pi.add_apply]
    · ring
  have hmain := h3.mul hF1
  have hs3 : (Real.sin (2 * θ)) ^ (3 - γ) = (Real.sin (2 * θ)) ^ (2 - γ) * Real.sin (2 * θ) := by
    rw [← Real.rpow_add_one (ne_of_gt hspos) (2 - γ)]
    congr 1; ring
  have hs4 : (Real.sin (2 * θ)) ^ (4 - γ)
      = (Real.sin (2 * θ)) ^ (2 - γ) * (Real.sin (2 * θ)) ^ 2 := by
    rw [show (4 : ℝ) - γ = (3 - γ) + 1 by ring, Real.rpow_add_one (ne_of_gt hspos) (3 - γ), hs3]
    ring
  have hval : (2 * Real.cos (2 * θ) * (3 - γ) * Real.sin (2 * θ) ^ (3 - γ - 1) * DivSinF1 γ h θ
      + Real.sin (2 * θ) ^ (3 - γ) *
        (4 * (-2 * Real.sin (2 * θ) * deriv (SinQ h) θ ^ 2 + Real.cos (2 * θ)
              * (2 * deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ))
          - 8 * (2 * Real.cos (2 * θ) * deriv (SinQ h) θ * SinQ h θ
              + Real.sin (2 * θ) * (deriv (deriv (SinQ h)) θ * SinQ h θ
                  + deriv (SinQ h) θ * deriv (SinQ h) θ))
          + 8 * (2 - γ) * (-2 * Real.sin (2 * θ) * SinQ h θ ^ 2 + Real.cos (2 * θ)
              * (2 * SinQ h θ * deriv (SinQ h) θ))))
      = Dfun γ h θ := by
    simp only [Dfun]
    rw [hrel, hs3, hs4, show (3 : ℝ) - γ - 1 = 2 - γ by ring]
    simp only [DivSinF1]
    ring
  change HasDerivAt ((fun y : ℝ => Real.sin (2 * y) ^ (3 - γ)) * DivSinF1 γ h)
    (Dfun γ h θ) θ
  rw [← hval]
  exact hmain


private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

private lemma abs_le_three (a b c : ℝ) : |a - b + c| ≤ |a| + |b| + |c| := by
  calc |a - b + c| ≤ |a - b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by linarith [abs_sub_le_abs_add a b]
    _ = |a| + |b| + |c| := by ring

/-- The bracket `F₁` of `DivSinB` is bounded by `20C²` wherever `|u| ≤ C` and `|u'| ≤ C`. -/
private lemma DivSinF1_bound (α C : ℝ) (h : ℝ → ℝ) (hC0 : 0 ≤ C)
    (h2g : |2 - Work.Spaces.gam α| ≤ 1) (θ : ℝ)
    (hu : |SinQ h θ| ≤ C) (hu1 : |deriv (SinQ h) θ| ≤ C) :
    |DivSinF1 (Work.Spaces.gam α) h θ| ≤ 20 * C ^ 2 := by
  have hT1 : |(4 * Real.cos (2 * θ)) * (deriv (SinQ h) θ) ^ 2| ≤ 4 * C ^ 2 := by
    rw [abs_mul, abs_pow]
    have h1 : |4 * Real.cos (2 * θ)| ≤ 4 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      nlinarith [Real.abs_cos_le_one (2 * θ)]
    have h2 : |deriv (SinQ h) θ| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu1 2
    exact le_trans (mul_le_mul h1 h2 (by positivity) (by norm_num)) (le_of_eq (by ring))
  have hT2 : |(8 * Real.sin (2 * θ)) * (deriv (SinQ h) θ * SinQ h θ)| ≤ 8 * C ^ 2 := by
    have h1 : |8 * Real.sin (2 * θ)| ≤ 8 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8)]
      nlinarith [Real.abs_sin_le_one (2 * θ)]
    have h2 : |deriv (SinQ h) θ * SinQ h θ| ≤ C * C := by
      rw [abs_mul]; exact mul_le_mul hu1 hu (abs_nonneg _) hC0
    calc |(8 * Real.sin (2 * θ)) * (deriv (SinQ h) θ * SinQ h θ)|
        = |8 * Real.sin (2 * θ)| * |deriv (SinQ h) θ * SinQ h θ| := abs_mul _ _
      _ ≤ 8 * (C * C) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 8 * C ^ 2 := by ring
  have hT3 : |(8 * (2 - Work.Spaces.gam α) * Real.cos (2 * θ)) * (SinQ h θ) ^ 2| ≤ 8 * C ^ 2 := by
    rw [abs_mul, abs_pow]
    have h1 : |8 * (2 - Work.Spaces.gam α) * Real.cos (2 * θ)| ≤ 8 := by
      rw [abs_mul, abs_mul]
      have := Real.abs_cos_le_one (2 * θ)
      rw [abs_of_pos (by norm_num : (0:ℝ) < 8)]
      nlinarith [this, h2g, abs_nonneg (Real.cos (2 * θ)),
        abs_nonneg (2 - Work.Spaces.gam α)]
    have h2 : |SinQ h θ| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
    exact le_trans (mul_le_mul h1 h2 (by positivity) (by norm_num)) (le_of_eq (by ring))
  simp only [DivSinF1]
  calc |(4 * Real.cos (2 * θ)) * (deriv (SinQ h) θ) ^ 2
        - (8 * Real.sin (2 * θ)) * (deriv (SinQ h) θ * SinQ h θ)
        + (8 * (2 - Work.Spaces.gam α) * Real.cos (2 * θ)) * (SinQ h θ) ^ 2|
      ≤ |(4 * Real.cos (2 * θ)) * (deriv (SinQ h) θ) ^ 2|
        + |(8 * Real.sin (2 * θ)) * (deriv (SinQ h) θ * SinQ h θ)|
        + |(8 * (2 - Work.Spaces.gam α) * Real.cos (2 * θ)) * (SinQ h θ) ^ 2| := abs_le_three _ _ _
    _ ≤ 20 * C ^ 2 := by linarith [hT1, hT2, hT3]

set_option maxHeartbeats 800000 in
theorem DivSinB_ends (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hh : Work.Elliptic.SmoothSlice h) (hb : Work.Elliptic.SliceBdd h) :
    Filter.Tendsto (Work.Elliptic.DivSinB (Work.Spaces.gam α) h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (Work.Elliptic.DivSinB (Work.Spaces.gam α) h)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨C, hC0, hA, _, hC1, hD, hE, hF, _, hH, hI, hJ⟩ := hb
  have h2g : |2 - Work.Spaces.gam α| ≤ 1 := by
    rw [abs_of_nonneg (by simp only [Work.Spaces.gam]; linarith [hα])]
    simp only [Work.Spaces.gam]; linarith [hα1]
  have h3' : 1 ≤ 3 - Work.Spaces.gam α := by
    simp only [Work.Spaces.gam]; linarith [hα1]
  have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
  -- bounds on the two half-intervals
  have hbound0 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 4),
      ‖Work.Elliptic.DivSinB (Work.Spaces.gam α) h θ‖ ≤ 40 * C ^ 2 * θ := by
    intro θ hθ
    have hsnn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α) ≤ Real.sin (2 * θ) :=
      Real.rpow_le_self_of_le_one hsnn (Real.sin_le_one _) h3'
    have hs2 : Real.sin (2 * θ) ≤ 2 * θ := le_of_lt (Real.sin_lt (by linarith [hθ.1]))
    have hF1 := DivSinF1_bound α C h hC0 h2g θ (hD θ hθ) (hE θ hθ)
    rw [Real.norm_eq_abs, DivSinB, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsnn _)]
    calc Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α) * |DivSinF1 (Work.Spaces.gam α) h θ|
        ≤ Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α) * (20 * C ^ 2) :=
          mul_le_mul_of_nonneg_left hF1 (Real.rpow_nonneg hsnn _)
      _ ≤ (2 * θ) * (20 * C ^ 2) :=
          mul_le_mul_of_nonneg_right (le_trans hs1 hs2) (by positivity)
      _ = 40 * C ^ 2 * θ := by ring
  have hbound1 : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      ‖Work.Elliptic.DivSinB (Work.Spaces.gam α) h θ‖ ≤ 40 * C ^ 2 * (Real.pi / 2 - θ) := by
    intro θ hθ
    have hsnn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α) ≤ Real.sin (2 * θ) :=
      Real.rpow_le_self_of_le_one hsnn (Real.sin_le_one _) h3'
    have hsin_eq : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    have hpos : 0 < 2 * (Real.pi / 2 - θ) := by linarith [hθ.2]
    have hs2 : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
      rw [hsin_eq]; exact le_of_lt (Real.sin_lt hpos)
    have hF1 := DivSinF1_bound α C h hC0 h2g θ (hI θ hθ) (hJ θ hθ)
    rw [Real.norm_eq_abs, DivSinB, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsnn _)]
    calc Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α) * |DivSinF1 (Work.Spaces.gam α) h θ|
        ≤ Real.sin (2 * θ) ^ (3 - Work.Spaces.gam α) * (20 * C ^ 2) :=
          mul_le_mul_of_nonneg_left hF1 (Real.rpow_nonneg hsnn _)
      _ ≤ (2 * (Real.pi / 2 - θ)) * (20 * C ^ 2) :=
          mul_le_mul_of_nonneg_right (le_trans hs1 hs2) (by positivity)
      _ = 40 * C ^ 2 * (Real.pi / 2 - θ) := by ring
  constructor
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hlim : Filter.Tendsto (fun θ : ℝ => 40 * C ^ 2 * θ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun θ : ℝ => θ) (𝓝 (0:ℝ)) (𝓝 0) :=
        (continuousAt_id : ContinuousAt (fun θ : ℝ => θ) (0:ℝ)).tendsto
      have h2 := h1.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
      have h2b := h2.const_mul (40 * C ^ 2)
      simp only [mul_zero] at h2b
      exact h2b.congr' (Filter.Eventually.of_forall (fun θ => by ring))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) ?_
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
        (Iio_mem_nhds hpi4)] with θ hθ0 hθ4
    exact hbound0 θ ⟨hθ0, hθ4⟩
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hlim : Filter.Tendsto (fun θ : ℝ => 40 * C ^ 2 * (Real.pi / 2 - θ))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      have hc : Filter.Tendsto (fun _ : ℝ => Real.pi / 2) (𝓝 (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
        (continuousAt_const : ContinuousAt (fun _ : ℝ => Real.pi / 2) (Real.pi / 2)).tendsto
      have h1 : Filter.Tendsto (fun θ : ℝ => θ) (𝓝 (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
        (continuousAt_id : ContinuousAt (fun θ : ℝ => θ) (Real.pi / 2)).tendsto
      have h1b : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2 - Real.pi / 2)) := hc.sub h1
      rw [sub_self] at h1b
      have h2 := h1b.mono_left (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
      have h2b := h2.const_mul (40 * C ^ 2)
      simp only [mul_zero] at h2b
      exact h2b.congr' (Filter.Eventually.of_forall (fun θ => by ring))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) ?_
    filter_upwards [(Filter.Eventually.filter_mono
        (nhdsWithin_le_nhds : 𝓝[<] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
        (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))),
      self_mem_nhdsWithin] with θ hθ4 hθ2
    exact hbound1 θ ⟨hθ4, hθ2⟩

theorem DivSinIdentityB (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hh : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0) (hπ : h (Real.pi / 2) = 0)
    (hb : Work.Elliptic.SliceBdd h) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α))
      = (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2)
        + 8 * (Work.Spaces.gam α - 1) * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2)
        + 16 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2)
        + 16 * (3 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2)
        - 16 * (2 - Work.Spaces.gam α) * (3 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2)
      ∧ MeasureTheory.IntegrableOn (fun θ => (deriv (Work.Elliptic.SinQ h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (deriv (deriv h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)) Work.Spaces.Iθ MeasureTheory.volume := by
  obtain ⟨hI1, hI3, hI4⟩ := Work.Elliptic.DivSinIntegrable_u1 α hα hα1 h hh hb
  have hI2 := Work.Elliptic.DivSinIntegrable_u2 α hα hα1 h hh hb
  obtain ⟨hI5, hI6, hI7⟩ := Work.Elliptic.DivSinIntegrable_u0 α hα hα1 h hh hb
  have htend := DivSinB_ends α hα hα1 h hh hb
  have hderivB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (Work.Elliptic.DivSinB (Work.Spaces.gam α) h)
        (Work.Elliptic.Dfun (Work.Spaces.gam α) h θ) θ :=
    fun θ hθ => DivSinB_hasDerivAt (Work.Spaces.gam α) h hh θ hθ
  -- integral splitting
  have hC2 : MeasureTheory.IntegrableOn
      (fun θ => 8 * (Work.Spaces.gam α - 1) * ((Real.cos (2*θ))^2
        * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2))
      Work.Spaces.Iθ := hI3.const_mul _
  have hC3 : MeasureTheory.IntegrableOn
      (fun θ => 16 * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2))
      Work.Spaces.Iθ := hI4.const_mul _
  have hC4 : MeasureTheory.IntegrableOn
      (fun θ => 16 * (3 - Work.Spaces.gam α) * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α)
        * (Work.Elliptic.SinQ h θ)^2)) Work.Spaces.Iθ := hI5.const_mul _
  have hC5 : MeasureTheory.IntegrableOn
      (fun θ => 16 * (2 - Work.Spaces.gam α) * (3 - Work.Spaces.gam α) * ((Real.cos (2*θ))^2
        * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2))
      Work.Spaces.Iθ := hI6.const_mul _
  have hAB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2
        + 8 * (Work.Spaces.gam α - 1) * ((Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
            * (deriv (Work.Elliptic.SinQ h) θ)^2)) Work.Spaces.Iθ := hI2.add hC2
  have hABC : MeasureTheory.IntegrableOn
      (fun θ => ((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2
        + 8 * (Work.Spaces.gam α - 1) * ((Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
            * (deriv (Work.Elliptic.SinQ h) θ)^2))
        + 16 * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2))
      Work.Spaces.Iθ := hAB.add hC3
  have hABCD : MeasureTheory.IntegrableOn
      (fun θ => (((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2
        + 8 * (Work.Spaces.gam α - 1) * ((Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
            * (deriv (Work.Elliptic.SinQ h) θ)^2))
        + 16 * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2))
        + 16 * (3 - Work.Spaces.gam α) * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α)
          * (Work.Elliptic.SinQ h θ)^2)) Work.Spaces.Iθ := hABC.add hC4
  have hREST : MeasureTheory.IntegrableOn
      (fun θ => ((((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2
        + 8 * (Work.Spaces.gam α - 1) * ((Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
            * (deriv (Work.Elliptic.SinQ h) θ)^2))
        + 16 * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2))
        + 16 * (3 - Work.Spaces.gam α) * ((Real.sin (2*θ))^(4 - Work.Spaces.gam α)
          * (Work.Elliptic.SinQ h θ)^2))
        - 16 * (2 - Work.Spaces.gam α) * (3 - Work.Spaces.gam α) * ((Real.cos (2*θ))^2
          * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2))
      Work.Spaces.Iθ := hABCD.sub hC5
  have hDint : MeasureTheory.IntegrableOn (Work.Elliptic.Dfun (Work.Spaces.gam α) h) Work.Spaces.Iθ :=
    hI7.sub hREST
  -- FTC
  have hDintI : IntervalIntegrable (Work.Elliptic.Dfun (Work.Spaces.gam α) h) volume 0 (Real.pi / 2) := by
    have h2 : MeasureTheory.IntegrableOn (Work.Elliptic.Dfun (Work.Spaces.gam α) h)
        (Set.uIcc 0 (Real.pi / 2)) volume := by
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)]
      simpa [Work.Spaces.Iθ] using hDint
    exact h2.intervalIntegrable
  have hFTC : ∫ θ in (0:ℝ)..(Real.pi / 2), Work.Elliptic.Dfun (Work.Spaces.gam α) h θ = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by positivity : (0:ℝ) < Real.pi/2)
      hderivB hDintI htend.1 htend.2, sub_self]
  have hconv : ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Dfun (Work.Spaces.gam α) h θ
      = ∫ θ in (0:ℝ)..(Real.pi / 2), Work.Elliptic.Dfun (Work.Spaces.gam α) h θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
  have h0int : ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Dfun (Work.Spaces.gam α) h θ = 0 :=
    hconv.trans hFTC
  have hsplit : ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Dfun (Work.Spaces.gam α) h θ
      = (∫ θ in Work.Spaces.Iθ, (deriv (deriv h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α))
        - ((∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2)
          + 8 * (Work.Spaces.gam α - 1) * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2)
          + 16 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2)
          + 16 * (3 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2)
          - 16 * (2 - Work.Spaces.gam α) * (3 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2)) := by
    simp only [Work.Elliptic.Dfun]
    rw [MeasureTheory.integral_sub hI7 hREST, MeasureTheory.integral_sub hABCD hC5,
      MeasureTheory.integral_add hABC hC4, MeasureTheory.integral_add hAB hC3,
      MeasureTheory.integral_add hI2 hC2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have hzero : (∫ θ in Work.Spaces.Iθ, (deriv (deriv h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α))
      - ((∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (deriv (Work.Elliptic.SinQ h)) θ)^2)
        + 8 * (Work.Spaces.gam α - 1) * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2)
        + 16 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (deriv (Work.Elliptic.SinQ h) θ)^2)
        + 16 * (3 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(4 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2)
        - 16 * (2 - Work.Spaces.gam α) * (3 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ)^2)) = 0 := by
    rw [← hsplit]; exact h0int
  refine ⟨by linarith [hzero], hI1, hI2, hI3, hI4, hI5, hI6, hI7⟩

end Work.Elliptic
