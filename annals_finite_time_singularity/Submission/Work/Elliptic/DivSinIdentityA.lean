import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinIdentitySetup
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant
import Submission.Work.Elliptic.exists_bound_of_continuousOn_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- On `(0, π/2)` the quotient `u = SinQ h` satisfies `h' = 2 cos(2θ) u + sin(2θ) u'`. -/
theorem deriv_eq_cos_sin_SinQ {h : ℝ → ℝ} (hh : Work.Elliptic.SmoothSlice h) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv h θ
      = 2 * Real.cos (2 * θ) * Work.Elliptic.SinQ h θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ := by
  have hsub : Set.Icc 0 (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hC : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) :=
    (hh.mono hsub).of_le le_top
  have key := (Work.Elliptic.htU_interior_facts h hC).2.2.2.1 θ hθ
  rw [show Work.Elliptic.htU h = Work.Elliptic.SinQ h from rfl] at key
  have hs : Real.sin (2 * θ) ≠ 0 := Work.Elliptic.sin_two_ne_zero' hθ
  have hhu : h θ = Real.sin (2 * θ) * Work.Elliptic.SinQ h θ := by
    simp only [Work.Elliptic.SinQ]; field_simp
  rw [hhu] at key
  have htarget : Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ
      = deriv h θ - 2 * Real.cos (2 * θ) * Work.Elliptic.SinQ h θ := by
    apply mul_left_cancel₀ hs
    linear_combination key
  linarith [htarget]


/-- The pointwise identity behind `DivSinIdentityA`: on `(0, π/2)` the difference of the two
integrands is the derivative `dPhiA h` of the primitive `PhiA h`. -/
theorem DivSinIdPointwise (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.F1A h θ = Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ
        + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ + 4 * Work.Elliptic.F4A h θ := by
  intro θ hθ
  have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
  have hlin := deriv_eq_cos_sin_SinQ hh hθ
  have e1 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) := by
    rw [show (2 : ℝ) - Work.Spaces.eta = 2 + (-Work.Spaces.eta) by ring,
      Real.rpow_add hs, Real.rpow_two]
  have e2 : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-Work.Spaces.eta) by ring,
      Real.rpow_add hs, Real.rpow_one]
  simp only [Work.Elliptic.F1A, Work.Elliptic.F2A, Work.Elliptic.F3A, Work.Elliptic.F4A,
    Work.Elliptic.dPhiA]
  rw [hlin, e1, e2]
  ring


/-- `HasDerivAt` of `fun x => Real.sin (2 * x)` at `θ`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa [mul_comm] using h2.sin

/-- `HasDerivAt` of `fun x => Real.cos (2 * x)` at `θ`. -/
theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa [mul_comm] using h2.cos

/-- On `(0, π/2)` the primitive `PhiA h = 2 cos(2θ) h(θ)² sin(2θ)^{-(1+η)}` agrees with the
quotient form `2 cos(2θ) (SinQ h θ)² sin(2θ)^{1-η}`. -/
theorem PhiA_eq_of_mem (h : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.PhiA h x
      = 2 * Real.cos (2 * x) * (Work.Elliptic.SinQ h x) ^ 2
        * (Real.sin (2 * x)) ^ (1 - Work.Spaces.eta) := by
  have hsx : 0 < Real.sin (2 * x) := Work.Elliptic.sin_two_pos hx
  have hsx2 : (Real.sin (2 * x)) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hsx)
  have hxu : h x = Real.sin (2 * x) * Work.Elliptic.SinQ h x := by
    simp only [Work.Elliptic.SinQ]; field_simp
  have hid : (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * x)) ^ (1 - Work.Spaces.eta) / (Real.sin (2 * x)) ^ 2 := by
    rw [eq_div_iff hsx2, ← Real.rpow_two, ← Real.rpow_add hsx]
    congr 1
    ring
  simp only [Work.Elliptic.PhiA]
  rw [hxu, hid, mul_pow]
  field_simp

/-- The eventual equality `PhiA h = 2 cos(2θ) (SinQ h θ)² sin(2θ)^{1-η}` near any interior point. -/
theorem PhiA_eventuallyEq (h : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.PhiA h =ᶠ[𝓝 θ]
      (fun x : ℝ => 2 * Real.cos (2 * x) * (Work.Elliptic.SinQ h x) ^ 2
        * (Real.sin (2 * x)) ^ (1 - Work.Spaces.eta)) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
  exact Work.Elliptic.PhiA_eq_of_mem h hx

/-- The explicit derivative of the primitive `PhiA h` on `(0, π/2)`. -/
theorem DivSinIdPhiDeriv (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (Work.Elliptic.PhiA h) (Work.Elliptic.dPhiA h θ) θ := by
  intro θ hθ
  have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
  have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
  have hsub : Set.Ioo 0 (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hcont : ContDiffOn ℝ ⊤ (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) :=
    (hh.mono hsub).div
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn)
      (fun x hx => Work.Elliptic.sin_two_ne_zero' hx)
  have hu : HasDerivAt (Work.Elliptic.SinQ h) (deriv (Work.Elliptic.SinQ h) θ) θ :=
    (((hcont.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt)
  have hAA : HasDerivAt (fun x : ℝ => 2 * Real.cos (2 * x))
      (2 * (-2 * Real.sin (2 * θ))) θ :=
    (hasDerivAt_cos_two θ).const_mul (2 : ℝ)
  have hBB : HasDerivAt (fun x : ℝ => (Work.Elliptic.SinQ h x) ^ 2)
      (2 * (Work.Elliptic.SinQ h θ) ^ (2 - 1) * deriv (Work.Elliptic.SinQ h) θ) θ :=
    hu.pow 2
  have hCC : HasDerivAt (fun x : ℝ => (Real.sin (2 * x)) ^ (1 - Work.Spaces.eta))
      ((2 * Real.cos (2 * θ)) * (1 - Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ ((1 - Work.Spaces.eta) - 1)) θ :=
    (hasDerivAt_sin_two θ).rpow_const (Or.inl hsne)
  have hss : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    rw [show (2 : ℝ) - Work.Spaces.eta = 1 + (1 - Work.Spaces.eta) by ring,
      Real.rpow_add hs, Real.rpow_one]
  have hse : (1 - Work.Spaces.eta) - 1 = -Work.Spaces.eta := by ring
  have key2 : HasDerivAt (fun x : ℝ => 2 * Real.cos (2 * x) * (Work.Elliptic.SinQ h x) ^ 2
      * (Real.sin (2 * x)) ^ (1 - Work.Spaces.eta)) (Work.Elliptic.dPhiA h θ) θ := by
    have hprod := (hAA.mul hBB).mul hCC
    convert hprod using 1
    rw [Work.Elliptic.dPhiA, ← hss, ← hse]
    simp only [Pi.mul_apply]
    ring
  exact (Work.Elliptic.PhiA_eventuallyEq h hθ).hasDerivAt_iff.2 key2


/-- `PhiA h` vanishes at both endpoints of `(0, π/2)` (from the bounds of `SliceBdd`). -/
theorem DivSinIdPhiTendsto (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) (hb : Work.Elliptic.SliceBdd h) :
    Filter.Tendsto (Work.Elliptic.PhiA h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (Work.Elliptic.PhiA h) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
  obtain ⟨C, hC0, -, -, -, huL, -, -, -, -, huR, -⟩ := hb
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4' : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hrpow : Filter.Tendsto (fun x : ℝ => x ^ (1 - Work.Spaces.eta)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hc := Real.continuousAt_rpow_const (0 : ℝ) (1 - Work.Spaces.eta)
      (Or.inr (le_of_lt Work.Elliptic.one_sub_eta_pos))
    have hval : (0 : ℝ) ^ (1 - Work.Spaces.eta) = 0 :=
      Real.zero_rpow (ne_of_gt Work.Elliptic.one_sub_eta_pos)
    simpa [hval] using hc.tendsto
  constructor
  · have hrhs : Filter.Tendsto (fun θ : ℝ => 2 * C ^ 2 * (2 * θ) ^ (1 - Work.Spaces.eta))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hbase : Filter.Tendsto (fun θ : ℝ => 2 * θ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hcont : Continuous fun θ : ℝ => 2 * θ := continuous_const.mul continuous_id
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using (hrpow.comp hbase).const_mul (2 * C ^ 2)
    have hbound : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
        ‖Work.Elliptic.PhiA h θ‖ ≤ 2 * C ^ 2 * (2 * θ) ^ (1 - Work.Spaces.eta) := by
      filter_upwards [Ioo_mem_nhdsGT hpi4] with θ hθ
      have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ'
      rw [Work.Elliptic.PhiA_eq_of_mem h hθ']
      have hsrp : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          ≤ (2 * θ) ^ (1 - Work.Spaces.eta) :=
        Real.rpow_le_rpow (le_of_lt hs) (Work.Elliptic.sin_two_le_left hθ)
          (le_of_lt Work.Elliptic.one_sub_eta_pos)
      have hsq : (Work.Elliptic.SinQ h θ) ^ 2 ≤ C ^ 2 := by
        have h := abs_le.mp (huL θ hθ)
        nlinarith [h.1, h.2, hC0]
      have hnorm : ‖2 * Real.cos (2 * θ) * (Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)‖
          = 2 * |Real.cos (2 * θ)| * (Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
          abs_of_nonneg (sq_nonneg (Work.Elliptic.SinQ h θ)),
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) (1 - Work.Spaces.eta))]
      rw [hnorm]
      have h3 : (Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          ≤ C ^ 2 * (2 * θ) ^ (1 - Work.Spaces.eta) :=
        mul_le_mul hsq hsrp (Real.rpow_nonneg (le_of_lt hs) _) (sq_nonneg C)
      have h4 : |Real.cos (2 * θ)|
            * ((Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta))
          ≤ 1 * (C ^ 2 * (2 * θ) ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul (Real.abs_cos_le_one (2 * θ)) h3
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _)) (by norm_num)
      linarith [h4]
    exact squeeze_zero_norm' hbound hrhs
  · have hrhs : Filter.Tendsto
        (fun θ : ℝ => 2 * C ^ 2 * (2 * (Real.pi / 2 - θ)) ^ (1 - Work.Spaces.eta))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      have hbase : Filter.Tendsto (fun θ : ℝ => 2 * (Real.pi / 2 - θ))
          (𝓝[<] (Real.pi / 2)) (𝓝 (0 : ℝ)) := by
        have hcont : Continuous fun θ : ℝ => 2 * (Real.pi / 2 - θ) :=
          continuous_const.mul (continuous_const.sub continuous_id)
        simpa using (hcont.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
      simpa using (hrpow.comp hbase).const_mul (2 * C ^ 2)
    have hbound : ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
        ‖Work.Elliptic.PhiA h θ‖ ≤ 2 * C ^ 2 * (2 * (Real.pi / 2 - θ)) ^ (1 - Work.Spaces.eta) := by
      filter_upwards [Ioo_mem_nhdsLT hpi4'] with θ hθ
      have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ'
      rw [Work.Elliptic.PhiA_eq_of_mem h hθ']
      have hsrp : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          ≤ (2 * (Real.pi / 2 - θ)) ^ (1 - Work.Spaces.eta) :=
        Real.rpow_le_rpow (le_of_lt hs) (Work.Elliptic.sin_two_le_right hθ)
          (le_of_lt Work.Elliptic.one_sub_eta_pos)
      have hsq : (Work.Elliptic.SinQ h θ) ^ 2 ≤ C ^ 2 := by
        have h := abs_le.mp (huR θ hθ)
        nlinarith [h.1, h.2, hC0]
      have hnorm : ‖2 * Real.cos (2 * θ) * (Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)‖
          = 2 * |Real.cos (2 * θ)| * (Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
          abs_of_nonneg (sq_nonneg (Work.Elliptic.SinQ h θ)),
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) (1 - Work.Spaces.eta))]
      rw [hnorm]
      have h3 : (Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          ≤ C ^ 2 * (2 * (Real.pi / 2 - θ)) ^ (1 - Work.Spaces.eta) :=
        mul_le_mul hsq hsrp (Real.rpow_nonneg (le_of_lt hs) _) (sq_nonneg C)
      have h4 : |Real.cos (2 * θ)|
            * ((Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta))
          ≤ 1 * (C ^ 2 * (2 * (Real.pi / 2 - θ)) ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul (Real.abs_cos_le_one (2 * θ)) h3
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _)) (by norm_num)
      linarith [h4]
    exact squeeze_zero_norm' hbound hrhs


/-- Jordan's inequality `sin(2θ) ≥ (4/π) θ` on the closed half-interval `(0, π/4]`. -/
theorem sin_two_ge_left_closed {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 4)) :
    4 / π * θ ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ π / 2 := by linarith [hθ.2, Real.pi_pos]
  have h := Real.mul_le_sin h1 h2
  rwa [show (2 : ℝ) / π * (2 * θ) = 4 / π * θ by ring] at h

/-- Jordan's inequality `sin(2θ) ≥ (4/π) (π/2 - θ)` on the closed half-interval `[π/4, π/2)`. -/
theorem sin_two_ge_right_closed {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    4 / π * (π / 2 - θ) ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * (π / 2 - θ) := by linarith [hθ.2, Real.pi_pos]
  have h2 : 2 * (π / 2 - θ) ≤ π / 2 := by linarith [hθ.1, Real.pi_pos]
  have h := Real.mul_le_sin h1 h2
  have heq : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
    rw [show 2 * θ = π - 2 * (π / 2 - θ) by ring, Real.sin_pi_sub]
  rw [heq]
  rwa [show (2 : ℝ) / π * (2 * (π / 2 - θ)) = 4 / π * (π / 2 - θ) by ring] at h

/-- `θ ↦ sin(2θ)^p` is continuous on `(0, π/2)` for every real exponent `p`. -/
theorem continuousOn_sin_two_rpow (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (Real.pi / 2)) :=
  ((Real.continuous_sin.comp
      (continuous_const.mul continuous_id : Continuous fun x : ℝ => (2 : ℝ) * x)).continuousOn).rpow_const
    (fun x hx => Or.inl (Work.Elliptic.sin_two_ne_zero' hx))

/-- The singular weight `sin(2θ)^{-η}` is dominated by the standard endpoint majorant. -/
theorem rpow_sin_two_le_majorant {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      ≤ (Real.pi / 4) ^ Work.Spaces.eta
        * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
  have hη : (-Work.Spaces.eta) ≤ 0 := by linarith [Work.Elliptic.eta_pos']
  have hM : (0 : ℝ) ≤ (Real.pi / 4) ^ Work.Spaces.eta :=
    le_of_lt (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _)
  have hpos1 : (0 : ℝ) ≤ θ ^ (-Work.Spaces.eta) := Real.rpow_nonneg (le_of_lt hθ.1) _
  have hpos2 : (0 : ℝ) ≤ (Real.pi / 2 - θ) ^ (-Work.Spaces.eta) :=
    Real.rpow_nonneg (by linarith [hθ.2]) _
  by_cases hle : θ ≤ Real.pi / 4
  · have hx : 0 < 4 / π * θ := mul_pos (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) hθ.1
    have h1 : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) ≤ (4 / π * θ) ^ (-Work.Spaces.eta) :=
      Real.rpow_le_rpow_of_nonpos hx (sin_two_ge_left_closed ⟨hθ.1, hle⟩) hη
    have h2 : (4 / π * θ) ^ (-Work.Spaces.eta)
        = (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-Work.Spaces.eta) := by
      rw [Real.mul_rpow (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)) (le_of_lt hθ.1),
        Real.rpow_neg_eq_inv_rpow, inv_div]
    have h3 : (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-Work.Spaces.eta)
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
          * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hpos2) hM
    exact le_trans h1 (le_trans h2.le h3)
  · have hx : 0 < 4 / π * (Real.pi / 2 - θ) :=
      mul_pos (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) (by linarith [hθ.2])
    have h1 : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        ≤ (4 / π * (Real.pi / 2 - θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_le_rpow_of_nonpos hx
        (sin_two_ge_right_closed ⟨le_of_lt (lt_of_not_ge hle), hθ.2⟩) hη
    have h2 : (4 / π * (Real.pi / 2 - θ)) ^ (-Work.Spaces.eta)
        = (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (-Work.Spaces.eta) := by
      rw [Real.mul_rpow (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)) (by linarith [hθ.2]),
        Real.rpow_neg_eq_inv_rpow, inv_div]
    have h3 : (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
          * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hpos1) hM
    exact le_trans h1 (le_trans h2.le h3)

/-- `θ ↦ sin(2θ)^{-η}` is integrable on `Iθ`. -/
theorem integrableOn_sin_two_neg_eta :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ MeasureTheory.volume := by
  have hM : (0 : ℝ) ≤ (Real.pi / 4) ^ Work.Spaces.eta :=
    le_of_lt (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _)
  simpa only [Work.Spaces.Iθ] using
    Work.Elliptic.integrableOn_of_rpow_majorant Work.Elliptic.eta_nonneg'
      Work.Elliptic.eta_lt_one' hM (continuousOn_sin_two_rpow (-Work.Spaces.eta))
      (fun θ hθ => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt (Work.Elliptic.sin_two_pos hθ)) _)]
        exact rpow_sin_two_le_majorant hθ)


/-- The four integrands of `DivSinIdentityA` are integrable on `Iθ`. -/
theorem DivSinIdIntegr (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) (hb : Work.Elliptic.SliceBdd h) :
    MeasureTheory.IntegrableOn (Work.Elliptic.F1A h) Work.Spaces.Iθ MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (Work.Elliptic.F2A h) Work.Spaces.Iθ MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (Work.Elliptic.F3A h) Work.Spaces.Iθ MeasureTheory.volume ∧
    MeasureTheory.IntegrableOn (Work.Elliptic.F4A h) Work.Spaces.Iθ MeasureTheory.volume := by
  obtain ⟨C, hC0, hA1, hA2, hA3, huL, hvL, hA6, hA7, hA8, huR, hvR⟩ := hb
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hsub : Set.Ioo 0 (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hcdDen : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hcdSinQ : ContDiffOn ℝ ⊤ (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) :=
    (hh.mono hsub).div hcdDen (fun x hx => Work.Elliptic.sin_two_ne_zero' hx)
  have hcontSinQ : ContinuousOn (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) :=
    hcdSinQ.continuousOn
  have hcontDSinQ : ContinuousOn (fun θ : ℝ => deriv (Work.Elliptic.SinQ h) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hcdSinQ.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontDh : ContinuousOn (fun θ : ℝ => deriv h θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hh.mono hsub).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontCos2 : ContinuousOn (fun θ : ℝ => (Real.cos (2 * θ)) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id : Continuous fun x : ℝ => (2 : ℝ) * x)).continuousOn).pow 2
  -- global bounds
  obtain ⟨Q1, hQ1⟩ := Work.Elliptic.exists_bound_of_continuousOn_Ioo hpi2 hcontSinQ
    ⟨C, Real.pi / 4, hpi4, fun x hx => huL x ⟨hx.1, by linarith [hx.2]⟩⟩
    ⟨C, Real.pi / 4, hpi4, fun x hx => huR x ⟨by linarith [hx.1], hx.2⟩⟩
  obtain ⟨Q2, hQ2⟩ := Work.Elliptic.exists_bound_of_continuousOn_Ioo hpi2 hcontDSinQ
    ⟨C, Real.pi / 4, hpi4, fun x hx => hvL x ⟨hx.1, by linarith [hx.2]⟩⟩
    ⟨C, Real.pi / 4, hpi4, fun x hx => hvR x ⟨by linarith [hx.1], hx.2⟩⟩
  have hleftD : ∃ B δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Ioo 0 (0 + δ), |deriv h x| ≤ B :=
    ⟨C * (Real.pi / 4) + |derivWithin h (Set.Icc 0 (Real.pi / 2)) 0|, Real.pi / 4, hpi4, by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 4) := ⟨hx.1, by linarith [hx.2]⟩
      have h1 := hA2 x hx'
      have h2 : |deriv h x|
          ≤ |deriv h x - derivWithin h (Set.Icc 0 (Real.pi / 2)) 0|
            + |derivWithin h (Set.Icc 0 (Real.pi / 2)) 0| := by
        simpa [sub_add_cancel]
          using abs_add_le (deriv h x - derivWithin h (Set.Icc 0 (Real.pi / 2)) 0)
            (derivWithin h (Set.Icc 0 (Real.pi / 2)) 0)
      nlinarith [h1, h2, hC0, hx'.2, Real.pi_pos]⟩
  have hrightD : ∃ B δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |deriv h x| ≤ B :=
    ⟨C * (Real.pi / 4) + |derivWithin h (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2)|,
      Real.pi / 4, hpi4, by
      intro x hx
      have hx' : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := ⟨by linarith [hx.1], hx.2⟩
      have h1 := hA7 x hx'
      have h2 : |deriv h x|
          ≤ |deriv h x - derivWithin h (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2)|
            + |derivWithin h (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2)| := by
        simpa [sub_add_cancel]
          using abs_add_le (deriv h x - derivWithin h (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2))
            (derivWithin h (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2))
      nlinarith [h1, h2, hC0, hx'.1, Real.pi_pos]⟩
  obtain ⟨D, hD⟩ := Work.Elliptic.exists_bound_of_continuousOn_Ioo hpi2 hcontDh hleftD hrightD
  -- the weight is integrable
  have hWint : MeasureTheory.Integrable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sin_two_neg_eta.integrable
  have hmeasIoo : ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Ioo 0 (Real.pi / 2)) →
      AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro g hg
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl]
    rw [Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]
    exact hg.aestronglyMeasurable measurableSet_Ioo
  have hkey : ∀ (f : ℝ → ℝ) (c : ℝ), 0 ≤ c →
      ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        ‖f θ‖ ≤ c * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) →
      MeasureTheory.IntegrableOn f Work.Spaces.Iθ MeasureTheory.volume := by
    intro f c hc hcont hbnd
    have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖f θ‖ ≤ c * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Work.Elliptic.ae_mem_Ioo_Iθ.mono fun θ hθ => hbnd θ hθ
    exact (hWint.const_mul c).mono' (hmeasIoo hcont) hbd
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hkey (Work.Elliptic.F1A h) (D ^ 2) (sq_nonneg D)
      ((hcontDh.pow 2).mul (continuousOn_sin_two_rpow (-Work.Spaces.eta))) ?_
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_nonneg (le_of_lt hs) _
    have hDθ : |deriv h θ| ≤ D := by
      simpa [Real.norm_eq_abs] using hD θ hθ
    have hDnn : 0 ≤ D := le_trans (abs_nonneg _) hDθ
    have hsq : (deriv h θ) ^ 2 ≤ D ^ 2 := by
      nlinarith [hDθ, hDnn, le_abs_self (deriv h θ), neg_abs_le (deriv h θ)]
    have heq : ‖Work.Elliptic.F1A h θ‖
        = (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [Work.Elliptic.F1A, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hsq hsnn
  · refine hkey (Work.Elliptic.F2A h) (Q2 ^ 2) (sq_nonneg Q2)
      ((hcontDSinQ.pow 2).mul (continuousOn_sin_two_rpow (2 - Work.Spaces.eta))) ?_
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_nonneg (le_of_lt hs) _
    have hQ2θ : |deriv (Work.Elliptic.SinQ h) θ| ≤ Q2 := by
      simpa [Real.norm_eq_abs] using hQ2 θ hθ
    have hQ2nn : 0 ≤ Q2 := le_trans (abs_nonneg _) hQ2θ
    have hsq : (deriv (Work.Elliptic.SinQ h) θ) ^ 2 ≤ Q2 ^ 2 := by
      nlinarith [hQ2θ, hQ2nn, le_abs_self (deriv (Work.Elliptic.SinQ h) θ),
        neg_abs_le (deriv (Work.Elliptic.SinQ h) θ)]
    have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
      pow_le_one₀ (le_of_lt hs) (Real.sin_le_one _)
    have hsplit : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [show (2 : ℝ) - Work.Spaces.eta = 2 + (-Work.Spaces.eta) by ring,
        Real.rpow_add hs, Real.rpow_two]
    have heq : ‖Work.Elliptic.F2A h θ‖
        = (deriv (Work.Elliptic.SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      rw [Work.Elliptic.F2A, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _))]
    rw [heq, hsplit, ← mul_assoc]
    calc (deriv (Work.Elliptic.SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        ≤ (Q2 ^ 2 * 1) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
          mul_le_mul (mul_le_mul hsq hs2 (pow_nonneg (le_of_lt hs) 2) (sq_nonneg Q2))
            le_rfl hsnn (mul_nonneg (sq_nonneg Q2) zero_le_one)
      _ = Q2 ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by ring
  · refine hkey (Work.Elliptic.F3A h) (Q1 ^ 2) (sq_nonneg Q1)
      ((hcontCos2.mul (hcontSinQ.pow 2)).mul
        (continuousOn_sin_two_rpow (-Work.Spaces.eta))) ?_
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_nonneg (le_of_lt hs) _
    have hQ1θ : |Work.Elliptic.SinQ h θ| ≤ Q1 := by
      simpa [Real.norm_eq_abs] using hQ1 θ hθ
    have hQ1nn : 0 ≤ Q1 := le_trans (abs_nonneg _) hQ1θ
    have hsq : (Work.Elliptic.SinQ h θ) ^ 2 ≤ Q1 ^ 2 := by
      nlinarith [hQ1θ, hQ1nn, le_abs_self (Work.Elliptic.SinQ h θ),
        neg_abs_le (Work.Elliptic.SinQ h θ)]
    have hc2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
      nlinarith [Real.abs_cos_le_one (2 * θ), le_abs_self (Real.cos (2 * θ)),
        neg_abs_le (Real.cos (2 * θ))]
    have heq : ‖Work.Elliptic.F3A h θ‖
        = (Real.cos (2 * θ)) ^ 2 * (Work.Elliptic.SinQ h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [Work.Elliptic.F3A, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsnn)]
    rw [heq]
    calc (Real.cos (2 * θ)) ^ 2 * (Work.Elliptic.SinQ h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        ≤ (1 * Q1 ^ 2) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
          mul_le_mul (mul_le_mul hc2 hsq (sq_nonneg _) zero_le_one) le_rfl hsnn
            (mul_nonneg zero_le_one (sq_nonneg Q1))
      _ = Q1 ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by ring
  · refine hkey (Work.Elliptic.F4A h) (Q1 ^ 2) (sq_nonneg Q1)
      ((continuousOn_sin_two_rpow (2 - Work.Spaces.eta)).mul (hcontSinQ.pow 2)) ?_
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := Work.Elliptic.sin_two_pos hθ
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_nonneg (le_of_lt hs) _
    have hQ1θ : |Work.Elliptic.SinQ h θ| ≤ Q1 := by
      simpa [Real.norm_eq_abs] using hQ1 θ hθ
    have hQ1nn : 0 ≤ Q1 := le_trans (abs_nonneg _) hQ1θ
    have hsq : (Work.Elliptic.SinQ h θ) ^ 2 ≤ Q1 ^ 2 := by
      nlinarith [hQ1θ, hQ1nn, le_abs_self (Work.Elliptic.SinQ h θ),
        neg_abs_le (Work.Elliptic.SinQ h θ)]
    have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
      pow_le_one₀ (le_of_lt hs) (Real.sin_le_one _)
    have hsplit : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [show (2 : ℝ) - Work.Spaces.eta = 2 + (-Work.Spaces.eta) by ring,
        Real.rpow_add hs, Real.rpow_two]
    have heq : ‖Work.Elliptic.F4A h θ‖
        = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) * (Work.Elliptic.SinQ h θ) ^ 2 := by
      rw [Work.Elliptic.F4A, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (sq_nonneg _))]
    rw [heq, hsplit]
    calc ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          * (Work.Elliptic.SinQ h θ) ^ 2
        = ((Real.sin (2 * θ)) ^ 2 * (Work.Elliptic.SinQ h θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by ring
      _ ≤ (1 * Q1 ^ 2) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
          mul_le_mul (mul_le_mul hs2 hsq (sq_nonneg _) zero_le_one) le_rfl hsnn
            (mul_nonneg zero_le_one (sq_nonneg Q1))
      _ = Q1 ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by ring

theorem DivSinIdentityA (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) (hb : Work.Elliptic.SliceBdd h) :
    (∫ θ in Work.Spaces.Iθ, (deriv h θ)^2 * (Real.sin (2*θ))^(- Work.Spaces.eta))
      = (∫ θ in Work.Spaces.Iθ, (deriv (Work.Elliptic.SinQ h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.eta))
        + 4 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (Real.cos (2*θ))^2 * (Work.Elliptic.SinQ h θ)^2 * (Real.sin (2*θ))^(- Work.Spaces.eta))
        + 4 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^(2 - Work.Spaces.eta) * (Work.Elliptic.SinQ h θ)^2)
      ∧ MeasureTheory.IntegrableOn (fun θ => (deriv (Work.Elliptic.SinQ h) θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.eta)) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.cos (2*θ))^2 * (Work.Elliptic.SinQ h θ)^2 * (Real.sin (2*θ))^(- Work.Spaces.eta)) Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun θ => (Real.sin (2*θ))^(2 - Work.Spaces.eta) * (Work.Elliptic.SinQ h θ)^2) Work.Spaces.Iθ MeasureTheory.volume := by
  obtain ⟨hi1, hi2, hi3, hi4⟩ := Work.Elliptic.DivSinIdIntegr h hh h0 hπ hb
  have hpt := Work.Elliptic.DivSinIdPointwise h hh
  have hT := Work.Elliptic.DivSinIdPhiTendsto h hh h0 hπ hb
  have hDer := Work.Elliptic.DivSinIdPhiDeriv h hh
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hInt1 : MeasureTheory.Integrable (Work.Elliptic.F1A h)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hi1.integrable
  have hInt2 : MeasureTheory.Integrable (Work.Elliptic.F2A h)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hi2.integrable
  have hInt3 : MeasureTheory.Integrable (Work.Elliptic.F3A h)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hi3.integrable
  have hInt4 : MeasureTheory.Integrable (Work.Elliptic.F4A h)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hi4.integrable
  have hInt3m : MeasureTheory.Integrable (fun θ : ℝ => 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hInt3.const_mul (4 * Work.Spaces.eta)
  have hInt4m : MeasureTheory.Integrable (fun θ : ℝ => 4 * Work.Elliptic.F4A h θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hInt4.const_mul (4 : ℝ)
  -- the primitive is integrable
  have hcomb : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Elliptic.F1A h θ - Work.Elliptic.F2A h θ
        - 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ - 4 * Work.Elliptic.F4A h θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hInt1.sub hInt2).sub hInt3m).sub hInt4m
  have hIntdPhi : MeasureTheory.Integrable (Work.Elliptic.dPhiA h)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hae : Work.Elliptic.dPhiA h =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => Work.Elliptic.F1A h θ - Work.Elliptic.F2A h θ
          - 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ - 4 * Work.Elliptic.F4A h θ) := by
      filter_upwards [Work.Elliptic.ae_mem_Ioo_Iθ] with θ hθ
      have hp := hpt θ hθ
      show Work.Elliptic.dPhiA h θ = Work.Elliptic.F1A h θ - Work.Elliptic.F2A h θ
        - 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ - 4 * Work.Elliptic.F4A h θ
      linarith [hp]
    exact hcomb.congr hae.symm
  have hIntdPhiIoc : MeasureTheory.Integrable (Work.Elliptic.dPhiA h)
      (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.pi / 2))) := by
    rw [Measure.restrict_congr_set
      (Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
    exact hIntdPhi
  have hIntInterval : IntervalIntegrable (Work.Elliptic.dPhiA h) MeasureTheory.volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := MeasureTheory.volume) hpi2.le).2 hIntdPhiIoc
  have hFTC : ∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Elliptic.dPhiA h θ = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2
      (fun x hx => hDer x hx) hIntInterval hT.1 hT.2
    simpa using h
  have hZero : ∫ θ in Work.Spaces.Iθ, Work.Elliptic.dPhiA h θ = 0 := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl]
    rw [← Measure.restrict_congr_set
        (Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2)),
      ← intervalIntegral.integral_of_le hpi2.le]
    exact hFTC
  -- the pointwise identity, almost everywhere
  have hae1 : Work.Elliptic.F1A h =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ
        + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ + 4 * Work.Elliptic.F4A h θ) := by
    filter_upwards [Work.Elliptic.ae_mem_Ioo_Iθ] with θ hθ
    exact hpt θ hθ
  have hIntDF2 : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntdPhi.add hInt2
  have hIntG' : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ)
        + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntDF2.add hInt3m
  have hEq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F1A h θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F2A h θ)
        + 4 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F3A h θ)
        + 4 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F4A h θ) := by
    have hcongr : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F1A h θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ
              + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ
              + 4 * Work.Elliptic.F4A h θ) :=
      integral_congr_ae hae1
    have hs1 : (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ
            + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ
            + 4 * Work.Elliptic.F4A h θ))
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ)
              + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ)
          + (∫ θ in Work.Spaces.Iθ, 4 * Work.Elliptic.F4A h θ) :=
      integral_add hIntG' hInt4m
    have hs2 : (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ)
              + 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ)
        = (∫ θ in Work.Spaces.Iθ,
            Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ)
          + (∫ θ in Work.Spaces.Iθ, 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ) :=
      integral_add hIntDF2 hInt3m
    have hs3 : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.dPhiA h θ + Work.Elliptic.F2A h θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.dPhiA h θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F2A h θ) :=
      integral_add hIntdPhi hInt2
    have hs4 : (∫ θ in Work.Spaces.Iθ, 4 * Work.Spaces.eta * Work.Elliptic.F3A h θ)
        = 4 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F3A h θ) :=
      integral_const_mul (4 * Work.Spaces.eta) (Work.Elliptic.F3A h)
    have hs5 : (∫ θ in Work.Spaces.Iθ, 4 * Work.Elliptic.F4A h θ)
        = 4 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.F4A h θ) :=
      integral_const_mul (4 : ℝ) (Work.Elliptic.F4A h)
    rw [hcongr, hs1, hs2, hs3, hZero, zero_add, hs4, hs5]
  exact ⟨hEq, hi2, hi3, hi4⟩

end Work.Elliptic
