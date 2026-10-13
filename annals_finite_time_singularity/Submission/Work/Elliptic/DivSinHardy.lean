import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.power_hardy
import Submission.Work.Elliptic.power_hardy_bounds
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.integrableOn_majorant_rpow

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
set_option maxHeartbeats 1000000

/-! ## Small measure/integral helpers -/

/-- Pointwise statements on a measurable set give a.e. statements on its restriction. -/
private lemma ae_restrict_of_forall {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {p : ℝ → Prop} (h : ∀ x ∈ s, p x) : ∀ᵐ x ∂(μ.restrict s), p x :=
  (MeasureTheory.ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun x hx => h x hx)

/-- A set integral over `[a,b]` is an interval integral. -/
private lemma integral_Icc_eq_intervalIntegral (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

private lemma restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc

/-! ## The reflected weighted Hardy inequality on `Iθ` -/

/-- The right-endpoint mirror of `power_hardy`: `∫_{Iθ} f² (π/2-θ)^{-(2+η)} ≤ 4/(1+η)² ∫_{Iθ} (f')² (π/2-θ)^{-η}`
for `f` smooth on a neighbourhood of `[0,π/2]` with `f (π/2) = 0`. -/
theorem HardyIccRight {f : ℝ → ℝ} (hf : Work.Elliptic.SmoothSlice f)
    (h0 : f (Real.pi / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))
      ≤ 4 / (1 + Work.Spaces.eta) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (deriv f θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
  set g : ℝ → ℝ := fun t => f (Real.pi / 2 - t) with hgdef
  have hg_sm : ContDiffOn ℝ ⊤ g (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
    have hmap : Set.MapsTo (fun t : ℝ => Real.pi / 2 - t) (Set.Ioo (-1) (Real.pi / 2 + 1))
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hinner : ContDiffOn ℝ ⊤ (fun t : ℝ => Real.pi / 2 - t)
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
      have h1 : ContDiffOn ℝ ⊤ (fun _ : ℝ => Real.pi / 2) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
        contDiffOn_const
      exact h1.sub contDiffOn_id
    have hcomp := hf.comp hinner hmap
    rw [hgdef]
    exact hcomp
  have hg0 : g 0 = 0 := by simp [hgdef, h0]
  have hcd1 : ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi / 2)) :=
    (hg_sm.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).of_le le_top
  have hph := power_hardy (a := Real.pi / 2) pi_half_pos Work.Spaces.eta_nonneg
    Work.Spaces.eta_lt_one hcd1 hg0
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), deriv g t = - deriv f (Real.pi / 2 - t) := by
    intro t ht
    have hmem : Real.pi / 2 - t ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hcd : ContDiffAt ℝ ⊤ f (Real.pi / 2 - t) :=
      (hf.contDiffWithinAt hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have hdiff : DifferentiableAt ℝ f (Real.pi / 2 - t) := hcd.differentiableAt (by simp)
    have h1 : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t := by
      have hfun : ((fun _ : ℝ => Real.pi / 2) - id) = (fun s : ℝ => Real.pi / 2 - s) := by
        funext s; simp
      have h := (hasDerivAt_const (x := t) (c := Real.pi / 2)).sub (hasDerivAt_id t)
      rw [hfun] at h
      simpa using h
    have h2 : HasDerivAt f (deriv f (Real.pi / 2 - t)) (Real.pi / 2 - t) := hdiff.hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => f (Real.pi / 2 - s)) (deriv f (Real.pi / 2 - t) * (-1)) t :=
      h2.comp t h1
    have h4 : deriv (fun s : ℝ => f (Real.pi / 2 - s)) t = deriv f (Real.pi / 2 - t) * (-1) := h3.deriv
    rw [hgdef]
    rw [h4]; ring
  have hcompL := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
    (fun s : ℝ => f s ^ 2 * (Real.pi / 2 - s) ^ (-(2 + Work.Spaces.eta))) (Real.pi / 2)
  have hcompR := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
    (fun s : ℝ => (deriv f s) ^ 2 * (Real.pi / 2 - s) ^ (-(Work.Spaces.eta))) (Real.pi / 2)
  have E1 : (∫ t in (0 : ℝ)..(Real.pi / 2), g t ^ 2 * t ^ (-(2 + Work.Spaces.eta)))
      = ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)) := by
    rw [hgdef]
    trans ∫ x in (0 : ℝ)..(Real.pi / 2),
        f (Real.pi / 2 - x) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - x)) ^ (-(2 + Work.Spaces.eta))
    · refine intervalIntegral.integral_congr (fun x _ => ?_)
      show f (Real.pi / 2 - x) ^ 2 * x ^ (-(2 + Work.Spaces.eta))
          = f (Real.pi / 2 - x) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - x)) ^ (-(2 + Work.Spaces.eta))
      rw [show Real.pi / 2 - (Real.pi / 2 - x) = x by ring]
    · trans ∫ x in (0 : ℝ)..(Real.pi / 2), f x ^ 2 * (Real.pi / 2 - x) ^ (-(2 + Work.Spaces.eta))
      · simpa using hcompL
      · exact (integral_Icc_eq_intervalIntegral
          (fun x => f x ^ 2 * (Real.pi / 2 - x) ^ (-(2 + Work.Spaces.eta))) pi_half_pos.le).symm
  have E2 : (∫ t in (0 : ℝ)..(Real.pi / 2), (deriv g t) ^ 2 * t ^ (-(Work.Spaces.eta)))
      = ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
    trans ∫ x in (0 : ℝ)..(Real.pi / 2),
        (deriv f (Real.pi / 2 - x)) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - x)) ^ (-(Work.Spaces.eta))
    · refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le pi_half_pos.le] at hx
      rw [hderiv x hx]
      show (-deriv f (Real.pi / 2 - x)) ^ 2 * x ^ (-(Work.Spaces.eta))
          = (deriv f (Real.pi / 2 - x)) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - x)) ^ (-(Work.Spaces.eta))
      rw [show Real.pi / 2 - (Real.pi / 2 - x) = x by ring, neg_sq]
    · trans ∫ x in (0 : ℝ)..(Real.pi / 2), (deriv f x) ^ 2 * (Real.pi / 2 - x) ^ (-(Work.Spaces.eta))
      · simpa using hcompR
      · exact (integral_Icc_eq_intervalIntegral
          (fun x => (deriv f x) ^ 2 * (Real.pi / 2 - x) ^ (-(Work.Spaces.eta))) pi_half_pos.le).symm
  rw [← E1, ← E2]
  exact hph

/-! ## Integrability of the three weighted integrands -/

private theorem integrableOn_weights {h : ℝ → ℝ} (hh : SmoothSlice h) (h0 : h 0 = 0)
    (h1 : h (Real.pi / 2) = 0) :
    IntegrableOn (fun θ : ℝ => h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))) Work.Spaces.Iθ ∧
    IntegrableOn (fun θ : ℝ => h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))
      Work.Spaces.Iθ ∧
    IntegrableOn (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  have hηp : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hpi4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := pi_half_pos.le
  have hcd1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) :=
    (hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).of_le le_top
  obtain ⟨C, hC, hbf, hbd⟩ := power_hardy_bounds pi_half_pos hcd1 h0
  -- upper bounds from the reflected function
  set g : ℝ → ℝ := fun t => h (Real.pi / 2 - t) with hgdef
  have hg_sm : ContDiffOn ℝ ⊤ g (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
    have hmap : Set.MapsTo (fun t : ℝ => Real.pi / 2 - t) (Set.Ioo (-1) (Real.pi / 2 + 1))
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hinner : ContDiffOn ℝ ⊤ (fun t : ℝ => Real.pi / 2 - t)
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := contDiffOn_const.sub contDiffOn_id
    have hcomp := hh.comp hinner hmap
    rw [hgdef]
    exact hcomp
  have hg0 : g 0 = 0 := by simp [hgdef, h1]
  have hgcd1 : ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi / 2)) :=
    (hg_sm.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).of_le le_top
  obtain ⟨C2, hC2, hbg, _hbdg⟩ := power_hardy_bounds pi_half_pos hgcd1 hg0
  have hb2 : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h s| ≤ C2 * (Real.pi / 2 - s) := by
    intro s hs
    have ht : Real.pi / 2 - s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hh' := hbg (Real.pi / 2 - s) ht
    simp only [hgdef] at hh'
    rwa [show Real.pi / 2 - (Real.pi / 2 - s) = s by ring] at hh'
  -- the constant of the majorant, dominating all three bounds
  set A : ℝ := C ^ 2 + C2 ^ 2 + C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta with hAdef
  have hA1 : C ^ 2 ≤ A := by
    have hp : 0 ≤ C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta :=
      mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hpi4 _)
    rw [hAdef]; linarith [sq_nonneg C2]
  have hA2 : C2 ^ 2 ≤ A := by
    have hp : 0 ≤ C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta :=
      mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hpi4 _)
    rw [hAdef]; linarith [sq_nonneg C]
  have hA3 : C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta ≤ A := by
    rw [hAdef]; linarith [sq_nonneg C2, sq_nonneg C]
  -- integrability of the majorant
  have hη_neg : -1 < -(Work.Spaces.eta) := by linarith [Work.Spaces.eta_lt_one]
  have hM1 : IntegrableOn (fun θ : ℝ => θ ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, ← intervalIntegrable_iff_integrableOn_Icc_of_le hpi2]
    exact intervalIntegral.intervalIntegrable_rpow' hη_neg
  have hM2 : IntegrableOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, ← intervalIntegrable_iff_integrableOn_Icc_of_le hpi2]
    simpa using
      (IntervalIntegrable.comp_sub_left_iff (f := fun θ : ℝ => θ ^ (-(Work.Spaces.eta)))
        (Real.pi / 2) (a := Real.pi / 2) (b := 0)).mpr
        (intervalIntegral.intervalIntegrable_rpow' hη_neg).symm
  have hMsum : IntegrableOn
      (fun θ : ℝ => θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hM1.add hM2
  have hMaj : IntegrableOn
      (fun θ : ℝ => A * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.IntegrableOn.mono_set (MeasureTheory.Integrable.const_mul hMsum A)
      Set.Ioo_subset_Icc_self
  -- continuity on the open interval
  have hcont_h : ContinuousOn h (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hh.continuousOn.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hcont_dh : ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1' : ContinuousOn (derivWithin h (Set.Icc 0 (Real.pi / 2)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hcd1.continuousOn_derivWithin (uniqueDiffOn_Icc pi_half_pos) le_rfl).mono
        Set.Ioo_subset_Icc_self
    refine h1'.congr (fun t ht => ?_)
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
  have hcont_sin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    fun_prop
  have hc1 : ContinuousOn (fun θ : ℝ => h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont_h.pow 2).mul (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1)))
  have hsub : ContinuousOn (fun x : ℝ => Real.pi / 2 - x) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_const.sub continuousOn_id
  have hc2 : ContinuousOn (fun θ : ℝ => h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont_h.pow 2).mul (hsub.rpow_const (fun x hx => Or.inl (ne_of_gt (by linarith [hx.2]))))
  have hc3 : ContinuousOn
      (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont_dh.pow 2).mul (hcont_sin.rpow_const (fun x hx => Or.inl (ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])))))
  -- the generic domination argument
  have key : ∀ {G : ℝ → ℝ}, ContinuousOn G (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |G θ| ≤ A * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) →
      IntegrableOn G Work.Spaces.Iθ := by
    intro G hcontG hbG
    have hIoo : IntegrableOn G (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono' hMaj (hcontG.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hbG θ hθ
    exact hIoo.congr_set_ae (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm)
  refine ⟨key hc1 ?_, key hc2 ?_, key hc3 ?_⟩
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hp2 : 0 ≤ θ ^ (-(2 + Work.Spaces.eta)) := Real.rpow_nonneg (le_of_lt hθ0) _
    have hsum : 0 ≤ θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) :=
      add_nonneg (Real.rpow_nonneg (le_of_lt hθ0) _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
    have h1' : h θ ^ 2 ≤ (C * θ) ^ 2 := by
      have hh' := pow_le_pow_left₀ (abs_nonneg (h θ)) (hbf θ hθ) 2
      simpa [sq_abs] using hh'
    have h2' : θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)) = θ ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_two θ, ← Real.rpow_add hθ0]; congr 1; ring
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hp2)]
    calc h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
        ≤ (C * θ) ^ 2 * θ ^ (-(2 + Work.Spaces.eta)) := mul_le_mul_of_nonneg_right h1' hp2
      _ = C ^ 2 * θ ^ (-(Work.Spaces.eta)) := by rw [mul_pow, mul_assoc, h2']
      _ ≤ C ^ 2 * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [hθ.2]) _)) (sq_nonneg C)
      _ ≤ A * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hA1 hsum
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hd : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hp2 : 0 ≤ (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)) := Real.rpow_nonneg (le_of_lt hd) _
    have hsum : 0 ≤ θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) :=
      add_nonneg (Real.rpow_nonneg (le_of_lt hθ0) _) (Real.rpow_nonneg (le_of_lt hd) _)
    have h1' : h θ ^ 2 ≤ (C2 * (Real.pi / 2 - θ)) ^ 2 := by
      have hh' := pow_le_pow_left₀ (abs_nonneg (h θ)) (hb2 θ hθ) 2
      simpa [sq_abs] using hh'
    have h2' : (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))
        = (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_two (Real.pi / 2 - θ), ← Real.rpow_add hd]; congr 1; ring
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hp2)]
    calc h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))
        ≤ (C2 * (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right h1' hp2
      _ = C2 ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by rw [mul_pow, mul_assoc, h2']
      _ ≤ C2 ^ 2 * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt hθ0) _)) (sq_nonneg C2)
      _ ≤ A * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hA2 hsum
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hp : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg (le_of_lt hsinpos) _
    have hsum : 0 ≤ θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) :=
      add_nonneg (Real.rpow_nonneg (le_of_lt hθ0) _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
    have h1' : (deriv h θ) ^ 2 ≤ C ^ 2 := by
      have hh' := pow_le_pow_left₀ (abs_nonneg (deriv h θ)) (hbd θ hθ) 2
      simpa [sq_abs] using hh'
    have hstep2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant Work.Spaces.eta θ hηp hθIθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
    calc (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := mul_le_mul_of_nonneg_right h1' hp
      _ ≤ C ^ 2 * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hstep2 (sq_nonneg C)
      _ = (C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta)
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by ring
      _ ≤ A * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hA3 hsum

/-! ## The weighted Hardy inequality for `sin(2θ)` -/

theorem DivSinHardy :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ), Work.Elliptic.SmoothSlice h → h 0 = 0 →
      h (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, h θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  refine ⟨(Real.pi / 4) ^ (2 + Work.Spaces.eta) * (4 / (1 + Work.Spaces.eta) ^ 2) * 2
      * 2 ^ Work.Spaces.eta, ?_, ?_⟩
  · have h1 : 0 < (Real.pi / 4) ^ (2 + Work.Spaces.eta) :=
      Real.rpow_pos_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4) _
    have h2 : 0 < (1 + Work.Spaces.eta) ^ 2 := pow_pos (by linarith [Work.Spaces.eta_nonneg]) 2
    have h3 : 0 < (2 : ℝ) ^ Work.Spaces.eta := Real.rpow_pos_of_pos (by norm_num) _
    have h4 : 0 < 4 / (1 + Work.Spaces.eta) ^ 2 := div_pos (by norm_num) h2
    exact mul_pos (mul_pos (mul_pos h1 h4) (by norm_num)) h3
  · intro h hh h0 h1
    have hη0 : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
    have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
    have hsin_nonneg : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hcd1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) :=
      (hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).of_le le_top
    obtain ⟨hI1, hI2, hI3⟩ := integrableOn_weights hh h0 h1
    -- (A) the weighted Hardy inequality at the left endpoint
    have hPL : (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)))
        ≤ 4 / (1 + Work.Spaces.eta) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta)) := by
      rw [Work.Spaces.Iθ]
      rw [integral_Icc_eq_intervalIntegral (fun θ => h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)))
            pi_half_pos.le,
          integral_Icc_eq_intervalIntegral
            (fun θ => (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta))) pi_half_pos.le]
      exact power_hardy (a := Real.pi / 2) pi_half_pos hη0 hη1 hcd1 h0
    -- (B) the weighted Hardy inequality at the right endpoint
    have hPR := HardyIccRight hh h1
    -- (C) majorant comparison for the left-hand side
    have hL : (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * ∫ θ in Work.Spaces.Iθ, (h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
                + h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) := by
      have hfnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) :=
        ae_restrict_of_forall hIθm (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (hsin_nonneg θ hθ) _))
      have hgint : Integrable (fun θ : ℝ => (Real.pi / 4) ^ (2 + Work.Spaces.eta)
          * (h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
            + h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))))
          (volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.Integrable.const_mul (hI1.add hI2) _
      have hfle : (fun θ : ℝ => h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
          ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
              + h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))) :=
        ae_restrict_of_forall hIθm (fun θ hθ => by
          have hs := Work.Spaces.sin_rpow_le_majorant (2 + Work.Spaces.eta) θ (by linarith) hθ
          calc h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
              ≤ h θ ^ 2 * ((Real.pi / 4) ^ (2 + Work.Spaces.eta)
                  * (θ ^ (-(2 + Work.Spaces.eta))
                    + (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))) :=
                mul_le_mul_of_nonneg_left hs (sq_nonneg _)
            _ = (Real.pi / 4) ^ (2 + Work.Spaces.eta)
                  * (h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
                    + h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) := by ring)
      have hcmp := MeasureTheory.integral_mono_of_nonneg hfnn hgint hfle
      rwa [MeasureTheory.integral_const_mul] at hcmp
    -- (D) split of the sum of integrals
    have hsplit : (∫ θ in Work.Spaces.Iθ, (h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
            + h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))))
        = (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ,
                h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) :=
      integral_add hI1 hI2
    -- (E) lower bounds for the right-hand side
    have hRsinL : (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta)))
        ≤ 2 ^ Work.Spaces.eta
            * ∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hfnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta))) :=
        ae_restrict_of_forall hIθm (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg hθ.1 _))
      have hgint : Integrable (fun θ : ℝ => 2 ^ Work.Spaces.eta
          * ((deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          (volume.restrict Work.Spaces.Iθ) := MeasureTheory.Integrable.const_mul hI3 _
      have hfle : (fun θ : ℝ => (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta)))
          ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => 2 ^ Work.Spaces.eta
            * ((deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
        rw [← restrict_Iθ_eq_restrict_Ioo]
        refine ae_restrict_of_forall measurableSet_Ioo (fun θ hθ => ?_)
        have hθ0 : 0 < θ := hθ.1
        have hsinpos : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
        have hle : θ ^ (-(Work.Spaces.eta))
            ≤ 2 ^ Work.Spaces.eta * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          have hsin_le : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith [hθ0])
          have hmono : (2 * θ) ^ (-(Work.Spaces.eta))
              ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            Real.rpow_le_rpow_of_nonpos hsinpos hsin_le (by linarith [hη0])
          have hmul : (2 * θ) ^ (-(Work.Spaces.eta)) = (2 : ℝ) ^ (-(Work.Spaces.eta))
              * θ ^ (-(Work.Spaces.eta)) := Real.mul_rpow (by norm_num) hθ0.le
          have hone : (2 : ℝ) ^ Work.Spaces.eta * (2 : ℝ) ^ (-(Work.Spaces.eta)) = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              show Work.Spaces.eta + -(Work.Spaces.eta) = 0 by ring, Real.rpow_zero]
          calc θ ^ (-(Work.Spaces.eta))
              = (2 : ℝ) ^ Work.Spaces.eta
                  * ((2 : ℝ) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta))) := by
                rw [← mul_assoc, hone, one_mul]
            _ = (2 : ℝ) ^ Work.Spaces.eta * (2 * θ) ^ (-(Work.Spaces.eta)) := by rw [hmul]
            _ ≤ (2 : ℝ) ^ Work.Spaces.eta * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
                mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by norm_num) _)
        calc (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta))
            ≤ (deriv h θ) ^ 2 * (2 ^ Work.Spaces.eta
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
              mul_le_mul_of_nonneg_left hle (sq_nonneg _)
          _ = 2 ^ Work.Spaces.eta
                * ((deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hcmp := MeasureTheory.integral_mono_of_nonneg hfnn hgint hfle
      rwa [MeasureTheory.integral_const_mul] at hcmp
    have hRsinR : (∫ θ in Work.Spaces.Iθ,
            (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
        ≤ 2 ^ Work.Spaces.eta
            * ∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hfnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
        ae_restrict_of_forall hIθm (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (by linarith [hθ.2]) _))
      have hgint : Integrable (fun θ : ℝ => 2 ^ Work.Spaces.eta
          * ((deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          (volume.restrict Work.Spaces.Iθ) := MeasureTheory.Integrable.const_mul hI3 _
      have hfle : (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
          ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => 2 ^ Work.Spaces.eta
            * ((deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
        rw [← restrict_Iθ_eq_restrict_Ioo]
        refine ae_restrict_of_forall measurableSet_Ioo (fun θ hθ => ?_)
        have hd : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
        have hsinpos : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
        have hsin_le : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
          have h1 : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) := (Real.sin_pi_sub (2 * θ)).symm
          rw [h1, show Real.pi - 2 * θ = 2 * (Real.pi / 2 - θ) by ring]
          exact Real.sin_le (by linarith [hθ.2])
        have hle : (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))
            ≤ 2 ^ Work.Spaces.eta * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          have hmono : (2 * (Real.pi / 2 - θ)) ^ (-(Work.Spaces.eta))
              ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            Real.rpow_le_rpow_of_nonpos hsinpos hsin_le (by linarith [hη0])
          have hmul : (2 * (Real.pi / 2 - θ)) ^ (-(Work.Spaces.eta))
              = (2 : ℝ) ^ (-(Work.Spaces.eta))
                * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) :=
            Real.mul_rpow (by norm_num) hd.le
          have hone : (2 : ℝ) ^ Work.Spaces.eta * (2 : ℝ) ^ (-(Work.Spaces.eta)) = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              show Work.Spaces.eta + -(Work.Spaces.eta) = 0 by ring, Real.rpow_zero]
          calc (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))
              = (2 : ℝ) ^ Work.Spaces.eta
                  * ((2 : ℝ) ^ (-(Work.Spaces.eta))
                    * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
                rw [← mul_assoc, hone, one_mul]
            _ = (2 : ℝ) ^ Work.Spaces.eta
                  * (2 * (Real.pi / 2 - θ)) ^ (-(Work.Spaces.eta)) := by rw [hmul]
            _ ≤ (2 : ℝ) ^ Work.Spaces.eta * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
                mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by norm_num) _)
        calc (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))
            ≤ (deriv h θ) ^ 2 * (2 ^ Work.Spaces.eta
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
              mul_le_mul_of_nonneg_left hle (sq_nonneg _)
          _ = 2 ^ Work.Spaces.eta
                * ((deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hcmp := MeasureTheory.integral_mono_of_nonneg hfnn hgint hfle
      rwa [MeasureTheory.integral_const_mul] at hcmp
    -- final assembly
    set R : ℝ := ∫ θ in Work.Spaces.Iθ,
        (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hRdef
    have hc : 0 ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta) :=
      Real.rpow_nonneg (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 4) _
    have hc2 : 0 ≤ 4 / (1 + Work.Spaces.eta) ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
    have key : (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ ((Real.pi / 4) ^ (2 + Work.Spaces.eta) * (4 / (1 + Work.Spaces.eta) ^ 2) * 2
            * 2 ^ Work.Spaces.eta) * R := by
      calc (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
          ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (∫ θ in Work.Spaces.Iθ, (h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
                  + h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))) := hL
        _ = (Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * ((∫ θ in Work.Spaces.Iθ, h θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)))
                  + (∫ θ in Work.Spaces.Iθ,
                      h θ ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))) := by rw [hsplit]
        _ ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (((4 / (1 + Work.Spaces.eta) ^ 2)
                    * (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * θ ^ (-(Work.Spaces.eta))))
                + ((4 / (1 + Work.Spaces.eta) ^ 2)
                    * (∫ θ in Work.Spaces.Iθ,
                        (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))))) := by
              refine mul_le_mul_of_nonneg_left ?_ hc
              exact add_le_add hPL hPR
        _ ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (((4 / (1 + Work.Spaces.eta) ^ 2) * (2 ^ Work.Spaces.eta * R))
                + ((4 / (1 + Work.Spaces.eta) ^ 2) * (2 ^ Work.Spaces.eta * R))) := by
              refine mul_le_mul_of_nonneg_left ?_ hc
              exact add_le_add (mul_le_mul_of_nonneg_left hRsinL hc2)
                (mul_le_mul_of_nonneg_left hRsinR hc2)
        _ = ((Real.pi / 4) ^ (2 + Work.Spaces.eta) * (4 / (1 + Work.Spaces.eta) ^ 2) * 2
              * 2 ^ Work.Spaces.eta) * R := by ring
    have hLdiv : (∫ θ in Work.Spaces.Iθ,
          h θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        = ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
      refine MeasureTheory.setIntegral_congr_fun hIθm (fun θ hθ => ?_)
      rw [div_eq_mul_inv, ← Real.rpow_neg (hsin_nonneg θ hθ)]
    have hRdiv : (∫ θ in Work.Spaces.Iθ,
          (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        = ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      refine MeasureTheory.setIntegral_congr_fun hIθm (fun θ hθ => ?_)
      rw [div_eq_mul_inv, ← Real.rpow_neg (hsin_nonneg θ hθ)]
    rw [hLdiv, hRdiv, ← hRdef]
    exact key

end Work.Elliptic
