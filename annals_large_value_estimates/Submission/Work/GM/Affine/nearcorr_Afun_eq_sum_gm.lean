import Mathlib
import Submission.Work.GM.Affine.nearcorr_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

noncomputable section

/-- Affine change of variables with a weight: for `a ≠ 0`,
`∫ u, F (a*u+b) * G u = (1/|a|) * ∫ y, F y * G ((y-b)/a)`. -/
lemma integral_comp_affine_mul (F G : ℝ → ℝ) {a b : ℝ} (ha : a ≠ 0) :
    ∫ u, F (a * u + b) * G u = (1 / |a|) * ∫ y, F y * G ((y - b) / a) := by
  set H : ℝ → ℝ := fun y => F y * G ((y - b) / a) with hH
  have key : ∀ u : ℝ, F (a * u + b) * G u = H (a * u + b) := by
    intro u
    rw [hH]
    show F (a * u + b) * G u = F (a * u + b) * G ((a * u + b - b) / a)
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ ha]
  calc ∫ u, F (a * u + b) * G u
      = ∫ u, H (a * u + b) := by
          refine integral_congr_ae (Filter.Eventually.of_forall key)
    _ = ∫ u, (fun y => H (y + b)) (a * u) := rfl
    _ = |a⁻¹| • ∫ y, H (y + b) :=
          MeasureTheory.Measure.integral_comp_mul_left (fun y => H (y + b)) a
    _ = |a⁻¹| • ∫ y, H y := by rw [MeasureTheory.integral_add_right_eq_self H b]
    _ = (1 / |a|) * ∫ y, F y * G ((y - b) / a) := by
          rw [hH, smul_eq_mul, abs_inv, inv_eq_one_div]

/-- Integrability of a single summand of `Afun`. -/
lemma integrable_affine_mul_psi {C₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f)
    {s v m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    Integrable (fun u : ℝ => f ((v - s * u) / m) * psiSmooth u) := by
  have hsub : Function.support (fun u : ℝ => f ((v - s * u) / m))
      ⊆ Set.Icc ((v - m * C₀) / s) ((v - m / C₀) / s) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hmem : (v - s * u) / m ∈ Set.Icc (1 / C₀) C₀ := hsup _ hu
    rw [Set.mem_Icc] at hmem
    have h1 : m / C₀ ≤ v - s * u := by
      rw [le_div_iff₀ hm] at hmem; simpa [div_eq_mul_inv, mul_comm] using hmem.1
    have h2 : v - s * u ≤ C₀ * m := by
      rw [div_le_iff₀ hm] at hmem; exact hmem.2
    rw [Set.mem_Icc]
    constructor
    · rw [div_le_iff₀ hs]; nlinarith [h2]
    · rw [le_div_iff₀ hs]; nlinarith [h1]
  have hcs : HasCompactSupport (fun u : ℝ => f ((v - s * u) / m)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub
  have hcont : Continuous (fun u : ℝ => f ((v - s * u) / m)) :=
    hf.comp (by fun_prop)
  exact (hcont.mul psiSmooth_contDiff.continuous).integrable_of_hasCompactSupport
    (hcs.mul_right (f' := psiSmooth))

theorem nearcorr_Afun_eq_sum_gm {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f)
    {M₂ K T : ℝ} (hM₂ : 0 < M₂) (hK : 0 < K) (hT : 0 < T) (v : ℝ) :
    Afun f M₂ K T v = ∑ m ∈ R2 M₂, gm f (smScale K T M₂) m (v / (m : ℝ)) := by
  have hs : 0 < smScale K T M₂ := smScale_pos hK hT hM₂
  have hsne : smScale K T M₂ ≠ 0 := ne_of_gt hs
  have hgm : ∀ m ∈ R2 M₂,
      gm f (smScale K T M₂) m (v / (m : ℝ))
        = ∫ u, f ((v - smScale K T M₂ * u) / (m : ℝ)) * psiSmooth u := by
    intro m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := R2_pos' hm
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have ha : -(smScale K T M₂) / (m : ℝ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr hsne) hmne
    have h := integral_comp_affine_mul (F := f) (G := psiSmooth)
      (a := -(smScale K T M₂) / (m : ℝ)) (b := v / (m : ℝ)) ha
    have hcongr1 : (∫ u, f ((v - smScale K T M₂ * u) / (m : ℝ)) * psiSmooth u)
        = ∫ u, f ((-(smScale K T M₂) / (m : ℝ)) * u + v / (m : ℝ)) * psiSmooth u := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have harg : (v - smScale K T M₂ * u) / (m : ℝ)
          = (-(smScale K T M₂) / (m : ℝ)) * u + v / (m : ℝ) := by
        field_simp
        ring
      show f ((v - smScale K T M₂ * u) / (m : ℝ)) * psiSmooth u
        = f ((-(smScale K T M₂) / (m : ℝ)) * u + v / (m : ℝ)) * psiSmooth u
      rw [harg]
    rw [hcongr1, h]
    rw [gm]
    have hcoef : (1 / |(-(smScale K T M₂) / (m : ℝ))|) = (m : ℝ) / smScale K T M₂ := by
      rw [abs_div, abs_neg, abs_of_pos hs, abs_of_pos hmpos, one_div, inv_div]
    have harg2 : ∀ y : ℝ,
        (y - v / (m : ℝ)) / (-(smScale K T M₂) / (m : ℝ))
          = (m : ℝ) * (v / (m : ℝ) - y) / smScale K T M₂ := by
      intro y
      field_simp
      ring
    rw [hcoef]
    rw [show (∫ y, f y * psiSmooth ((y - v / (m : ℝ)) / (-(smScale K T M₂) / (m : ℝ))))
        = ∫ y, f y * psiSmooth ((m : ℝ) * (v / (m : ℝ) - y) / smScale K T M₂) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show f y * psiSmooth ((y - v / (m : ℝ)) / (-(smScale K T M₂) / (m : ℝ)))
        = f y * psiSmooth ((m : ℝ) * (v / (m : ℝ) - y) / smScale K T M₂)
      rw [harg2 y]]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  have hL : Afun f M₂ K T v
      = ∫ u, ∑ m ∈ R2 M₂, f ((v - smScale K T M₂ * u) / (m : ℝ)) * psiSmooth u := by
    rw [Afun]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Hprof, Finset.sum_mul]
  have hswap : (∫ u, ∑ m ∈ R2 M₂, f ((v - smScale K T M₂ * u) / (m : ℝ)) * psiSmooth u)
      = ∑ m ∈ R2 M₂, ∫ u, f ((v - smScale K T M₂ * u) / (m : ℝ)) * psiSmooth u := by
    rw [MeasureTheory.integral_finsetSum]
    exact fun m hm => integrable_affine_mul_psi hf hsup hs (R2_pos' hm)
  rw [hL, hswap]
  exact Finset.sum_congr rfl (fun m hm => (hgm m hm).symm)

end

end Work.GM.Affine
