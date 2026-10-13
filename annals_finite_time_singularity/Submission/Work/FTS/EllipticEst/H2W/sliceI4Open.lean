import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngClean.I4_lower_bound_slice
import Submission.Work.FTS.EllipticEst.Honest.slice_ident_honest
import Submission.Work.FTS.EllipticEst.Honest.psi_boundary_vanish

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

theorem sliceI4Open (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ z, Ψ z 0 = 0) (hpi : ∀ z, Ψ z (Real.pi / 2) = 0) {z : ℝ} (hz : 0 < z)
    (hM1 : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hM2 : Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hM3 : Work.FTS.EllipticEst.AngSecond.IPMem Ψ Ψ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (hBD : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (hB2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (hBD2 : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ) ^ 2
        * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ (1 - Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  -- shortcuts
  set u : ℝ → ℝ := fun θ => Ψ z θ with hu
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIooM : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self
  -- ## smoothness and boundary values of the slice
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := by
    have hp : ContDiffOn ℝ 2 (fun t : ℝ => (z, t)) (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmap : Set.MapsTo (fun t : ℝ => (z, t)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun t ht => ⟨hz, ht⟩
    have h := (hsm 2).comp hp hmap
    simpa [Function.comp_def, Function.uncurry, hu] using h
  have hu0 : u 0 = 0 := by simpa only [hu] using h0 z
  have hu1 : u (Real.pi / 2) = 0 := by simpa only [hu] using hpi z
  -- ## the integrability inputs of the honest slice lemmas
  have hA_u : MeasureTheory.IntegrableOn (fun θ => u θ ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => (u θ ^ 2 * AngSecond.sig θ) * AngSecond.w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun (hM3.1 z hzI) ?_ measurableSet_Icc
      intro θ _
      simp only [hu]
      ring
    exact (AngSecond.integrableOn_of_mul_w2 hz measurableSet_Icc h1).mono_set hsub
  have hX : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * AngSecond.sig θ) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun hB2 ?_ measurableSet_Icc
      intro θ _
      rfl
    exact h2.mono_set hsub
  have hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hBD2.mono_set hsub) ?_ hIooM
    intro θ _
    simp only [hu]
  have hAd : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hB.mono_set hsub) ?_ hIooM
    intro θ _
    simp only [hu]
  have hAd' : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hBD.mono_set hsub) ?_ hIooM
    intro θ _
    simp only [hu]
  -- ## the endpoint vanishing of the integration-by-parts boundary terms
  obtain ⟨hv1, hv2, hv3, hv4⟩ :=
    Honest.psi_boundary_vanish u hu2 hu0 hu1 hA_u hX hY hAd hAd'
  -- ## the honest slice identity
  have hident := Honest.slice_ident_honest u hu2 hu0 hu1 hA_u hX hY hAd hAd' hv1 hv2 hv3 hv4
  -- ## the pointwise identity `∂_θ(tan θ · u) - u = sin θ · ∂_θ(u / cos θ)`
  have htan : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
        = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
    intro θ hθ
    have hdiff : DifferentiableAt ℝ u θ :=
      (hu2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have h := AngSecond.I4_tan_mul_sub_deriv u hθ hdiff
    simp only [Work.Spaces.pth, hu] at h ⊢
    exact h
  -- ## step 1: linearity of the `θ`-integral
  have step1 :
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
        - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ
            * AngSecond.w2 z * AngSecond.sig θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ := by
    rw [← MeasureTheory.integral_sub (hM1.1 z hzI) (hM2.1 z hzI)]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Pi.sub_apply]; ring
  -- ## step 2: nothing happens on the endpoints
  have step2 :
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ := by
    rw [AngSecond.setIntegral_Ioo_Iθ]
  -- ## step 3: rewrite the integrand as `sin θ ψ' u'' σ` and pull out `w²`
  have step3 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
      = AngSecond.w2 z * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
            * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ
            * AngSecond.sig θ) := by
    rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
            * Work.Spaces.pthIter 2 Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ
            * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ
            * AngSecond.sig θ) * AngSecond.w2 z from
      MeasureTheory.setIntegral_congr_fun hIooM fun θ hθ => by
        have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
        rw [htan θ hθ, hf]; ring]
    rw [MeasureTheory.integral_mul_const]; ring
  -- ## step 4: the value of the slice integral
  have step5 :
      (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
      = AngSecond.w2 z * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          u θ * u θ * AngSecond.sig θ) := by
    rw [← AngSecond.setIntegral_Ioo_Iθ
      (fun θ => Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)]
    rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (u θ * u θ * AngSecond.sig θ) * AngSecond.w2 z from
      MeasureTheory.setIntegral_congr_fun hIooM fun θ _ => by
        simp only [hu]; ring]
    rw [MeasureTheory.integral_mul_const]; ring
  -- ## the two numerical inputs of the final inequality
  have hCnn : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), AngSecond.acoef θ
      * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ := by
    refine MeasureTheory.setIntegral_nonneg hIooM fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (AngSecond.acoef_nonneg θ) (sq_nonneg _))
      (AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hN : MeasureTheory.IntegrableOn (fun θ => u θ * u θ * AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hA_u ?_ hIooM
    intro θ _
    ring
  have hcosle : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * AngSecond.sig θ)
      ≤ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), u θ * u θ * AngSecond.sig θ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hIooM fun θ hθ => ?_
    · have h := AngSecond.integrableOn_continuousOn_mul (g := fun θ => Real.cos (2 * θ)) hAd
        (by fun_prop) hIooM fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ hIooM
      intro θ _
      ring
    · exact hN.const_mul 2
    · have h1 := AngSecond.cos_two_mul_mul_div_cos_sq_le (a := u θ) hθ
      have h2 : 0 ≤ AngSecond.sig θ := AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      have h4 : 2 * u θ ^ 2 * AngSecond.sig θ = 2 * (u θ * u θ * AngSecond.sig θ) := by ring
      linarith [h3, h4]
  -- ## assemble
  rw [step1, step2, step3, hident, step5]
  set B : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * AngSecond.sig θ with hBdef
  set C : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), AngSecond.acoef θ
      * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * AngSecond.sig θ with hCdef
  set N : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), u θ * u θ * AngSecond.sig θ with hNdef
  have hBle : B ≤ 2 * N := by rw [hBdef, hNdef]; exact hcosle
  have hCnn' : 0 ≤ C := by rw [hCdef]; exact hCnn
  have hw2nn : 0 ≤ AngSecond.w2 z := AngSecond.w2_nonneg z
  have heta : 0 < (1 - Work.Spaces.eta) / 2 := by linarith [AngSecond.one_sub_eta_pos]
  have e1 : (1 - Work.Spaces.eta) / 2 * B - C ≤ (1 - Work.Spaces.eta) / 2 * B := by
    linarith [hCnn']
  have e2 : (1 - Work.Spaces.eta) / 2 * B ≤ (1 - Work.Spaces.eta) / 2 * (2 * N) :=
    mul_le_mul_of_nonneg_left hBle (le_of_lt heta)
  have e3 : (1 - Work.Spaces.eta) / 2 * (2 * N) = (1 - Work.Spaces.eta) * N := by ring
  have e4 : AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * B - C)
      ≤ AngSecond.w2 z * ((1 - Work.Spaces.eta) * N) :=
    calc AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * B - C)
        ≤ AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * B) :=
          mul_le_mul_of_nonneg_left e1 hw2nn
      _ ≤ AngSecond.w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N)) :=
          mul_le_mul_of_nonneg_left e2 hw2nn
      _ = AngSecond.w2 z * ((1 - Work.Spaces.eta) * N) := by rw [e3]
  have e5 : AngSecond.w2 z * ((1 - Work.Spaces.eta) * N)
      = (1 - Work.Spaces.eta) * (AngSecond.w2 z * N) := by ring
  linarith [e4, e5]

end

end Work.FTS.EllipticEst.H2W
