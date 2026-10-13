/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `I₄` lower bound (`Work.FTS.EllipticEst.AngSecond.I4_lower_bound`)

Proof of the angular term of Step 2 of Proposition `prop:H2` of
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021, tex 895–915.

Write `IP g h = ∫_z ∫_θ g z θ · h z θ · w z² · σ θ` with `σ θ = sin(2θ)^{-η}`
(`Submission.Work.FTS.EllipticEst.AngSecond.Defs`), and put `Ψ̄ = Ψ / cos θ`.  Then

* `pth_tan_sub`: pointwise, `∂_θ(tan θ·Ψ) - Ψ = sin θ·∂_θΨ̄` on the open quadrant;
* `slice_ident`: the slice-by-slice identity
  `∫_θ (∂_θ(tan θ·Ψ) - Ψ)·∂_θθΨ·σ = ((1-η)/2)∫_θ cos 2θ·Ψ̄²·σ - ∫_θ A(θ)·(∂_θΨ̄)²·σ`,
  with `A(θ) = ((1-η)/2)cos 2θ + 2 sin²θ ≥ 0`; it is the fundamental-theorem-of-calculus
  identity `∫_θ H = G(π/2) - G(0) = 0` for the primitive
  `G = (1/2)·sin θ cos θ·σ·((Ψ̄')² - Ψ̄²)` of `I4_aux_defs.Gprim`, whose derivative on the open
  interval is `Hintegrand` (this is the delegated lemma `I4_Gprim_deriv`, and
  `I4_psi_bounds_alt` is the boundedness of `Ψ̄`, `Ψ̄'` which makes `G` vanish at the endpoints);
* `slice_le`: multiplying by `w z² ≥ 0` and integrating in `z` gives
  `IP (∂_θ(tan θ·Ψ)) (∂_θθΨ) - IP Ψ (∂_θθΨ) ≤ (1-η)·IP Ψ Ψ`, using
  `cos 2θ·Ψ̄² ≤ 2Ψ²` (`cos_two_mul_mul_div_cos_sq_le`) and `∫ A(∂_θΨ̄)²σ ≥ 0`.

The main theorem `I4_lower_bound` is then one application of `slice_le` plus the monotonicity
of the outer `z`-integral (`setIntegral_mono_on`, with the boundary point `z = 0` — where
`w2 0 = 0` makes both sides vanish — handled separately).
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs
import Submission.Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv
import Submission.Work.FTS.EllipticEst.AngSecond.I4_psi_bounds_alt
import Submission.Work.FTS.EllipticEst.AngSecond.I4_Gprim_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

theorem setIntegral_Ioo_Iθ (g : ℝ → ℝ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), g θ) = ∫ θ in Work.Spaces.Iθ, g θ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))

theorem integrableOn_continuousOn_mul {f : ℝ → ℝ} {A : Set ℝ} (hf : IntegrableOn f A)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 (Real.pi / 2)))
    (hAm : MeasurableSet A) (hA : A ⊆ Set.Icc 0 (Real.pi / 2)) :
    IntegrableOn (fun x => f x * g x) A :=
  hf.mul_continuousOn_of_subset hg hAm isCompact_Icc hA

theorem integrableOn_of_mul_w2 {g : ℝ → ℝ} {s : Set ℝ} {z : ℝ} (hz : 0 < z)
    (hs : MeasurableSet s) (h : IntegrableOn (fun θ => g θ * w2 z) s) : IntegrableOn g s := by
  have hw : w2 z ≠ 0 := ne_of_gt (by rw [w2]; exact pow_pos (w_pos hz) 2)
  have h' := h.const_mul ((w2 z))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h' ?_ hs
  intro θ hθ
  field_simp

theorem cos_two_mul_mul_div_cos_sq_le {a θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (2 * θ) * (a / Real.cos θ) ^ 2 ≤ 2 * a ^ 2 := by
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_pos hcpos
  have hkey : (2 * Real.cos θ ^ 2 - 1) * (a ^ 2 / Real.cos θ ^ 2)
      = 2 * a ^ 2 - a ^ 2 / Real.cos θ ^ 2 := by
    field_simp
  rw [div_pow, Real.cos_two_mul, hkey]
  have hnn : 0 ≤ a ^ 2 / Real.cos θ ^ 2 := div_nonneg (sq_nonneg a) (le_of_lt hc2)
  linarith

theorem IP_sub_left {g₁ g₂ h : ℝ → ℝ → ℝ} (h1 : IPMem g₁ h) (h2 : IPMem g₂ h) :
    IP g₁ h - IP g₂ h = IP (fun z θ => g₁ z θ - g₂ z θ) h := by
  have hF : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, g₁ z θ * h z θ * w2 z * sig θ)
        - (∫ θ in Work.Spaces.Iθ, g₂ z θ * h z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, (g₁ z θ - g₂ z θ) * h z θ * w2 z * sig θ := by
    intro z hz
    rw [← MeasureTheory.integral_sub (h1.1 z hz) (h2.1 z hz)]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring
  rw [IP, IP, IP, ← MeasureTheory.integral_sub h1.2 h2.2]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z hz => hF z hz

/-! ## The pointwise identity in the language of `Ψ` -/

theorem pth_tan_sub (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
      = Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ := by
  have hz1 : (-1 : ℝ) < z := by linarith
  have hdiff : DifferentiableAt ℝ (fun θ => Ψ z θ) θ := by
    have hs : ContDiffOn ℝ ⊤ (fun t : ℝ => Ψ z t) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
      have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
        contDiffOn_const.prodMk contDiffOn_id
      have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
      simpa [Function.comp_def, Function.uncurry] using h
    exact (hs.contDiffAt (Ioo_mem_nhds (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))).differentiableAt (by simp)
  simpa [Work.Spaces.pth] using I4_tan_mul_sub_deriv (fun θ => Ψ z θ) hθ hdiff

/-! ## The slice identity, from the fundamental theorem of calculus -/

theorem slice_ident (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0)
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C)
    (hiA : IntegrableOn (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hiB : IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hiC : IntegrableOn (fun θ => Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
      * deriv (deriv u) θ * sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
        * deriv (deriv u) θ * sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2),
            acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  set P1 : ℝ → ℝ := fun θ => acoef θ * (deriv ψ θ) ^ 2 * sig θ with hP1
  set P2 : ℝ → ℝ := fun θ => Real.sin θ * deriv ψ θ * deriv (deriv u) θ * sig θ with hP2
  set P3 : ℝ → ℝ := fun θ => (((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ)) * ψ θ ^ 2 * sig θ
    with hP3
  have hI : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hcA : ContinuousOn acoef (Set.Icc 0 (Real.pi / 2)) := by
    unfold acoef; fun_prop
  have hcC : ContinuousOn (fun θ => ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ))
      (Set.Icc 0 (Real.pi / 2)) := by fun_prop
  have hP1int : IntegrableOn P1 (Set.Ioo 0 (Real.pi / 2)) := by
    have h := integrableOn_continuousOn_mul (g := acoef) hiA hcA hI hsub
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ hI
    intro θ hθ
    first
      | (simp only [hP1, hψ]; ring)
      | (simp only [hP1, hψ])
  have hP2int : IntegrableOn P2 (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hiC ?_ hI
    intro θ hθ
    first
      | (simp only [hP2, hψ]; ring)
      | (simp only [hP2, hψ])
  have hP3int : IntegrableOn P3 (Set.Ioo 0 (Real.pi / 2)) := by
    have h := integrableOn_continuousOn_mul
      (g := fun θ => ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ)) hiB hcC hI hsub
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ hI
    intro θ hθ
    first
      | (simp only [hP3, hψ, mul_assoc]; ring)
      | (simp only [hP3, hψ]; ring)
      | (simp only [hP3, hψ])
  have hHint : IntegrableOn (Hintegrand u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := (hP1int.add hP2int).sub hP3int
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ hI
    intro θ hθ
    simp only [Hintegrand, hP1, hP2, hP3, hψ, Pi.add_apply, Pi.sub_apply]
    try ring
  have hG := I4_Gprim_deriv u hu hu1 hbdd
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hint : IntervalIntegrable (Hintegrand u) volume 0 (Real.pi / 2) := by
    constructor
    · exact hHint.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)).symm
    · have hset : Set.Ioc (Real.pi / 2) (0 : ℝ) = ∅ :=
        Set.Ioc_eq_empty_iff.mpr (by linarith [Real.pi_pos])
      rw [hset]
      exact integrableOn_empty
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hπ hG.1 hint hG.2.1 hG.2.2
  have hzero : (∫ θ in Set.Ioo 0 (Real.pi / 2), Hintegrand u θ) = 0 := by
    have h1 : (∫ θ in Set.Ioc 0 (Real.pi / 2), Hintegrand u θ) = 0 := by
      rw [← intervalIntegral.integral_of_le hπ.le]
      simpa using hFTC
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))]
    exact h1
  have hsplit : (∫ θ in Set.Ioo 0 (Real.pi / 2), Hintegrand u θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ) + (∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ := by
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), Hintegrand u θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ - P3 θ := by
      refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
      simp only [Hintegrand, hP1, hP2, hP3, hψ]
      try ring
    rw [hcongr]
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ - P3 θ)
        = (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ)
          - ∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ :=
      MeasureTheory.integral_sub (hP1int.add hP2int) hP3int
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ + P2 θ)
        = (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ)
          + ∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ :=
      MeasureTheory.integral_add hP1int hP2int
    linarith [h2, h3]
  have hP3rew : (∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ) := by
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2),
            ((1 - Work.Spaces.eta) / 2)
              * (Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ) := by
      refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
      simp only [hP3, hψ]
      try ring
    rw [hcongr, MeasureTheory.integral_const_mul]
  have hP1rew : (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ := by
    refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
    simp only [hP1, hψ]
  have hP2rew : (∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
          * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ * sig θ := by
    refine MeasureTheory.setIntegral_congr_fun hI fun θ hθ => ?_
    simp only [hP2, hψ]
  have key : (∫ θ in Set.Ioo 0 (Real.pi / 2), P2 θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), P3 θ) - (∫ θ in Set.Ioo 0 (Real.pi / 2), P1 θ) := by
    linarith [hzero, hsplit]
  rw [← hP2rew, key, hP3rew, ← hP1rew]

/-! ## The pointwise-in-`z` inequality -/

theorem slice_le (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hpi : ∀ z, Ψ z (Real.pi / 2) = 0) {z : ℝ} (hz : 0 < z)
    (hM1 : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hM2 : IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hM3 : IPMem Ψ Ψ)
    (hM4 : IPMem (fun z θ => Ψ z θ / Real.cos θ) (fun z θ => Ψ z θ / Real.cos θ))
    (hM5 : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ)
      (fun z θ => Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ)) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      ≤ (1 - Work.Spaces.eta) * (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * w2 z * sig θ) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hIooM : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  set u : ℝ → ℝ := fun θ => Ψ z θ with hu
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ
  have hzu : ContDiffOn ℝ ⊤ u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry, hu] using h
  have hzu2 : ContDiffOn ℝ 2 u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hzu.of_le (by norm_num)
  have hu1 : u (Real.pi / 2) = 0 := by simp only [hu]; exact hpi z
  have hA : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM5.1 z hzI
    have h' : IntegrableOn (fun θ => (deriv ψ θ) ^ 2 * sig θ * w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Work.Spaces.pth, hψ, hu]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hB : IntegrableOn (fun θ => ψ θ ^ 2 * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM4.1 z hzI
    have h' : IntegrableOn (fun θ => ψ θ ^ 2 * sig θ * w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [hψ, hu]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hN : IntegrableOn (fun θ => Ψ z θ * Ψ z θ * sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hM3.1 z hzI
    have h' : IntegrableOn (fun θ => (Ψ z θ * Ψ z θ * sig θ) * w2 z) Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Pi.sub_apply]
      ring
    exact (integrableOn_of_mul_w2 hz measurableSet_Icc h').mono_set Set.Ioo_subset_Icc_self
  have hC : IntegrableOn (fun θ => Real.sin θ * deriv ψ θ * deriv (deriv u) θ * sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hd : IntegrableOn (fun θ => (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        - Ψ z θ) * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ) Work.Spaces.Iθ := by
      have h := (hM1.1 z hzI).sub (hM2.1 z hzI)
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Icc
      intro θ hθ
      simp only [Pi.sub_apply]
      ring
    have hd' : IntegrableOn
        (fun θ => (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
          * deriv (deriv u) θ * sig θ) * w2 z) (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.IntegrableOn.congr_fun (hd.mono_set Set.Ioo_subset_Icc_self)
        ?_ hIooM
      intro θ hθ
      have htan := pth_tan_sub Ψ hsm hz hθ
      have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
      dsimp only
      rw [htan, hf]
      ring
    exact integrableOn_of_mul_w2 hz hIooM hd'
  have hbdd := I4_psi_bounds_alt u hzu2 hu1
  have hident := slice_ident u hzu2 hu1 hbdd hA hB hC
  have htan_all : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ
        = Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ :=
    fun θ hθ => pth_tan_sub Ψ hsm hz hθ
  have step1 :
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
        - (∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
    rw [← MeasureTheory.integral_sub (hM1.1 z hzI) (hM2.1 z hzI)]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Pi.sub_apply]; ring
  have step2 :
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
    rw [setIntegral_Ioo_Iθ]
  have step3 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ) * w2 z := by
    refine MeasureTheory.setIntegral_congr_fun hIooM ?_
    intro θ hθ
    have hf : Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv u) θ := rfl
    dsimp only
    rw [htan_all θ hθ, hf]
    ring
  have step4 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ) * w2 z)
      = w2 z * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ := by
    rw [MeasureTheory.integral_mul_const, mul_comm]
  have step5 :
      (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.sin θ * Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
            * deriv (deriv u) θ * sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
            * (Ψ z θ / Real.cos θ) ^ 2 * sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
            * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ := by
    simpa [Work.Spaces.pth] using hident
  have hPnn : 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
      * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ := by
    refine MeasureTheory.setIntegral_nonneg hIooM fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (acoef_nonneg θ) (sq_nonneg _))
      (sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hcos_le : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
        * (Ψ z θ / Real.cos θ) ^ 2 * sig θ)
      ≤ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hIooM fun θ hθ => ?_
    · have h := integrableOn_continuousOn_mul (g := fun θ => Real.cos (2 * θ)) hB
        (by fun_prop) hIooM fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ hIooM
      intro θ hθ
      first
        | (simp only [hψ, hu]; ring)
        | (simp only [hu]; ring)
        | (simp only [hψ]; ring)
        | ring
    · exact hN.const_mul 2
    · have h1 := cos_two_mul_mul_div_cos_sq_le (a := Ψ z θ) hθ
      have h2 : 0 ≤ sig θ := sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      nlinarith [h3]
  have hE3 : (∫ θ in Work.Spaces.Iθ, Ψ z θ * Ψ z θ * w2 z * sig θ)
      = w2 z * ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ := by
    rw [← setIntegral_Ioo_Iθ (fun θ => Ψ z θ * Ψ z θ * w2 z * sig θ)]
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * w2 z * sig θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Ψ z θ * Ψ z θ * sig θ) * w2 z :=
      MeasureTheory.setIntegral_congr_fun hIooM fun θ _ => by ring
    rw [hcongr, MeasureTheory.integral_mul_const, mul_comm]
  rw [step1, step2, step3, step4, step5, hE3]
  have hw2nn : 0 ≤ w2 z := w2_nonneg z
  have heta2nn : 0 ≤ (1 - Work.Spaces.eta) / 2 := by linarith [one_sub_eta_pos]
  set B : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Real.cos (2 * θ) * (Ψ z θ / Real.cos θ) ^ 2 * sig θ with hBdef
  set P : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), acoef θ
      * (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) ^ 2 * sig θ with hPdef
  set N : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Ψ z θ * Ψ z θ * sig θ with hNdef
  have hB' : B ≤ 2 * N := by rw [hBdef, hNdef]; exact hcos_le
  have hP' : 0 ≤ P := by rw [hPdef]; exact hPnn
  have e1 : w2 z * ((1 - Work.Spaces.eta) / 2 * B - P)
      ≤ w2 z * ((1 - Work.Spaces.eta) / 2 * B) := by
    apply mul_le_mul_of_nonneg_left _ hw2nn
    linarith [hP']
  have e2 : w2 z * ((1 - Work.Spaces.eta) / 2 * B)
      ≤ w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N)) := by
    apply mul_le_mul_of_nonneg_left _ hw2nn
    exact mul_le_mul_of_nonneg_left hB' heta2nn
  have e3 : w2 z * ((1 - Work.Spaces.eta) / 2 * (2 * N))
      = (1 - Work.Spaces.eta) * (w2 z * N) := by ring
  linarith [e1, e2, e3]



/-- **The `I₄` lower bound** (namespace `Work.FTS.EllipticEst.AngSecond`).

The angular term of the paper's Step 2 computation.  With `Ψ` smooth on a neighbourhood of the
closed quadrant and vanishing on the two angular boundaries,

  `-IP (∂_θ(tan θ Ψ)) (∂_θθΨ) ≥ -IP Ψ (∂_θθΨ) - C · IP Ψ Ψ`,

i.e. `I₄ = -∫∫ ∂_θ(tan θ Ψ) ∂_θθΨ w²σ ≥ -∫∫Ψ ∂_θθΨ w²σ - C ‖Ψ·W‖²`.

Route (the paper's `I₄`, tex 895–915): put `Ψ̄ = Ψ/cos θ`, so `Ψ = cos θ Ψ̄` and
`∂_θθΨ = -cos θ Ψ̄ - 2 sin θ ∂_θΨ̄ + cos θ ∂_θθΨ̄`.  Substituting into `I₄` and moving `∂_θ` off
`∂_θθΨ̄` and off `∂_θΨ̄ ∂_θθΨ̄` by integration by parts in `θ` (all boundary terms vanish because
`Ψ̄(θ) = Ψ(θ)/cos θ` is smooth on the closed quadrant with `Ψ̄(0) = 0` and `sin 2θ·W² → 0` at both
endpoints) gives the *identity*

  `P = I₄ + IP Ψ (∂_θθΨ) - ((1-η)/2) ∫∫ Ψ̄² cos 2θ w²σ`,   `P := ∫∫ (∂_θΨ̄)² (2sin²θ + ((1-η)/2)cos 2θ) w²σ ≥ 0`.

Since `cos 2θ > 0` only for `θ < π/4`, where `cos²θ ≥ 1/2` so that `Ψ̄² = Ψ²/cos²θ ≤ 2Ψ²`,
the last term is bounded below by `-((1-η)/2)·2‖ΨW‖²`; dropping the positive `P` gives the claim
(with `C ≥ 1 - η`).  The `Ψ̄`-honesty hypotheses below are what make the identity honest (the
integration by parts replaces a junk value by an honest one otherwise); the prover may replace
them by any route (e.g. a truncation of the singular weight) that avoids them. -/

theorem I4_lower_bound : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    Work.Spaces.SmoothNbhd Ψ → (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) →
    IPMem Ψ (Work.Spaces.pthIter 2 Ψ) →
    IPMem Ψ Ψ →
    IPMem (fun z θ => Ψ z θ / Real.cos θ) (fun z θ => Ψ z θ / Real.cos θ) →
    IPMem (fun z θ => Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ)
      (fun z θ => Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ) →
    - IP Ψ (Work.Spaces.pthIter 2 Ψ) - C * IP Ψ Ψ
      ≤ - IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ) := by
  refine ⟨1, one_pos, ?_⟩
  intro Ψ hsm h0 hpi hM1 hM2 hM3 hM4 hM5
  have hmono : IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ≤ (1 - Work.Spaces.eta) * IP Ψ Ψ := by
    rw [IP, IP]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ici fun z hz => ?_
    · have h := (hM1.2).sub (hM2.2)
      refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ici
      intro z hz
      simp only [Pi.sub_apply]
      rw [← MeasureTheory.integral_sub (hM1.1 z hz) (hM2.1 z hz)]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
        simp only [Pi.sub_apply]; ring
    · exact hM3.2.const_mul (1 - Work.Spaces.eta)
    · have hz' : (0 : ℝ) ≤ z := hz
      rcases eq_or_lt_of_le hz' with h | h
      · subst h
        have hw0 : w2 (0 : ℝ) = 0 := by rw [w2, Work.Spaces.w]; norm_num
        simp [hw0]
      · have hinner : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - Ψ z θ)
              * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
            = ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
                    * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ
                  - Ψ z θ * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring
        rw [hinner, MeasureTheory.integral_sub (hM1.1 z hz) (hM2.1 z hz)]
        exact slice_le Ψ hsm hpi h hM1 hM2 hM3 hM4 hM5
  have hkey : IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Work.Spaces.pthIter 2 Ψ) - IP Ψ (Work.Spaces.pthIter 2 Ψ)
      ≤ 1 * IP Ψ Ψ := by
    rw [IP_sub_left hM1 hM2]
    have hnonneg : 0 ≤ IP Ψ Ψ := IP_self_nonneg Ψ
    have hle : (1 - Work.Spaces.eta) * IP Ψ Ψ ≤ 1 * IP Ψ Ψ := by
      have h1 : (1 - Work.Spaces.eta) ≤ 1 := by rw [Work.Spaces.eta]; norm_num
      exact mul_le_mul_of_nonneg_right h1 hnonneg
    linarith [hmono, hle]
  linarith [hkey]

end Work.FTS.EllipticEst.AngSecond
