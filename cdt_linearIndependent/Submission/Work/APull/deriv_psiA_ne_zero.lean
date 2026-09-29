import Mathlib
import Submission.Work.APsi.psiA_facts
import Submission.Work.APsi.defs
import Submission.Work.APsi.deriv_slit_ne_zero
import Submission.Work.APsi.deriv_lune_ne_zero

/-!
# Area `APull`: `deriv ψ_A` does not vanish on the unit disc

`ψ_A = -(4/5) · lune (36/5) ∘ Neg ∘ slitsA`, where `slitsA` is the composition of the four
rotated slit maps of Calegari--Dimitrov--Tang (arXiv:2408.15403).  The derivative of `ψ_A` is a
product of the derivatives of the individual factors, each of which is non-zero on the open unit
disc:

* `deriv (slit r) w ≠ 0` for `‖w‖ < 1` (the Joukowski relation `w + w⁻¹ = α(z + z⁻¹) + β`
  differentiated gives `w' (1 - w⁻²) = α (1 - z⁻²)`, and `z² = 1` is impossible inside the disc);
* `deriv (lune c) w ≠ 0` for `‖w‖ < 1` (`lune c` is a section of the degree-two rational map
  `luneF c`, so `luneF c ∘ lune c = id` and the chain rule gives
  `deriv (luneF c) (lune c w) · deriv (lune c) w = 1`);
* the four rotating constants, the scaling `491/500` and the final factors `-4/5` have non-zero
  modulus.

The two bulleted analytic facts are proved in `Submission.Work.APsi.deriv_slit_ne_zero` and
`Submission.Work.APsi.deriv_lune_ne_zero`; below they are used as the explicit hypotheses
`hslit` / `hlune` of `deriv_psiA_ne_zero_of`.
-/

namespace Work.APull

open Submission.CDTPlan Metric
open Work.APsi

noncomputable section

/-! ## Chain-rule helpers: non-vanishing is preserved by composition and scalar multiplication -/

lemma deriv_comp_ne_zero {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (g z))
    (hg : DifferentiableAt ℂ g z) (hf' : deriv f (g z) ≠ 0) (hg' : deriv g z ≠ 0) :
    deriv (f ∘ g) z ≠ 0 := by
  rw [deriv_comp z hf hg]
  exact mul_ne_zero hf' hg'

lemma deriv_const_mul_ne_zero {c : ℂ} (hc : c ≠ 0) {f : ℂ → ℂ} {z : ℂ}
    (hf' : deriv f z ≠ 0) : deriv (fun y => c * f y) z ≠ 0 := by
  rw [show deriv (fun y : ℂ => c * f y) z = c * deriv f z from deriv_const_mul_field c]
  exact mul_ne_zero hc hf'

lemma deriv_neg_ne_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hf' : deriv f z ≠ 0) : deriv (fun y => -f y) z ≠ 0 := by
  have h : (fun y : ℂ => -f y) = (fun y : ℂ => (-1 : ℂ) * f y) := by funext y; ring
  rw [h]
  exact deriv_const_mul_ne_zero (by norm_num) hf'

lemma deriv_rot_mul_ne_zero (t : ℝ) {f : ℂ → ℂ} {z : ℂ} (hf' : deriv f z ≠ 0) :
    deriv (fun y => rot t * f y) z ≠ 0 :=
  deriv_const_mul_ne_zero (rot_ne_zero t) hf'

/-! ## The four slit stages and the final rotation -/

/-- One stage of the four-slit composition: composing a differentiable map of non-vanishing
derivative with a rotation and then with a slit map preserves non-vanishing. -/
lemma deriv_slit_comp_ne_zero
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (r t : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hf' : deriv f z ≠ 0) (hfb : ‖f z‖ < 1) :
    deriv (fun y => slit r (rot t * f y)) z ≠ 0 := by
  have hg : DifferentiableAt ℂ (fun y : ℂ => rot t * f y) z := (differentiableAt_const _).mul hf
  have hgz : ‖rot t * f z‖ < 1 := by rw [norm_mul, norm_rot, one_mul]; exact hfb
  have houter : DifferentiableAt ℂ (slit r) (rot t * f z) :=
    (differentiableOn_slit r hr0 hr1).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; exact hgz))
  have houter' : deriv (slit r) (rot t * f z) ≠ 0 := hslit r hr0 hr1 _ hgz
  have h := deriv_comp_ne_zero (f := slit r) (g := fun y : ℂ => rot t * f y)
    houter hg houter' (deriv_rot_mul_ne_zero t hf')
  simpa only [Function.comp_def] using h

lemma deriv_psiA_st1_ne_zero
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : deriv psiA_st1 z ≠ 0 := by
  have hc : (491 / 500 : ℂ) ≠ 0 := by norm_num
  have hlin : DifferentiableAt ℂ (fun y : ℂ => (491 / 500 : ℂ) * y) z :=
    (differentiableAt_const _).mul differentiableAt_id
  have hlin' : deriv (fun y : ℂ => (491 / 500 : ℂ) * y) z ≠ 0 := by
    rw [deriv_const_mul_id]; exact hc
  have hcz : ‖(491 / 500 : ℂ) * z‖ < 1 := by
    rw [norm_mul]
    have h1 : ‖(491 / 500 : ℂ)‖ = (491 / 500 : ℝ) := by
      rw [show ((491 : ℂ) / 500) = ((491 / 500 : ℝ) : ℂ) by norm_num, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    rw [h1]
    nlinarith [norm_nonneg z]
  have houter : DifferentiableAt ℂ (slit (9 / 10)) ((fun y : ℂ => (491 / 500 : ℂ) * y) z) :=
    (differentiableOn_slit (9 / 10) (by norm_num) (by norm_num)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; exact hcz))
  have houter' : deriv (slit (9 / 10)) ((fun y : ℂ => (491 / 500 : ℂ) * y) z) ≠ 0 :=
    hslit (9 / 10) (by norm_num) (by norm_num) _ hcz
  have h := deriv_comp_ne_zero (f := slit (9 / 10)) (g := fun y : ℂ => (491 / 500 : ℂ) * y)
    houter hlin houter' hlin'
  rw [show psiA_st1 = slit (9 / 10) ∘ (fun y : ℂ => (491 / 500 : ℂ) * y) from rfl]
  simpa only [Function.comp_def] using h

lemma deriv_psiA_st2_ne_zero
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : deriv psiA_st2 z ≠ 0 := by
  have hz' : z ∈ ball (0 : ℂ) 1 := by rwa [mem_ball, dist_zero_right]
  have hd : DifferentiableAt ℂ psiA_st1 z :=
    psiA_st1_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz')
  have hm : ‖psiA_st1 z‖ < 1 := by
    have h := psiA_st1_maps_ball hz'
    rwa [mem_ball, dist_zero_right] at h
  have h := deriv_slit_comp_ne_zero hslit (379 / 625) (2033 / 25000) (by norm_num) (by norm_num)
    hd (deriv_psiA_st1_ne_zero hslit z hz) hm
  rw [show psiA_st2 = (fun y : ℂ => slit (379 / 625) (rot (2033 / 25000) * psiA_st1 y)) from rfl]
  exact h

lemma deriv_psiA_st3_ne_zero
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : deriv psiA_st3 z ≠ 0 := by
  have hz' : z ∈ ball (0 : ℂ) 1 := by rwa [mem_ball, dist_zero_right]
  have hd : DifferentiableAt ℂ psiA_st2 z :=
    psiA_st2_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz')
  have hm : ‖psiA_st2 z‖ < 1 := by
    have h := psiA_st2_maps_ball hz'
    rwa [mem_ball, dist_zero_right] at h
  have h := deriv_slit_comp_ne_zero hslit (673 / 1250) (2927 / 25000) (by norm_num) (by norm_num)
    hd (deriv_psiA_st2_ne_zero hslit z hz) hm
  rw [show psiA_st3 = (fun y : ℂ => slit (673 / 1250) (rot (2927 / 25000) * psiA_st2 y)) from rfl]
  exact h

lemma deriv_psiA_st4_ne_zero
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : deriv psiA_st4 z ≠ 0 := by
  have hz' : z ∈ ball (0 : ℂ) 1 := by rwa [mem_ball, dist_zero_right]
  have hd : DifferentiableAt ℂ psiA_st3 z :=
    psiA_st3_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz')
  have hm : ‖psiA_st3 z‖ < 1 := by
    have h := psiA_st3_maps_ball hz'
    rwa [mem_ball, dist_zero_right] at h
  have h := deriv_slit_comp_ne_zero hslit (7487 / 10000) (453 / 12500) (by norm_num) (by norm_num)
    hd (deriv_psiA_st3_ne_zero hslit z hz) hm
  rw [show psiA_st4 = (fun y : ℂ => slit (7487 / 10000) (rot (453 / 12500) * psiA_st3 y)) from rfl]
  exact h

lemma deriv_psiA_st5_ne_zero
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : deriv psiA_st5 z ≠ 0 := by
  have hz' : z ∈ ball (0 : ℂ) 1 := by rwa [mem_ball, dist_zero_right]
  have hd : DifferentiableAt ℂ psiA_st4 z :=
    psiA_st4_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz')
  have h := deriv_rot_mul_ne_zero (-1971 / 25000) (deriv_psiA_st4_ne_zero hslit z hz)
  rw [show psiA_st5 = (fun y : ℂ => rot (-1971 / 25000) * psiA_st4 y) from rfl]
  exact h

/-! ## The non-vanishing of `deriv ψ_A` -/

/-- **The non-vanishing of `deriv ψ_A` on the open unit disc**, given the two non-vanishing facts
for the slit and the lune maps. -/
lemma deriv_psiA_ne_zero_of
    (hslit : ∀ (r : ℝ), 0 < r → r < 1 → ∀ z : ℂ, ‖z‖ < 1 → deriv (slit r) z ≠ 0)
    (hlune : ∀ (c : ℝ), 1 < c → ∀ z : ℂ, ‖z‖ < 1 → deriv (lune c) z ≠ 0) :
    ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → deriv psiA z ≠ 0 := by
  intro z hz
  have hz' : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have h5 := deriv_psiA_st5_ne_zero hslit z hz'
  have hd5 : DifferentiableAt ℂ psiA_st5 z :=
    psiA_st5_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hw : ‖-(psiA_st5 z)‖ < 1 := by
    have h := psiA_st5_maps_ball hz
    rw [mem_ball, dist_zero_right] at h
    simpa using h
  have hnegd : DifferentiableAt ℂ (fun y : ℂ => -psiA_st5 y) z := hd5.neg
  have hneg' : deriv (fun y : ℂ => -psiA_st5 y) z ≠ 0 := deriv_neg_ne_zero hd5 h5
  have hLd : DifferentiableAt ℂ (lune (36 / 5)) (-(psiA_st5 z)) :=
    (lune_differentiableOn_ball (36 / 5) (by norm_num)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; exact hw))
  have hL' : deriv (lune (36 / 5)) (-(psiA_st5 z)) ≠ 0 := hlune (36 / 5) (by norm_num) _ hw
  have hcomp' : deriv (lune (36 / 5) ∘ (fun y : ℂ => -psiA_st5 y)) z ≠ 0 :=
    deriv_comp_ne_zero (f := lune (36 / 5)) (g := fun y : ℂ => -psiA_st5 y) hLd hnegd hL' hneg'
  have hfin : deriv (fun y : ℂ => -(4 / 5) * lune (36 / 5) (-(psiA_st5 y))) z ≠ 0 := by
    have h := deriv_const_mul_ne_zero (c := -(4 / 5)) (f := lune (36 / 5) ∘ (fun y : ℂ => -psiA_st5 y))
      (by norm_num) hcomp'
    simpa only [Function.comp_def] using h
  have hpsiA : psiA = (fun y : ℂ => -(4 / 5) * lune (36 / 5) (-(psiA_st5 y))) := by
    funext y
    simp only [psiA, psiA_slitsA_eq]
  rw [hpsiA]
  exact hfin

theorem deriv_psiA_ne_zero :
    ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) 1 → deriv Submission.CDTPlan.psiA z ≠ 0 :=
  deriv_psiA_ne_zero_of deriv_slit_ne_zero deriv_lune_ne_zero

end

end Work.APull
