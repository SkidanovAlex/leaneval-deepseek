import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.psiA_facts
import Submission.Work.Haupt.haupt_facts

/-!
# Z0 — `φ_A` is analytic on `|z| < 500/491`

`φ_A = h ∘ ψ_A` where `h = hauptH` is holomorphic on the unit disc and
`ψ_A(z) = -(4/5)·lune(36/5, -w₄(z))` with `w₄ = slitsA` the composition of the four slit maps
and the four rotations (Calegari--Dimitrov--Tang, arXiv:2408.15403).

The first stage of `slitsA` sees `(491/500)·z`, which lies in the open unit disc exactly when
`|z| < 500/491`.  Every slit map and the lune map are holomorphic on the open unit disc and map
it strictly into itself (`Work.APsi.slit_facts`, `Work.APsi.lune_facts`), so the whole
composition is holomorphic on `|z| < 500/491` and takes values there of modulus `< 4/5 < 1`;
`hauptH` then composes with it.

The argument is the same as in `Work.APsi.psiA_facts`, but carried out on the larger disc
`ball 0 (500/491)` instead of the unit disc, and with holomorphy (`AnalyticOnNhd`) in place of
`DifferentiableOn`.
-/

namespace Work.ANum3

open Submission.CDTPlan Complex Metric

noncomputable section

/-! ## Elementary disc facts -/

/-- `z ∈ ball 0 (500/491) ↔ ‖z‖ < 500/491`. -/
lemma mem_ball_big {z : ℂ} : z ∈ ball 0 (500 / 491) ↔ ‖z‖ < 500 / 491 := by
  rw [mem_ball, dist_zero_right]

/-- The first stage sees `(491/500) z`, of modulus `< 1` on `ball 0 (500/491)`. -/
lemma norm_scale_lt_one {z : ℂ} (hz : z ∈ ball 0 (500 / 491)) :
    ‖(491 / 500 : ℂ) * z‖ < 1 := by
  rw [mem_ball_big] at hz
  have hc : ‖(491 / 500 : ℂ)‖ = (491 / 500 : ℝ) := by
    rw [show (491 / 500 : ℂ) = ((491 / 500 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  rw [norm_mul, hc]
  calc (491 / 500 : ℝ) * ‖z‖ < (491 / 500 : ℝ) * (500 / 491) :=
        mul_lt_mul_of_pos_left hz (by norm_num)
    _ = 1 := by norm_num

/-! ## Generic composition helpers

All the maps of the contour are built from three ingredients: multiplication by a constant, the
rotations `rot t` (of modulus one, hence preserving the open unit disc), and one slit map (or the
lune map, at the last step).  The next three lemmas package the corresponding composition step. -/

/-- Composition of a `DifferentiableOn` map with a slit map, the inner map taking its values in
the open unit disc. -/
lemma diffOn_slit_comp {s : Set ℂ} {f : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hf : DifferentiableOn ℂ f s) (hm : Set.MapsTo f s (ball 0 1)) :
    DifferentiableOn ℂ (fun z => slit r (f z)) s := by
  have h := (Work.APsi.differentiableOn_slit r hr0 hr1).comp hf hm
  simpa only [Function.comp_def] using h

/-- A slit map maps the values of `f` (lying in the open unit disc) strictly into the open unit
disc. -/
lemma mapsTo_slit_ball {s : Set ℂ} {f : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hm : Set.MapsTo f s (ball 0 1)) :
    Set.MapsTo (fun z => slit r (f z)) s (ball 0 1) := by
  intro z hz
  have h1 := hm hz
  rw [Work.APsi.psiA_mem_ball_one] at h1 ⊢
  exact (Work.APsi.slit_facts r hr0 hr1).2.2.2.2.1 _ h1

/-- Multiplication by a rotation preserves the open unit disc. -/
lemma mapsTo_rot_ball {s : Set ℂ} {f : ℂ → ℂ} (hm : Set.MapsTo f s (ball 0 1)) (t : ℝ) :
    Set.MapsTo (fun z => rot t * f z) s (ball 0 1) := by
  intro z hz
  have h1 := hm hz
  rw [Work.APsi.psiA_mem_ball_one] at h1 ⊢
  rw [norm_mul, Work.APsi.norm_rot, one_mul]
  exact h1

/-! ## The five stages of the contour, on `|z| < 500/491` -/

lemma st1_diff : DifferentiableOn ℂ Work.APsi.psiA_st1 (ball 0 (500 / 491)) := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => (491 / 500 : ℂ) * z) (ball 0 (500 / 491)) :=
    differentiableOn_id.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => (491 / 500 : ℂ) * z) (ball 0 (500 / 491)) (ball 0 1) :=
    fun z hz => by
      rw [Work.APsi.psiA_mem_ball_one]
      exact norm_scale_lt_one hz
  exact diffOn_slit_comp (by norm_num) (by norm_num) hf hm

lemma st1_maps : Set.MapsTo Work.APsi.psiA_st1 (ball 0 (500 / 491)) (ball 0 1) := by
  have hm : Set.MapsTo (fun z : ℂ => (491 / 500 : ℂ) * z) (ball 0 (500 / 491)) (ball 0 1) :=
    fun z hz => by
      rw [Work.APsi.psiA_mem_ball_one]
      exact norm_scale_lt_one hz
  exact mapsTo_slit_ball (by norm_num) (by norm_num) hm

lemma st2_diff : DifferentiableOn ℂ Work.APsi.psiA_st2 (ball 0 (500 / 491)) := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => rot (2033 / 25000) * Work.APsi.psiA_st1 z)
      (ball 0 (500 / 491)) :=
    st1_diff.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (2033 / 25000) * Work.APsi.psiA_st1 z)
      (ball 0 (500 / 491)) (ball 0 1) :=
    mapsTo_rot_ball st1_maps (2033 / 25000)
  exact diffOn_slit_comp (by norm_num) (by norm_num) hf hm

lemma st2_maps : Set.MapsTo Work.APsi.psiA_st2 (ball 0 (500 / 491)) (ball 0 1) :=
  mapsTo_slit_ball (by norm_num) (by norm_num) (mapsTo_rot_ball st1_maps (2033 / 25000))

lemma st3_diff : DifferentiableOn ℂ Work.APsi.psiA_st3 (ball 0 (500 / 491)) := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => rot (2927 / 25000) * Work.APsi.psiA_st2 z)
      (ball 0 (500 / 491)) :=
    st2_diff.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (2927 / 25000) * Work.APsi.psiA_st2 z)
      (ball 0 (500 / 491)) (ball 0 1) :=
    mapsTo_rot_ball st2_maps (2927 / 25000)
  exact diffOn_slit_comp (by norm_num) (by norm_num) hf hm

lemma st3_maps : Set.MapsTo Work.APsi.psiA_st3 (ball 0 (500 / 491)) (ball 0 1) :=
  mapsTo_slit_ball (by norm_num) (by norm_num) (mapsTo_rot_ball st2_maps (2927 / 25000))

lemma st4_diff : DifferentiableOn ℂ Work.APsi.psiA_st4 (ball 0 (500 / 491)) := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => rot (453 / 12500) * Work.APsi.psiA_st3 z)
      (ball 0 (500 / 491)) :=
    st3_diff.const_mul _
  have hm : Set.MapsTo (fun z : ℂ => rot (453 / 12500) * Work.APsi.psiA_st3 z)
      (ball 0 (500 / 491)) (ball 0 1) :=
    mapsTo_rot_ball st3_maps (453 / 12500)
  exact diffOn_slit_comp (by norm_num) (by norm_num) hf hm

lemma st4_maps : Set.MapsTo Work.APsi.psiA_st4 (ball 0 (500 / 491)) (ball 0 1) :=
  mapsTo_slit_ball (by norm_num) (by norm_num) (mapsTo_rot_ball st3_maps (453 / 12500))

lemma st5_diff : DifferentiableOn ℂ Work.APsi.psiA_st5 (ball 0 (500 / 491)) :=
  st4_diff.const_mul _

lemma st5_maps : Set.MapsTo Work.APsi.psiA_st5 (ball 0 (500 / 491)) (ball 0 1) :=
  mapsTo_rot_ball st4_maps (-1971 / 25000)

/-! ## `ψ_A` on `|z| < 500/491` -/

/-- Pointwise form of `ψ_A = -(4/5)·lune(36/5, -w₄)`. -/
lemma psiA_eq_lune_st5 (z : ℂ) :
    psiA z = -((4 : ℂ) / 5) * lune (36 / 5) (-(Work.APsi.psiA_st5 z)) := by
  simp only [psiA, Work.APsi.psiA_slitsA_eq]

lemma psiA_eq_lune_st5_fun :
    psiA = fun z => -((4 : ℂ) / 5) * lune (36 / 5) (-(Work.APsi.psiA_st5 z)) :=
  funext psiA_eq_lune_st5

lemma psiA_ext_diff : DifferentiableOn ℂ psiA (ball 0 (500 / 491)) := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => -(Work.APsi.psiA_st5 z)) (ball 0 (500 / 491)) :=
    st5_diff.neg
  have hm : Set.MapsTo (fun z : ℂ => -(Work.APsi.psiA_st5 z)) (ball 0 (500 / 491)) (ball 0 1) := by
    intro z hz
    have h1 := st5_maps hz
    rw [Work.APsi.psiA_mem_ball_one] at h1 ⊢
    simpa using h1
  have hl : DifferentiableOn ℂ (lune (36 / 5)) (ball 0 1) :=
    (Work.APsi.lune_facts (36 / 5) (by norm_num)).2.1
  have h : DifferentiableOn ℂ (fun z => lune (36 / 5) (-(Work.APsi.psiA_st5 z)))
      (ball 0 (500 / 491)) := by
    simpa only [Function.comp_def] using hl.comp hf hm
  rw [psiA_eq_lune_st5_fun]
  exact h.const_mul _

lemma psiA_ext_maps : Set.MapsTo psiA (ball 0 (500 / 491)) (ball 0 1) := by
  intro z hz
  rw [Work.APsi.psiA_mem_ball_one]
  have h5 : ‖Work.APsi.psiA_st5 z‖ < 1 := by
    have h1 := st5_maps hz
    rwa [Work.APsi.psiA_mem_ball_one] at h1
  have hl : ‖lune (36 / 5) (-(Work.APsi.psiA_st5 z))‖ < 1 :=
    (Work.APsi.lune_facts (36 / 5) (by norm_num)).2.2.2.2.1 _ (by simpa using h5)
  rw [psiA_eq_lune_st5]
  have hc : ‖(-((4 : ℂ) / 5))‖ = (4 / 5 : ℝ) := by
    rw [norm_neg, show ((4 : ℂ) / 5) = ((4 / 5 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  rw [norm_mul, hc]
  have h := mul_lt_mul_of_pos_left hl (by norm_num : (0 : ℝ) < 4 / 5)
  have h1 : (4 / 5 : ℝ) * 1 = 4 / 5 := by norm_num
  linarith

/-! ## The main statement -/

theorem phiA_analytic_ext : AnalyticOnNhd ℂ phiA (ball 0 (500 / 491)) := by
  have hpsiA : AnalyticOnNhd ℂ psiA (ball 0 (500 / 491)) :=
    psiA_ext_diff.analyticOnNhd isOpen_ball
  have hH : AnalyticOnNhd ℂ hauptH (ball 0 1) :=
    Work.Haupt.differentiableOn_hauptH.analyticOnNhd isOpen_ball
  have h := hH.comp hpsiA psiA_ext_maps
  have hphi : phiA = fun z => hauptH (psiA z) := rfl
  rw [hphi]
  simpa only [Function.comp_def] using h

end

end Work.ANum3
