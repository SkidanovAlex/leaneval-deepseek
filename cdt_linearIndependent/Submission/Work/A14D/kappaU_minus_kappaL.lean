import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.D_local_at_one_refined
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.kappaU_zero_imp_D_zero
import Submission.Work.A14D.slitDisk_continuation
import Submission.Work.A14D.log_sub_one_split
import Submission.Work.A14D.LogCoeff_unique

namespace Work.A14D

open Complex Metric
open scoped Topology

noncomputable section

/-- The strip `1/9 + ρ < re z < 1 - ρ`, `|im z| < ρ`. -/
def strip (ρ : ℝ) : Set ℂ := {z : ℂ | 1 / 9 + ρ < z.re ∧ z.re < 1 - ρ ∧ |z.im| < ρ}

lemma mem_strip {ρ : ℝ} {z : ℂ} :
    z ∈ strip ρ ↔ 1 / 9 + ρ < z.re ∧ z.re < 1 - ρ ∧ |z.im| < ρ := Iff.rfl

lemma isOpen_strip (ρ : ℝ) : IsOpen (strip ρ) := by
  have h1 : IsOpen {z : ℂ | (1 / 9 + ρ : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < (1 - ρ : ℝ)} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | -ρ < z.im ∧ z.im < ρ} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hset : strip ρ = {z : ℂ | (1 / 9 + ρ : ℝ) < z.re} ∩ {z : ℂ | z.re < (1 - ρ : ℝ)}
      ∩ {z : ℂ | -ρ < z.im ∧ z.im < ρ} := by
    ext z
    simp only [mem_strip, Set.mem_inter_iff, Set.mem_ofPred_eq, abs_lt]
    tauto
  rw [hset]
  exact (h1.inter h2).inter h3

lemma convex_strip (ρ : ℝ) : Convex ℝ (strip ρ) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  rw [mem_strip] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  rw [abs_lt] at hx3 hy3 ⊢
  obtain ⟨hx3a, hx3b⟩ := hx3
  obtain ⟨hy3a, hy3b⟩ := hy3
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;>
    nlinarith

lemma strip_subset_re_gt {ρ : ℝ} (hρ : 0 ≤ ρ) : strip ρ ⊆ {z : ℂ | (1 : ℝ) / 9 < z.re} := by
  intro z hz
  have h := (mem_strip.mp hz).1
  show (1 : ℝ) / 9 < z.re
  linarith

lemma strip_subset_re_lt_one {ρ : ℝ} (hρ : 0 ≤ ρ) : strip ρ ⊆ {z : ℂ | z.re < 1} := by
  intro z hz
  have h := (mem_strip.mp hz).2.1
  show z.re < 1
  linarith

lemma strip_subset_slitComp {ρ : ℝ} (hρ : 0 ≤ ρ) : strip ρ ⊆ slitComp := by
  intro z hz
  refine Or.inr ?_
  have h := strip_subset_re_gt hρ hz
  have h9 : ninth.re = (1 : ℝ) / 9 := by simp [ninth]
  rw [h9]
  exact h

lemma strip_PZ_ne_zero {ρ : ℝ} (hρ : 0 < ρ) : ∀ z ∈ strip ρ, PZ z ≠ 0 := by
  intro z hz h0
  obtain ⟨h1, h2, h3⟩ := mem_strip.mp hz
  simp only [PZ] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · have : z.re = 0 := by rw [h]; simp
      linarith
    · have hz1 : z = 1 := by linear_combination -h
      have : z.re = 1 := by rw [hz1]; simp
      linarith
  · have hz9 : z = (1 : ℂ) / 9 := by
      have h9 : 9 * z = 1 := by linear_combination -h
      rw [← h9]; ring
    have : z.re = 1 / 9 := by rw [hz9]; norm_num
    linarith

lemma strip_subset_ball_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ8 : ρ < 8 / 9) :
    strip ρ ⊆ Metric.ball 1 (8 / 9) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := mem_strip.mp hz
  rw [Metric.mem_ball, Complex.dist_eq]
  have him : z.im ^ 2 < ρ ^ 2 := by
    nlinarith [abs_nonneg z.im, sq_abs z.im, h3]
  have hre : (1 - z.re) ^ 2 < (8 / 9 - ρ) ^ 2 := by
    have hA : ρ < 1 - z.re := by linarith
    have hB : 1 - z.re < 8 / 9 - ρ := by linarith
    nlinarith
  have key : (8 / 9 - ρ) ^ 2 + ρ ^ 2 < (8 / 9) ^ 2 := by nlinarith
  have hsq : ‖z - 1‖ ^ 2 < (8 / 9) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    nlinarith
  nlinarith [norm_nonneg (z - 1), hsq]

lemma differentiableOn_log_one_sub_strip {ρ : ℝ} (hρ : 0 ≤ ρ) :
    DifferentiableOn ℂ (fun z : ℂ => Complex.log (1 - z)) (strip ρ) := by
  intro z hz
  have hmem : (1 : ℂ) - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    obtain ⟨h1, h2, h3⟩ := mem_strip.mp hz
    have h3' : ((1 : ℂ) - z).re = 1 - z.re := by simp
    rw [h3']
    show (0 : ℝ) < 1 - z.re
    linarith
  exact ((Complex.differentiableAt_log hmem).comp z
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)).differentiableWithinAt

/-- Convexity of the upper half-plane in `ℂ`. -/
lemma convex_im_pos : Convex ℝ {z : ℂ | 0 < z.im} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx hy ⊢
  nlinarith

/-- Convexity of the lower half-plane in `ℂ`. -/
lemma convex_im_neg : Convex ℝ {z : ℂ | z.im < 0} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx hy ⊢
  nlinarith

lemma norm_le_abs_re_add_abs_im (w : ℂ) : ‖w‖ ≤ |w.re| + |w.im| := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  calc ‖w‖ = ‖(w.re : ℂ) + (w.im : ℂ) * I‖ := by conv_lhs => rw [hw]
    _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * I‖ := norm_add_le _ _
    _ = |w.re| + |w.im| := by simp

lemma LogCoeff_mono {y9 : ℂ → ℂ} {δ : ℝ} {V W : Set ℂ} {f : ℂ → ℂ} {κ : ℂ}
    (h : LogCoeff y9 δ V f κ) (hWV : W ⊆ V) : LogCoeff y9 δ W f κ := by
  obtain ⟨hh, hd, heq⟩ := h
  exact ⟨hh, hd, fun z hz => heq z (hWV hz)⟩

lemma LogCoeff_smul {y9 : ℂ → ℂ} {δ : ℝ} {V : Set ℂ} {f : ℂ → ℂ} {κ cst : ℂ}
    (h : LogCoeff y9 δ V f κ) : LogCoeff y9 δ V (fun z => cst * f z) (cst * κ) := by
  obtain ⟨hh, hd, heq⟩ := h
  refine ⟨fun z => cst * hh z, hd.const_mul cst, fun z hz => ?_⟩
  show cst * f z = cst * κ * y9 z * Complex.log (z - ninth) + cst * hh z
  rw [heq z hz]; ring

lemma norm_ofReal_add_ofReal_mul_I (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * I‖ ≤ |a| + |b| := by
  calc ‖(a : ℂ) + (b : ℂ) * I‖ ≤ ‖(a : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ = |a| + |b| := by simp [Complex.norm_real]

lemma norm_ofReal_sub_ofReal_mul_I (a b : ℝ) : ‖(a : ℂ) - (b : ℂ) * I‖ ≤ |a| + |b| := by
  calc ‖(a : ℂ) - (b : ℂ) * I‖ ≤ ‖(a : ℂ)‖ + ‖(b : ℂ) * I‖ := by
        simpa using norm_sub_le (a : ℂ) ((b : ℂ) * I)
    _ = |a| + |b| := by simp [Complex.norm_real]

lemma norm_neg_ofReal_add_ofReal_mul_I (a b : ℝ) :
    ‖-((a : ℂ)) + (b : ℂ) * I‖ ≤ |a| + |b| := by
  calc ‖-((a : ℂ)) + (b : ℂ) * I‖ ≤ ‖-((a : ℂ))‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ = |a| + |b| := by simp [Complex.norm_real]

lemma norm_neg_ofReal_sub_ofReal_mul_I (a b : ℝ) :
    ‖-((a : ℂ)) - (b : ℂ) * I‖ ≤ |a| + |b| := by
  calc ‖-((a : ℂ)) - (b : ℂ) * I‖ ≤ ‖-((a : ℂ))‖ + ‖(b : ℂ) * I‖ := by
        simpa using norm_sub_le (-((a : ℂ))) ((b : ℂ) * I)
    _ = |a| + |b| := by simp [Complex.norm_real]

theorem kappaU_minus_kappaL (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU Work.A14D.SU ∧
      (∀ z ∈ Work.A14D.SU, Work.A14D.LZ HU z = Work.A14D.rhsZ b c z) ∧
      ∀ z ∈ Work.A14D.SU ∩ Metric.ball 0 1, HU z = Work.A14D.Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL Work.A14D.SL ∧
      (∀ z ∈ Work.A14D.SL, Work.A14D.LZ HL z = Work.A14D.rhsZ b c z) ∧
      ∀ z ∈ Work.A14D.SL ∩ Metric.ball 0 1, HL z = Work.A14D.Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Work.A14D.Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Work.A14D.Om1)
    (hDL : ∀ z ∈ Work.A14D.Om1, Work.A14D.LZ D z = 0)
    (hDj : ∀ z ∈ Work.A14D.SU ∩ Work.A14D.SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : Work.A14D.LogCoeff y9 δ (Work.A14D.halfU δ) D κU)
    (hL : Work.A14D.LogCoeff y9 δ (Work.A14D.halfL δ) D κL) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      Work.A14D.LogCoeff y9 δ (Metric.ball Work.A14D.ninth δ ∩ Metric.ball 1 (8 / 9))
        Work.A14D.uh lam ∧
      κU - κL = -(Real.pi ^ 2 * (c : ℂ) / 2) * lam := by
  obtain ⟨lam0, hlam0, hlam0ne⟩ := uh_logCoeff_lens (y9 := y9) (δ := δ) hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  obtain ⟨hud, hu1, huode⟩ := uh_ode
  obtain ⟨δ₁, hδ₁pos, hδ₁89, A, hAd, hAloc⟩ :=
    D_local_at_one_refined a b c h HU HL hHU hHL D hD hDL hDj
  set ρ : ℝ := min δ δ₁ / 8 with hρdef
  have hminpos : 0 < min δ δ₁ := lt_min hδpos hδ₁pos
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρleδ : ρ ≤ δ / 8 := by rw [hρdef]; linarith [min_le_left δ δ₁]
  have hρleδ₁ : ρ ≤ δ₁ / 8 := by rw [hρdef]; linarith [min_le_right δ δ₁]
  have hρδ : ρ < δ := by linarith
  have hρδ₁ : ρ < δ₁ := by linarith
  have hρ8 : ρ < 8 / 9 := by linarith
  have hρsmall : ρ ≤ 1 / 160 := by linarith
  -- ## the strip and the distinguished points
  set zU : ℂ := ninth + ((2 * ρ : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I with hzUdef
  set zD : ℂ := ninth + ((2 * ρ : ℝ) : ℂ) - ((ρ / 2 : ℝ) : ℂ) * I with hzDdef
  set wU : ℂ := 1 - ((3 * ρ : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I with hwUdef
  set wD : ℂ := 1 - ((3 * ρ : ℝ) : ℂ) - ((ρ / 2 : ℝ) : ℂ) * I with hwDdef
  have hzU_re : zU.re = 1 / 9 + 2 * ρ := by rw [hzUdef]; simp [ninth]
  have hzU_im : zU.im = ρ / 2 := by rw [hzUdef]; simp [ninth]
  have hzD_re : zD.re = 1 / 9 + 2 * ρ := by rw [hzDdef]; simp [ninth]
  have hzD_im : zD.im = -(ρ / 2) := by rw [hzDdef]; simp [ninth]
  have hwU_re : wU.re = 1 - 3 * ρ := by rw [hwUdef]; simp
  have hwU_im : wU.im = ρ / 2 := by rw [hwUdef]; simp
  have hwD_re : wD.re = 1 - 3 * ρ := by rw [hwDdef]; simp
  have hwD_im : wD.im = -(ρ / 2) := by rw [hwDdef]; simp
  have hzU_impos : 0 < zU.im := by rw [hzU_im]; linarith
  have hzD_imneg : zD.im < 0 := by rw [hzD_im]; linarith
  have hwU_impos : 0 < wU.im := by rw [hwU_im]; linarith
  have hwD_imneg : wD.im < 0 := by rw [hwD_im]; linarith
  have hzU_strip : zU ∈ strip ρ := by
    rw [mem_strip]
    refine ⟨?_, ?_, ?_⟩
    · rw [hzU_re]; linarith
    · rw [hzU_re]; linarith
    · rw [hzU_im, abs_of_pos (by linarith : (0:ℝ) < ρ / 2)]; linarith
  have hzD_strip : zD ∈ strip ρ := by
    rw [mem_strip]
    refine ⟨?_, ?_, ?_⟩
    · rw [hzD_re]; linarith
    · rw [hzD_re]; linarith
    · rw [hzD_im, abs_neg, abs_of_pos (by linarith : (0:ℝ) < ρ / 2)]; linarith
  have hwU_strip : wU ∈ strip ρ := by
    rw [mem_strip]
    refine ⟨?_, ?_, ?_⟩
    · rw [hwU_re]; linarith
    · rw [hwU_re]; linarith
    · rw [hwU_im, abs_of_pos (by linarith : (0:ℝ) < ρ / 2)]; linarith
  have hwD_strip : wD ∈ strip ρ := by
    rw [mem_strip]
    refine ⟨?_, ?_, ?_⟩
    · rw [hwD_re]; linarith
    · rw [hwD_re]; linarith
    · rw [hwD_im, abs_neg, abs_of_pos (by linarith : (0:ℝ) < ρ / 2)]; linarith
  have hzU_ball : zU ∈ Metric.ball ninth δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h1 : zU - ninth = ((2 * ρ : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I := by rw [hzUdef]; ring
    have h2 := norm_ofReal_add_ofReal_mul_I (2 * ρ) (ρ / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ρ),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ / 2)] at h2
    rw [h1]
    linarith
  have hzD_ball : zD ∈ Metric.ball ninth δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h1 : zD - ninth = ((2 * ρ : ℝ) : ℂ) - ((ρ / 2 : ℝ) : ℂ) * I := by rw [hzDdef]; ring
    have h2 := norm_ofReal_sub_ofReal_mul_I (2 * ρ) (ρ / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ρ),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ / 2)] at h2
    rw [h1]
    linarith
  have hwU_ball : wU ∈ Metric.ball 1 δ₁ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h1 : wU - 1 = -(((3 * ρ : ℝ)) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I := by rw [hwUdef]; ring
    have h2 := norm_neg_ofReal_add_ofReal_mul_I (3 * ρ) (ρ / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 3 * ρ),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ / 2)] at h2
    rw [h1]
    linarith
  have hwD_ball : wD ∈ Metric.ball 1 δ₁ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h1 : wD - 1 = -(((3 * ρ : ℝ)) : ℂ) - ((ρ / 2 : ℝ) : ℂ) * I := by rw [hwDdef]; ring
    have h2 := norm_neg_ofReal_sub_ofReal_mul_I (3 * ρ) (ρ / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 3 * ρ),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ / 2)] at h2
    rw [h1]
    linarith
  -- ## the two extensions of D across the real axis
  have hSUp_sol : IsSolLZ D (strip ρ ∩ {z : ℂ | 0 < z.im}) :=
    ⟨hD.mono (fun z hz => Or.inl (ne_of_gt hz.2)), fun z hz => hDL z (Or.inl (ne_of_gt hz.2))⟩
  obtain ⟨Dup, hDupSol, hDupEq⟩ := extend_sol_LZ
    ((isOpen_strip ρ).inter (isOpen_lt continuous_const Complex.continuous_im))
    ((convex_strip ρ).inter convex_im_pos) (isOpen_strip ρ) (convex_strip ρ)
    (fun z hz => strip_PZ_ne_zero hρpos z (hz.elim (fun h => h.1) (fun h => h)))
    hSUp_sol ⟨zU, ⟨hzU_strip, hzU_impos⟩, hzU_strip⟩
  have hSDn_sol : IsSolLZ D (strip ρ ∩ {z : ℂ | z.im < 0}) :=
    ⟨hD.mono (fun z hz => Or.inl (ne_of_lt hz.2)), fun z hz => hDL z (Or.inl (ne_of_lt hz.2))⟩
  obtain ⟨Dlow, hDlowSol, hDlowEq⟩ := extend_sol_LZ
    ((isOpen_strip ρ).inter (isOpen_lt Complex.continuous_im continuous_const))
    ((convex_strip ρ).inter convex_im_neg) (isOpen_strip ρ) (convex_strip ρ)
    (fun z hz => strip_PZ_ne_zero hρpos z (hz.elim (fun h => h.1) (fun h => h)))
    hSDn_sol ⟨zD, ⟨hzD_strip, hzD_imneg⟩, hzD_strip⟩
  set J : ℂ → ℂ := fun z => Dup z - Dlow z with hJdef
  have hJd : DifferentiableOn ℂ J (strip ρ) := hDupSol.1.sub hDlowSol.1
  -- ## the equations `D = A + K·u_h·log(z-1)` split by the logarithmic branch
  set Lf : ℂ → ℂ := fun z => Complex.log (1 - z) with hLfdef
  set KK : ℂ := Real.pi * Complex.I * (c : ℂ) / 4 with hKKdef
  set EE : ℂ → ℂ := fun z => -(Real.pi ^ 2 * (c : ℂ) / 4) * uh z with hEEdef
  have hLfd : DifferentiableOn ℂ Lf (strip ρ) := differentiableOn_log_one_sub_strip hρpos.le
  have huhd : DifferentiableOn ℂ uh (strip ρ) := hud.mono (strip_subset_ball_one hρpos.le hρ8)
  have hAd' : DifferentiableOn ℂ A (strip ρ ∩ Metric.ball 1 δ₁) := hAd.mono Set.inter_subset_right
  have huhd' : DifferentiableOn ℂ uh (strip ρ ∩ Metric.ball 1 δ₁) :=
    hud.mono (Set.inter_subset_right.trans (Metric.ball_subset_ball hδ₁89))
  have hLfd' : DifferentiableOn ℂ Lf (strip ρ ∩ Metric.ball 1 δ₁) := hLfd.mono Set.inter_subset_left
  have hEEd' : DifferentiableOn ℂ EE (strip ρ ∩ Metric.ball 1 δ₁) :=
    (differentiableOn_const _).mul huhd'
  -- Ξ₁
  set X1 : ℂ → ℂ := fun z => (Dup z - A z) - KK * uh z * Lf z with hX1def
  have hX1d : DifferentiableOn ℂ X1 (strip ρ ∩ Metric.ball 1 δ₁) :=
    ((hDupSol.1.mono Set.inter_subset_left).sub hAd').sub
      (((differentiableOn_const KK).mul huhd').mul hLfd')
  have hX1val : ∀ z ∈ strip ρ ∩ Metric.ball 1 δ₁, 0 < z.im → X1 z = EE z := by
    intro z hz hzim
    have hz1 : z ∈ strip ρ := hz.1
    have hz2 : z ∈ Metric.ball 1 δ₁ := hz.2
    have hDupz : Dup z = D z := hDupEq ⟨⟨hz1, hzim⟩, hz1⟩
    have hDz := hAloc z ⟨hz2, Or.inl (ne_of_gt hzim)⟩
    have hlog := (log_sub_one_split z).1 hzim
    have key : (KK * uh z) * (Complex.log (1 - z) + Real.pi * I) - (KK * uh z) * Complex.log (1 - z)
        = -(Real.pi ^ 2 * (c : ℂ) / 4) * uh z := by
      rw [hKKdef]
      have h : ((Real.pi : ℂ) * I) * ((Real.pi : ℂ) * I) = -((Real.pi : ℂ) ^ 2) := by
        rw [show ((Real.pi : ℂ) * I) * ((Real.pi : ℂ) * I) = ((Real.pi : ℂ) ^ 2) * (I * I) by ring,
          Complex.I_mul_I]
        ring
      linear_combination ((c : ℂ) * uh z / 4) * h
    have key1 : X1 z = (KK * uh z) * (Complex.log (1 - z) + Real.pi * I)
        - (KK * uh z) * Complex.log (1 - z) := by
      simp only [hX1def, hDupz, hDz, hlog, hLfdef]
      ring
    rw [key1, key, hEEdef]
  have hX1eq : ∀ z ∈ strip ρ ∩ Metric.ball 1 δ₁, X1 z = EE z := by
    have hopen : IsOpen (strip ρ ∩ Metric.ball 1 δ₁) := (isOpen_strip ρ).inter Metric.isOpen_ball
    have hpre : IsPreconnected (strip ρ ∩ Metric.ball 1 δ₁) :=
      ((convex_strip ρ).inter (convex_ball (1 : ℂ) δ₁)).isPreconnected
    have hz₀ : wU ∈ strip ρ ∩ Metric.ball 1 δ₁ := ⟨hwU_strip, hwU_ball⟩
    have hev : X1 =ᶠ[𝓝 wU] EE := by
      filter_upwards [hopen.inter (isOpen_lt continuous_const Complex.continuous_im) |>.mem_nhds
        ⟨hz₀, hwU_impos⟩] with z hz
      exact hX1val z hz.1 hz.2
    intro z hz
    exact (hX1d.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
      (hEEd'.analyticOnNhd hopen) hpre hz₀ hev hz
  -- Ξ₂
  set X2 : ℂ → ℂ := fun z => (Dlow z - A z) - KK * uh z * Lf z with hX2def
  have hX2d : DifferentiableOn ℂ X2 (strip ρ ∩ Metric.ball 1 δ₁) :=
    ((hDlowSol.1.mono Set.inter_subset_left).sub hAd').sub
      (((differentiableOn_const KK).mul huhd').mul hLfd')
  have hX2val : ∀ z ∈ strip ρ ∩ Metric.ball 1 δ₁, z.im < 0 → X2 z = -EE z := by
    intro z hz hzim
    have hz1 : z ∈ strip ρ := hz.1
    have hz2 : z ∈ Metric.ball 1 δ₁ := hz.2
    have hDlowz : Dlow z = D z := hDlowEq ⟨⟨hz1, hzim⟩, hz1⟩
    have hDz := hAloc z ⟨hz2, Or.inl (ne_of_lt hzim)⟩
    have hlog := (log_sub_one_split z).2 hzim
    have key : (KK * uh z) * (Complex.log (1 - z) - Real.pi * I) - (KK * uh z) * Complex.log (1 - z)
        = (Real.pi ^ 2 * (c : ℂ) / 4) * uh z := by
      rw [hKKdef]
      have h : ((Real.pi : ℂ) * I) * ((Real.pi : ℂ) * I) = -((Real.pi : ℂ) ^ 2) := by
        rw [show ((Real.pi : ℂ) * I) * ((Real.pi : ℂ) * I) = ((Real.pi : ℂ) ^ 2) * (I * I) by ring,
          Complex.I_mul_I]
        ring
      linear_combination (-((c : ℂ) * uh z / 4)) * h
    have key1 : X2 z = (KK * uh z) * (Complex.log (1 - z) - Real.pi * I)
        - (KK * uh z) * Complex.log (1 - z) := by
      simp only [hX2def, hDlowz, hDz, hlog, hLfdef]
      ring
    rw [key1, key]
    simp only [hEEdef]
    ring
  have hX2eq : ∀ z ∈ strip ρ ∩ Metric.ball 1 δ₁, X2 z = -EE z := by
    have hopen : IsOpen (strip ρ ∩ Metric.ball 1 δ₁) := (isOpen_strip ρ).inter Metric.isOpen_ball
    have hpre : IsPreconnected (strip ρ ∩ Metric.ball 1 δ₁) :=
      ((convex_strip ρ).inter (convex_ball (1 : ℂ) δ₁)).isPreconnected
    have hz₀ : wD ∈ strip ρ ∩ Metric.ball 1 δ₁ := ⟨hwD_strip, hwD_ball⟩
    have hev : X2 =ᶠ[𝓝 wD] (-EE) := by
      filter_upwards [hopen.inter (isOpen_lt Complex.continuous_im continuous_const) |>.mem_nhds
        ⟨hz₀, hwD_imneg⟩] with z hz
      exact hX2val z hz.1 hz.2
    intro z hz
    exact (hX2d.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
      (hEEd'.neg.analyticOnNhd hopen) hpre hz₀ hev hz
  -- the jump
  have hJval : ∀ z ∈ strip ρ ∩ Metric.ball 1 δ₁, J z = -(Real.pi ^ 2 * (c : ℂ) / 2) * uh z := by
    intro z hz
    have h1 := hX1eq z hz
    have h2 := hX2eq z hz
    have e1 : Dup z = A z + KK * uh z * Lf z + X1 z := by rw [hX1def]; ring
    have e2 : Dlow z = A z + KK * uh z * Lf z + X2 z := by rw [hX2def]; ring
    rw [hJdef]
    simp only []
    rw [e1, e2, h1, h2, hEEdef]
    ring
  have hJuh : ∀ z ∈ strip ρ, J z = -(Real.pi ^ 2 * (c : ℂ) / 2) * uh z := by
    have hopen : IsOpen (strip ρ) := isOpen_strip ρ
    have hpre : IsPreconnected (strip ρ) := (convex_strip ρ).isPreconnected
    have hGGd : DifferentiableOn ℂ (fun z => J z + (Real.pi ^ 2 * (c : ℂ) / 2) * uh z) (strip ρ) :=
      hJd.add ((differentiableOn_const (Real.pi ^ 2 * (c : ℂ) / 2)).mul huhd)
    have hz₀ : wU ∈ strip ρ := hwU_strip
    have hev : (fun z => J z + (Real.pi ^ 2 * (c : ℂ) / 2) * uh z) =ᶠ[𝓝 wU] 0 := by
      filter_upwards [(hopen.inter Metric.isOpen_ball).mem_nhds ⟨hwU_strip, hwU_ball⟩] with z hz
      have h := hJval z hz
      simp only [Pi.zero_apply]
      rw [h]
      ring
    intro z hz
    have h := hGGd.analyticOnNhd hopen |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hpre hz₀ hev hz
    have h' : J z + (Real.pi ^ 2 * (c : ℂ) / 2) * uh z = 0 := h
    linear_combination h'
  -- ## log coefficients on `V = strip ρ ∩ ball (1/9) δ`
  set V : Set ℂ := strip ρ ∩ Metric.ball ninth δ with hVdef
  have hVo : IsOpen V := (isOpen_strip ρ).inter Metric.isOpen_ball
  have hVc : Convex ℝ V := (convex_strip ρ).inter (convex_ball ninth δ)
  have hVsub : V ⊆ Metric.ball ninth δ := Set.inter_subset_right
  have hVslit : ∀ z ∈ V, z - ninth ∈ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    left
    have hh : (1 : ℝ) / 9 < z.re := strip_subset_re_gt hρpos.le hz.1
    have h9 : (z - ninth).re = z.re - 1 / 9 := by simp [ninth]
    rw [h9]; linarith
  have hVne : V.Nonempty := ⟨zU, hzU_strip, hzU_ball⟩
  have hVlog : DifferentiableOn ℂ (fun z : ℂ => Complex.log (z - ninth)) V := by
    intro z hz
    exact ((Complex.differentiableAt_log (hVslit z hz)).comp z
      (differentiableAt_id.sub_const ninth)).differentiableWithinAt
  obtain ⟨hUfun, hUfund, hUeq⟩ := hU
  obtain ⟨hLfun, hLfund, hLeq⟩ := hL
  have hDupV : ∀ z ∈ V, Dup z = κU * y9 z * Complex.log (z - ninth) + hUfun z := by
    have hAnal1 : AnalyticOnNhd ℂ Dup V := (hDupSol.1.mono Set.inter_subset_left).analyticOnNhd hVo
    have hAnal2 : AnalyticOnNhd ℂ (fun z => κU * y9 z * Complex.log (z - ninth) + hUfun z) V :=
      (((differentiableOn_const κU).mul (hy9d.mono hVsub)).mul hVlog).add
        (hUfund.mono hVsub) |>.analyticOnNhd hVo
    have hz₀ : zU ∈ V := ⟨hzU_strip, hzU_ball⟩
    have hev : Dup =ᶠ[𝓝 zU] (fun z => κU * y9 z * Complex.log (z - ninth) + hUfun z) := by
      filter_upwards [(hVo.inter (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds
        ⟨hz₀, hzU_impos⟩] with z hz
      have hDupz : Dup z = D z := hDupEq ⟨⟨hz.1.1, hz.2⟩, hz.1.1⟩
      rw [hDupz]
      exact hUeq z ⟨hz.1.2, hz.2⟩
    intro z hz
    exact hAnal1.eqOn_of_preconnected_of_eventuallyEq hAnal2 hVc.isPreconnected hz₀ hev hz
  have hDlowV : ∀ z ∈ V, Dlow z = κL * y9 z * Complex.log (z - ninth) + hLfun z := by
    have hAnal1 : AnalyticOnNhd ℂ Dlow V := (hDlowSol.1.mono Set.inter_subset_left).analyticOnNhd hVo
    have hAnal2 : AnalyticOnNhd ℂ (fun z => κL * y9 z * Complex.log (z - ninth) + hLfun z) V :=
      (((differentiableOn_const κL).mul (hy9d.mono hVsub)).mul hVlog).add
        (hLfund.mono hVsub) |>.analyticOnNhd hVo
    have hz₀ : zD ∈ V := ⟨hzD_strip, hzD_ball⟩
    have hev : Dlow =ᶠ[𝓝 zD] (fun z => κL * y9 z * Complex.log (z - ninth) + hLfun z) := by
      filter_upwards [(hVo.inter (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds
        ⟨hz₀, hzD_imneg⟩] with z hz
      have hDlowz : Dlow z = D z := hDlowEq ⟨⟨hz.1.1, hz.2⟩, hz.1.1⟩
      rw [hDlowz]
      exact hLeq z ⟨hz.1.2, hz.2⟩
    intro z hz
    exact hAnal1.eqOn_of_preconnected_of_eventuallyEq hAnal2 hVc.isPreconnected hz₀ hev hz
  have hLogCoeffV : LogCoeff y9 δ V J (κU - κL) :=
    ⟨fun z => hUfun z - hLfun z, hUfund.sub hLfund, fun z hz => by
      rw [hJdef]
      simp only []
      rw [hDupV z hz, hDlowV z hz]
      ring⟩
  have hVlens : V ⊆ Metric.ball ninth δ ∩ Metric.ball 1 (8 / 9) :=
    fun z hz => ⟨hVsub hz, strip_subset_ball_one hρpos.le hρ8 hz.1⟩
  have hLogCoeffV' : LogCoeff y9 δ V J (-(Real.pi ^ 2 * (c : ℂ) / 2) * lam0) := by
    obtain ⟨hlf, hlfd, hlfeq⟩ := hlam0
    refine ⟨fun z => -(Real.pi ^ 2 * (c : ℂ) / 2) * hlf z,
      (hlfd.const_mul _), fun z hz => ?_⟩
    show J z = (-(Real.pi ^ 2 * (c : ℂ) / 2) * lam0) * y9 z * Complex.log (z - ninth)
      + -(Real.pi ^ 2 * (c : ℂ) / 2) * hlf z
    rw [hJuh z hz.1, hlfeq z (hVlens hz)]
    ring
  have huniq := LogCoeff_unique hy9d hy9ne hVo hVne hVsub hVslit hVo hVne hVsub hVslit
    (hVne.mono (fun z hz => ⟨hz, hz⟩)) hLogCoeffV hLogCoeffV'
  exact ⟨lam0, hlam0ne, hlam0, huniq⟩

end

end Work.A14D
