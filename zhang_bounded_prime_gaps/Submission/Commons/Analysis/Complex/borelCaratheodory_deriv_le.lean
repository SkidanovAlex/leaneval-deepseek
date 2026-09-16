import Mathlib
import Submission.Commons.Analysis.Complex.schwarzPick_norm_deriv

noncomputable section
open Complex Metric Set Filter Function
open scoped Topology ComplexConjugate

namespace Commons.Analysis.Complex

private lemma bc_unit_bound {B g z : ℝ} (hB : 0 ≤ B) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (_hg0 : 0 ≤ g) (hgz : g ≤ z) :
    (2 * B / (1 - g) ^ 2) * ((1 - g ^ 2) / (1 - z ^ 2)) ≤ 2 * B / (1 - z) ^ 2 := by
  have hz1' : 0 < 1 - z := sub_pos.mpr hz1
  have hg1 : g < 1 := lt_of_le_of_lt hgz hz1
  have hg1' : 0 < 1 - g := sub_pos.mpr hg1
  have h1mz2 : 0 < (1 - z) ^ 2 := sq_pos_of_pos hz1'
  have h1mzsq : 0 < 1 - z ^ 2 := by
    nlinarith [mul_self_lt_mul_self hz0 hz1]
  have h1mg : 1 - g ≠ 0 := (ne_of_gt hg1')
  have h1mzsqn : 1 - z ^ 2 ≠ 0 := (ne_of_gt h1mzsq)
  have hratio : (1 + g) / ((1 - g) * (1 - z ^ 2)) ≤ 1 / (1 - z) ^ 2 := by
    rw [le_div_iff₀ h1mz2]
    field_simp [h1mg, h1mzsqn]
    nlinarith [hgz, hz0]
  calc
    (2 * B / (1 - g) ^ 2) * ((1 - g ^ 2) / (1 - z ^ 2))
        = 2 * B * (1 + g) / ((1 - g) * (1 - z ^ 2)) := by
            field_simp [h1mg, h1mzsqn]
            ring
    _ = 2 * B * ((1 + g) / ((1 - g) * (1 - z ^ 2))) := by ring
    _ ≤ 2 * B * (1 / (1 - z) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hB)
    _ = 2 * B / (1 - z) ^ 2 := by ring

private lemma norm_le_norm_two_mul_sub_of_re_le {B : ℝ} (hB : 0 < B) {v : ℂ} (hv : v.re ≤ B) :
    ‖v‖ ≤ ‖(2 * B : ℂ) - v‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  have h1 : ‖v‖ ^ 2 = v.re * v.re + v.im * v.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖(2 * B : ℂ) - v‖ ^ 2 = (2 * B - v.re) * (2 * B - v.re) + v.im * v.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [h1, h2]
  nlinarith [hv, hB]

private lemma halfPlane_mapsTo_closedUnitBall {B : ℝ} (hB : 0 < B) :
    Set.MapsTo (fun v : ℂ => v / ((2 * B : ℂ) - v)) {v | v.re ≤ B}
      (Metric.closedBall (0 : ℂ) 1) := by
  intro v hv
  rw [mem_closedBall_zero_iff]
  have hnn := norm_le_norm_two_mul_sub_of_re_le hB hv
  calc
    ‖v / ((2 * B : ℂ) - v)‖ = ‖v‖ / ‖(2 * B : ℂ) - v‖ := by rw [norm_div]
    _ ≤ 1 := div_le_one_of_le₀ hnn (norm_nonneg _)

private lemma phi_hasDerivAt {B : ℝ} {w : ℂ} (hw : (1 : ℂ) + w ≠ 0) :
    HasDerivAt (fun v : ℂ => (2 * B : ℂ) * v / ((1 : ℂ) + v))
      ((2 * B : ℂ) / ((1 : ℂ) + w) ^ 2) w := by
  have hnum : HasDerivAt (fun v : ℂ => (2 * B : ℂ) * v) (2 * B : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (2 * (B : ℂ)))
  have hden0 : HasDerivAt (fun v : ℂ => (1 : ℂ) + v) (1 : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_add (1 : ℂ))
  have h := hnum.div hden0 hw
  exact h.congr_deriv (by field_simp [hw]; ring)

private lemma norm_two_mul_of_pos {B : ℝ} (hB : 0 < B) : ‖(2 * B : ℂ)‖ = 2 * B := by
  rw [norm_mul]
  rw [Complex.norm_ofNat]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]

private lemma norm_div_ofReal {r : ℝ} (hr : 0 ≤ r) (z : ℂ) : ‖z / (r : ℂ)‖ = ‖z‖ / r := by
  rw [norm_div, Complex.norm_of_nonneg hr]

private theorem unit_deriv_le_of_re_le {f : ℂ → ℂ} {B : ℝ} (hB : 0 < B)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hf0 : f 0 = 0)
    (hRe : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → (f w).re ≤ B) :
    ∀ z : ℂ, ‖z‖ < 1 → ‖deriv f z‖ ≤ 2 * B / (1 - ‖z‖) ^ 2 := by
  intro z hz
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz
  let G : ℂ → ℂ := f / (fun u : ℂ => (2 * B : ℂ) - f u)
  let φ : ℂ → ℂ := fun v => (2 * B : ℂ) * v / ((1 : ℂ) + v)
  have hden_ne : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) 1 → (2 * B : ℂ) - f u ≠ 0 := by
    intro u hu h
    have hfu : f u = (2 * B : ℂ) := (sub_eq_zero.mp h).symm
    have hre_u : (f u).re ≤ B := hRe u hu
    rw [hfu] at hre_u
    simp at hre_u
    linarith
  have hG : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1) := by
    intro u hu
    have hfuAt : HasDerivAt f (deriv f u) u :=
      (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hu)).hasDerivAt
    have hdenAt : HasDerivAt (fun x : ℂ => (2 * B : ℂ) - f x) (-(deriv f u)) u := by
      simpa using (hfuAt.const_sub (2 * (B : ℂ)))
    have hq := hfuAt.div hdenAt (hden_ne u hu)
    exact hq.differentiableAt.differentiableWithinAt
  have hGball : Set.MapsTo G (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro u hu
    have h := (halfPlane_mapsTo_closedUnitBall hB) (hRe u hu)
    simpa [G, mem_closedBall_zero_iff] using h
  have hG0 : G 0 = 0 := by simp [G, hf0]
  have hGzle : ‖G z‖ ≤ ‖z‖ := by
    exact Complex.norm_le_norm_of_mapsTo_ball (f := G) (R := 1) hG hGball hG0 hz
  have hGzlt : ‖G z‖ < 1 := lt_of_le_of_lt hGzle hz
  have hSP := schwarzPick_norm_deriv (g := G) (z := z) hG hGball hzmem hGzlt
  have h_eq_on : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) 1 → f u = φ (G u) := by
    intro u hu
    have hfu2 : f u ≠ (2 * B : ℂ) := by
      intro h; have : (2 * B : ℂ).re ≤ B := by simpa [h] using hRe u hu
      simp at this; linarith
    have hBcn : (B : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
    dsimp [φ, G]
    field_simp [hfu2, hBcn]
    ring
  have hEqNear : f =ᶠ[𝓝 z] (φ ∘ G) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with u hu
    exact h_eq_on u hu
  have hGz_ne : (1 : ℂ) + G z ≠ 0 := by
    intro h
    have hlo : (1 : ℝ) - ‖G z‖ ≤ ‖(1 : ℂ) + G z‖ := by
      simpa using (norm_sub_le_norm_add (1 : ℂ) (G z))
    have hpos : 0 < ‖(1 : ℂ) + G z‖ := lt_of_lt_of_le (sub_pos.mpr hGzlt) hlo
    rw [h] at hpos
    simp at hpos
  have hφder : HasDerivAt φ ((2 * B : ℂ) / (1 + G z) ^ 2) (G z) := by
    simpa [φ] using phi_hasDerivAt (B := B) (w := G z) hGz_ne
  have hGder : HasDerivAt G (deriv G z) z :=
    hG.hasDerivAt (Metric.isOpen_ball.mem_nhds hzmem)
  have hφGcomp : HasDerivAt (φ ∘ G) (((2 * B : ℂ) / (1 + G z) ^ 2) * deriv G z) z :=
    hφder.comp z hGder
  have hfder : HasDerivAt f (((2 * B : ℂ) / (1 + G z) ^ 2) * deriv G z) z :=
    hφGcomp.congr_of_eventuallyEq hEqNear
  have hder_eq : deriv f z = ((2 * B : ℂ) / (1 + G z) ^ 2) * deriv G z := hfder.deriv
  have hnorm_den : (1 : ℝ) - ‖G z‖ ≤ ‖1 + G z‖ := by
    simpa using (norm_sub_le_norm_add (1 : ℂ) (G z))
  have hnum1_bound : ‖((2 * B : ℂ) / (1 + G z) ^ 2)‖ ≤ 2 * B / (1 - ‖G z‖) ^ 2 := by
    rw [norm_div, norm_pow]
    rw [norm_two_mul_of_pos hB]
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg (by norm_num) hB.le
    · exact sq_pos_of_pos (sub_pos.mpr hGzlt)
    · exact (sq_le_sq₀ (sub_nonneg.mpr hGzlt.le) (norm_nonneg _)).mpr hnorm_den
  have hposfactor : 0 ≤ 2 * B / (1 - ‖G z‖) ^ 2 := by
    exact div_nonneg (mul_nonneg (by norm_num) hB.le) (sq_nonneg _)
  calc
    ‖deriv f z‖ = ‖((2 * B : ℂ) / (1 + G z) ^ 2) * deriv G z‖ := by rw [hder_eq]
    _ = ‖(2 * B : ℂ) / (1 + G z) ^ 2‖ * ‖deriv G z‖ := by rw [norm_mul]
    _ ≤ (2 * B / (1 - ‖G z‖) ^ 2) * ‖deriv G z‖ := by
        exact mul_le_mul_of_nonneg_right hnum1_bound (norm_nonneg _)
    _ ≤ (2 * B / (1 - ‖G z‖) ^ 2) * ((1 - ‖G z‖ ^ 2) / (1 - ‖z‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hSP hposfactor
    _ ≤ 2 * B / (1 - ‖z‖) ^ 2 := by
        exact bc_unit_bound hB.le (norm_nonneg z) hz (norm_nonneg (G z)) hGzle

private lemma deriv_comp_affine {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {u : ℂ}
    (hF : AnalyticAt ℂ F (c + (R : ℂ) * u)) :
    deriv (F ∘ (fun v : ℂ => c + (R : ℂ) * v)) u = (R : ℂ) * deriv F (c + (R : ℂ) * u) := by
  have hT : HasDerivAt (fun v : ℂ => c + (R : ℂ) * v) (R : ℂ) u := by
    have h1 : HasDerivAt (fun v : ℂ => (R : ℂ) * v) (R : ℂ) u := by
      simpa using ((hasDerivAt_id u).const_mul (R : ℂ))
    simpa using (h1.const_add c)
  have hFAt : HasDerivAt F (deriv F (c + (R : ℂ) * u)) (c + (R : ℂ) * u) :=
    hF.differentiableAt.hasDerivAt
  have hc : HasDerivAt (F ∘ (fun v : ℂ => c + (R : ℂ) * v))
      (deriv F (c + (R : ℂ) * u) * (R : ℂ)) u := hFAt.comp u hT
  have h := hc.deriv
  rw [mul_comm] at h
  exact h

private lemma borelCaratheodory_deriv_le_pos {F : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 < B)
    (hF : AnalyticOnNhd ℂ F (Metric.ball c R))
    (hFc : F c = 0)
    (hRe : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ B) :
    ∀ z : ℂ, z ∈ Metric.ball c R → ‖deriv F z‖ ≤ 2 * R * B / (R - ‖z - c‖) ^ 2 := by
  intro z hz
  let T : ℂ → ℂ := fun v : ℂ => c + (R : ℂ) * v
  let g : ℂ → ℂ := F ∘ T
  let u0 : ℂ := (z - c) / (R : ℂ)
  have hTdiff : DifferentiableOn ℂ T (Metric.ball (0 : ℂ) 1) := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℂ => (R : ℂ) * v) (R : ℂ) u := by
      simpa using ((hasDerivAt_id u).const_mul (R : ℂ))
    simpa [T] using (h1.const_add c).differentiableAt.differentiableWithinAt
  have hTmaps : Set.MapsTo T (Metric.ball (0 : ℂ) 1) (Metric.ball c R) := by
    intro u hu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hnorm : ‖T u - c‖ = R * ‖u‖ := by
      dsimp [T]
      rw [add_sub_cancel_left]
      rw [norm_mul, Complex.norm_of_nonneg hR.le]
    rw [mem_ball, dist_eq_norm]
    rw [hnorm]
    simpa using (mul_lt_mul_of_pos_left hu1 hR)
  have hFdiff : DifferentiableOn ℂ F (Metric.ball c R) := hF.differentiableOn
  have hgDiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    simpa [g, T] using hFdiff.comp hTdiff hTmaps
  have hg0 : g 0 = 0 := by simp [g, T, hFc]
  have hgRe : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → (g w).re ≤ B := by
    intro w hw
    simpa [g] using hRe (T w) (hTmaps hw)
  have hu0lt : ‖u0‖ < 1 := by
    have hr : ‖z - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
    dsimp [u0]
    rw [norm_div_ofReal hR.le]
    exact (div_lt_one hR).mpr hr
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  have hTu0 : T u0 = z := by
    dsimp [T, u0]
    field_simp [hRne]
    ring
  have hbd := unit_deriv_le_of_re_le (f := g) (B := B) hB hgDiff hg0 hgRe u0 hu0lt
  have hTu0mem : T u0 ∈ Metric.ball c R := by simpa [hTu0] using hz
  have hder : deriv g u0 = (R : ℂ) * deriv F z := by
    have hh := deriv_comp_affine (F := F) (c := c) (R := R) (u := u0) (hF (T u0) hTu0mem)
    simpa [g, T, hTu0] using hh
  have hnormg : ‖deriv g u0‖ = R * ‖deriv F z‖ := by
    rw [hder, norm_mul, Complex.norm_of_nonneg hR.le]
  have hbd2 : R * ‖deriv F z‖ ≤ 2 * B / (1 - ‖u0‖) ^ 2 := by
    rwa [← hnormg]
  have hmain : ‖deriv F z‖ ≤ 2 * B / (R * (1 - ‖u0‖) ^ 2) := by
    have hu0pos : 0 < 1 - ‖u0‖ := sub_pos.mpr hu0lt
    have hdR' : ‖deriv F z‖ * R ≤ 2 * B / (1 - ‖u0‖) ^ 2 := by nlinarith [hbd2]
    have hd' : ‖deriv F z‖ ≤ (2 * B / (1 - ‖u0‖) ^ 2) / R := (le_div_iff₀ hR).2 hdR'
    have heq : (2 * B / (1 - ‖u0‖) ^ 2) / R = 2 * B / (R * (1 - ‖u0‖) ^ 2) := by
      field_simp [hR.ne', (ne_of_gt (sq_pos_of_pos hu0pos))]
    exact hd'.trans_eq heq
  calc
    ‖deriv F z‖ ≤ 2 * B / (R * (1 - ‖u0‖) ^ 2) := hmain
    _ = 2 * R * B / (R - ‖z - c‖) ^ 2 := by
      have hr : ‖z - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
      have hRr : R - ‖z - c‖ ≠ 0 := by linarith
      have hu0n : ‖u0‖ = ‖z - c‖ / R := by
        dsimp [u0]
        rw [norm_div_ofReal hR.le]
      rw [hu0n]
      field_simp [hRr, hR.ne']

theorem borelCaratheodory_deriv_le {F : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B)
    (hF : AnalyticOnNhd ℂ F (Metric.ball c R))
    (hFc : F c = 0)
    (hRe : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ B) :
    ∀ z : ℂ, z ∈ Metric.ball c R → ‖deriv F z‖ ≤ 2 * R * B / (R - ‖z - c‖) ^ 2 := by
  intro z hz
  by_cases hBpos : 0 < B
  · exact borelCaratheodory_deriv_le_pos hR hBpos hF hFc hRe z hz
  · have hB0 : B = 0 := by linarith
    have hzall : ∀ ε : ℝ, 0 < ε → ‖deriv F z‖ ≤ ε := by
      intro ε hε
      have hr : ‖z - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
      have hRrpos : 0 < R - ‖z - c‖ := sub_pos.mpr hr
      have hB'pos : 0 < ε * (R - ‖z - c‖) ^ 2 / (2 * R) := by positivity
      have hRe' : ∀ w : ℂ, w ∈ Metric.ball c R → (F w).re ≤ ε * (R - ‖z - c‖) ^ 2 / (2 * R) := by
        intro w hw
        have hwle : (F w).re ≤ 0 := by simpa [hB0] using hRe w hw
        have hB'nn : 0 ≤ ε * (R - ‖z - c‖) ^ 2 / (2 * R) := le_of_lt hB'pos
        linarith
      have hzε := borelCaratheodory_deriv_le_pos hR hB'pos hF hFc hRe' z hz
      -- hzε : ‖deriv F z‖ ≤ 2 * R * (ε * (R - ‖z - c‖)^2/(2R)) / (R - ‖z - c‖)^2 = ε
      have hcalc : 2 * R * (ε * (R - ‖z - c‖) ^ 2 / (2 * R)) / (R - ‖z - c‖) ^ 2 = ε := by
        field_simp [hR.ne', hRrpos.ne']
      rwa [hcalc] at hzε
    have hd0 : ‖deriv F z‖ ≤ 0 := by
      exact le_of_forall_pos_le_add (a := ‖deriv F z‖) (b := 0)
        (by intro ε hε; simpa using hzall ε hε)
    calc
      ‖deriv F z‖ ≤ 0 := hd0
      _ = 2 * R * B / (R - ‖z - c‖) ^ 2 := by rw [hB0]; simp

end Commons.Analysis.Complex
