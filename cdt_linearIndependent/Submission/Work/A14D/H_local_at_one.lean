import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_conv_alt
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.frobenius_double_exponent_simple_pole

namespace Work.A14D

open Complex Metric

/-- The factor `q` of `PZ` at the singular point `z = 1`. -/
private def qOne (z : ℂ) : ℂ := -(z * (1 - 9 * z))

private lemma PZ_fac_one (z : ℂ) : PZ z = (z - 1) * qOne z := by
  simp only [PZ, qOne]; ring

private lemma PZ'_at_one : PZ' 1 = qOne 1 := by
  simp only [PZ', qOne]; norm_num

private lemma qOne_ne_zero {z : ℂ} (hz : z ∈ ball (1 : ℂ) (1 / 2)) : qOne z ≠ 0 := by
  have hz1 : dist z 1 < (1 / 2 : ℝ) := hz
  have hz0 : z ≠ 0 := by
    intro h
    have h' : dist (0 : ℂ) 1 < (1 / 2 : ℝ) := by rw [← h]; exact hz1
    simp [Complex.dist_eq] at h'; norm_num at h'
  have h9 : (1 : ℂ) - 9 * z ≠ 0 := by
    intro h
    have hz9 : z = (1 : ℂ) / 9 := by
      field_simp at h ⊢
      linear_combination -h
    have h' : dist ((1 : ℂ) / 9) 1 < (1 / 2 : ℝ) := by rw [← hz9]; exact hz1
    simp [Complex.dist_eq] at h'; norm_num at h'
  intro hzq
  simp only [qOne] at hzq
  have h : z * (1 - 9 * z) = 0 := neg_eq_zero.mp hzq
  rcases mul_eq_zero.mp h with h' | h'
  · exact hz0 h'
  · exact h9 h'

theorem H_local_at_one (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 8 / 9 ∧ ∃ e0 e1 : ℂ → ℂ,
      DifferentiableOn ℂ e0 (ball 1 δ) ∧ DifferentiableOn ℂ e1 (ball 1 δ) ∧
      ∀ z ∈ lens1 δ, Hfun a b c z = e0 z + e1 z * ell z - (c : ℂ) / 16 * uh z * ell z ^ 2 := by
  obtain ⟨hHd, hHode⟩ := H_conv_alt a b c h
  obtain ⟨hud, hu1, huode⟩ := uh_ode
  have hu1ne : uh 1 ≠ 0 := by rw [hu1]; norm_num
  have hcont : ContinuousAt uh 1 :=
    (hud.differentiableAt (Metric.ball_mem_nhds 1 (by norm_num))).continuousAt
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hcont.eventually_ne hu1ne)
  set δ : ℝ := min (1 / 2) ε with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by norm_num) hεpos
  have hδle : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδε : δ ≤ ε := by rw [hδdef]; exact min_le_right _ _
  have hδ89 : δ < 8 / 9 := lt_of_le_of_lt hδle (by norm_num)
  have hδ89' : δ ≤ 8 / 9 := le_of_lt hδ89
  obtain ⟨e0, e1, he0, he1, hident⟩ :=
    frobenius_double_exponent_simple_pole (s := (1 : ℂ)) (δ := δ) hδpos
      (y1 := uh) (φ := Hfun a b c) (P2 := PZ) (P1 := PZ') (P0 := RZ)
      (G := fun _ => (b : ℂ)) (Ω := lens1 δ) (q := qOne) (A := (c : ℂ))
      (hud.mono (Metric.ball_subset_ball hδ89'))
      (fun z hz => hε (Metric.ball_subset_ball hδε hz))
      (by rw [hu1]; norm_num)
      (fun z hz => by
        have hz' : z ∈ ball (1 : ℂ) (8 / 9) := Metric.ball_subset_ball hδ89' hz
        have hh := huode z hz'
        simpa only [LZ] using hh)
      (fun z _ => PZ_fac_one z)
      (by unfold qOne; fun_prop)
      (fun z hz => qOne_ne_zero (Metric.ball_subset_ball hδle hz))
      (by simp only [qOne]; norm_num)
      (by rw [PZ'_at_one])
      (by unfold PZ'; fun_prop)
      (by unfold RZ; fun_prop)
      (differentiableOn_const (b : ℂ))
      (by unfold lens1; exact Metric.isOpen_ball.inter Metric.isOpen_ball)
      (by unfold lens1
          exact (convex_ball (1 : ℂ) δ).inter (convex_ball (0 : ℂ) 1) |>.isPreconnected)
      (fun z hz => hz.1)
      (fun hz => by
        have h1 : (1 : ℂ) ∈ ball (0 : ℂ) 1 := hz.2
        simp [Metric.mem_ball] at h1)
      (fun z hz => by
        rw [Complex.mem_slitPlane_iff]
        left
        have h1 : ‖z‖ < 1 := by
          have h2 := hz.2
          rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at h2
        have h2 : z.re ≤ ‖z‖ := Complex.re_le_norm z
        have h3 : ((1 : ℂ) - z).re = 1 - z.re := Complex.sub_re 1 z
        rw [h3]; linarith)
      (hHd.mono (fun z hz => hz.2))
      (fun z hz => by
        have hh := hHode z hz.2
        simp only [LZ, rhsZ] at hh
        rw [hh]; ring)
  refine ⟨δ, hδpos, hδ89, e0, e1, he0, he1, ?_⟩
  intro z hz
  have hz' := hident z hz
  simp only [ell] at hz' ⊢
  rw [hz']
  have hc16 : (c : ℂ) / (2 * (uh 1 * qOne 1)) = (c : ℂ) / 16 := by
    simp only [qOne]; rw [hu1]; norm_num
  rw [hc16]

end Work.A14D
