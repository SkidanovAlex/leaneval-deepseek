import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.RoucheBridge
import Submission.Work.Repel.two_point_lower_half_ball

namespace Work.Repel

open Metric Filter
open scoped Topology

/--
**Uniformly close univalent maps are locally bijective.**

Let `g` be holomorphic and injective on the closed ball `closedBall c r` with `deriv g c ≠ 0`,
and let `f` be holomorphic there with `‖f z - g z‖ ≤ δ`.  If `128 δ < r ‖deriv g c‖` then `f` is
injective on a ball around `c` and its image covers a ball around `g c`.

The quantitative input is the two-point distortion bound
`Work.Repel.two_point_lower_half_ball` (a consequence of Koebe's distortion theorem): a univalent
map on `ball c r` is `(1/50)‖deriv g c‖`-Lipschitz from below on the half-ball.  The proof is then
Rouché's theorem for the covering part and the mean value inequality for the injectivity part.
-/
theorem locally_bij_explicit {f g : ℂ → ℂ} {c : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c r))
    (hg : DifferentiableOn ℂ g (Metric.closedBall c r))
    (hg' : deriv g c ≠ 0) (hginj : Set.InjOn g (Metric.ball c r))
    (hclose : ∀ z ∈ Metric.closedBall c r, ‖f z - g z‖ ≤ δ)
    (hsmall : (128 : ℝ) * δ < r * ‖deriv g c‖) :
    Set.InjOn f (Metric.ball c (r / 2)) ∧
      Metric.ball (g c) ((1 / 50 : ℝ) * ‖deriv g c‖ * (r / 2) - δ) ⊆
        f '' Metric.ball c (r / 2) := by
  have hgnorm : 0 < ‖deriv g c‖ := norm_pos_iff.mpr hg'
  have hr2 : (0:ℝ) < r / 2 := by linarith
  have hr2ne : r / 2 ≠ 0 := ne_of_gt hr2
  have hrpos : (0:ℝ) < r := hr
  -- the two-point distortion input on the half-ball
  have hinp : ∀ u ∈ Metric.closedBall c (r / 2), ∀ v ∈ Metric.closedBall c (r / 2),
      (1 / 50 : ℝ) * ‖deriv g c‖ * ‖u - v‖ ≤ ‖g u - g v‖ :=
    two_point_lower_half_ball hr hg hginj
  -- the covering radius
  set lam : ℝ := (1/50 : ℝ) * ‖deriv g c‖ * (r/2) - δ with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    have h1 : (128:ℝ) * δ < r * ‖deriv g c‖ := hsmall
    have h2 : (1:ℝ)/50 * ‖deriv g c‖ * (r/2) = ‖deriv g c‖ * r / 100 := by ring
    rw [h2]
    nlinarith [hgnorm, hrpos, h1]
  -- 2δ/r < (1/50)‖g'c‖
  have htwo : 2*δ/r < (1:ℝ)/50 * ‖deriv g c‖ := by
    have h1 : (128:ℝ) * δ < r * ‖deriv g c‖ := hsmall
    rw [div_lt_iff₀ hrpos]
    nlinarith [hgnorm, hrpos, h1]
  -- the derivative bound for h = f - g on the half-ball
  have hfh : DifferentiableOn ℂ (fun y => f y - g y) (Metric.ball c r) :=
    (hf.mono Metric.ball_subset_closedBall).sub (hg.mono Metric.ball_subset_closedBall)
  have hch : ContinuousOn (fun y => f y - g y) (Metric.closedBall c r) :=
    (hf.continuousOn).sub (hg.continuousOn)
  have hderiv_bound : ∀ x ∈ Metric.closedBall c (r/2), ‖deriv (fun y => f y - g y) x‖ ≤ 2*δ/r := by
    intro x hx
    have hxr : ‖x - c‖ ≤ r/2 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hx; exact hx
    have hdc : DiffContOnCl ℂ (fun y => f y - g y) (Metric.ball x (r/2)) := by
      refine ⟨?_, ?_⟩
      · intro y hy
        have hyball : y ∈ Metric.ball c r := by
          rw [Metric.mem_ball, dist_eq_norm]
          rw [Metric.mem_ball, dist_eq_norm] at hy
          have h1 : ‖y - c‖ ≤ ‖y - x‖ + ‖x - c‖ := by
            calc ‖y - c‖ = ‖(y - x) + (x - c)‖ := by ring_nf
              _ ≤ ‖y - x‖ + ‖x - c‖ := norm_add_le _ _
          linarith
        exact (hfh.differentiableAt (Metric.isOpen_ball.mem_nhds hyball)).differentiableWithinAt
      · rw [closure_ball x hr2ne]
        refine hch.mono ?_
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
        have h1 : ‖y - c‖ ≤ ‖y - x‖ + ‖x - c‖ := by
          calc ‖y - c‖ = ‖(y - x) + (x - c)‖ := by ring_nf
            _ ≤ ‖y - x‖ + ‖x - c‖ := norm_add_le _ _
        linarith
    have hsp : ∀ y ∈ Metric.sphere x (r/2), ‖f y - g y‖ ≤ δ := by
      intro y hy
      have hyc : y ∈ Metric.closedBall c r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hyx : ‖y - x‖ = r/2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hy
        calc ‖y - c‖ ≤ ‖y - x‖ + ‖x - c‖ := by
              calc ‖y - c‖ = ‖(y - x) + (x - c)‖ := by ring_nf
                _ ≤ ‖y - x‖ + ‖x - c‖ := norm_add_le _ _
          _ ≤ r/2 + r/2 := by rw [hyx]; linarith
          _ = r := by ring
      exact hclose y hyc
    have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (f := fun y => f y - g y) (c := x) (R := r/2) (C := δ) hr2 hdc hsp
    calc ‖deriv (fun y => f y - g y) x‖ ≤ δ / (r/2) := hmain
      _ = 2*δ/r := by field_simp
  -- injectivity of `f` on the half-ball
  have hInj : Set.InjOn f (Metric.ball c (r/2)) := by
    intro u hu v hv huv
    by_contra hne
    have hu' : u ∈ Metric.closedBall c (r/2) := Metric.ball_subset_closedBall hu
    have hv' : v ∈ Metric.closedBall c (r/2) := Metric.ball_subset_closedBall hv
    have hdiff_at : ∀ x ∈ Metric.closedBall c (r/2), DifferentiableAt ℂ (fun y => f y - g y) x := by
      intro x hx
      have hxball : x ∈ Metric.ball c r := by
        rw [Metric.mem_ball, dist_eq_norm]
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        linarith
      exact (hfh.differentiableAt (Metric.isOpen_ball.mem_nhds hxball))
    have hlip : ‖(f u - g u) - (f v - g v)‖ ≤ (2*δ/r) * ‖u - v‖ := by
      have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff_at hderiv_bound
        (convex_closedBall c (r/2)) hv' hu'
      simpa using h
    have hsep := hinp u hu' v hv'
    have hkey : 0 < ((1:ℝ)/50 * ‖deriv g c‖ - 2*δ/r) * ‖u - v‖ := by
      have h1 : 0 < (1:ℝ)/50 * ‖deriv g c‖ - 2*δ/r := by linarith [htwo]
      have h2 : 0 < ‖u - v‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
      exact mul_pos h1 h2
    have hle : ((1:ℝ)/50 * ‖deriv g c‖ - 2*δ/r) * ‖u - v‖ ≤ ‖f u - f v‖ := by
      have h1 : f u - f v = (g u - g v) + ((f u - g u) - (f v - g v)) := by ring
      rw [h1]
      have h2 : ‖g u - g v‖ - ‖(f u - g u) - (f v - g v)‖
          ≤ ‖(g u - g v) + ((f u - g u) - (f v - g v))‖ := by
        have h3 := norm_add_le ((g u - g v) + ((f u - g u) - (f v - g v)))
          (-((f u - g u) - (f v - g v)))
        have h4 : (g u - g v) + ((f u - g u) - (f v - g v)) + -((f u - g u) - (f v - g v))
            = g u - g v := by ring
        rw [h4] at h3
        rw [norm_neg] at h3
        linarith
      linarith [hsep, hlip]
    have hpos : 0 < ‖f u - f v‖ := lt_of_lt_of_le hkey hle
    rw [huv, sub_self, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨hInj, ?_⟩
  -- covering via Rouché
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  set F : ℂ → ℂ := fun u => g (c + u) - g c with hF
  set G : ℂ → ℂ := fun u => (f (c + u) - g (c + u)) - (w - g c) with hG
  have hmaps0 : Set.MapsTo (fun u : ℂ => c + u) (Metric.closedBall (0:ℂ) (r/2))
      (Metric.closedBall c r) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu ⊢
    simp only [sub_zero] at hu
    rw [add_sub_cancel_left]
    linarith
  have h1tr : DifferentiableOn ℂ (fun u : ℂ => c + u) (Metric.closedBall (0:ℂ) (r/2)) :=
    differentiableOn_id.const_add c
  have hFdiff : DifferentiableOn ℂ F (Metric.closedBall (0:ℂ) (r/2)) := by
    rw [hF]
    exact ((hg.comp h1tr hmaps0).sub_const (g c))
  have hGdiff : DifferentiableOn ℂ G (Metric.closedBall (0:ℂ) (r/2)) := by
    rw [hG]
    exact ((hf.comp h1tr hmaps0).sub (hg.comp h1tr hmaps0)).sub_const (w - g c)
  have hsphere : ∀ z ∈ Metric.sphere (0:ℂ) (r/2), ‖G z‖ < ‖F z‖ := by
    intro z hz
    have hzn : ‖z‖ = r/2 := by simpa using hz
    have hzc : c + z ∈ Metric.closedBall c (r/2) := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hzn]
    have hc_ball : c ∈ Metric.closedBall c (r/2) := Metric.mem_closedBall_self (by linarith)
    have hGle : ‖G z‖ ≤ δ + ‖w - g c‖ := by
      rw [hG]
      calc ‖(f (c + z) - g (c + z)) - (w - g c)‖
          ≤ ‖f (c+z) - g (c+z)‖ + ‖w - g c‖ := norm_sub_le _ _
        _ ≤ δ + ‖w - g c‖ := by
            have h := hclose (c+z) (Metric.closedBall_subset_closedBall (by linarith) hzc)
            linarith
    have hFge : (1:ℝ)/50 * ‖deriv g c‖ * (r/2) ≤ ‖F z‖ := by
      have h := hinp (c+z) hzc c hc_ball
      rw [hF]
      have hcz : ‖(c + z) - c‖ = r/2 := by rw [add_sub_cancel_left, hzn]
      rw [hcz] at h
      exact h
    have hlt : δ + ‖w - g c‖ < (1:ℝ)/50 * ‖deriv g c‖ * (r/2) := by
      have h := hw
      rw [hlam] at h
      linarith
    linarith
  have hderF : deriv F 0 = deriv g c := by
    have h1 : HasDerivAt (fun u : ℂ => c + u) 1 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).const_add c
    have hd : DifferentiableAt ℂ g c :=
      (hg.mono Metric.ball_subset_closedBall).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    have h2 : HasDerivAt g (deriv g c) (c + 0) := by simpa using hd.hasDerivAt
    have h5 : HasDerivAt (g ∘ fun u : ℂ => c + u) (deriv g c) 0 := by
      have h4 := h2.comp 0 h1
      simpa only [mul_one] using h4
    rw [hF, deriv_sub_const]
    exact h5.deriv
  have hFonly : ∀ z ∈ Metric.ball (0:ℂ) (r/2), F z = 0 → z = 0 := by
    intro z hz hz0
    rw [hF] at hz0
    have h1 : g (c + z) = g c := sub_eq_zero.mp hz0
    have hcz : c + z ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      have hz' : ‖z‖ < r/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      linarith
    have hcc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
    have h2 := hginj hcz hcc h1
    simpa using h2
  obtain ⟨z, hzball, hsum, -⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero (R := r/2) hr2 (a := 0) (f := F) (g := G)
      (by simp only [norm_zero]; linarith) hFdiff hFdiff.continuousOn hGdiff hGdiff.continuousOn hsphere
      (by rw [hF]; simp) (by rw [hderF]; exact hg') hFonly
  refine ⟨c + z, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hz' : ‖z‖ < r/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hzball
    exact hz'
  · have h : f (c + z) - w = 0 := by
      have h' := hsum
      rw [hF, hG] at h'
      ring_nf at h'
      linear_combination h'
    exact sub_eq_zero.mp h

end Work.Repel
