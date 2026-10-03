import Mathlib
import Submission.Work.Pert.RoucheBridge
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.Repel.koebe_covering_scaled
import Submission.Work.Repel.deriv_lower_scaled

/-!
# Two-point lower bound on the half-ball, from Koebe's distortion theorem

If `g` is holomorphic and injective on the disc `ball c r`, then `g` does not contract distances
by more than a factor `50` on the half-ball:

  `(1/50) * ‖deriv g c‖ * ‖u - v‖ ≤ ‖g u - g v‖`  for `u, v ∈ closedBall c (r/2)`.

The proof uses two classical inputs, both consequences of Grönwall's area theorem (via
Bieberbach's coefficient inequality `‖a₂‖ ≤ 2`):

* `koebe_covering_scaled`: the sharp Koebe one-quarter theorem, i.e. the image of
  `ball p ρ` contains `ball (g p) (ρ/4 · ‖deriv g p‖)`;
* `deriv_lower_scaled`: `‖deriv g z‖ ≥ ‖deriv g c‖/12` on `closedBall c (r/2)`.

Given both, the argument is: for `u ≠ v` put `s = ‖u - v‖/2`.  The open discs
`ball u s` and `ball v s` are disjoint, hence (by injectivity) their images are disjoint and so
the two Koebe discs `ball (g u) (s/4 · ‖deriv g u‖)` and `ball (g v) (s/4 · ‖deriv g v‖)` are
disjoint.  Therefore

  `‖g u - g v‖ ≥ (s/4) (‖deriv g u‖ + ‖deriv g v‖) ≥ (s/4) (2/12) ‖deriv g c‖`
  `= ‖u - v‖ ‖deriv g c‖ / 48 ≥ (1/50) ‖deriv g c‖ ‖u - v‖`.
-/

namespace Work.Repel

open Metric Filter

/-- Two disjoint open balls in `ℂ` (with positive radii) have centres at distance at least the sum
of their radii. -/
private lemma add_radii_le_dist_of_disjoint {z w : ℂ} {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (h : Disjoint (Metric.ball z ρ) (Metric.ball w σ)) : ρ + σ ≤ dist z w := by
  by_contra hle
  rw [not_le] at hle
  have hsum : 0 < ρ + σ := by linarith
  have hzw : ‖w - z‖ = dist z w := by rw [dist_eq_norm, norm_sub_rev]
  set t : ℝ := ρ / (ρ + σ) with ht
  have ht0 : 0 < t := div_pos hρ hsum
  have ht1 : t < 1 := by rw [ht, div_lt_one hsum]; linarith
  have h1t : 0 < 1 - t := by linarith
  set p : ℂ := z + (t : ℂ) * (w - z) with hp
  have hpz : p ∈ Metric.ball z ρ := by
    rw [Metric.mem_ball, dist_eq_norm, hp]
    have hsub : z + (t : ℂ) * (w - z) - z = (t : ℂ) * (w - z) := by ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hzw]
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hsum]
    nlinarith
  have hpw : p ∈ Metric.ball w σ := by
    rw [Metric.mem_ball, dist_eq_norm, hp]
    have hsub : z + (t : ℂ) * (w - z) - w = ((t - 1 : ℝ) : ℂ) * (w - z) := by
      push_cast; ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |t - 1| = 1 - t := by rw [abs_of_neg (by linarith)]; ring
    rw [habs, hzw, ht]
    have hkey : (1 - ρ / (ρ + σ)) = σ / (ρ + σ) := by field_simp; ring
    rw [hkey, div_mul_eq_mul_div, div_lt_iff₀ hsum]
    nlinarith
  have hmem : p ∈ (Metric.ball z ρ) ∩ (Metric.ball w σ) := ⟨hpz, hpw⟩
  rw [Set.disjoint_iff_inter_eq_empty] at h
  rw [h] at hmem
  exact hmem

/-- A holomorphic injection on a disc has nonvanishing derivative at every interior point. -/
private lemma deriv_ne_zero_of_injOn_closed {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.closedBall c r))
    (hinj : Set.InjOn g (Metric.ball c r)) {z : ℂ} (hz : ‖z - c‖ < r) : deriv g z ≠ 0 := by
  have hsub : Metric.ball z ((r - ‖z - c‖) / 2) ⊆ Metric.ball c r := by
    intro a ha
    rw [Metric.mem_ball, dist_eq_norm] at ha ⊢
    have h1 : ‖a - c‖ ≤ ‖a - z‖ + ‖z - c‖ := by
      calc ‖a - c‖ = ‖(a - z) + (z - c)‖ := by ring_nf
        _ ≤ ‖a - z‖ + ‖z - c‖ := norm_add_le _ _
    linarith
  have hzball : z ∈ Metric.ball c r := by rw [Metric.mem_ball, dist_eq_norm]; exact hz
  have hnhds : Metric.closedBall c r ∈ nhds z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzball) Metric.ball_subset_closedBall
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn (by linarith)
    (hg.analyticAt hnhds) (fun a ha b hb hab => hinj (hsub ha) (hsub hb) hab)

theorem two_point_lower_half_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.closedBall c r))
    (hinj : Set.InjOn g (Metric.ball c r)) :
    ∀ u ∈ Metric.closedBall c (r / 2), ∀ v ∈ Metric.closedBall c (r / 2),
      (1 / 50 : ℝ) * ‖deriv g c‖ * ‖u - v‖ ≤ ‖g u - g v‖ := by
  intro u hu v hv
  have huc : ‖u - c‖ ≤ r / 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hu; exact hu
  have hvc : ‖v - c‖ ≤ r / 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hv; exact hv
  rcases eq_or_ne u v with rfl | huv
  · simp
  have huvpos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  set s : ℝ := ‖u - v‖ / 2 with hs
  have hspos : 0 < s := by rw [hs]; linarith
  have hsle : s ≤ r / 2 := by
    rw [hs]
    have h1 : ‖u - v‖ ≤ ‖u - c‖ + ‖v - c‖ := by
      calc ‖u - v‖ = ‖(u - c) - (v - c)‖ := by ring_nf
        _ ≤ ‖u - c‖ + ‖v - c‖ := norm_sub_le _ _
    linarith
  -- inclusions of the small discs in the big disc
  have hbalu : Metric.ball u s ⊆ Metric.ball c r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have h1 : ‖z - c‖ ≤ ‖z - u‖ + ‖u - c‖ := by
      calc ‖z - c‖ = ‖(z - u) + (u - c)‖ := by ring_nf
        _ ≤ ‖z - u‖ + ‖u - c‖ := norm_add_le _ _
    linarith
  have hbalv : Metric.ball v s ⊆ Metric.ball c r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have h1 : ‖z - c‖ ≤ ‖z - v‖ + ‖v - c‖ := by
      calc ‖z - c‖ = ‖(z - v) + (v - c)‖ := by ring_nf
        _ ≤ ‖z - v‖ + ‖v - c‖ := norm_add_le _ _
    linarith
  have hcbalu : Metric.closedBall u s ⊆ Metric.closedBall c r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    have h1 : ‖z - c‖ ≤ ‖z - u‖ + ‖u - c‖ := by
      calc ‖z - c‖ = ‖(z - u) + (u - c)‖ := by ring_nf
        _ ≤ ‖z - u‖ + ‖u - c‖ := norm_add_le _ _
    linarith
  have hcbalv : Metric.closedBall v s ⊆ Metric.closedBall c r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    have h1 : ‖z - c‖ ≤ ‖z - v‖ + ‖v - c‖ := by
      calc ‖z - c‖ = ‖(z - v) + (v - c)‖ := by ring_nf
        _ ≤ ‖z - v‖ + ‖v - c‖ := norm_add_le _ _
    linarith
  -- the two-point input at `u` and `v`
  have hderu : (1 / 12 : ℝ) * ‖deriv g c‖ ≤ ‖deriv g u‖ :=
    deriv_lower_scaled hr hg hinj u hu
  have hderv : (1 / 12 : ℝ) * ‖deriv g c‖ ≤ ‖deriv g v‖ :=
    deriv_lower_scaled hr hg hinj v hv
  -- nonvanishing of the derivatives (from injectivity)
  have hgu_ne : deriv g u ≠ 0 := deriv_ne_zero_of_injOn_closed hr hg hinj (by linarith)
  have hgv_ne : deriv g v ≠ 0 := deriv_ne_zero_of_injOn_closed hr hg hinj (by linarith)
  -- Koebe covering for the two small discs
  have hcovu : Metric.ball (g u) (s / 4 * ‖deriv g u‖) ⊆ g '' Metric.ball u s :=
    koebe_covering_scaled (f := g) (c := u) (R := s) hspos (hg.mono hcbalu) (hinj.mono hbalu)
  have hcovv : Metric.ball (g v) (s / 4 * ‖deriv g v‖) ⊆ g '' Metric.ball v s :=
    koebe_covering_scaled (f := g) (c := v) (R := s) hspos (hg.mono hcbalv) (hinj.mono hbalv)
  -- the small discs `ball u s`, `ball v s` are disjoint
  have hdisj_balls : Disjoint (Metric.ball u s) (Metric.ball v s) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [Metric.mem_ball, dist_comm z u] at hz1
    rw [Metric.mem_ball] at hz2
    have h2s : dist u v = 2 * s := by rw [dist_eq_norm, hs]; ring
    have htri := dist_triangle u z v
    rw [h2s] at htri
    linarith
  have hdisj : Disjoint (g '' Metric.ball u s) (g '' Metric.ball v s) := by
    rw [Set.disjoint_left]
    rintro w ⟨z1, hz1, hz1w⟩ ⟨z2, hz2, hz2w⟩
    have heq : g z1 = g z2 := by rw [hz1w, hz2w]
    have hz12 : z1 = z2 := hinj (hbalu hz1) (hbalv hz2) heq
    subst hz12
    exact Set.disjoint_left.mp hdisj_balls hz1 hz2
  have hdisj' : Disjoint (Metric.ball (g u) (s / 4 * ‖deriv g u‖))
      (Metric.ball (g v) (s / 4 * ‖deriv g v‖)) := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro a ha hb
    exact hdisj (hcovu ha) (hcovv hb)
  -- hence the centres are far apart
  have hru : 0 < s / 4 * ‖deriv g u‖ := by
    have hpos : (0:ℝ) < ‖deriv g u‖ := norm_pos_iff.mpr hgu_ne
    positivity
  have hrv : 0 < s / 4 * ‖deriv g v‖ := by
    have hpos : (0:ℝ) < ‖deriv g v‖ := norm_pos_iff.mpr hgv_ne
    positivity
  have hkey : s / 4 * ‖deriv g u‖ + s / 4 * ‖deriv g v‖ ≤ ‖g u - g v‖ := by
    have h := add_radii_le_dist_of_disjoint hru hrv hdisj'
    rw [dist_eq_norm] at h
    linarith
  -- arithmetic
  have hsum : ‖deriv g c‖ / 6 ≤ ‖deriv g u‖ + ‖deriv g v‖ := by linarith
  have hstep : ‖u - v‖ / 8 * (‖deriv g c‖ / 6) ≤ s / 4 * (‖deriv g u‖ + ‖deriv g v‖) := by
    have h8 : (0:ℝ) ≤ ‖u - v‖ / 8 := by positivity
    have hs4 : s / 4 = ‖u - v‖ / 8 := by rw [hs]; ring
    rw [hs4]
    exact mul_le_mul_of_nonneg_left hsum h8
  have hfin : s / 4 * (‖deriv g u‖ + ‖deriv g v‖) ≤ ‖g u - g v‖ := by
    have h1 : s / 4 * (‖deriv g u‖ + ‖deriv g v‖)
        = s / 4 * ‖deriv g u‖ + s / 4 * ‖deriv g v‖ := by ring
    rw [h1]; exact hkey
  calc (1 / 50 : ℝ) * ‖deriv g c‖ * ‖u - v‖
      ≤ (1 / 48 : ℝ) * ‖deriv g c‖ * ‖u - v‖ := by
        nlinarith [norm_nonneg (deriv g c), norm_nonneg (u - v)]
    _ = ‖u - v‖ / 8 * (‖deriv g c‖ / 6) := by ring
    _ ≤ s / 4 * (‖deriv g u‖ + ‖deriv g v‖) := hstep
    _ ≤ ‖g u - g v‖ := hfin

end Work.Repel
