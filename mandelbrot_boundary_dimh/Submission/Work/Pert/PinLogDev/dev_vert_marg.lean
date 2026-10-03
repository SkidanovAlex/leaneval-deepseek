import Mathlib
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Pin3.dev_deriv_le_pt
import Submission.Work.Pert.Pin3.dev_seg_const
import Submission.Work.Interfaces.FatouNarrow

/-!
# `Work.Pert.PinLogDev.dev_vert_marg`

Transport of the deviation `Dev z = Φ z - z` of a (pinned) Fatou coordinate along a **vertical
segment**: if the two margins of the gate `Qm Ξ α` are at least `√2 Rde` at every point of the
segment `W → Re W + i Y`, then

  `‖(Φ q - q) - (Φ W - W)‖ ≤ (C₂ / Rde + 1 / 31) * |Y - W.im|`,   `q = Re W + i Y`.

The proof is the mean-value bound `Work.Pert.Pin3.dev_seg_const` applied to the straight segment
from `W` to `q`, with the pointwise derivative bound

  `‖Φ' z - 1‖ ≤ C₂ / Rde + 1 / 31`

which is `Work.Pert.Pin3.dev_deriv_le_pt` (the `D⁻Φ = 1/v` estimate `hDE` instantiated at
`v = F - id`) combined with the `1/32`-near-translation of `F` on the gate:
`‖Φ' z - 1‖ ≤ C₂ / Rde + (32/31)·‖F z - (z+1)‖ ≤ C₂ / Rde + (32/31)·(1/32) = C₂ / Rde + 1/31`.

The clearance `√2 Rde ≤ margA, margB` is converted into `ball z Rde ⊆ Qm Ξ α` by
`Work.Pert.ball_subset_Qm_of_marg_le`, which is exactly the hypothesis the derivative estimate
consumes.
-/

namespace Work.Pert.PinLogDev

open Complex Metric Set

/-- The point of the vertical segment from `W` to `Re W + i Y` at parameter `t`. -/
private lemma vert_point (W : ℂ) (Y t : ℝ) :
    W + t • (((W.re : ℂ) + (Y : ℂ) * Complex.I) - W)
      = (W.re : ℂ) + ((W.im + t * (Y - W.im) : ℝ) : ℂ) * Complex.I := by
  rw [Complex.real_smul]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add] <;>
    ring

/-- The pointwise derivative bound on a ball inside the gate: `‖Φ' z - 1‖ ≤ C₂/Rde + 1/31`. -/
private lemma dev_deriv_bound {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Rde C₂ : ℝ}
    (hRde : 0 < Rde)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α)) {z : ℂ}
    (hball : Metric.ball z Rde ⊆ Work.Pert.Qm Ξ α) :
    ‖deriv Φ z - 1‖ ≤ C₂ / Rde + 1 / 31 := by
  obtain ⟨hFdiff, hFclose⟩ := hNT.1
  have hb := Work.Pert.Pin3.dev_deriv_le_pt (Ξ := Ξ) (β := α) (Rde := Rde) (C₂ := C₂)
    hDE hFdiff (fun w hw => (hFclose w hw).1) hΦ.1 hΦ.2.1 hΦ.2.2 hRde le_rfl hball
  have hzQ : z ∈ Work.Pert.Qm Ξ α := hball (Metric.mem_ball_self hRde)
  have hF : ‖F z - (z + 1)‖ ≤ 1 / 32 := (hFclose z hzQ).1
  have h32 : (32 / 31 : ℝ) * (1 / 32) = 1 / 31 := by norm_num
  linarith [hb, hF, h32]

theorem dev_vert_marg {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Rde C₂ : ℝ} {W : ℂ} {Y : ℝ}
    (hRde : 0 < Rde)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hvert : ∀ y ∈ Set.Icc (min W.im Y) (max W.im Y),
      Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I) ∧
      Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(Φ ((W.re : ℂ) + (Y : ℂ) * Complex.I) - ((W.re : ℂ) + (Y : ℂ) * Complex.I)) - (Φ W - W)‖
      ≤ (C₂ / Rde + 1 / 31) * |Y - W.im| := by
  -- The `Rde`-ball inside the gate is nondegenerate, and `hDE` holds for the identity with
  -- displacement `1`: hence `0 ≤ C₂ / Rde`, so the slope `C₂ / Rde + 1 / 31` is nonnegative.
  have hC₂R : 0 ≤ C₂ / Rde := by
    have h := hDE (fun z : ℂ => z) (fun _ : ℂ => 1) 0 Rde le_rfl
      differentiableOn_id (Set.injOn_id _) (differentiableOn_const 1)
      (by intro z hz; norm_num) (by intro z hz hz'; simp)
    simpa using h
  have hΛ0 : (0 : ℝ) ≤ C₂ / Rde + 1 / 31 := by linarith
  set q : ℂ := (W.re : ℂ) + (Y : ℂ) * Complex.I with hq
  -- The parameter `t` of the segment and the height `y t` of the corresponding point.
  have hpt : ∀ t : ℝ, W + t • (q - W)
      = (W.re : ℂ) + ((W.im + t * (Y - W.im) : ℝ) : ℂ) * Complex.I := by
    intro t
    rw [hq]
    exact vert_point W Y t
  have hy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      W.im + t * (Y - W.im) ∈ Set.Icc (min W.im Y) (max W.im Y) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · nlinarith [ht.1, ht.2, min_le_left W.im Y, min_le_right W.im Y]
    · nlinarith [ht.1, ht.2, le_max_left W.im Y, le_max_right W.im Y]
  -- the clearance at the point of parameter `t`, as `ball · Rde ⊆ Qm Ξ α`
  have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.ball ((W.re : ℂ) + ((W.im + t * (Y - W.im) : ℝ) : ℂ) * Complex.I) Rde
        ⊆ Work.Pert.Qm Ξ α := by
    intro t ht
    obtain ⟨h1, h2⟩ := hvert _ (hy t ht)
    exact Work.Pert.ball_subset_Qm_of_marg_le hRde.le (le_min h1 h2)
  -- the pointwise derivative bound along the segment
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv Φ (W + t • (q - W)) - 1‖ ≤ C₂ / Rde + 1 / 31 := by
    intro t ht
    rw [hpt t]
    exact dev_deriv_bound hRde hDE hNT hΦ (hball t ht)
  -- differentiability of `Φ` along the segment
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (W + t • (q - W)) := by
    intro t ht
    rw [hpt t]
    obtain ⟨h1, h2⟩ := hvert _ (hy t ht)
    have hzQ : (W.re : ℂ) + ((W.im + t * (Y - W.im) : ℝ) : ℂ) * Complex.I
        ∈ Work.Pert.Qm Ξ α := by
      rw [Work.Pert.mem_Qm_iff_marg]
      have hs : 0 < Real.sqrt 2 * Rde := by positivity
      exact ⟨by linarith [h1, hs], by linarith [h2, hs]⟩
    exact hΦ.1.differentiableAt ((Work.Pert.isOpen_Qm_ Ξ α).mem_nhds hzQ)
  -- the mean-value bound along the segment
  have hkey := Work.Pert.Pin3.dev_seg_const (Φ := Φ) (p := W) (q := q) hΛ0 hdiff hderiv
  have hnorm : ‖q - W‖ = |Y - W.im| := by
    have h : q - W = ((Y - W.im : ℝ) : ℂ) * Complex.I := by
      rw [hq]
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hkey
  simpa [hq] using hkey

end Work.Pert.PinLogDev
