import Mathlib
import Submission.Work.L62.lift_fatou

namespace Work.L62

open Complex Filter Set Topology
open scoped Topology

/-- `im z - R ≤ im w` whenever `‖w - z‖ ≤ R`: the imaginary part is `1`-Lipschitz for the
euclidean norm. -/
private lemma im_ge_of_norm_sub_le {z w : ℂ} {R : ℝ} (h : ‖w - z‖ ≤ R) :
    Complex.im z - R ≤ Complex.im w := by
  have h1 : |(w - z).im| ≤ R := (Complex.abs_im_le_norm _).trans h
  have h2 : (w - z).im = Complex.im w - Complex.im z := Complex.sub_im w z
  have h3 : -(R) ≤ (w - z).im := (abs_le.mp h1).1
  rw [h2] at h3
  linarith

/-- Monotonicity of `Real.exp` composed with `x ↦ -2πx`. -/
private lemma exp_neg_two_pi_le {x y : ℝ} (h : y ≤ x) :
    Real.exp (-2 * Real.pi * x) ≤ Real.exp (-2 * Real.pi * y) :=
  Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])

/-- A series of holomorphic functions on the half-plane `{a < im}`, dominated there by the
exponentially weighted geometric progression `n ↦ A * exp (-2π (im z - a)) * r ^ n`, converges on
`{a < im}`, its sum is holomorphic on the deeper half-plane `{Y < im}` (where `a + 1/2 ≤ Y`), and
its derivative there is bounded by `2 * A * exp (-2 π (Y - a - 1/2)) / (1 - r)` (Cauchy's estimate
on the disc of radius `1/2`). -/
lemma tsum_decay {g : ℕ → ℂ → ℂ} {a Y A r : ℝ} (haY : a + 1 / 2 ≤ Y)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hA : 0 ≤ A)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (g n) {z : ℂ | a < Complex.im z})
    (hbd : ∀ (n : ℕ) (z : ℂ), a < Complex.im z →
      ‖g n z‖ ≤ A * Real.exp (-2 * Real.pi * (Complex.im z - a)) * r ^ n) :
    (∀ z : ℂ, a < Complex.im z → Summable fun n => g n z) ∧
    DifferentiableOn ℂ (fun z => ∑' n, g n z) {z : ℂ | Y < Complex.im z} ∧
    (∀ z : ℂ, Y < Complex.im z → ‖deriv (fun z => ∑' n, g n z) z‖ ≤
      2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) / (1 - r)) := by
  have hHYopen : IsOpen {z : ℂ | Y < Complex.im z} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hsub : {z : ℂ | Y < Complex.im z} ⊆ {z : ℂ | a < Complex.im z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    linarith
  have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
  have hu : Summable fun n : ℕ => A * Real.exp (-2 * Real.pi * (Y - a)) * r ^ n :=
    Summable.mul_left _ hgeom
  have hFle : ∀ (i : ℕ) (w : ℂ), w ∈ {z : ℂ | Y < Complex.im z} →
      ‖g i w‖ ≤ A * Real.exp (-2 * Real.pi * (Y - a)) * r ^ i := by
    intro n w hw
    simp only [Set.mem_ofPred_eq] at hw
    have haw : a < Complex.im w := by linarith
    calc ‖g n w‖ ≤ A * Real.exp (-2 * Real.pi * (Complex.im w - a)) * r ^ n := hbd n w haw
      _ ≤ A * Real.exp (-2 * Real.pi * (Y - a)) * r ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (exp_neg_two_pi_le (by linarith)) hA)
            (pow_nonneg hr0 n)
  have hdiffY : ∀ n : ℕ, DifferentiableOn ℂ (g n) {z : ℂ | Y < Complex.im z} :=
    fun n => (hdiff n).mono hsub
  refine ⟨?_, ?_, ?_⟩
  · -- pointwise summability on `{a < im}`
    intro z hz
    have hzsum : Summable fun n : ℕ =>
        A * Real.exp (-2 * Real.pi * (Complex.im z - a)) * r ^ n :=
      Summable.mul_left _ hgeom
    exact hzsum.of_norm_bounded fun n => hbd n z hz
  · -- holomorphy of the sum on `{Y < im}`
    exact Complex.differentiableOn_tsum_of_summable_norm hu hdiffY hHYopen hFle
  · -- the derivative bound by Cauchy's estimate
    intro z hz
    have hz' : z ∈ {z : ℂ | Y < Complex.im z} := hz
    have hHasSum : HasSum (fun n => deriv (g n) z) (deriv (fun w => ∑' n, g n w) z) :=
      Complex.hasSum_deriv_of_summable_norm hu hdiffY hHYopen hFle hz'
    have hcauchy : ∀ n : ℕ, ‖deriv (g n) z‖ ≤
        2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n := by
      intro n
      have hball : DiffContOnCl ℂ (g n) (Metric.ball z (1 / 2 : ℝ)) := by
        refine (hdiff n).diffContOnCl_ball ?_
        intro w hw
        simp only [Set.mem_ofPred_eq]
        have h1 : ‖w - z‖ ≤ (1 / 2 : ℝ) := by simpa [dist_eq_norm] using hw
        have h2 := im_ge_of_norm_sub_le h1
        linarith
      have hsphere : ∀ w ∈ Metric.sphere z (1 / 2 : ℝ),
          ‖g n w‖ ≤ A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n := by
        intro w hw
        have h1 : ‖w - z‖ ≤ (1 / 2 : ℝ) := by
          have hdist : dist w z = (1 / 2 : ℝ) := Metric.mem_sphere.mp hw
          rw [dist_eq_norm] at hdist
          exact le_of_eq hdist
        have h2 := im_ge_of_norm_sub_le h1
        have haw : a < Complex.im w := by linarith
        calc ‖g n w‖ ≤ A * Real.exp (-2 * Real.pi * (Complex.im w - a)) * r ^ n := hbd n w haw
          _ ≤ A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (exp_neg_two_pi_le (x := Complex.im w - a) (y := Y - a - 1 / 2) (by linarith))
                  hA)
                (pow_nonneg hr0 n)
      have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
        (c := z) (R := (1 / 2 : ℝ))
        (C := A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n)
        (by norm_num) hball hsphere
      have hdiv : (A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n) / (1 / 2 : ℝ)
          = 2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n := by ring
      rwa [hdiv] at hbound
    have hsumm_deriv : Summable fun n : ℕ => ‖deriv (g n) z‖ := hHasSum.summable.norm
    have hbnd : (∑' n, ‖deriv (g n) z‖) ≤
        ∑' n, (2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n) :=
      Summable.tsum_le_tsum hcauchy hsumm_deriv (Summable.mul_left _ hgeom)
    have hnorm : ‖deriv (fun w => ∑' n, g n w) z‖ ≤ ∑' n, ‖deriv (g n) z‖ := by
      rw [← hHasSum.tsum_eq]
      exact norm_tsum_le_tsum_norm hsumm_deriv
    have hval : (∑' n, (2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n))
        = 2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      ring
    calc ‖deriv (fun w => ∑' n, g n w) z‖ ≤ ∑' n, ‖deriv (g n) z‖ := hnorm
      _ ≤ ∑' n, (2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) * r ^ n) := hbnd
      _ = 2 * A * Real.exp (-2 * Real.pi * (Y - a - 1 / 2)) / (1 - r) := hval

end Work.L62
