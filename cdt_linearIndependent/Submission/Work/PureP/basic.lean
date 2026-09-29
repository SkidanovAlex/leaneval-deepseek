import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.CPhi.exists_differentiableOn_log_ball
import Submission.Work.CPull.germs

/-!
# Area PureP — generic consequences of `LiftData` and the odd logarithm

`Submission.CDTPlan.LiftData φ Φ` says that `Φ` is a holomorphic lift of `z ↦ φ (z^2)` through
the symmetrisation `y ↦ y^2/(y-1)`:

* `Φ z + Φ (-z) = φ (z^2)`,
* `Φ z * Φ (-z) = φ (z^2)`,
* `Φ z = 0 → z = 0` on the disc.

Everything in `Work.PureP` is proved from these three relations plus `φ 0 = 0`.  This module
collects the elementary consequences used by all the per-function pullback arguments:

* `lift_zero`, `lift_sq`, `lift_ne_one`, `lift_neg_eq`, `phi_sq_eq`, `one_sub_neg`;
* `phi_ne_zero`: `φ` has no zero in the punctured unit disc;
* `exists_odd_log_phi`: a holomorphic logarithm `ℓ` of `1 - Φ` on the disc which is *odd*
  (`ℓ (-z) = - ℓ z`) and agrees with the principal logarithm near `0`.
-/

namespace Work.PureP

open Complex Metric Filter
open scoped Topology
open Submission.CDTPlan

/-- From `φ 0 = 0` and the lift relations: `Φ 0 = 0`. -/
theorem lift_zero {φ Φ : ℂ → ℂ} (hφ0 : φ 0 = 0) (h : LiftData φ Φ) : Φ 0 = 0 := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [Metric.mem_ball]
  have h1 := (h.2.1 0 h0).1
  rw [neg_zero, show (0 : ℂ) ^ 2 = 0 from by norm_num, hφ0] at h1
  linear_combination h1 / 2

/-- The lift relations give `Φ z ^ 2 = φ (z^2) * (Φ z - 1)`. -/
theorem lift_sq {φ Φ : ℂ → ℂ} (h : LiftData φ Φ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ^ 2 = φ (z ^ 2) * (Φ z - 1) := by
  intro z hz
  have h1 := (h.2.1 z hz).1
  have h2 := (h.2.1 z hz).2
  linear_combination (Φ z) * h1 - h2

/-- The lift never takes the value `1` on the disc. -/
theorem lift_ne_one {φ Φ : ℂ → ℂ} (h : LiftData φ Φ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ≠ 1 := by
  intro z hz hc
  have h' := lift_sq h z hz
  rw [hc] at h'
  norm_num at h'

/-- The reflection of the lift: `Φ (-z) = Φ z / (Φ z - 1)`. -/
theorem lift_neg_eq {φ Φ : ℂ → ℂ} (h : LiftData φ Φ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ (-z) = Φ z / (Φ z - 1) := by
  intro z hz
  have h1 := (h.2.1 z hz).1
  have h2 := (h.2.1 z hz).2
  have hne : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (lift_ne_one h z hz)
  rw [eq_div_iff hne]
  linear_combination h2 - h1

/-- The symmetrisation identity: `φ (z^2) = Φ z ^ 2 / (Φ z - 1)`. -/
theorem phi_sq_eq {φ Φ : ℂ → ℂ} (h : LiftData φ Φ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, φ (z ^ 2) = Φ z ^ 2 / (Φ z - 1) := by
  intro z hz
  rw [eq_div_iff (sub_ne_zero.mpr (lift_ne_one h z hz))]
  exact (lift_sq h z hz).symm

/-- `1 - Φ (-z) = (1 - Φ z)⁻¹`, the multiplicative form of the reflection.
From `Φ z + Φ (-z) = Φ z * Φ (-z)` one gets `(1 - Φ z) * (1 - Φ (-z)) = 1`. -/
theorem one_sub_neg {φ Φ : ℂ → ℂ} (h : LiftData φ Φ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 - Φ (-z) = (1 - Φ z)⁻¹ := by
  intro z hz
  have h1 := (h.2.1 z hz).1
  have h2 := (h.2.1 z hz).2
  have hx : Φ z + Φ (-z) = Φ z * Φ (-z) := by rw [h1, h2]
  have hne : (1 : ℂ) - Φ z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (lift_ne_one h z hz))
  have hkey : (1 - Φ (-z)) * (1 - Φ z) = 1 := by linear_combination -hx
  field_simp
  exact hkey

/-- `φ` has no zero in the punctured unit disc.  (Every `w` in the disc is a square, and
`φ (z^2) = Φ z^2/(Φ z - 1)` vanishes only when `Φ z = 0`.) -/
theorem phi_ne_zero {φ Φ : ℂ → ℂ} (h : LiftData φ Φ) :
    ∀ w ∈ Metric.ball (0 : ℂ) 1, φ w = 0 → w = 0 := by
  intro w hw hw0
  set z : ℂ := Complex.sqrt w with hzdef
  have hzsq : z ^ 2 = w := by rw [hzdef]; exact Work.CPull.sq_sqrt_c w
  have hzn : ‖z‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hzsq]
  have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz1
  have hsq := phi_sq_eq h z hzball
  rw [hzsq, hw0] at hsq
  have hne : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (lift_ne_one h z hzball)
  have hz2 : Φ z ^ 2 = 0 := by
    rw [eq_div_iff hne] at hsq
    simpa using hsq.symm
  have hz2' : Φ z * Φ z = 0 := by rwa [pow_two] at hz2
  have hz0 : z = 0 := h.2.2 z hzball (mul_self_eq_zero.mp hz2')
  rw [← hzsq, hz0]
  simp

/-- **The odd logarithm of `1 - Φ`.**  If `Φ` is holomorphic on the unit disc, `Φ 0 = 0`,
`Φ ≠ 1` and `1 - Φ (-z) = (1 - Φ z)⁻¹` there, then `1 - Φ` has a holomorphic logarithm `ℓ` on
the disc with `ℓ 0 = 0`, `ℓ (-z) = - ℓ z`, and `ℓ = Complex.log (1 - Φ ·)` near `0`. -/
theorem exists_odd_log_phi {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (Metric.ball 0 1))
    (hΦ0 : Φ 0 = 0) (hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ≠ 1)
    (hinv : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 - Φ (-z) = (1 - Φ z)⁻¹) :
    ∃ (ℓ : ℂ → ℂ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧ DifferentiableOn ℂ ℓ (Metric.ball 0 1) ∧ ℓ 0 = 0 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (ℓ z) = 1 - Φ z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, ℓ (-z) = -ℓ z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ℓ z = Complex.log (1 - Φ z)) := by
  have hball0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [Metric.mem_ball]
  have hne' : ∀ z ∈ Metric.ball (0 : ℂ) 1, (1 : ℂ) - Φ z ≠ 0 := fun z hz =>
    sub_ne_zero.mpr (Ne.symm (hne z hz))
  have hneg_maps : Set.MapsTo (fun z : ℂ => -z) (Metric.ball (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    simpa using hz
  -- a holomorphic logarithm of `1 - Φ`
  obtain ⟨L, hLdiff, hLexp⟩ := Work.CPhi.exists_differentiableOn_log_ball (c := 0) (r := 1)
    (V := fun z => (1 : ℂ) - Φ z) ((differentiableOn_const (1 : ℂ)).sub hΦ) hne'
  -- normalise so that `ℓ 0 = 0`
  set ℓ : ℂ → ℂ := fun z => L z - L 0 with hldef
  have hℓdiff : DifferentiableOn ℂ ℓ (Metric.ball 0 1) := by
    rw [hldef]
    exact hLdiff.sub (differentiableOn_const _)
  have hℓ0 : ℓ 0 = 0 := by simp [hldef]
  have hℓexp : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (ℓ z) = (1 : ℂ) - Φ z := by
    intro z hz
    have hL00 : Complex.exp (L 0) = (1 : ℂ) := by
      have h := hLexp 0 hball0
      rwa [hΦ0, sub_zero] at h
    have h := hLexp z hz
    simp only [hldef]
    rw [Complex.exp_sub, h, hL00, div_one]
  -- `ℓ` is odd: `exp (ℓ (-z) + ℓ z) = 1`, and the sum vanishes at `0`
  have hsumdiff : DifferentiableOn ℂ (fun z => ℓ (-z) + ℓ z) (Metric.ball 0 1) :=
    (hℓdiff.comp differentiable_neg.differentiableOn hneg_maps).add hℓdiff
  have hsumexp : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (ℓ (-z) + ℓ z) = 1 := by
    intro z hz
    have hz' : -z ∈ Metric.ball (0 : ℂ) 1 := hneg_maps hz
    rw [Complex.exp_add, hℓexp (-z) hz', hℓexp z hz, hinv z hz]
    exact inv_mul_cancel₀ (hne' z hz)
  have hsumderiv : Set.EqOn (deriv (fun z => ℓ (-z) + ℓ z)) 0 (Metric.ball 0 1) := by
    intro z hz
    have hdz : DifferentiableAt ℂ (fun z => ℓ (-z) + ℓ z) z :=
      hsumdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hc := hdz.hasDerivAt.cexp
    have heq : (fun w => Complex.exp (ℓ (-w) + ℓ w)) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => hsumexp w hw
    have hzero : deriv (fun w => Complex.exp (ℓ (-w) + ℓ w)) z = 0 := by
      rw [heq.deriv_eq]
      simp
    rw [hc.deriv] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _)
  have hconst : ∀ z ∈ Metric.ball (0 : ℂ) 1, ℓ (-z) + ℓ z = 0 := by
    intro z hz
    have h := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      hsumdiff hsumderiv hz hball0
    simpa [hℓ0] using h
  have hodd : ∀ z ∈ Metric.ball (0 : ℂ) 1, ℓ (-z) = -ℓ z := by
    intro z hz
    have h := hconst z hz
    linear_combination h
  -- an explicit radius on which `ℓ` is the principal logarithm
  have hΦcont : ContinuousAt Φ 0 :=
    hΦ.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hℓcont : ContinuousAt ℓ 0 :=
    hℓdiff.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Φ z‖ < 1 / 2 := by
    have h := hΦcont.eventually (Metric.ball_mem_nhds (Φ 0) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h] with z hz
    rw [hΦ0] at hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖ℓ z‖ < Real.pi / 2 := by
    have h := hℓcont.eventually
      (Metric.ball_mem_nhds (ℓ 0) (by positivity : (0 : ℝ) < Real.pi / 2))
    filter_upwards [h] with z hz
    rw [hℓ0] at hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨r₀, hr₀pos, hr₀⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  refine ⟨ℓ, min r₀ 1, lt_min hr₀pos one_pos, min_le_right _ _, hℓdiff, hℓ0, hℓexp, hodd, ?_⟩
  intro z hz
  have hzr : ‖z‖ < r₀ := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨-, hzLsmall⟩ := hr₀ (by rw [dist_zero_right]; exact hzr)
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz1
  have hzim : |(ℓ z).im| < Real.pi / 2 := lt_of_le_of_lt (Complex.abs_im_le_norm _) hzLsmall
  have him1 : -Real.pi < (ℓ z).im := by
    have := (abs_lt.mp hzim).1; linarith [Real.pi_pos]
  have him2 : (ℓ z).im ≤ Real.pi := by
    have := (abs_lt.mp hzim).2; linarith [Real.pi_pos]
  rw [← hℓexp z hzball, Complex.log_exp him1 him2]

end Work.PureP
