import Mathlib
import Submission.Work.CPull.germs
import Submission.Work.CPull.hasSum_coeff_B3_yps
import Submission.Work.CPhi.exists_differentiableOn_log_ball
import Submission.Work.CPsi.psiC_facts

/-!
# Area CPull — the germ of `B₃ ∘ φ_C` with denominator `1` (numerator exhibited)

The target `Work.CPull.germ_B3`: for a holomorphic lift `Φ` of `z ↦ φ_C (z²)` through
`y = x²/(x−1)` (the two relations of `PhiLift`), the germ at `0` of
`Σₙ [yⁿ]B₃ · φ_C(w)ⁿ` is the germ of a function `N` holomorphic on the whole unit disc.

The proof.  Write `g = 1 - Φ`; the lift relation gives `g(-z) = 1/g(z)`, so `g` is a zero free
holomorphic function on the disc, and `Work.CPhi.exists_differentiableOn_log_ball` produces a
holomorphic logarithm `L`, normalised to `L₀ = L - L 0`.  The identity
`exp (L₀ (-z) + L₀ z) = g(-z)·g(z) = 1`, together with holomorphy and `L₀ 0 = 0`, forces
`L₀ (-z) + L₀ z = 0`: `L₀` is odd.  Hence

`E z = -(1/2)·L₀ z ²`

is holomorphic and even on the disc.  Near `0`, `L₀ z = Complex.log (1 - Φ z)` (the principal
logarithm of a point near `1` inverts `exp`), and `φ_C (z²) = Φ z ² /(Φ z - 1)`, so
`E z = -(1/2)·log (1 - Φ z)² = Σₙ [yⁿ]B₃ · φ_C(z²)ⁿ` by `hasSum_coeff_B3_yps`.
`germ_of_even` (even descent through the square map) converts this into the germ of
`Σₙ [yⁿ]B₃ · φ_C(w)ⁿ`.
-/

namespace Work.CPull

open Complex Metric Filter
open scoped Topology

private lemma phiC_at_zero : Submission.CDTPlan.phiC (0 : ℂ) = 0 := by
  simp [Submission.CDTPlan.phiC, Submission.CDTPlan.hauptH, Work.CPsi.psiC_zero]

theorem germ_B3 (Φ : ℂ → ℂ) (hΦ : DifferentiableOn ℂ Φ (Metric.ball 0 1))
    (hΦneq : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z ≠ 1)
    (hrel : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z + Φ (-z) = Submission.CDTPlan.phiC (z^2) ∧
      Φ z * Φ (-z) = Submission.CDTPlan.phiC (z^2)) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in nhds (0:ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ) * Submission.CDTPlan.phiC w ^ n) (N w) := by
  have hball0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [Metric.mem_ball]
  -- `Φ 0 = 0`
  have hPhi0 : Φ 0 = 0 := by
    have h := (hrel 0 hball0).1
    rw [neg_zero, show (0 : ℂ) ^ 2 = 0 from by norm_num, phiC_at_zero] at h
    linear_combination h / 2
  -- `1 - Φ z ≠ 0` on the disc
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, (1 : ℂ) - Φ z ≠ 0 := fun z hz =>
    sub_ne_zero.mpr (hΦneq z hz).symm
  have hneg_maps : Set.MapsTo (fun z : ℂ => -z) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    simpa using hz
  -- `1 - Φ (-z) = (1 - Φ z)⁻¹`
  have hinv : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 - Φ (-z) = (1 - Φ z)⁻¹ := by
    intro z hz
    have h1 := (hrel z hz).1
    have h2 := (hrel z hz).2
    have hx : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (hΦneq z hz)
    have hx' : (1 : ℂ) - Φ z ≠ 0 := hne z hz
    have hkey : Φ (-z) * (Φ z - 1) = Φ z := by
      have hc : Φ z + Φ (-z) = Φ z * Φ (-z) := by rw [h1, h2]
      linear_combination -hc
    have hval : Φ (-z) = Φ z / (Φ z - 1) := by
      rw [eq_div_iff hx]
      exact hkey
    rw [hval]
    field_simp
    ring
  -- `φ_C (z²) = Φ z ² / (Φ z - 1)`
  have hphiC_sq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Submission.CDTPlan.phiC (z ^ 2) = Φ z ^ 2 / (Φ z - 1) := by
    intro z hz
    have h1 := (hrel z hz).1
    have h2 := (hrel z hz).2
    rw [eq_div_iff (sub_ne_zero.mpr (hΦneq z hz))]
    linear_combination - (Φ z) * h1 + h2
  -- a holomorphic logarithm of `1 - Φ` on the disc
  obtain ⟨L, hLdiff, hLexp⟩ := Work.CPhi.exists_differentiableOn_log_ball (c := 0) (r := 1)
    (V := fun z => (1 : ℂ) - Φ z) ((differentiableOn_const (1 : ℂ)).sub hΦ) hne
  -- normalise so that `L₀ 0 = 0`
  set L₀ : ℂ → ℂ := fun z => L z - L 0 with hL₀def
  have hL₀diff : DifferentiableOn ℂ L₀ (Metric.ball 0 1) := by
    rw [hL₀def]
    exact hLdiff.sub (differentiableOn_const _)
  have hL₀0 : L₀ 0 = 0 := by simp [hL₀def]
  have hL₀exp : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (L₀ z) = (1 : ℂ) - Φ z := by
    intro z hz
    have hL00 : Complex.exp (L 0) = (1 : ℂ) := by
      have h := hLexp 0 hball0
      rwa [hPhi0, sub_zero] at h
    have h := hLexp z hz
    simp only [hL₀def]
    rw [Complex.exp_sub, h, hL00, div_one]
  -- `L₀` is odd
  have hφdiff : DifferentiableOn ℂ (fun z => L₀ (-z) + L₀ z) (Metric.ball 0 1) :=
    (hL₀diff.comp differentiable_neg.differentiableOn hneg_maps).add hL₀diff
  have hφexp : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (L₀ (-z) + L₀ z) = 1 := by
    intro z hz
    have hz' : -z ∈ Metric.ball (0 : ℂ) 1 := hneg_maps hz
    rw [Complex.exp_add, hL₀exp (-z) hz', hL₀exp z hz, hinv z hz]
    exact inv_mul_cancel₀ (hne z hz)
  have hφderiv : Set.EqOn (deriv (fun z => L₀ (-z) + L₀ z)) 0 (Metric.ball 0 1) := by
    intro z hz
    have hdz : DifferentiableAt ℂ (fun z => L₀ (-z) + L₀ z) z :=
      hφdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hc := hdz.hasDerivAt.cexp
    have heq : (fun w => Complex.exp (L₀ (-w) + L₀ w)) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => hφexp w hw
    have hzero : deriv (fun w => Complex.exp (L₀ (-w) + L₀ w)) z = 0 := by
      rw [heq.deriv_eq]
      simp
    rw [hc.deriv] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _)
  have hconst : ∀ z ∈ Metric.ball (0 : ℂ) 1, L₀ (-z) + L₀ z = 0 := by
    intro z hz
    have h := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      hφdiff hφderiv hz hball0
    simpa [hL₀0] using h
  have hodd : ∀ z ∈ Metric.ball (0 : ℂ) 1, L₀ (-z) = -L₀ z := by
    intro z hz
    have h := hconst z hz
    linear_combination h
  -- the even holomorphic auxiliary function
  set E : ℂ → ℂ := fun z => -(1 / 2 : ℂ) * L₀ z ^ 2 with hEdef
  have hEdiff : DifferentiableOn ℂ E (Metric.ball 0 1) := by
    rw [hEdef]
    exact (hL₀diff.pow 2).const_mul _
  have heven : ∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z := by
    intro z hz
    show -(1 / 2 : ℂ) * L₀ (-z) ^ 2 = -(1 / 2 : ℂ) * L₀ z ^ 2
    rw [hodd z hz]
    ring
  -- the germ identity
  have hgerm : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ) *
        Submission.CDTPlan.phiC (z ^ 2) ^ n) (E z) := by
    have hΦcont : ContinuousAt Φ 0 :=
      hΦ.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    have hsmall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Φ z‖ < 1 / 2 := by
      have h := hΦcont.eventually (Metric.ball_mem_nhds (Φ 0) (by norm_num : (0 : ℝ) < 1 / 2))
      filter_upwards [h] with z hz
      rw [hPhi0] at hz
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hL₀cont : ContinuousAt L₀ 0 :=
      hL₀diff.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    have hLsmall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖L₀ z‖ < Real.pi / 2 := by
      have h := hL₀cont.eventually
        (Metric.ball_mem_nhds (L₀ 0) (by positivity : (0 : ℝ) < Real.pi / 2))
      filter_upwards [h] with z hz
      rw [hL₀0] at hz
      simpa [Metric.mem_ball, dist_zero_right] using hz
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos, hsmall, hLsmall] with z hzball hzsmall hzLsmall
    have him : |(L₀ z).im| < Real.pi / 2 := lt_of_le_of_lt (Complex.abs_im_le_norm _) hzLsmall
    have hzlog : Complex.log (1 - Φ z) = L₀ z := by
      have h1 : -Real.pi < (L₀ z).im := by
        have := (abs_lt.mp him).1
        linarith [Real.pi_pos]
      have h2 : (L₀ z).im ≤ Real.pi := by
        have := (abs_lt.mp him).2
        linarith [Real.pi_pos]
      rw [← hL₀exp z hzball, Complex.log_exp h1 h2]
    have hmain := hasSum_coeff_B3_yps (Φ z) hzsmall
    rw [hzlog] at hmain
    refine hmain.congr_fun (fun n => ?_)
    rw [hphiC_sq z hzball]
  exact germ_of_even hEdiff heven hgerm

end Work.CPull
