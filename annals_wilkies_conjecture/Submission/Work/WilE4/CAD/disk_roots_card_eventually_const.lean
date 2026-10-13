import Mathlib
import Submission.Work.WilLibTS.TS.FiniteProperMapOpen
import Submission.Work.WilE4.CAD.logDeriv_circleIntegral_eq
import Submission.Work.WilE4.CAD.family_eval_eventually_close
import Submission.Work.WilE4.CAD.exists_pos_le_norm_on_sphere

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open Polynomial

/-! ## Two elementary helpers

The main result below is a continuity/stability statement for the number of complex roots of a
family of polynomials in a fixed disk.  The proof rests on two ingredients:

* `logDeriv_circleIntegral_eq` — the argument-principle counting formula for a single complex
  polynomial (the circle integral of the logarithmic derivative counts the roots inside);
* `family_eval_eventually_close` — coefficientwise continuity plus a locally bounded degree makes
  the family of evaluations uniformly close on any bounded set.

The remaining work, done here, is to compare the logarithmic derivatives of two nearby members of
the family and to deduce that the difference of the two (a priori integral) counts has modulus
`< 1`, whence it is `0` because it is an integer. -/

/-- Two natural numbers whose images in `ℂ` differ by less than `1` are equal. -/
lemma nat_eq_of_norm_sub_lt_one {a b : ℕ} (h : ‖((a : ℂ) - (b : ℂ))‖ < 1) : a = b := by
  have hcast : ‖((a : ℂ) - (b : ℂ))‖ = |(a : ℝ) - (b : ℝ)| := by
    simp only [← Complex.ofReal_natCast (n := a), ← Complex.ofReal_natCast (n := b)]
    rw [← Complex.ofReal_sub, Complex.norm_real]
    rfl
  rw [hcast] at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hb : (b : ℝ) - (a : ℝ) ≥ 1 := by
      have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      linarith
    rw [abs_of_nonpos (by linarith : (a : ℝ) - (b : ℝ) ≤ 0)] at h
    linarith
  · have hb : (a : ℝ) - (b : ℝ) ≥ 1 := by
      have : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      linarith
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (a : ℝ) - (b : ℝ))] at h
    linarith

/-- The number of complex roots (with multiplicity) of `q x` in the open disk of centre `z₀` and
radius `ρ` is eventually constant, provided that the coefficients of `q` depend continuously on `x`,
that the degree of `q x` is eventually bounded and that `q x₀` has no root on the boundary circle.

This is the local constancy of the "argument-principle" count: the count equals
`(2πi)⁻¹ ∮ (q x)'/(q x)`, the integral is continuous in `x` by uniform closeness on the compact
circle, and an integer-valued continuous perturbation cannot move by less than `1` unless it stops
moving. -/
theorem disk_roots_card_eventually_const {m : ℕ} (q : (Fin m → ℝ) → Polynomial ℂ) (d : ℕ)
    (hcont : ∀ k : ℕ, Continuous fun x : Fin m → ℝ => (q x).coeff k)
    (x₀ : Fin m → ℝ)
    (hdeg : ∀ᶠ x in nhds x₀, (q x).natDegree ≤ d)
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hno : ∀ z : ℂ, dist z z₀ = ρ → (q x₀).eval z ≠ 0) :
    ∀ᶠ x in nhds x₀,
      ((q x).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card
        = ((q x₀).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card := by
  classical
  -- a positive uniform lower bound for `‖(q x₀).eval ·‖` on the boundary circle
  obtain ⟨mm, hmm_pos, hmm⟩ := exists_pos_le_norm_on_sphere (q x₀) z₀ ρ hno
  -- coefficientwise continuity of the derivative family
  have hcontD : ∀ k : ℕ, Continuous fun x : Fin m → ℝ => ((q x).derivative).coeff k := by
    intro k
    have hfun : (fun x : Fin m → ℝ => ((q x).derivative).coeff k)
        = fun x => (q x).coeff (k + 1) * ((k : ℂ) + 1) := by
      funext x; rw [Polynomial.coeff_derivative]
    rw [hfun]
    exact (hcont (k + 1)).mul continuous_const
  -- degree bounds
  have hdegD : ∀ᶠ x in nhds x₀, ((q x).derivative).natDegree ≤ d :=
    hdeg.mono fun x hx => le_trans (Polynomial.natDegree_derivative_le (q x))
      (le_trans (Nat.sub_le _ _) hx)
  have hdeg₀ : (q x₀).natDegree ≤ d := hdeg.self_of_nhds
  have hdegD₀ : ((q x₀).derivative).natDegree ≤ d :=
    le_trans (Polynomial.natDegree_derivative_le (q x₀)) (le_trans (Nat.sub_le _ _) hdeg₀)
  -- the numerator family `(q x)' * (q x₀) - (q x₀)' * (q x)`
  set P : (Fin m → ℝ) → Polynomial ℂ :=
    fun x => (q x).derivative * (q x₀) - (q x₀).derivative * (q x) with hP
  have hcontP : ∀ k : ℕ, Continuous fun x : Fin m → ℝ => (P x).coeff k := by
    intro k
    have hfun : (fun x : Fin m → ℝ => (P x).coeff k)
        = fun x => ((q x).derivative * (q x₀)).coeff k - ((q x₀).derivative * (q x)).coeff k := by
      funext x
      rw [hP]
      simp
    rw [hfun]
    apply Continuous.sub
    · have h2 : (fun x : Fin m → ℝ => ((q x).derivative * (q x₀)).coeff k)
          = fun x => ∑ i ∈ Finset.HasAntidiagonal.antidiagonal k,
              ((q x).derivative).coeff i.1 * (q x₀).coeff i.2 := by
        funext x; rw [Polynomial.coeff_mul]
      rw [h2]
      exact continuous_finsetSum _ (fun i _ => (hcontD i.1).mul continuous_const)
    · have h2 : (fun x : Fin m → ℝ => ((q x₀).derivative * (q x)).coeff k)
          = fun x => ∑ i ∈ Finset.HasAntidiagonal.antidiagonal k,
              ((q x₀).derivative).coeff i.1 * (q x).coeff i.2 := by
        funext x; rw [Polynomial.coeff_mul]
      rw [h2]
      exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hcont i.2))
  have hdegP : ∀ᶠ x in nhds x₀, (P x).natDegree ≤ 2 * d := by
    filter_upwards [hdeg] with x hx
    have hxd : ((q x).derivative).natDegree ≤ d :=
      le_trans (Polynomial.natDegree_derivative_le (q x)) (le_trans (Nat.sub_le _ _) hx)
    rw [hP]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [two_mul]; exact add_le_add hxd hdeg₀
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [two_mul]; exact add_le_add hdegD₀ hx
  -- numerical constants
  set C : ℝ := 1 / (2 * ρ) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hrhoC : ρ * C < 1 := by
    rw [hC, mul_one_div, div_lt_one (by positivity)]; linarith
  set εP : ℝ := C * (mm / 2) * mm with hεP
  have hεPpos : 0 < εP := by rw [hεP]; positivity
  set K : ℝ := ‖z₀‖ + ρ with hK
  have hmm2pos : 0 < mm / 2 := by linarith
  -- eventual uniform closeness of the numerator and of the family itself
  have hPclose : ∀ᶠ x in nhds x₀, ∀ z : ℂ, ‖z‖ ≤ K → ‖(P x).eval z‖ ≤ εP := by
    filter_upwards [family_eval_eventually_close P (2 * d) hcontP x₀ hdegP K hεPpos] with x hx
    intro z hz
    have h0 : (P x₀).eval z = 0 := by rw [hP]; simp
    have := hx z hz
    rwa [h0, sub_zero] at this
  have hqclose : ∀ᶠ x in nhds x₀, ∀ z : ℂ, ‖z‖ ≤ K → ‖(q x).eval z - (q x₀).eval z‖ ≤ mm / 2 :=
    family_eval_eventually_close q d hcont x₀ hdeg K hmm2pos
  -- points of the circle satisfy `‖z‖ ≤ K`
  have hZK : ∀ z : ℂ, dist z z₀ = ρ → ‖z‖ ≤ K := by
    intro z hz
    have h1 : ‖z - z₀‖ = ρ := by rw [← dist_eq_norm]; exact hz
    rw [hK]
    calc ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ = ρ + ‖z₀‖ := by rw [h1]
      _ = ‖z₀‖ + ρ := by ring
  filter_upwards [hPclose, hqclose] with x hPx hqx
  -- `q x` does not vanish on the circle
  have hlower : ∀ z : ℂ, dist z z₀ = ρ → mm / 2 ≤ ‖(q x).eval z‖ := by
    intro z hz
    have h1 := hqx z (hZK z hz)
    have h2 := hmm z hz
    have h3 : ‖(q x₀).eval z‖ ≤ ‖(q x).eval z‖ + ‖(q x).eval z - (q x₀).eval z‖ := by
      have h := norm_sub_le ((q x).eval z) ((q x).eval z - (q x₀).eval z)
      have he : (q x).eval z - ((q x).eval z - (q x₀).eval z) = (q x₀).eval z := by ring
      rwa [he] at h
    linarith
  set ld : ℂ → ℂ := fun z => (q x).derivative.eval z / (q x).eval z with hld
  set ld₀ : ℂ → ℂ := fun z => (q x₀).derivative.eval z / (q x₀).eval z with hld0
  have hne_x : ∀ z : ℂ, dist z z₀ = ρ → (q x).eval z ≠ 0 := by
    intro z hz h0
    have := hlower z hz; rw [h0, norm_zero] at this; linarith
  have hne_0 : ∀ z : ℂ, dist z z₀ = ρ → (q x₀).eval z ≠ 0 := by
    intro z hz h0
    have := hmm z hz; rw [h0, norm_zero] at this; linarith
  -- the logarithmic derivatives differ by at most `C` on the circle
  have hdiff : ∀ z : ℂ, dist z z₀ = ρ → ‖ld z - ld₀ z‖ ≤ C := by
    intro z hz
    have hDpos : 0 < ‖(q x).eval z‖ * ‖(q x₀).eval z‖ :=
      mul_pos (lt_of_lt_of_le hmm2pos (hlower z hz)) (lt_of_lt_of_le hmm_pos (hmm z hz))
    have hzx : (q x).eval z ≠ 0 := hne_x z hz
    have hz0 : (q x₀).eval z ≠ 0 := hne_0 z hz
    have hkey : ld z - ld₀ z = (P x).eval z / ((q x).eval z * (q x₀).eval z) := by
      rw [hld, hld0, hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul]
      field_simp
    rw [hkey, norm_div, norm_mul, div_le_iff₀ hDpos]
    calc ‖(P x).eval z‖ ≤ εP := hPx z (hZK z hz)
      _ = C * (mm / 2 * mm) := by rw [hεP]; ring
      _ ≤ C * (‖(q x).eval z‖ * ‖(q x₀).eval z‖) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          exact mul_le_mul (hlower z hz) (hmm z hz) hmm_pos.le (by positivity)
  -- both logarithmic derivatives are circle integrable
  have hci_x : CircleIntegrable ld z₀ ρ :=
    ContinuousOn.circleIntegrable hρ.le (by
      rw [hld]
      exact ((q x).derivative.continuous.continuousOn).div ((q x).continuous.continuousOn)
        (fun z hz => hne_x z (by rwa [Metric.mem_sphere] at hz)))
  have hci_0 : CircleIntegrable ld₀ z₀ ρ :=
    ContinuousOn.circleIntegrable hρ.le (by
      rw [hld0]
      exact ((q x₀).derivative.continuous.continuousOn).div ((q x₀).continuous.continuousOn)
        (fun z hz => hne_0 z (by rwa [Metric.mem_sphere] at hz)))
  have hIntSub : (∮ z in C(z₀, ρ), (ld z - ld₀ z))
      = (∮ z in C(z₀, ρ), ld z) - (∮ z in C(z₀, ρ), ld₀ z) :=
    circleIntegral.integral_sub hci_x hci_0
  -- the counting formula applied to both fibres
  have hcnt_x : (∮ z in C(z₀, ρ), ld z)
      = 2 * Real.pi * Complex.I * (((q x).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card : ℂ) := by
    rw [hld]
    exact logDeriv_circleIntegral_eq (q x) z₀ hρ hne_x
  have hcnt_0 : (∮ z in C(z₀, ρ), ld₀ z)
      = 2 * Real.pi * Complex.I * (((q x₀).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card : ℂ) := by
    rw [hld0]
    exact logDeriv_circleIntegral_eq (q x₀) z₀ hρ hno
  -- the difference of the two counts, read as a complex number, is a small integral
  have hNrm : ‖(((q x).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card : ℂ)
      - (((q x₀).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card : ℂ)‖ ≤ ρ * C := by
    have hkey : (((q x).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card : ℂ)
        - (((q x₀).roots.filter (fun z : ℂ => dist z z₀ < ρ)).card : ℂ)
        = (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(z₀, ρ), (ld z - ld₀ z) := by
      rw [hIntSub, hcnt_x, hcnt_0]
      have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Complex.I_ne_zero, Real.pi_ne_zero]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hI, one_mul, ← mul_assoc, inv_mul_cancel₀ hI,
        one_mul]
    rw [hkey]
    have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      have he : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    calc ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ z in C(z₀, ρ), (ld z - ld₀ z)‖
        = ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * ‖∮ z in C(z₀, ρ), (ld z - ld₀ z)‖ := norm_mul _ _
      _ = (2 * Real.pi)⁻¹ * ‖∮ z in C(z₀, ρ), (ld z - ld₀ z)‖ := by rw [norm_inv, h2pi]
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ρ * C) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact circleIntegral.norm_integral_le_of_norm_le_const hρ.le
            (fun z hz => hdiff z (by rwa [Metric.mem_sphere] at hz))
      _ = ρ * C := by field_simp
  exact nat_eq_of_norm_sub_lt_one (lt_of_le_of_lt hNrm hrhoC)

end Work.WilE4.CAD
