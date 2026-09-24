import Mathlib
import Submission.Work.GM.Energy.EnergyCore.FourthMomentDefs

/-!
# Locality of `Gsum` (GM §11, Lemma 11.3 / 11.7 shape)

The paper's locality principle: a Dirichlet polynomial of length `~N` at a point `t` is bounded by
its average over a unit window plus a small "tail" term.  Here we take that principle as a
hypothesis `hloc` (it is the statement GM Lemma 11.3 proves, in the form the `Energy` area needs),
and derive the squared form used by the fourth-moment argument: if `τ` and `d` are within `1` of
each other, then `‖Gsum M τ‖²` is controlled by the `L²` mass of `Gsum` on the doubled window
`[d - 2K, d + 2K]`.

The proof is elementary: apply `hloc` with trivial coefficients, square (`(x+y)² ≤ 2x² + 2y²`),
Cauchy–Schwarz on the window integral and monotonicity of the integral under the inclusion
`[τ-K, τ+K] ⊆ [d-2K, d+2K]` (valid since `|τ-d| ≤ 1 ≤ K`).
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset MeasureTheory
open scoped BigOperators
set_option autoImplicit false

/-- `Gsum` written with trivial coefficients, the shape in which the locality hypothesis
`hloc` is fed. -/
lemma Gsum_eq_sum_one (M : ℕ) (u : ℝ) :
    Gsum M u = ∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (u : ℂ)) := by
  rw [Gsum]
  exact Finset.sum_congr rfl (fun n _ => by simp)

/-- `u ↦ Gsum M u` is continuous (a finite sum of continuous characters). -/
lemma continuous_Gsum {M : ℕ} (hM : 1 ≤ M) : Continuous fun u : ℝ => Gsum M u := by
  unfold Gsum
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn1 : 1 ≤ n := le_trans hM (Finset.mem_Icc.mp hn).1
  have hb : (n : ℂ) ≠ 0 := by
    have hnne : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    exact_mod_cast hnne
  exact (continuous_const.mul Complex.continuous_ofReal).const_cpow (Or.inl hb)

/-- **Cauchy–Schwarz.** For a continuous nonnegative `f` on `[a,b]`,
`(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
lemma sq_integral_le_mul_integral_sq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hfu : ContinuousOn f (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hf2u : ContinuousOn (fun x => f x ^ 2) (Set.uIcc a b) := hfu.pow 2
  have hfI : IntervalIntegrable f volume a b := hfu.intervalIntegrable
  have hf2I : IntervalIntegrable (fun x => f x ^ 2) volume a b := hf2u.intervalIntegrable
  -- the quadratic `t ↦ ∫ (t - f)²` is nonnegative
  have hQuad : ∀ t : ℝ, 0 ≤ t ^ 2 * (b - a) - 2 * t * (∫ x in a..b, f x)
      + ∫ x in a..b, f x ^ 2 := by
    intro t
    have hnonneg : 0 ≤ ∫ x in a..b, (t - f x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : ∫ x in a..b, (t - f x) ^ 2
        = t ^ 2 * (b - a) - 2 * t * (∫ x in a..b, f x) + ∫ x in a..b, f x ^ 2 := by
      have h1 : IntervalIntegrable (fun x : ℝ => t ^ 2) volume a b := intervalIntegrable_const
      have h2 : IntervalIntegrable (fun x : ℝ => 2 * t * f x) volume a b :=
        (continuousOn_const.mul hfu).intervalIntegrable
      calc ∫ x in a..b, (t - f x) ^ 2
          = ∫ x in a..b, (t ^ 2 - 2 * t * f x + f x ^ 2) := by
            apply intervalIntegral.integral_congr
            intro x _; ring
        _ = (∫ x in a..b, (t ^ 2 - 2 * t * f x)) + ∫ x in a..b, f x ^ 2 :=
            intervalIntegral.integral_add (h1.sub h2) hf2I
        _ = ((∫ x in a..b, t ^ 2) - ∫ x in a..b, 2 * t * f x) + ∫ x in a..b, f x ^ 2 := by
            rw [intervalIntegral.integral_sub h1 h2]
        _ = t ^ 2 * (b - a) - 2 * t * (∫ x in a..b, f x) + ∫ x in a..b, f x ^ 2 := by
            rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
            simp only [smul_eq_mul]
            ring
    rw [hexp] at hnonneg
    exact hnonneg
  rcases eq_or_lt_of_le (sub_nonneg.mpr hab) with hB | hBpos
  · -- degenerate case `b = a`
    have hba : b = a := by linarith
    rw [hba, intervalIntegral.integral_same, intervalIntegral.integral_same]
    simp
  · -- evaluate the quadratic at `t = C/B`
    have h := hQuad ((∫ x in a..b, f x) / (b - a))
    have he : ((∫ x in a..b, f x) / (b - a)) ^ 2 * (b - a)
          - 2 * ((∫ x in a..b, f x) / (b - a)) * (∫ x in a..b, f x)
          + ∫ x in a..b, f x ^ 2
        = (∫ x in a..b, f x ^ 2) - (∫ x in a..b, f x) ^ 2 / (b - a) := by
      field_simp
      ring
    rw [he] at h
    have hle : (∫ x in a..b, f x) ^ 2 / (b - a) ≤ ∫ x in a..b, f x ^ 2 := by linarith
    rw [div_le_iff₀ hBpos] at hle
    linarith

/-- **Locality of `Gsum`.**  Given the locality hypothesis `hloc` for Dirichlet polynomials of
length `~N` (GM Lemma 11.3), the value `‖Gsum M τ‖²` at a point `τ` is bounded by the `L²` mass of
`Gsum` on the window `[d-2K, d+2K]` (for any `d` with `|τ-d| ≤ 1`) plus the square of the tail
error. -/
theorem locality_Gsum (m : ℕ) (Cloc K : ℝ) (M : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hCloc : 0 < Cloc)
    (hloc : ∀ (N' : ℕ), 1 ≤ N' → ∀ (a : ℕ → ℂ), ∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖∑ n ∈ Finset.Icc N' (2 * N'), a n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤
          Cloc * (∫ u in t - K..t + K,
                    ‖∑ n ∈ Finset.Icc N' (2 * N'), a n * (n : ℂ) ^ (Complex.I * (u : ℂ))‖)
            + Cloc / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N' (2 * N'), ‖a n‖))
    (τ d : ℝ) (hd : |τ - d| ≤ 1) :
    ‖Gsum M τ‖ ^ 2 ≤ 4 * K * Cloc ^ 2 * (∫ u in d - 2 * K..d + 2 * K, ‖Gsum M u‖ ^ 2)
      + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 := by
  classical
  set Iw : ℝ := ∫ u in τ - K..τ + K, ‖Gsum M u‖ with hIw
  set Sw : ℝ := ∫ u in τ - K..τ + K, ‖Gsum M u‖ ^ 2 with hSw
  set S : ℝ := ∫ u in d - 2 * K..d + 2 * K, ‖Gsum M u‖ ^ 2 with hS
  set Bb : ℝ := Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1) with hB
  have hGcont : Continuous fun u : ℝ => Gsum M u := continuous_Gsum hM
  have hGnorm : Continuous fun u : ℝ => ‖Gsum M u‖ := hGcont.norm
  have hGsq : Continuous fun u : ℝ => ‖Gsum M u‖ ^ 2 := hGnorm.pow 2
  -- geometry of the windows
  have hτd := abs_le.mp hd
  have hab : τ - K ≤ τ + K := by linarith
  have hca : d - 2 * K ≤ τ - K := by linarith [hτd.2, hK]
  have hbd : τ + K ≤ d + 2 * K := by linarith [hτd.1, hK]
  -- (1) the locality hypothesis with trivial coefficients
  have hstep : ‖Gsum M τ‖ ≤ Cloc * Iw + Bb := by
    have h := hloc M hM (fun _ : ℕ => (1 : ℂ)) K hK τ
    have hint_eq : (∫ u in τ - K..τ + K,
        ‖∑ n ∈ Finset.Icc M (2 * M), (1 : ℂ) * (n : ℂ) ^ (Complex.I * (u : ℂ))‖) = Iw := by
      rw [hIw]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [Gsum_eq_sum_one M u]
    have hsum1 : (∑ n ∈ Finset.Icc M (2 * M), ‖(1 : ℂ)‖) = ((M : ℝ) + 1) := by
      have hcard : (Finset.Icc M (2 * M)).card = M + 1 := by
        rw [Nat.card_Icc]
        omega
      simp only [norm_one]
      rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [← Gsum_eq_sum_one M τ, hint_eq, hsum1, ← hB] at h
    exact h
  -- (2) Cauchy–Schwarz on the window `[τ-K, τ+K]`
  have hCS : Iw ^ 2 ≤ (2 * K) * Sw := by
    rw [hIw, hSw]
    have h := sq_integral_le_mul_integral_sq hab hGnorm.continuousOn
    have hsub : (τ + K) - (τ - K) = 2 * K := by ring
    rwa [hsub] at h
  -- (3) monotonicity of the integral under enlarging the window
  have hmono : Sw ≤ S := by
    rw [hSw, hS]
    exact intervalIntegral.integral_mono_interval hca hab hbd
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hGsq.intervalIntegrable (d - 2 * K) (d + 2 * K))
  -- (4) square the locality bound and feed in (2), (3)
  have hA : 2 * (Cloc * Iw) ^ 2 ≤ 4 * K * Cloc ^ 2 * S := by
    have hK0 : 0 ≤ 2 * K := by linarith
    have h1 : Iw ^ 2 ≤ 2 * K * S :=
      le_trans hCS (mul_le_mul_of_nonneg_left hmono hK0)
    have h2 : Cloc ^ 2 * Iw ^ 2 ≤ Cloc ^ 2 * (2 * K * S) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg Cloc)
    nlinarith [h2]
  have hsq : ‖Gsum M τ‖ ^ 2 ≤ 2 * (Cloc * Iw) ^ 2 + 2 * Bb ^ 2 := by
    have h0 : 0 ≤ ‖Gsum M τ‖ := norm_nonneg _
    have hs1 : ‖Gsum M τ‖ ^ 2 ≤ (Cloc * Iw + Bb) ^ 2 := by
      have := mul_self_le_mul_self h0 hstep
      simpa [pow_two] using this
    have hs2 : (Cloc * Iw + Bb) ^ 2 ≤ 2 * (Cloc * Iw) ^ 2 + 2 * Bb ^ 2 := by
      nlinarith [sq_nonneg (Cloc * Iw - Bb)]
    linarith
  have hfinal : ‖Gsum M τ‖ ^ 2 ≤ 4 * K * Cloc ^ 2 * S + 2 * Bb ^ 2 := by linarith
  exact hfinal

end Work.GM.Energy.EnergyCore
