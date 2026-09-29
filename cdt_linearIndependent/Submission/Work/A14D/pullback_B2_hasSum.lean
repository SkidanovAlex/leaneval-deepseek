import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C7.g_form
import Submission.Work.PureP.hasSum_coeff_B2_yps

/-!
# The HasSum form of the pullback of `B₂` along `y = x²/(x−1)` on the unit disc

`Submission.CDTPlan.B2.subst Submission.CDT.sympY` is the formal power series `B₂ ∘ y`,
`y = x²/(x−1)`.  Its coefficients are the Taylor coefficients of the analytic function
`2y − c·log(1−x)` on the unit disc (`c = x(x−2)/(x−1)`), the pullback identity
`Work.C7.g_form.1`.  We prove that the coefficient series of the composite converges, for every
`‖z‖ < 1`, to that function.

Unlike the small-disc statements `Work.PureP.hasSum_coeff_B2_yps` (which sum the *inner* series
`Σ aₙ y(z)ⁿ`, valid for `‖y(z)‖ < 4`), the coefficient series of the composite has genuinely
harmonic-size coefficients and converges on the whole unit disc; the proof therefore goes through
the Cauchy product of the two convergent series `c` and `log(1−x)`, not through `evp_subst`.
-/

namespace Work.A14D

open Complex Metric
open PowerSeries

theorem pullback_B2_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDTPlan.B2.subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ n)
      (2 * (z ^ 2 / (z - 1)) - (z * (z - 2) / (z - 1)) * Complex.log (1 - z)) := by
  -- the formal pullback identity `B₂ ∘ y = 2y − c·L`
  have hform : Submission.CDTPlan.B2.subst Submission.CDT.sympY
      = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps := by
    have h := Work.C7.g_form.1
    have hg1 : Work.C7.g 1 = Submission.CDTPlan.B2.subst Work.C7.yps := by
      simp [Work.C7.g, Submission.CDTPlan.pureB]
    rw [hg1] at h
    exact h
  have hgeom : Summable fun n : ℕ => ‖z‖ ^ n :=
    summable_geometric_of_norm_lt_one (by simpa using hz)
  -- ## the coefficient series of `y = x²/(x−1)`
  have hYn : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖z‖ ^ n := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeom
    rw [Work.CPull.coeff_sympY_eq n]
    split_ifs <;> simp
  have hY : Summable fun n : ℕ => ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n :=
    (hYn.congr (fun n => by rw [norm_mul, norm_pow])).of_norm
  have hYval : (∑' n : ℕ, ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n)
      = z ^ 2 / (z - 1) := by
    simpa [Work.CPull.evp] using (Work.CPull.evp_sympPhi z hz).2
  have hYsum : HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n) (z ^ 2 / (z - 1)) :=
    hYval ▸ hY.hasSum
  -- ## the coefficient series of `2y`
  have h2Ysum : HasSum (fun n : ℕ => ((PowerSeries.coeff n (2 * Work.C7.yps) : ℚ) : ℂ) * z ^ n)
      (2 * (z ^ 2 / (z - 1))) := by
    have h' : HasSum (fun n : ℕ => 2 * (((PowerSeries.coeff n Work.C7.yps : ℚ) : ℂ) * z ^ n))
        (2 * (z ^ 2 / (z - 1))) := hYsum.mul_left 2
    refine h'.congr_fun fun n => ?_
    rw [show (2 * Work.C7.yps : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) * Work.C7.yps from rfl,
      PowerSeries.coeff_C_mul]
    push_cast
    ring
  -- ## the coefficient series of `c = x(x−2)/(x−1)`
  have hCn : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ) * z ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeom.mul_left 2)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (Work.PureP.norm_coeff_cfun_le n) (by positivity)
  have hCval : (∑' n : ℕ, ((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ) * z ^ n)
      = z * (z - 2) / (z - 1) := by
    simpa [Work.CPull.evp] using Work.PureP.evp_cfun z hz
  -- ## the coefficient series of `L = log(1−x)`
  have hLsum : HasSum (fun n : ℕ => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n)
      (Complex.log (1 - z)) := Work.C7.hasSum_Lps hz
  have hLn : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n‖ :=
    hLsum.summable.norm
  -- ## the Cauchy product `c·L`
  have hconvN : Summable fun n : ℕ => ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (((PowerSeries.coeff kl.1 Work.C7.cfun : ℚ) : ℂ) * z ^ kl.1)
          * (((PowerSeries.coeff kl.2 Work.C7.Lps : ℚ) : ℂ) * z ^ kl.2)‖ :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => ((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ) * z ^ n)
      (g := fun n => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n) hCn hLn
  have hkey := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (f := fun n => ((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ) * z ^ n)
      (g := fun n => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n) hCn hLn
  have hvalP : (∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (((PowerSeries.coeff kl.1 Work.C7.cfun : ℚ) : ℂ) * z ^ kl.1)
          * (((PowerSeries.coeff kl.2 Work.C7.Lps : ℚ) : ℂ) * z ^ kl.2))
      = (z * (z - 2) / (z - 1)) * Complex.log (1 - z) := by
    rw [← hkey, hCval, hLsum.tsum_eq]
  have hconvSum : HasSum (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (((PowerSeries.coeff kl.1 Work.C7.cfun : ℚ) : ℂ) * z ^ kl.1)
          * (((PowerSeries.coeff kl.2 Work.C7.Lps : ℚ) : ℂ) * z ^ kl.2))
      ((z * (z - 2) / (z - 1)) * Complex.log (1 - z)) :=
    hvalP ▸ hconvN.of_norm.hasSum
  have hcoeff : ∀ n : ℕ, ((PowerSeries.coeff n (Work.C7.cfun * Work.C7.Lps) : ℚ) : ℂ) * z ^ n
      = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (((PowerSeries.coeff kl.1 Work.C7.cfun : ℚ) : ℂ) * z ^ kl.1)
            * (((PowerSeries.coeff kl.2 Work.C7.Lps : ℚ) : ℂ) * z ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [← hp', pow_add]
    ring
  have hprodSum : HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Work.C7.cfun * Work.C7.Lps) : ℚ) : ℂ) * z ^ n)
      ((z * (z - 2) / (z - 1)) * Complex.log (1 - z)) :=
    hconvSum.congr_fun fun n => hcoeff n
  -- ## assembly
  refine (h2Ysum.sub hprodSum).congr_fun fun n => ?_
  rw [hform, map_sub]
  push_cast
  ring

end Work.A14D
