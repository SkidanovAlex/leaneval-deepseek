import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.IonescuWainger.tsum_two_scale_bound
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mstHat_decay
import Submission.Work.BourgainPlan.Maximal.fourierCoeff_mstEta

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- The norm of the inverse of a positive real, read in `ℂ`. -/
private lemma norm_inv_ofReal_pos (c : ℝ) (hc : 0 < c) : ‖(((c : ℝ) : ℂ))⁻¹‖ = c⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

/-- **The assembly of the `ℓ¹` bound** from the three analytic inputs: the trivial bound
`‖mstHat η t‖ ≤ M`, the quadratic decay `‖mstHat η t‖ ≤ E / t²`, and the dilation dictionary
`fourierCoeff (mstEta d χ η n) m = c_n⁻¹ mstHat η (m / c_n)`.

With `c := c_n ≥ 1`, `M' := max M 1`, the summand `f m := ‖fourierCoeff ... m‖ / M'` satisfies
`f m ≤ 1/c = 2 ε` with `ε = 1/(2c)` and `f m ≤ (E c / M') / m²` for `m ≠ 0`; the two-scale sum bound
`tsum_two_scale_bound` gives `Σ_m f m ≤ 5 + E/M'`, and multiplying by `M'` gives
`Σ_m ‖fourierCoeff ... m‖ ≤ 5 M' + E`. -/
private theorem mst_err1_bump_coeff_assembly {d : ℕ} {χ : ℝ} (hχ : χ + 1 ≤ (d : ℝ)) (η : ℝ → ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, ‖mstHat η t‖ ≤ M)
    (hdecay : ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, t ≠ 0 → ‖mstHat η t‖ ≤ E / t ^ 2)
    (hcoeff : ∀ (n : ℕ) (m : ℤ),
      fourierCoeff (mstEta d χ η n) m
        = ((mstScale d χ n : ℝ) : ℂ)⁻¹ * mstHat η ((m : ℝ) / mstScale d χ n)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Summable (fun m : ℤ => ‖fourierCoeff (mstEta d χ η n) m‖) ∧
        (∑' m : ℤ, ‖fourierCoeff (mstEta d χ η n) m‖) ≤ K := by
  obtain ⟨E, hE0, hE⟩ := hdecay
  set M' : ℝ := max M 1 with hM'def
  have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hM'ne : M' ≠ 0 := hM'pos.ne'
  have hMM' : M ≤ M' := le_max_left M 1
  refine ⟨5 * M' + E + 1, by linarith, ?_⟩
  intro n
  have hcpos : 0 < mstScale d χ n := mstScale_pos d χ n
  have hcne : mstScale d χ n ≠ 0 := hcpos.ne'
  have hc1 : 1 ≤ mstScale d χ n := one_le_mstScale hχ n
  -- pointwise bounds on the Fourier coefficients of the level bump
  have hsup : ∀ m : ℤ,
      ‖fourierCoeff (mstEta d χ η n) m‖ ≤ M / mstScale d χ n := by
    intro m
    rw [hcoeff n m, norm_mul, norm_inv_ofReal_pos (mstScale d χ n) hcpos]
    calc (mstScale d χ n)⁻¹ * ‖mstHat η ((m : ℝ) / mstScale d χ n)‖
        ≤ (mstScale d χ n)⁻¹ * M := mul_le_mul_of_nonneg_left (hbound _) (by positivity)
      _ = M / mstScale d χ n := by ring
  have hdec_pt : ∀ m : ℤ, m ≠ 0 →
      ‖fourierCoeff (mstEta d χ η n) m‖ ≤ E * mstScale d χ n / (m : ℝ) ^ 2 := by
    intro m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [hcoeff n m, norm_mul, norm_inv_ofReal_pos (mstScale d χ n) hcpos]
    have harg : ((m : ℝ) / mstScale d χ n) ≠ 0 := div_ne_zero hm' hcne
    calc (mstScale d χ n)⁻¹ * ‖mstHat η ((m : ℝ) / mstScale d χ n)‖
        ≤ (mstScale d χ n)⁻¹ * (E / ((m : ℝ) / mstScale d χ n) ^ 2) :=
          mul_le_mul_of_nonneg_left (hE _ harg) (by positivity)
      _ = E * mstScale d χ n / (m : ℝ) ^ 2 := by
          field_simp [hcne, hm']
  -- the two hypotheses of the two-scale sum bound for `f m = ‖·‖ / M'`
  have hf1 : ∀ m : ℤ, ‖fourierCoeff (mstEta d χ η n) m‖ / M'
      ≤ 2 * (1 / (2 * mstScale d χ n)) := by
    intro m
    rw [div_le_iff₀ hM'pos]
    have heq : 2 * (1 / (2 * mstScale d χ n)) * M' = M' / mstScale d χ n := by
      field_simp [hcne, hM'ne]
    rw [heq]
    exact le_trans (hsup m) (div_le_div_of_nonneg_right hMM' hcpos.le)
  have hf2 : ∀ m : ℤ, m ≠ 0 →
      ‖fourierCoeff (mstEta d χ η n) m‖ / M'
        ≤ (E * mstScale d χ n / M') / (m : ℝ) ^ 2 := by
    intro m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have heq : (E * mstScale d χ n / (m : ℝ) ^ 2) / M'
        = (E * mstScale d χ n / M') / (m : ℝ) ^ 2 := by
      field_simp [hcne, hm', hM'ne]
    rw [← heq]
    exact div_le_div_of_nonneg_right (hdec_pt m hm) hM'pos.le
  have hB : 0 ≤ E * mstScale d χ n / M' :=
    div_nonneg (mul_nonneg hE0 hcpos.le) hM'pos.le
  have hεpos : 0 < 1 / (2 * mstScale d χ n) := by positivity
  have hε1 : 1 / (2 * mstScale d χ n) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * mstScale d χ n) (by norm_num : (0:ℝ) < 2)]
    linarith
  obtain ⟨hsumf, hlef⟩ :=
    Work.BourgainPlan.IonescuWainger.tsum_two_scale_bound (1 / (2 * mstScale d χ n))
      (E * mstScale d χ n / M') (fun m : ℤ => ‖fourierCoeff (mstEta d χ η n) m‖ / M')
      hεpos hε1 hB (fun m => div_nonneg (norm_nonneg _) hM'pos.le) hf1 hf2
  have hval : 2 * (E * mstScale d χ n / M') * (1 / (2 * mstScale d χ n)) = E / M' := by
    field_simp [hcne, hM'ne]
  rw [hval] at hlef
  refine ⟨?_, ?_⟩
  · refine (hsumf.mul_left M').congr fun m => ?_
    field_simp [hM'ne]
  · have hEq : (∑' m : ℤ, ‖fourierCoeff (mstEta d χ η n) m‖)
        = M' * ∑' m : ℤ, (‖fourierCoeff (mstEta d χ η n) m‖ / M') := by
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      field_simp [hM'ne]
    rw [hEq]
    have hstep : M' * (∑' m : ℤ, (‖fourierCoeff (mstEta d χ η n) m‖ / M'))
        ≤ M' * (5 + E / M') := mul_le_mul_of_nonneg_left hlef hM'pos.le
    have hfin : M' * (5 + E / M') = 5 * M' + E := by
      field_simp [hM'ne]
    linarith [hstep, hfin]

/-- **The `ℓ¹` summability of the Fourier coefficients of the level bump `η_n = mstEta d χ η n`**,
uniformly in the level `n` (MST §4.2: the `ℓ¹`-kernel bound for the narrow bump).

The level bump is `mstEta d χ η n ξ = η (c_n · iwRep ξ)` with the level scale `c_n = 2^{n (d − χ)}`;
the hypothesis `χ + 1 ≤ d` makes `c_n ≥ 1`.  Then the Fourier coefficients of `mstEta d χ η n` on the
circle are summable with a bound independent of `n`.

Route.  `fourierCoeff (mstEta d χ η n) m = ∫ x in (-1/2)..(1/2), η (c_n * x) * exp (-(2πi m x))`
(interval form of `fourierCoeff`, `fourier_coe_apply` and `AddCircle.liftIoc_coe_apply` for
`iwRep (x : Circle) = x` on `Ioc (-1/2) (1/2]`).  Scaling identity: for `c ≥ 1` and `t : ℝ`,
`∫ x in (-1/2)..(1/2), η (c*x) * exp (-(2πi t x)) = (1/c) * rho (t/c)`, where
`rho t := ∫ u in (-1/2)..(1/2), η u * exp (-(2πi t u))` — substitute `u = c*x` and use `hη2` to
shrink `(-c/2, c/2)` back to `(-1/2, 1/2)`.  `rho` is bounded by `M` (from `hηbd`) and decays
quadratically: `ϑ := circleLift (mstEta d χ η 0)` is `ContDiff ℝ 2` (`hcd0`) with compact support
and `ϑ x = η (-x)` on `(-1/2, 1/2)`, so `rho t = 𝓕 ϑ (-t)` and `Real.fourier_iteratedDeriv` at
`n = 2` gives `‖rho t‖ ≤ (∫ ‖ϑ''‖) / (2π t)²`.  Finally the sampling bound
`Σ_m (1/c) ‖rho ((m + s)/c)‖ ≤ K` uniformly in `c ≥ 1`, `s : ℝ`: split `|(m+s)/c| ≤ 1` (at most
`2c+1` terms) from the two tails, bounded by the decaying estimate and comparison with
`∫_{|y| ≥ 1} E/y² dy = 2E`. -/
theorem mst_err1_bump_coeff {d : ℕ} {χ : ℝ} (hχ : χ + 1 ≤ (d : ℝ)) (η : ℝ → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Summable (fun m : ℤ => ‖fourierCoeff (mstEta d χ η n) m‖) ∧
        (∑' m : ℤ, ‖fourierCoeff (mstEta d χ η n) m‖) ≤ K := by
  obtain ⟨E, hE0, hE⟩ := mstHat_decay η hcd0
  exact mst_err1_bump_coeff_assembly hχ η hM (mstHat_bound hM hηbd) ⟨E, hE0, hE⟩
    (fun n m => fourierCoeff_mstEta hχ η hη2 n m)

end Work.BourgainPlan.Maximal

end Work.BourgainPlan.Maximal

/-- Alias for the harness-lifted namespace prefix (the declaration above lands in
`Work.BourgainPlan.Maximal.Work.BourgainPlan.Maximal.`): the theorem is also available under the
plain `Work.BourgainPlan.Maximal.` prefix used by its consumers. -/
alias Work.BourgainPlan.Maximal.mst_err1_bump_coeff :=
  Work.BourgainPlan.Maximal.Work.BourgainPlan.Maximal.mst_err1_bump_coeff
