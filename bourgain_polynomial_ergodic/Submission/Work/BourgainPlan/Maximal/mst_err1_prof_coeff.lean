import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile
import Submission.Work.BourgainPlan.Maximal.mst_prof_err1_defs
import Submission.Work.BourgainPlan.Maximal.profSampling_bound
import Submission.Work.BourgainPlan.Maximal.profCoeff_eq

set_option linter.unusedVariables false

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **The `ℓ¹` summability of the Fourier coefficients of the profile-times-bump
`h_n = star (mstProf P (2^n) ·) · mstEta P.natDegree χ η n`**, uniformly in `n` (MST §4.2: the kernel
of the major-arc model symbol).

With `c_n = 2^{n (d − χ)}` (`d = P.natDegree`, `c_n ≥ 1` by `χ + 1 ≤ d`) one has
`star (mstProf P N ξ) = ∫_0^1 exp (-(2πi · iwRep ξ · P(N s))) ds` (`star_polyProfile`), hence on the
fundamental domain
`fourierCoeff (fun ξ => star (mstProf P (2^n) ξ) * mstEta d χ η n ξ) m
   = ∫ x in (-1/2)..(1/2), (∫_0^1 exp (-(2πi x P(2^n s))) ds) * η (c_n x) * exp (-(2πi m x))`,
and Fubini on the rectangle `(-1/2,1/2) × (0,1)` together with the scaling identity for `η`
(`∫ x, η (c*x) * exp (-(2πi t x)) = (1/c) * rho (t/c)` with
`rho t := ∫ u in (-1/2)..(1/2), η u * exp (-(2πi t u))`, valid for `c ≥ 1`, proved by the
substitution `u = c*x` and `hη2`) turns the coefficient into
`∫_0^1 (1/c_n) * rho ((m + P (2^n s))/c_n) ds`
(note the two exponents combine with the *same* sign, `-(2πi x (P(2^n s) + m))`).

Then `Σ_m ‖·‖ ≤ ∫_0^1 Σ_m (1/c_n) ‖rho ((m + P(2^n s))/c_n)‖ ds ≤ K`, using the *sampling bound*
`Σ_m (1/c) ‖rho ((m + s)/c)‖ ≤ K` uniform in `c ≥ 1` and `s : ℝ`.  That sampling bound needs `rho`
bounded (`‖rho t‖ ≤ M`, from `hηbd`) and quadratically decaying (`‖rho t‖ ≤ E/t²` for `1 ≤ |t|`),
the latter obtained by two integrations by parts on `ϑ := circleLift (mstEta d χ η 0)` — which is
`ContDiff ℝ 2` with compact support by `hcd0`, and equals `x ↦ η (-x)` on `(-1/2,1/2)` — via
Mathlib's `Real.fourier_iteratedDeriv` at `n = 2`.

The sibling lemma `Work.BourgainPlan.Maximal.mst_err1_bump_coeff` is the same computation for the
bump alone; the two are independent (this one additionally uses `polyProfile`). -/
theorem mst_err1_prof_coeff (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ}
    (hχ : χ + 1 ≤ (P.natDegree : ℝ)) (η : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η 0))) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Summable (fun m : ℤ => ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖) ≤ K := by
  have hηm : AEStronglyMeasurable η (volume : Measure ℝ) :=
    aestronglyMeasurable_profEta (d := P.natDegree) (χ := χ) hη2 hcd0
  obtain ⟨A, hA0, hAmaj⟩ :=
    exists_mstHat_radial_majorant (d := P.natDegree) (χ := χ) η hM hηbd hcd0
  set ρ : ℝ → ℂ := fun t' => ((A * (1 + |t'|) ^ (-(2 : ℝ)) : ℝ) : ℂ) with hρ
  have hρdec : ∀ t : ℝ, ‖ρ t‖ = A * (1 + |t|) ^ (-(2 : ℝ)) := by
    intro t
    have hnn : 0 ≤ A * (1 + |t|) ^ (-(2 : ℝ)) := by positivity
    rw [hρ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  obtain ⟨K, hKpos, hK⟩ := profSampling_bound hA0 (fun t => (hρdec t).le)
  refine ⟨K, hKpos, fun n => ?_⟩
  -- abbreviations
  set c : ℝ := mstScale P.natDegree χ n with hc
  have hc1 : 1 ≤ c := by rw [hc]; exact one_le_mstScale hχ n
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcne : c ≠ 0 := hcpos.ne'
  set ev : ℝ → ℝ := fun s' => (toRealPoly P).eval (((2 : ℝ) ^ n) * s') with hev
  set w : ℤ → ℝ → ℝ := fun m' s' =>
    c⁻¹ * (A * (1 + |((m' : ℝ) + ev s') / c|) ^ (-(2 : ℝ))) with hw
  -- the coefficient identity, in set-integral form
  have hcoeff : ∀ m : ℤ,
      fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m
      = ∫ s in Set.Ioc (0 : ℝ) 1,
          ((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c) := by
    intro m
    rw [profCoeff_eq P (d := P.natDegree) (χ := χ) hχ (M := M) hM hηbd hη2 hηm n m]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- basic facts about the majorant
  have hwnn : ∀ (m : ℤ) (s : ℝ), 0 ≤ w m s := by
    intro m s
    rw [hw]
    positivity
  have hwle : ∀ (m : ℤ) (s : ℝ), w m s ≤ c⁻¹ * A := by
    intro m s
    rw [hw]
    beta_reduce
    have h1 : (1 + |((m : ℝ) + ev s) / c|) ^ (-(2 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      exact inv_le_one_of_one_le₀ (by nlinarith [abs_nonneg (((m : ℝ) + ev s) / c)])
    calc c⁻¹ * (A * (1 + |((m : ℝ) + ev s) / c|) ^ (-(2 : ℝ)))
        ≤ c⁻¹ * (A * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hA0) (by positivity)
      _ = c⁻¹ * A := by ring
  have hwpt : ∀ (m : ℤ) (s : ℝ),
      ‖((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c)‖ ≤ w m s := by
    intro m s
    have hnorm : ‖((c : ℝ) : ℂ)⁻¹‖ = c⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [norm_mul, hnorm, hw]
    beta_reduce
    rw [show (ev s + (m : ℝ)) = ((m : ℝ) + ev s) from by ring]
    exact mul_le_mul_of_nonneg_left (hAmaj _) (by positivity)
  have hwcont : ∀ m : ℤ, Continuous (fun s : ℝ => w m s) := by
    intro m
    rw [hw]
    have h1 : Continuous fun s : ℝ => ((m : ℝ) + ev s) / c :=
      (((continuous_const.add ((Polynomial.continuous (toRealPoly P)).comp
        (continuous_const.mul continuous_id)))).div_const c)
    have h2 : Continuous fun s : ℝ => 1 + |((m : ℝ) + ev s) / c| :=
      continuous_const.add h1.abs
    have h3 : Continuous fun s : ℝ => (1 + |((m : ℝ) + ev s) / c|) ^ (-(2 : ℝ)) :=
      h2.rpow continuous_const (fun s => Or.inl (by positivity))
    exact continuous_const.mul (continuous_const.mul h3)
  have hmeas : ∀ m : ℤ, AEMeasurable (fun s : ℝ => ENNReal.ofReal (w m s))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro m
    exact ((hwcont m).aemeasurable).ennreal_ofReal
  have hfin_lt : ∀ m : ℤ, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
      ‖((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c)‖) < ⊤ := by
    intro m
    calc ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
          ‖((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c)‖
        ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (c⁻¹ * A) :=
          lintegral_mono (fun s => ENNReal.ofReal_le_ofReal ((hwpt m s).trans (hwle m s)))
      _ = ENNReal.ofReal (c⁻¹ * A) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
          norm_num
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- the termwise bound
  have hkey : ∀ m : ℤ, ENNReal.ofReal ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖
      ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (w m s) := by
    intro m
    rw [hcoeff m]
    calc ENNReal.ofReal ‖∫ s in Set.Ioc (0 : ℝ) 1,
            ((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c)‖
        ≤ ENNReal.ofReal ((∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
            ‖((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c)‖).toReal) :=
          ENNReal.ofReal_le_ofReal (MeasureTheory.norm_integral_le_lintegral_norm
            (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) _)
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal
            ‖((c : ℝ) : ℂ)⁻¹ * mstHat η ((ev s + (m : ℝ)) / c)‖ :=
          ENNReal.ofReal_toReal (hfin_lt m).ne
      _ ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (w m s) :=
          lintegral_mono (fun s => ENNReal.ofReal_le_ofReal (hwpt m s))
  -- the sampling bounds, in `w` form
  have hsam_sum : ∀ s : ℝ, Summable (fun m : ℤ => w m s) := by
    intro s
    have h1 : Summable (fun m : ℤ => ‖ρ (((m : ℝ) + ev s) / c)‖) := (hK c hc1 (ev s)).1
    refine (h1.mul_left c⁻¹).congr (fun m => ?_)
    show c⁻¹ * ‖ρ (((m : ℝ) + ev s) / c)‖ = w m s
    rw [hw]
    beta_reduce
    rw [hρdec]
  have hsam_bd : ∀ s : ℝ, (∑' m : ℤ, w m s) ≤ K := by
    intro s
    have h1 : (∑' m : ℤ, ‖ρ (((m : ℝ) + ev s) / c)‖) ≤ K * c := (hK c hc1 (ev s)).2
    have h2 : (∑' m : ℤ, w m s) = c⁻¹ * ∑' m : ℤ, ‖ρ (((m : ℝ) + ev s) / c)‖ := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun m => by
        rw [hw]
        beta_reduce
        rw [hρdec, add_comm])
    calc (∑' m : ℤ, w m s) = c⁻¹ * ∑' m : ℤ, ‖ρ (((m : ℝ) + ev s) / c)‖ := h2
      _ ≤ c⁻¹ * (K * c) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K := by field_simp
  -- the main ENNReal computation
  have hmain : (∑' m : ℤ, ENNReal.ofReal ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖) ≤ ENNReal.ofReal K := by
    calc (∑' m : ℤ, ENNReal.ofReal ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖)
        ≤ ∑' m : ℤ, ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (w m s) :=
          ENNReal.tsum_le_tsum hkey
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1, ∑' m : ℤ, ENNReal.ofReal (w m s) :=
          (MeasureTheory.lintegral_tsum hmeas).symm
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (∑' m : ℤ, w m s) := by
          refine lintegral_congr (fun s => ?_)
          exact (ENNReal.ofReal_tsum_of_nonneg (fun m => hwnn m s) (hsam_sum s)).symm
      _ ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal K :=
          lintegral_mono (fun s => ENNReal.ofReal_le_ofReal (hsam_bd s))
      _ = ENNReal.ofReal K := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
          norm_num
  have hfin' : (∑' m : ℤ, ENNReal.ofReal ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmain
  constructor
  · refine (ENNReal.summable_toReal hfin').congr (fun m => ?_)
    exact ENNReal.toReal_ofReal (norm_nonneg _)
  · have hcast : (∑' m : ℤ, ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖)
        = (∑' m : ℤ, ENNReal.ofReal ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖).toReal := by
      rw [ENNReal.tsum_toReal_eq (f := fun m : ℤ => ENNReal.ofReal ‖fourierCoeff
        (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖)
        (fun m => ENNReal.ofReal_ne_top)]
      exact tsum_congr (fun m => (ENNReal.toReal_ofReal (norm_nonneg _)).symm)
    rw [hcast]
    calc (∑' m : ℤ, ENNReal.ofReal ‖fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
            star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ) m‖).toReal
        ≤ (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
      _ = K := ENNReal.toReal_ofReal hKpos.le


end Work.BourgainPlan.Maximal

end Work.BourgainPlan.Maximal

/-- Alias for the harness-lifted namespace prefix (the declaration above lands in
`Work.BourgainPlan.Maximal.Work.BourgainPlan.Maximal.`): the theorem is also available under the
plain `Work.BourgainPlan.Maximal.` prefix used by its consumers. -/
alias Work.BourgainPlan.Maximal.mst_err1_prof_coeff :=
  Work.BourgainPlan.Maximal.Work.BourgainPlan.Maximal.mst_err1_prof_coeff
