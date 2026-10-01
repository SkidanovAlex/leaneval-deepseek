import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.zetaPerronIdentity
import Submission.Work.ZeroDensity.Ingham.detSumSplit
import Submission.Work.ZeroDensity.Ingham.zetaPerronShift
import Submission.Work.ZeroDensity.Ingham.detFarTailSmall
import Submission.Work.ZeroDensity.Ingham.residueTermSmall
import Submission.Work.ZeroDensity.Ingham.critTailSmall

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory


/-! ## Elementary bookkeeping used in the assembly -/

/-- The modulus of the Perron integrand on the critical line `Re w = 1/2 - Re ρ`: it is
`Y^{1/2-Re ρ}` times the critical-line integrand `critIntegrand`. -/
lemma norm_perronInt_critLine (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) (t : ℝ) :
    ‖perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
      = Y ^ (1 / 2 - ρ.re) * critIntegrand K ρ t := by
  have harg : ρ + (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hre : (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I).re = 1 / 2 - ρ.re := by
    simp
  rw [perronInt, critIntegrand, harg, Complex.norm_mul, Complex.norm_mul, Complex.norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hY, hre]
  ring

/-- Splitting a Lebesgue integral over `ℝ` into the integral over `[-H,H]` and the two tails. -/
lemma integral_eq_Ioc_add_tails {f : ℝ → ℂ} (hf : Integrable f) {H : ℝ} (hH : 0 ≤ H) :
    (∫ t : ℝ, f t)
      = (∫ t in (-H)..H, f t) + (∫ t in Set.Ioi H, f t) + (∫ t in Set.Iic (-H), f t) := by
  have hmeas : MeasurableSet (Set.Ioc (-H) H) := measurableSet_Ioc
  have hcompl : (Set.Ioc (-H) H)ᶜ = Set.Ioi H ∪ Set.Iic (-H) := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Ioi, Set.mem_Iic]
    constructor
    · intro h
      by_cases ht : t ≤ H
      · right
        by_contra h2
        push_neg at h2
        exact h ⟨h2, ht⟩
      · left
        push_neg at ht
        exact ht
    · rintro (h | h) ⟨h1, h2⟩
      · linarith
      · linarith
  have hdisj : Disjoint (Set.Ioi H) (Set.Iic (-H)) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    simp only [Set.mem_Ioi] at ht1
    simp only [Set.mem_Iic] at ht2
    linarith
  have hunion : (∫ t in Set.Ioi H ∪ Set.Iic (-H), f t)
      = (∫ t in Set.Ioi H, f t) + (∫ t in Set.Iic (-H), f t) :=
    setIntegral_union hdisj measurableSet_Iic hf.integrableOn hf.integrableOn
  have hofle : (∫ t in (-H)..H, f t) = ∫ t in Set.Ioc (-H) H, f t :=
    intervalIntegral.integral_of_le (by linarith)
  have hmain := integral_add_compl hmeas hf
  rw [hcompl, hunion, ← hofle] at hmain
  rw [← hmain]
  ring

/-- The error budget of the detector is strictly smaller than `e^{-1}`. -/
lemma detector_error_lt_exp_neg_one :
    (1 / 12 + 1 / (24 * Real.pi) + 3 / 20 : ℝ) < Real.exp (-1) := by
  have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpow : Real.exp (-(1 : ℝ)) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have hinv : (1 / 3 : ℝ) < (Real.exp 1)⁻¹ := by
    simpa using one_div_lt_one_div_of_lt (Real.exp_pos 1) h3
  have hb : 1 / (24 * Real.pi) < 1 / 12 := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [Real.pi_gt_three]
  rw [hpow]
  linarith



/-! ## The assembly step

This auxiliary lemma isolates the numerical bookkeeping of the detector: from the Perron identity,
the contour shift, the splitting of the detector sum and the three smallness estimates, the
disjunction follows. -/
private lemma assembly_step (T : ℝ) (hT : 2 ≤ T) (K : ℕ) (Y : ℝ) (ρ : ℂ) (A : ℝ)
    (hY1 : 1 ≤ Y) (hA6 : 6 ≤ A)
    (hfar : ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ ≤ 1 / 20)
    (hres : ‖residueTerm K Y ρ‖ ≤ 1 / 20)
    (hcrit : Y ^ (1 / 2 - ρ.re) * ((∫ v in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ v)
          + (∫ v in Set.Iic (-(A * Real.log (A * T))), critIntegrand K ρ v)) ≤ Real.pi / 10)
    (hline : Integrable (fun t : ℝ =>
        perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)))
    (hperron : detSum K Y ρ = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I))
    (hshift : (1 / (2 * Real.pi)) * (∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I))
        = residueTerm K Y ρ + (1 / (2 * Real.pi)) *
            (∫ t : ℝ, perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)))
    (hsplit : detSum K Y ρ = ((Real.exp (-(1 / Y)) : ℝ) : ℂ)
        + detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
        + detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ) :
    (1 / 12 ≤ ‖detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖)
      ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
            ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)), critIntegrand K ρ v) := by
  have hApos : 0 < A := by linarith
  have hH0 : 0 ≤ A * Real.log (A * T) := by
    have h1 : (1 : ℝ) ≤ A * T := by nlinarith
    exact mul_nonneg hApos.le (Real.log_nonneg h1)
  have hYpos : 0 < Y := by linarith
  rcases lt_or_ge (‖detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖) (1 / 12) with hlt | hge
  · refine Or.inr ?_
    by_contra hcon
    have hcon' : Y ^ (1 / 2 - ρ.re) * (∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
        critIntegrand K ρ v) < 1 / 12 := not_le.mp hcon
    have hIcrit : ‖∫ t : ℝ, perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
        ≤ 1 / 12 + Real.pi / 10 := by
      rw [integral_eq_Ioc_add_tails hline hH0]
      have hAi : ‖∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ < 1 / 12 := by
        refine lt_of_le_of_lt ?_ hcon'
        refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith [hH0])) ?_
        rw [intervalIntegral.integral_congr (fun t _ => norm_perronInt_critLine K Y hYpos ρ t),
          intervalIntegral.integral_const_mul]
      have hBi : ‖∫ t in Set.Ioi (A * Real.log (A * T)),
            perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
          + ‖∫ t in Set.Iic (-(A * Real.log (A * T))),
            perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ ≤ Real.pi / 10 := by
        have h1 : ‖∫ t in Set.Ioi (A * Real.log (A * T)),
              perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
            ≤ Y ^ (1 / 2 - ρ.re) * ∫ t in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ t := by
          refine le_trans (norm_integral_le_integral_norm _) ?_
          rw [show (∫ t in Set.Ioi (A * Real.log (A * T)),
                ‖perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖)
              = ∫ t in Set.Ioi (A * Real.log (A * T)),
                  Y ^ (1 / 2 - ρ.re) * critIntegrand K ρ t from
              setIntegral_congr_fun measurableSet_Ioi
                (fun t _ => norm_perronInt_critLine K Y hYpos ρ t)]
          exact le_of_eq (integral_const_mul _ _)
        have h2 : ‖∫ t in Set.Iic (-(A * Real.log (A * T))),
              perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
            ≤ Y ^ (1 / 2 - ρ.re) * ∫ t in Set.Iic (-(A * Real.log (A * T))),
                critIntegrand K ρ t := by
          refine le_trans (norm_integral_le_integral_norm _) ?_
          rw [show (∫ t in Set.Iic (-(A * Real.log (A * T))),
                ‖perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖)
              = ∫ t in Set.Iic (-(A * Real.log (A * T))),
                  Y ^ (1 / 2 - ρ.re) * critIntegrand K ρ t from
              setIntegral_congr_fun measurableSet_Iic
                (fun t _ => norm_perronInt_critLine K Y hYpos ρ t)]
          exact le_of_eq (integral_const_mul _ _)
        linarith [h1, h2, hcrit]
      calc ‖(∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
              perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))
            + (∫ t in Set.Ioi (A * Real.log (A * T)),
                perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))
            + ∫ t in Set.Iic (-(A * Real.log (A * T))),
                perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖
          ≤ ‖(∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
                perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))
              + (∫ t in Set.Ioi (A * Real.log (A * T)),
                perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))‖
            + ‖∫ t in Set.Iic (-(A * Real.log (A * T))),
                perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ :=
            norm_add_le _ _
        _ ≤ 1 / 12 + Real.pi / 10 := by
          have h2 := norm_add_le (∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
              perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))
            (∫ t in Set.Ioi (A * Real.log (A * T)),
              perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))
          linarith [hAi.le, hBi, h2]
    have hIcrit' : ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I))‖
        ≤ (1 / (2 * Real.pi)) * (1 / 12 + Real.pi / 10) := by
      have hcast : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
        push_cast; ring
      have hcn : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hcast, norm_mul, hcn]
      exact mul_le_mul_of_nonneg_left hIcrit (by positivity)
    have hdet : ‖detSum K Y ρ‖ ≤ 1 / 20 + (1 / (2 * Real.pi)) * (1 / 12 + Real.pi / 10) := by
      rw [hperron, hshift]
      refine le_trans (norm_add_le _ _) ?_
      linarith [hres, hIcrit']
    have hexpbd : Real.exp (-(1 / Y)) ≤ 3 / 20 + 1 / (24 * Real.pi) + 1 / 12 := by
      have hnorm : Real.exp (-(1 / Y)) = ‖((Real.exp (-(1 / Y)) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hrepr : ((Real.exp (-(1 / Y)) : ℝ) : ℂ)
          = detSum K Y ρ - detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
            - detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ := by
        rw [hsplit]; ring
      have harith : (1 / (2 * Real.pi)) * (1 / 12 + Real.pi / 10) = 1 / (24 * Real.pi) + 1 / 20 := by
        field_simp; ring
      rw [hnorm, hrepr]
      have h1 : ‖detSum K Y ρ - detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
            - detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖
          ≤ ‖detSum K Y ρ‖ + ‖detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖
            + ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        exact add_le_add (norm_sub_le _ _) le_rfl
      linarith [h1, hdet, hlt.le, hfar, harith.le]
    have hge1 : Real.exp (-1) ≤ Real.exp (-(1 / Y)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      simpa using one_div_le_one_div_of_le (zero_lt_one) hY1
    linarith [hge1, hexpbd, detector_error_lt_exp_neg_one]
  · exact Or.inl hge
/-- **Montgomery's zero detector for `ζ` in disjunctive form with the explicit threshold `1/12`**
(Montgomery–Vaughan, *Multiplicative Number Theory*, (28.39) with `q = Q = 1`: the same
alternatives as `Work.ZeroDensity.Montgomery.zeroDetectorAlternatives`, but for the principal
character, where the pole of `ζ` at `1` produces the extra residue term which is absorbed into
`1/12` for `|Im ρ| ≥ (log (A T))²`).  With `H ≍ T`, the mollifier `M_K(s) = Σ_{n≤K} μ(n)n^{-s}` and
`a_K(n) = Σ_{d | n, d ≤ K} μ(d)`, at every zero `ρ` of `ζ` in the strip `1/2 ≤ Re ρ ≤ 1`,
`|Im ρ| ≤ T`, `|Im ρ| ≥ (log (A T))²` at least one holds:

* the tail `Σ_{K<n≤Y (log (AT))²} a_K(n) n^{-ρ} e^{-n/Y}` has modulus `≥ 1/12`;
* the truncated critical-line integral
  `Y^{1/2-Re ρ} ∫_{|v| ≤ A log (AT)} ‖ζ(1/2+i Im ρ+iv)‖ ‖M_K(1/2+i Im ρ+iv)‖ ‖Γ(1/2-Re ρ+iv)‖ dv`
  is `≥ 1/12`.

The mechanism is the Mellin/Perron identity: shifting the contour from `Re w = 2-Re ρ` to
`Re w = 1/2-Re ρ` crosses `w = 0` (residue `ζ(ρ)M_K(ρ) = 0`) and the pole `w = 1-ρ` of `ζ` (residue
`Γ(1-ρ)M_K(1)Y^{1-ρ} ≪ 1/H` when `|Im ρ| ≥ (log (AT))²`), so
`e^{-1/Y} + tail = O(1/H) + (1/2πi)∫`, and `e^{-1} ≤ e^{-1/Y}` gives the alternatives. -/
theorem zetaDetector12 :
    ∃ C A : ℝ, 0 < C ∧ 6 ≤ A ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ C * T →
      1 ≤ Y → Y ≤ (C * T) ^ 2 →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        (1 / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖)
          ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
              ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
                ‖riemannZeta ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                  * ‖MK K ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                  * ‖Complex.Gamma (((1 / 2 : ℝ) - ρ.re : ℝ) + (v : ℝ) * Complex.I)‖) := by
  sorry

end Work.ZeroDensity.Ingham
