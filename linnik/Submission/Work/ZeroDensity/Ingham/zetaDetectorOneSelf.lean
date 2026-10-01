import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs
import Submission.Work.ZeroDensity.Ingham.detSumSplit
import Submission.Work.ZeroDensity.Ingham.zetaPerronIdentity
import Submission.Work.ZeroDensity.Ingham.detFarTailSmall
import Submission.Work.ZeroDensity.Ingham.residueTermSmall
import Submission.Work.ZeroDensity.Ingham.MK_critical_bound
import Submission.Work.ZeroDensity.Ingham.zeta_halfLine_poly_bound
import Submission.Work.ZeroDensity.Ingham.gamma_crit_bound
import Submission.Work.ZeroDensity.Ingham.perronHDifferentiableSelf
import Submission.Work.ZeroDensity.Ingham.verticalShiftPatchedPoleSelf
import Submission.Work.ZeroDensity.Ingham.perronIntIntegrableSelf
import Submission.Work.ZeroDensity.Ingham.OneDev
import Submission.Work.ZeroDensity.Ingham.OneIntegral
import Submission.Work.ZeroDensity.Ingham.OneSelf.critTailNumericOne

/-!
# Montgomery's zero detector for `ζ` at `C = 1` (self-contained assembly)

This module assembles the disjunctive zero detector `zetaDetectorOneSelf` out of

* the Mellin/Perron identity `zetaPerronIdentity`,
* the splitting of the detector sum `detSumSplit` and the smallness of the far tail
  (`detFarTailSmall`) and of the residue at the `ζ`-pole (`residueTermSmall`),
* the patched contour shift `perronShiftOne` (built here from `verticalShiftPatchedPoleSelf`,
  `perronHDifferentiableSelf`, `perronIntIntegrableSelf` and `perronHHorizontalOne`),
* the smallness of the tails of the critical-line integral `critTailSmallOne` (built here from
  `zeta_halfLine_poly_bound`, `gamma_crit_bound`, `MK_critical_bound`, `integralIoiPolyexpLocal`
  and `OneSelf.critTailNumericOne`),
* the numerical bookkeeping `assembly_step_one`.

All ingredients are complete and axiom-clean.
-/

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-! ## Elementary bookkeeping -/

/-- The modulus of the Perron integrand on the critical line `Re w = 1/2 - Re ρ`: it is
`Y^{1/2-Re ρ}` times the critical-line integrand `critIntegrand`. -/
lemma norm_perronInt_critLine_one (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) (t : ℝ) :
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
lemma integral_eq_Ioc_add_tails_one {f : ℝ → ℂ} (hf : Integrable f) {H : ℝ} (hH : 0 ≤ H) :
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
lemma detector_error_lt_exp_neg_one_one :
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

/-! ## The patched contour shift for the `ζ` detector -/

/-- The `1/2π`-normalised form of the patched contour shift: dividing
`verticalShiftPatchedPoleSelf` by `2π` turns the residue term `2π a` into `a`. -/
private theorem perronShiftSelf_divided_local (F H : ℂ → ℂ) (p q : ℝ) (hpq : p < q) (u a : ℂ)
    (hu : p < u.re ∧ u.re < q)
    (hH : ∀ R : ℝ, DifferentiableOn ℂ H (Set.uIcc p q ×ℂ Set.uIcc (-R) R))
    (hdec : ∀ R : ℝ, 1 ≤ R → ∀ s ∈ (Set.uIcc p q ×ℂ Set.uIcc (-R) R), s ≠ u → s ≠ 0 →
      F s = a / (s - u) + H s)
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hpint : Integrable (fun t : ℝ => F ((p : ℂ) + (t : ℂ) * Complex.I)))
    (hqint : Integrable (fun t : ℝ => F ((q : ℂ) + (t : ℂ) * Complex.I))) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      = a + (1 / (2 * Real.pi)) * (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) := by
  have h := verticalShiftPatchedPoleSelf F H p q hpq u a hu hH hdec htop hbot hpint hqint
  have key : (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  rw [h, mul_add, ← mul_assoc, key, one_mul]
  exact add_comm _ _

/-- The contour shift of the zero detector with its residue, normalised by `1/2π`. -/
theorem perronShiftOne (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (hβ0 : (1 : ℝ) / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I))
      = residueTerm K Y ρ
        + (1 / (2 * Real.pi)) *
            (∫ t : ℝ, perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)) := by
  have hreu : (1 - ρ).re = 1 - ρ.re := by simp
  have hp2 : ((1 / 2 : ℝ) - ρ.re) < 2 := by linarith
  have hu : ((1 / 2 : ℝ) - ρ.re) < (1 - ρ).re ∧ (1 - ρ).re < 2 := by
    rw [hreu]; exact ⟨by linarith, by linarith⟩
  have hH : ∀ R : ℝ, DifferentiableOn ℂ (perronH K Y ρ)
      (Set.uIcc ((1 / 2 : ℝ) - ρ.re) 2 ×ℂ Set.uIcc (-R) R) := fun R =>
    perronHDifferentiableSelf K Y hY ρ (p := (1 / 2 : ℝ) - ρ.re) (q := 2) (R := R)
      (by linarith) (by norm_num) (by linarith)
  have hdec : ∀ R : ℝ, 1 ≤ R →
      ∀ s ∈ (Set.uIcc ((1 / 2 : ℝ) - ρ.re) 2 ×ℂ Set.uIcc (-R) R), s ≠ 1 - ρ → s ≠ 0 →
      perronInt K Y ρ s = residueTerm K Y ρ / (s - (1 - ρ)) + perronH K Y ρ s :=
    fun _R _hR s _hs hsu hs0 => perronInt_eq_residueTerm_add_perronH K Y ρ hζ hρ1 hs0 hsu
  have hhor := perronHHorizontalOne K Y hY ρ hβ0 hβ1
  have hpint : Integrable (fun t : ℝ =>
      perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)) :=
    perronIntIntegrableSelf K Y hY ρ hζ hρ1 (c := (1 / 2 : ℝ) - ρ.re)
      (by linarith) (by linarith) (by intro h; rw [Complex.sub_re, Complex.one_re] at h; linarith) (by linarith) (by linarith)
  have hqint : Integrable (fun t : ℝ => perronInt K Y ρ (2 + (t : ℂ) * Complex.I)) := by
    have h := perronIntIntegrableSelf K Y hY ρ hζ hρ1 (c := (2 : ℝ))
      (by linarith) (by linarith) (by intro h; rw [Complex.sub_re, Complex.one_re] at h; linarith) (by norm_num) (by norm_num)
    simpa using h
  exact perronShiftSelf_divided_local (perronInt K Y ρ) (perronH K Y ρ) ((1 / 2 : ℝ) - ρ.re) 2 hp2
    (1 - ρ) (residueTerm K Y ρ) hu hH hdec hhor.1 hhor.2 hpint hqint

/-! ## Smallness of the tails of the critical-line integral -/


open scoped Classical BigOperators
open MeasureTheory

/-- (Put this in namespace `Work.ZeroDensity.Ingham`, with `open scoped Classical BigOperators` and
`open MeasureTheory`; import `Submission.Work.ZeroDensity.Ingham.Defs` and
`Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs`.)

**The tails of the critical-line integral of the detector are small.**  There is `A₀ ≥ 6` such that
for every `A ≥ A₀`, every `T ≥ 2`, all `K, Y` with `1 ≤ K ≤ T`, `1 ≤ Y ≤ T²`, and every `ρ` with
`1/2 ≤ Re ρ ≤ 1` and `|Im ρ| ≤ T`,

`Y^{1/2-Re ρ} ( ∫_{v > A log (A T)} critIntegrand K ρ v dv + ∫_{v ≤ -A log (A T)} critIntegrand K ρ v dv )
   ≤ π/10`,

where `critIntegrand K ρ v = ‖ζ(1/2 + i(Im ρ + v))‖ · ‖M_K(1/2 + i(Im ρ + v))‖ · ‖Γ(1/2 - Re ρ + iv)‖`. -/
theorem critTailSmallOne : ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ T : ℝ, 2 ≤ T →
    ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ T → 1 ≤ Y → Y ≤ T ^ 2 →
    ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      Y ^ (1 / 2 - ρ.re) *
        ((∫ v in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ v)
          + (∫ v in Set.Iic (-(A * Real.log (A * T))), critIntegrand K ρ v)) ≤ Real.pi / 10 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := zeta_halfLine_poly_bound
  have hK6pos : 0 < Commons.Analysis.Complex.K6 := Commons.Analysis.Complex.K6_pos
  set J : ℝ := ∫ s in Set.Ioi 0, (1 + s)^10 * Real.exp (-(Real.pi/2) * s) with hJdef
  set J' : ℝ := |J| + 1 with hJ'def
  have hJ'pos : 0 < J' := by rw [hJ'def]; exact add_pos_of_nonneg_of_pos (abs_nonneg J) one_pos
  have hJ'nn : 0 ≤ J' := le_of_lt hJ'pos
  have hJJ' : J ≤ J' := by rw [hJ'def]; linarith [le_abs_self J]
  set Kall : ℝ := 4 * Cz * Commons.Analysis.Complex.K6 * J' with hKalldef
  have hKallpos : 0 < Kall := by
    rw [hKalldef]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hCzpos) hK6pos) hJ'pos
  obtain ⟨A₀, hA₀6, hA₀main⟩ := OneSelf.critTailNumericOne Kall hKallpos
  refine ⟨A₀, hA₀6, ?_⟩
  intro A hA T hT K Y hK1 hKT hY1 hYT ρ hρ1 hρ2 hγ
  set H : ℝ := A * Real.log (A * T) with hHdef
  have hA6 : 6 ≤ A := le_trans hA₀6 hA
  have hApos : 0 < A := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  have hNpos : 0 < Real.log (A*T) := Real.log_pos hAT1
  have hHpos : 0 < H := by rw [hHdef]; exact mul_pos hApos hNpos
  have hlog1 : 1 ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0:ℝ) < A * T)]
    have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    nlinarith [hA6, hT, h3]
  have hH1 : 1 ≤ H := by
    rw [hHdef]
    have hmul : (6:ℝ) * 1 ≤ A * Real.log (A * T) :=
      mul_le_mul hA6 hlog1 (by norm_num) hApos.le
    linarith
  have hHnn : 0 ≤ H := le_of_lt hHpos
  have hYpow_le : Y ^ (1/2 - ρ.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hYpow_nn : 0 ≤ Y ^ (1/2 - ρ.re) := Real.rpow_nonneg (by linarith) _
  set c : ℝ := Cz * (2 * Real.sqrt K) * Commons.Analysis.Complex.K6 with hcdef
  have hc_nn : 0 ≤ c := by
    rw [hcdef]; exact mul_nonneg (mul_nonneg hCzpos.le
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg K))) hK6pos.le
  set X : ℝ := Real.exp (-(Real.pi/2)*H) * (3+T+H)^4 * (1+H)^6 with hXdef
  have h3TH : (0:ℝ) ≤ 3 + T + H := by linarith
  have h1H : (0:ℝ) ≤ 1 + H := by linarith
  have hX_nn : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg h3TH 4)) (pow_nonneg h1H 6)
  have key : ∀ u τ : ℝ, 1 ≤ |u| → |τ| ≤ T + |u| →
      ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ * ‖MK K ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ *
        ‖Complex.Gamma (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)‖
      ≤ c * ((3 + T + |u|)^4 * (1 + |u|)^6 * Real.exp (-(Real.pi/2)*|u|)) := by
    intro u τ hu hτ
    have hZ : ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ ≤ Cz * (3 + |τ|)^4 := hCz τ
    have hZ2 : Cz * (3 + |τ|)^4 ≤ Cz * (3 + T + |u|)^4 := by
      apply mul_le_mul_of_nonneg_left _ hCzpos.le
      apply pow_le_pow_left₀ (add_nonneg (by norm_num) (abs_nonneg τ)) _ 4
      linarith [hτ]
    have hM : ‖MK K ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ ≤ 2 * Real.sqrt K := by
      apply MK_critical_bound
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    have hre_z : Complex.re (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I) = (1/2:ℝ) - ρ.re := by
      simp [Complex.add_re, Complex.mul_re]
    have him_z : Complex.im (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I) = u := by
      simp [Complex.add_im, Complex.mul_im]
    have hG : ‖Complex.Gamma (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)‖ ≤
        Commons.Analysis.Complex.K6 * (1 + |u|)^(6:ℝ) * Real.exp (-(Real.pi/2)*|u|) := by
      have h := gamma_crit_bound (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)
        (by rw [hre_z]; linarith) (by rw [hre_z]; linarith) (by rw [him_z]; exact hu)
      simpa [him_z] using h
    have hZ3 : ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ ≤ Cz * (3 + T + |u|)^4 := le_trans hZ hZ2
    have hZt_nn : 0 ≤ Cz * (3 + T + |u|)^4 :=
      mul_nonneg hCzpos.le (pow_nonneg (by linarith [abs_nonneg u, hT] : (0:ℝ) ≤ 3 + T + |u|) 4)
    have hMt_nn : 0 ≤ 2 * Real.sqrt K := mul_nonneg (by norm_num) (Real.sqrt_nonneg K)
    have hGt_nn : 0 ≤ Commons.Analysis.Complex.K6 * (1 + |u|)^(6:ℝ) * Real.exp (-(Real.pi/2)*|u|) :=
      mul_nonneg (mul_nonneg hK6pos.le (Real.rpow_nonneg (add_nonneg (by norm_num) (abs_nonneg u)) 6)) (Real.exp_nonneg _)
    calc ‖riemannZeta ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ * ‖MK K ((1/2:ℂ) + (τ:ℂ)*Complex.I)‖ *
            ‖Complex.Gamma (((1/2:ℝ) - ρ.re:ℝ) + (u:ℝ)*Complex.I)‖
        ≤ (Cz * (3+T+|u|)^4) * (2*Real.sqrt K) *
            (Commons.Analysis.Complex.K6 * (1+|u|)^(6:ℝ) * Real.exp (-(Real.pi/2)*|u|)) := by
          exact mul_le_mul (mul_le_mul hZ3 hM (norm_nonneg _) hZt_nn) hG (norm_nonneg _)
            (mul_nonneg hZt_nn hMt_nn)
      _ = c * ((3+T+|u|)^4 * (1+|u|)^6 * Real.exp (-(Real.pi/2)*|u|)) := by
          rw [hcdef]
          have hpow : (1 + |u|) ^ (6:ℝ) = (1 + |u|) ^ 6 := Real.rpow_natCast (1 + |u|) 6
          rw [hpow]; ring
  have hpb_pos : ∀ v ∈ Set.Ioi H, critIntegrand K ρ v ≤
      c * ((3+T+v)^4 * (1+v)^6 * Real.exp (-(Real.pi/2)*v)) := by
    intro v hv
    have hvlt : H < v := by simpa using hv
    have hvpos : 0 < v := by linarith [hH1, hvlt]
    have harg : (1/2:ℂ) + (ρ.im:ℂ)*Complex.I + (v:ℂ)*Complex.I
        = (1/2:ℂ) + ((ρ.im + v:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hu : 1 ≤ |v| := by rw [abs_of_pos hvpos]; linarith [hH1, hvlt]
    have hτ : |ρ.im + v| ≤ T + |v| := by
      calc |ρ.im + v| ≤ |ρ.im| + |v| := abs_add_le _ _
        _ ≤ T + |v| := by linarith [hγ]
    have hk := key v (ρ.im + v) hu hτ
    rw [critIntegrand, harg]
    simpa [abs_of_pos hvpos] using hk
  have hpb_neg : ∀ v ∈ Set.Ioi H, critIntegrand K ρ (-v) ≤
      c * ((3+T+v)^4 * (1+v)^6 * Real.exp (-(Real.pi/2)*v)) := by
    intro v hv
    have hvlt : H < v := by simpa using hv
    have hvpos : 0 < v := by linarith [hH1, hvlt]
    have hargn : (1/2:ℂ) + (ρ.im:ℂ)*Complex.I + (((-v:ℝ)):ℂ)*Complex.I
        = (1/2:ℂ) + ((ρ.im - v:ℝ):ℂ)*Complex.I := by push_cast; ring
    have hu : 1 ≤ |(-v:ℝ)| := by rw [abs_neg, abs_of_pos hvpos]; linarith [hH1, hvlt]
    have hτ : |ρ.im - v| ≤ T + |(-v:ℝ)| := by
      rw [abs_neg, abs_of_pos hvpos]
      calc |ρ.im - v| ≤ |ρ.im| + |v| := by
              rw [sub_eq_add_neg]; exact le_trans (abs_add_le _ _) (by rw [abs_neg])
        _ ≤ T + v := by rw [abs_of_pos hvpos]; linarith [hγ]
    have hk := key (-v) (ρ.im - v) hu hτ
    rw [critIntegrand, hargn]
    simpa [abs_neg, abs_of_pos hvpos] using hk
  have hI1 : (∫ v in Set.Ioi H, critIntegrand K ρ v) ≤ c * (X * J) := by
    rw [hJdef, hXdef]
    refine integralIoiPolyexpLocal T H c (by linarith) hH1 hc_nn (fun v => critIntegrand K ρ v) ?_ ?_
    · intro v _; simp only [critIntegrand]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    · intro v hv; exact hpb_pos v hv
  have hI2 : (∫ v in Set.Iic (-H), critIntegrand K ρ v) ≤ c * (X * J) := by
    rw [hJdef, hXdef]
    rw [← integral_comp_neg_Ioi H (fun x => critIntegrand K ρ x)]
    refine integralIoiPolyexpLocal T H c (by linarith) hH1 hc_nn (fun v => critIntegrand K ρ (-v)) ?_ ?_
    · intro v _; simp only [critIntegrand]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    · intro v hv; exact hpb_neg v hv
  have hI1' : (∫ v in Set.Ioi H, critIntegrand K ρ v) ≤ c * (X * J') := by
    calc (∫ v in Set.Ioi H, critIntegrand K ρ v) ≤ c * (X * J) := hI1
      _ ≤ c * (X * J') := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJJ' hX_nn) hc_nn
  have hI2' : (∫ v in Set.Iic (-H), critIntegrand K ρ v) ≤ c * (X * J') := by
    calc (∫ v in Set.Iic (-H), critIntegrand K ρ v) ≤ c * (X * J) := hI2
      _ ≤ c * (X * J') := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJJ' hX_nn) hc_nn
  have hsum : (∫ v in Set.Ioi H, critIntegrand K ρ v) + (∫ v in Set.Iic (-H), critIntegrand K ρ v)
      ≤ 2 * (c * (X * J')) := by linarith [hI1', hI2']
  have h2X : 0 ≤ 2 * (c * (X * J')) :=
    mul_nonneg (by norm_num) (mul_nonneg hc_nn (mul_nonneg hX_nn hJ'nn))
  have hfin : 2 * (c * (X * J')) ≤ Kall * Real.sqrt T * X := by
    rw [hKalldef]
    have h2c : 2 * c * J' ≤ 4 * Cz * Commons.Analysis.Complex.K6 * J' * Real.sqrt T := by
      rw [show 2 * c * J' = (4 * Cz * Commons.Analysis.Complex.K6 * J') * Real.sqrt K by
            rw [hcdef]; ring]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKT)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCzpos.le) hK6pos.le) hJ'nn)
    calc 2 * (c * (X * J')) = (2 * c * J') * X := by ring
      _ ≤ (4 * Cz * Commons.Analysis.Complex.K6 * J' * Real.sqrt T) * X :=
            mul_le_mul_of_nonneg_right h2c hX_nn
      _ = 4 * Cz * Commons.Analysis.Complex.K6 * J' * Real.sqrt T * X := by ring
  calc Y ^ (1/2 - ρ.re) *
        ((∫ v in Set.Ioi H, critIntegrand K ρ v) + (∫ v in Set.Iic (-H), critIntegrand K ρ v))
      ≤ Y ^ (1/2 - ρ.re) * (2 * (c * (X * J'))) := mul_le_mul_of_nonneg_left hsum hYpow_nn
    _ ≤ 1 * (2 * (c * (X * J'))) := mul_le_mul_of_nonneg_right hYpow_le h2X
    _ = 2 * (c * (X * J')) := by ring
    _ ≤ Kall * Real.sqrt T * X := hfin
    _ ≤ Real.pi / 10 := by
        have hnum := hA₀main A hA T hT
        have heq : Kall * Real.sqrt T * X = Kall * Real.sqrt T * (3 + T + A*Real.log (A*T))^4
            * (1 + A*Real.log (A*T))^6 * Real.exp (-(Real.pi/2)*(A*Real.log (A*T))) := by
          rw [hXdef, hHdef]; ring
        rw [heq]; exact hnum



/-! ## The assembly step -/

private lemma assembly_step_one (T : ℝ) (hT : 2 ≤ T) (K : ℕ) (Y : ℝ) (ρ : ℂ) (A : ℝ)
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
      rw [integral_eq_Ioc_add_tails_one hline hH0]
      have hAi : ‖∫ t in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
          perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)‖ < 1 / 12 := by
        refine lt_of_le_of_lt ?_ hcon'
        refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith [hH0])) ?_
        rw [intervalIntegral.integral_congr (fun t _ => norm_perronInt_critLine_one K Y hYpos ρ t),
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
                (fun t _ => norm_perronInt_critLine_one K Y hYpos ρ t)]
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
                (fun t _ => norm_perronInt_critLine_one K Y hYpos ρ t)]
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
    linarith [hge1, hexpbd, detector_error_lt_exp_neg_one_one]
  · exact Or.inl hge

/-! ## The zero detector at `C = 1` -/

theorem zetaDetectorOneSelf :
    ∃ A : ℝ, 6 ≤ A ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ T →
      1 ≤ Y → Y ≤ T ^ 2 →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        (1 / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖)
          ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
              ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
                ‖riemannZeta ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                  * ‖MK K ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                  * ‖Complex.Gamma (((1 / 2 : ℝ) - ρ.re : ℝ) + (v : ℝ) * Complex.I)‖) := by
  obtain ⟨Af, hAf6, hAf⟩ := detFarTailSmall
  obtain ⟨Ar, hAr6, hAr⟩ := residueTermSmall
  obtain ⟨Ac, hAc6, hAc⟩ := critTailSmallOne
  refine ⟨max (max Af Ar) Ac, ?_, ?_⟩
  · exact le_trans hAf6 (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro T hT K Y hK1 hKT hY1 hYT2 ρ hζ hβ0 hβ1 hγ hlog
    have hAfA : Af ≤ max (max Af Ar) Ac := le_trans (le_max_left _ _) (le_max_left _ _)
    have hArA : Ar ≤ max (max Af Ar) Ac := le_trans (le_max_right _ _) (le_max_left _ _)
    have hAcA : Ac ≤ max (max Af Ar) Ac := le_max_right _ _
    set A : ℝ := max (max Af Ar) Ac with hA
    have hA6 : 6 ≤ A := le_trans hAf6 hAfA
    have hApos : 0 < A := by linarith
    have hTpos : 0 < T := by linarith
    have hYpos : 0 < Y := by linarith
    have hAT1 : 1 < A * T := by nlinarith
    have himne : ρ.im ≠ 0 := by
      intro h
      have h2 : (Real.log (A * T)) ^ 2 ≤ 0 := by
        rw [h, abs_zero] at hlog
        linarith
      have h3 : 0 < (Real.log (A * T)) ^ 2 := by
        apply pow_pos
        exact Real.log_pos hAT1
      linarith
    have hρ1 : ρ ≠ 1 := by
      intro h1
      apply himne
      rw [h1]
      simp
    have hfar : ‖detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ‖ ≤ 1 / 20 :=
      hAf A hAfA T hT K Y hK1 hKT hY1 hYT2 ρ hβ0 hβ1 hγ
    have hres : ‖residueTerm K Y ρ‖ ≤ 1 / 20 :=
      hAr A hArA T hT K Y hK1 hKT hY1 hYT2 ρ hβ0 hβ1 hγ hlog
    have hcrit : Y ^ (1 / 2 - ρ.re) *
        ((∫ v in Set.Ioi (A * Real.log (A * T)), critIntegrand K ρ v)
          + (∫ v in Set.Iic (-(A * Real.log (A * T))), critIntegrand K ρ v)) ≤ Real.pi / 10 :=
      hAc A hAcA T hT K Y hK1 hKT hY1 hYT2 ρ hβ0 hβ1 hγ
    have hline : Integrable (fun t : ℝ =>
        perronInt K Y ρ (((1 / 2 : ℝ) - ρ.re : ℝ) + (t : ℂ) * Complex.I)) :=
      perronIntIntegrableSelf K Y hYpos ρ hζ hρ1 (c := (1 / 2 : ℝ) - ρ.re)
        (by linarith) (by linarith) (by intro h; rw [Complex.sub_re, Complex.one_re] at h; linarith) (by linarith) (by linarith)
    have hperron : detSum K Y ρ = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I) :=
      zetaPerronIdentity K Y hYpos ρ (by linarith)
    have hshift := perronShiftOne K Y hYpos ρ hζ hβ0 hβ1 hρ1
    have hZ1 : 1 ≤ Y * (Real.log (A * T)) ^ 2 := by
      have h1 : (1 : ℝ) ≤ Real.log (A * T) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        nlinarith [Real.exp_one_lt_three, hA6, hT]
      have h2 : (1 : ℝ) ≤ (Real.log (A * T)) ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h1 2
        simpa using this
      nlinarith
    have hsplit : detSum K Y ρ = ((Real.exp (-(1 / Y)) : ℝ) : ℂ)
        + detTail K Y (Y * (Real.log (A * T)) ^ 2) ρ
        + detFarTail K Y (Y * (Real.log (A * T)) ^ 2) ρ :=
      detSumSplit K Y (Y * (Real.log (A * T)) ^ 2) hYpos hK1 hZ1 ρ
    rcases assembly_step_one T hT K Y ρ A hY1 hA6 hfar hres hcrit hline hperron hshift hsplit
      with h | h
    · left
      simpa only [detTail] using h
    · right
      simpa only [critIntegrand] using h

end Work.ZeroDensity.Ingham
