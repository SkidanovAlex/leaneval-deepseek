import Submission.Commons.Analysis.Fourier.localization_l2
import Submission.Commons.Analysis.Fourier.norm_sum_sq_le_of_bounded_overlap

open MeasureTheory FourierTransform
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `κ`-form of the localisation estimate with an EXPLICIT exponent

**WARNING (Session 55).**  This file is *correct* but is **NOT sufficient** for Han–Schlag's
Lemma 4.3, and nothing in the final chain should depend on it.  The interpolation below gives the
`κ`-form of the localisation estimate only with the *extra factor* `A_LS^κ = (C_LS/λ)^{C_LS·R·κ}`;
absorbing it into the constant `e^{C/q}` (which is what the reduction needs — the constant must be
independent of the band limit `R = σ`) requires `κ·C_LS·σ·log(C_LS/λ) ≤ C/q`, i.e.
`R·(log R)^{α}·e^{-C'(log R)^α} ≤ const`, which is **false for large `R`**.  Consequently the plain
Logvinenko–Sereda theorem cannot yield the fixed-`κ` localisation (`prop:locddim`) at all: see
`Submission/FUP/ROADMAP.md`, Session 55, §1.  Keep the *arithmetic* lemma
`kappa_interpolation` (it is a correct and reusable interpolation statement); do not treat
`localization_kappa_explicit` as the deep input.

`Commons.Analysis.Fourier.localization_kappa_d` states the band-limit-free localisation estimate
of Han–Schlag (`prop:locddim`) in the form `∃ κ ≤ U, ...`.  The proof of Han–Schlag's Lemma 4.3
(`lem:mainlem`) needs the estimate at a *specific*, explicit value of `κ` (it is raised to the
power `1/(2κ)` at the end, and the sum over the modulations `ℓ ∈ (2ℤ)^d` requires a single `κ`
for all `ℓ`), so the existential form is not sufficient.  Here we re-derive the estimate from the
plain quantitative Logvinenko–Sereda theorem `Commons.Analysis.Fourier.localization_l2`, by the
interpolation

  `A = A^{1-κ}A^κ ≤ W^{1-κ}(A_LS·P)^κ = A_LS^κ P^κ W^{1-κ} ≤ e^{C/q}P^κ W^{1-κ}`

valid for **every** `κ ∈ (0,1]` satisfying the absorption condition `κ log A_LS ≤ C/q`.
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The interpolation step: from `A ≤ A_LS · P`, `A ≤ W` and `κ log A_LS ≤ C/q` one gets
`A ≤ e^{C/q} P^κ W^{1-κ}`. -/
theorem kappa_interpolation {A_LS P W A q κ C : ℝ}
    (_hq : 0 < q) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hALS : 0 < A_LS) (hA : 0 ≤ A) (hAW : A ≤ W) (hAP : A ≤ A_LS * P)
    (habs : κ * Real.log A_LS ≤ C / q) :
    A ≤ Real.exp (C / q) * P ^ κ * W ^ (1 - κ) := by
  rcases eq_or_lt_of_le hA with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hP _))
      (Real.rpow_nonneg hW _)
  have hsplit : A = A ^ (1 - κ) * A ^ κ := by
    rw [← Real.rpow_add hpos]
    norm_num
  rw [hsplit]
  have h1 : A ^ (1 - κ) ≤ W ^ (1 - κ) := Real.rpow_le_rpow hA hAW (by linarith)
  have h2 : A ^ κ ≤ (A_LS * P) ^ κ := Real.rpow_le_rpow hA hAP (le_of_lt hκ)
  have h3 : (A_LS * P) ^ κ = A_LS ^ κ * P ^ κ :=
    Real.mul_rpow (le_of_lt hALS) hP
  have h4 : A_LS ^ κ ≤ Real.exp (C / q) := by
    rw [Real.rpow_def_of_pos hALS]
    exact Real.exp_le_exp.mpr (by rw [mul_comm]; exact habs)
  calc A ^ (1 - κ) * A ^ κ
      ≤ W ^ (1 - κ) * (A_LS ^ κ * P ^ κ) := by
        rw [← h3]; exact mul_le_mul h1 h2 (Real.rpow_nonneg hA κ) (Real.rpow_nonneg hW _)
    _ ≤ W ^ (1 - κ) * (Real.exp (C / q) * P ^ κ) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hP κ))
          (Real.rpow_nonneg hW _)
    _ = Real.exp (C / q) * P ^ κ * W ^ (1 - κ) := by ring

/-- **The `κ`-form of the localisation estimate with an explicit exponent.**
For every `κ ∈ (0,1]` satisfying the absorption condition `κ C σ log(C/lam) ≤ C/q`, every
`L²` function band-limited to `∑ᵢ|ξᵢ| ≤ σ` satisfies
`∫‖f‖² ≤ e^{C/q}(∫_E‖f‖²)^κ (∫e^{4πq|ξ|₁}‖𝓕f ξ‖²)^{1-κ}`,
where `E` meets every cell of the side-`2` grid in measure at least `lam·2^d`. -/
theorem localization_kappa_explicit :
    ∃ C : ℝ, 0 < C ∧
      ∀ (lam q σ κ : ℝ), 0 < lam → lam ≤ 1 → 0 < q → 1 ≤ σ → 0 < κ → κ ≤ 1 →
        κ * (C * σ * Real.log (C / lam)) ≤ C / q →
        ∀ (γ : ℝᵈ) (E : Set ℝᵈ), MeasurableSet E →
          (∀ n : Fin d → ℤ, lam * 2 ^ d ≤
            ((volume : Measure ℝᵈ) (E ∩ {x : ℝᵈ |
              ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ x i ∧
                x i ≤ 2 * (n i : ℝ) + γ i + 2})).toReal) →
          ∀ (f : ℝᵈ → ℂ) (hf : MemLp f 2 (volume : Measure ℝᵈ)),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ), σ < ∑ i : Fin d, |ξ i| →
              ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) →
            MeasureTheory.integral volume (fun x : ℝᵈ => ‖f x‖ ^ 2)
              ≤ Real.exp (C / q) *
                (MeasureTheory.integral (volume.restrict E)
                  (fun x : ℝᵈ => ‖f x‖ ^ 2)) ^ κ *
                (MeasureTheory.integral volume
                  (fun ξ : ℝᵈ => Real.exp (4 * Real.pi * q * (∑ i : Fin d, |ξ i|)) *
                    ‖((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ‖ ^ 2))
                  ^ (1 - κ) := by
  obtain ⟨C₀, hC₀pos, hLS⟩ := Commons.Analysis.Fourier.localization_l2 d
  refine ⟨max C₀ 1, lt_max_of_lt_left hC₀pos, ?_⟩
  intro lam q σ κ hlam hlam1 hq hσ hκ hκ1 habs γ E hE hEm f hf hsupp
  -- abbreviations
  set F : ℝᵈ → ℂ := ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) with hF
  set C : ℝ := max C₀ 1 with hC
  have hCpos : 0 < C := lt_max_of_lt_left hC₀pos
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC₀le : C₀ ≤ C := le_max_left _ _
  -- the LS and the absorption of its exponential loss
  have hLSapp : MeasureTheory.integral volume (fun x : ℝᵈ => ‖f x‖ ^ 2)
      ≤ (C₀ / lam) ^ (C₀ * σ) * MeasureTheory.integral (volume.restrict E)
          (fun x : ℝᵈ => ‖f x‖ ^ 2) :=
    hLS σ lam hσ hlam hlam1 γ E hE hEm f hf hsupp
  have hlog_abs : κ * Real.log ((C₀ / lam) ^ (C₀ * σ)) ≤ C / q := by
    have hqpos : 0 < C / q := div_pos hCpos hq
    rw [Real.log_rpow (div_pos hC₀pos hlam)]
    rcases lt_or_ge C₀ lam with hlt | hge
    · have hlogneg : Real.log (C₀ / lam) < 0 :=
        Real.log_neg (div_pos hC₀pos hlam) (by rw [div_lt_one hlam]; exact hlt)
      have h1 : C₀ * σ * Real.log (C₀ / lam) ≤ 0 := by
        have h2 : 0 ≤ C₀ * σ := mul_nonneg (le_of_lt hC₀pos) (by linarith)
        nlinarith [h2, hlogneg]
      nlinarith [h1, hqpos, hκ]
    · have hlogC₀ : 0 ≤ Real.log (C₀ / lam) := Real.log_nonneg (one_le_div hlam |>.mpr hge)
      have hlogC : Real.log (C₀ / lam) ≤ Real.log (C / lam) :=
        Real.log_le_log (div_pos hC₀pos hlam)
          (div_le_div_of_nonneg_right hC₀le (le_of_lt hlam))
      have h1 : C₀ * σ * Real.log (C₀ / lam) ≤ C * σ * Real.log (C / lam) := by
        have h2 : C₀ * Real.log (C₀ / lam) ≤ C * Real.log (C / lam) :=
          mul_le_mul hC₀le hlogC hlogC₀ (le_of_lt hCpos)
        have h3 : 0 ≤ σ := by linarith
        nlinarith [h2, h3, mul_nonneg (le_of_lt hC₀pos) h3,
          mul_nonneg (le_of_lt hCpos) h3]
      exact le_trans (mul_le_mul_of_nonneg_left h1 (le_of_lt hκ)) habs
  -- `F` is integrable and the weighted integrand is integrable
  have hFmem : MemLp F 2 (volume : Measure ℝᵈ) := Lp.memLp _
  have hFint : Integrable (fun ξ : ℝᵈ => ‖F ξ‖ ^ 2) (volume : Measure ℝᵈ) :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).mp hFmem
  have hbdd : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      Real.exp (4 * Real.pi * q * (∑ i : Fin d, |ξ i|)) * ‖F ξ‖ ^ 2
        ≤ Real.exp (4 * Real.pi * q * σ) * ‖F ξ‖ ^ 2 := by
    filter_upwards [hsupp] with ξ hξ
    by_cases hle : (∑ i : Fin d, |ξ i|) ≤ σ
    · exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle (by positivity))) (sq_nonneg _)
    · rw [hξ (lt_of_not_ge hle), norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero,
        mul_zero]
  have hWint : Integrable (fun ξ : ℝᵈ => Real.exp (4 * Real.pi * q * (∑ i : Fin d, |ξ i|))
      * ‖F ξ‖ ^ 2) (volume : Measure ℝᵈ) := by
    refine Integrable.mono' (hFint.const_mul (Real.exp (4 * Real.pi * q * σ))) ?_ ?_
    · refine ((Real.measurable_exp.comp ?_).aestronglyMeasurable).mul
        (hFmem.aestronglyMeasurable.norm.pow 2)
      fun_prop
    · filter_upwards [hbdd] with ξ hξ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
      exact hξ
  -- `A ≤ W`
  have hAeq : MeasureTheory.integral volume (fun x : ℝᵈ => ‖f x‖ ^ 2)
      = ∫ ξ : ℝᵈ, ‖F ξ‖ ^ 2 := by
    have h2 : ∫ x : ℝᵈ, ‖f x‖ ^ 2 = ‖hf.toLp f‖ ^ 2 := by
      rw [← Commons.Analysis.Fourier.lp_integral_norm_sq (hf.toLp f)]
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
    have h3 : ∫ ξ : ℝᵈ, ‖F ξ‖ ^ 2 = ‖(𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ))‖ ^ 2 := by
      rw [hF]
      exact Commons.Analysis.Fourier.lp_integral_norm_sq _
    rw [h2, h3, MeasureTheory.Lp.norm_fourier_eq]
  have hAW : MeasureTheory.integral volume (fun x : ℝᵈ => ‖f x‖ ^ 2)
      ≤ MeasureTheory.integral volume (fun ξ : ℝᵈ => Real.exp (4 * Real.pi * q * (∑ i : Fin d, |ξ i|))
          * ‖F ξ‖ ^ 2) := by
    rw [hAeq]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ξ => sq_nonneg _)) hWint ?_
    filter_upwards with ξ
    have h1 : (1 : ℝ) ≤ Real.exp (4 * Real.pi * q * (∑ i : Fin d, |ξ i|)) :=
      Real.one_le_exp (by positivity)
    nlinarith [sq_nonneg ‖F ξ‖]
  -- apply the interpolation
  have hALSpos : 0 < (C₀ / lam) ^ (C₀ * σ) :=
    Real.rpow_pos_of_pos (div_pos hC₀pos hlam) _
  have hkey := kappa_interpolation hq hκ hκ1
    (integral_nonneg (fun x => by positivity)) (integral_nonneg (fun x => by positivity))
    hALSpos (integral_nonneg (fun x => by positivity)) hAW hLSapp hlog_abs
  exact hkey

end Submission.FUP
