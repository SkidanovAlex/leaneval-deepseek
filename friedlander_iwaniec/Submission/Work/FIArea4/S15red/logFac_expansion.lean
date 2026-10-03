/-
# The log-sine Fourier expansion of `logFac` (FI (15.5)–(15.7))

This is the analytic input of the §15 separation: `-log(|sin α|/2)` is expanded, on the range
`1/N ≤ |α| ≤ 1`, as an **absolutely convergent complex Fourier series** with coefficients whose
`ℓ¹`-norm is `O((log N + 1)²)`.

The two ingredients are delegated:

* `Work.FIArea4.S15red.logSine_fourier_summable` — the mollified log-sine expansion of
  `Work.FIArea4.logSine_fourier`, upgraded to *summable* coefficients (the coefficients are the
  Fourier coefficients of the smooth `2π`-periodic mollification `logSine_Ffun N`, so absolute
  summability is available in the proof), on the range `2/N ≤ |α| ≤ 1`.

* `Work.FIArea4.S15red.symmetrize_coeffs` — the Hermitian symmetrisation `c ↦ (c ℓ + conj c(-ℓ))/2`,
  which does not increase the `ℓ¹`-norm and turns the real-part identity into a genuine *complex*
  identity (the symmetrised coefficients are real-valued/even, i.e. `d (-ℓ) = conj (d ℓ)`, so
  `Σ d ℓ e^{iℓα} = (F + conj F)/2 = Re F`).

Two elementary reductions turn the range `2/M ≤ |α|` of the expansion (applied with the integer
`M = ⌈2N⌉ ≥ 2N`) into the range `1/N ≤ |α|` asked for, and convert the constant: since `M ≤ 3N`
for `N ≥ 1`, one has `log M ≤ (log 3 + 1)(log N + 1)`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea4.S15red.logSine_fourier_summable
import Submission.Work.FIArea4.S15red.symmetrize_coeffs

namespace Work.FIArea4.S15red

theorem logFac_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params), ∃ c : ℤ → ℂ,
      Summable c ∧ Summable (fun ℓ : ℤ => ‖c ℓ‖) ∧
      (∑' ℓ : ℤ, ‖c ℓ‖) ≤ C * (Real.log (Pa.N : ℝ) + 1) ^ (2 : ℕ) ∧
      ∀ α : ℝ, 1 / (Pa.N : ℝ) ≤ |α| → |α| ≤ 1 →
        (-(Real.log (|Real.sin α| / 2)) : ℂ)
          = ∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := logSine_fourier_summable
  refine ⟨C0 * (Real.log 3 + 1) ^ 2, by positivity, ?_⟩
  intro Pa
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hNPpos : (0:ℝ) < Pa.N := by linarith
  -- the integer mollifying parameter: `⌈2N⌉ ≥ 2N`, so that `2/⌈2N⌉ ≤ 1/N`
  set N' : ℕ := ⌈2 * Pa.N⌉₊ with hN'def
  have hN'ge : 2 * Pa.N ≤ (N' : ℝ) := Nat.le_ceil _
  have hN'lt : (N' : ℝ) < 2 * Pa.N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN'pos : (0:ℝ) < (N' : ℝ) := by linarith
  have hN'2 : 2 ≤ N' := by
    have : (2:ℝ) ≤ (N' : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨c, _hcsum, hcn, hcbd, hcpt⟩ := hC0 N' hN'2
  obtain ⟨hdsum, hdn, hdbd, hdpt⟩ := symmetrize_coeffs hcn
  refine ⟨fun ℓ => (c ℓ + star (c (-ℓ))) / 2, hdsum, hdn, ?_, ?_⟩
  · -- `ℓ¹`-bound: `Σ ‖d‖ ≤ Σ ‖c‖ ≤ C₀ (log ⌈2N⌉)² ≤ C (log N + 1)²`
    have hlogN' : Real.log (N' : ℝ) ≤ (Real.log 3 + 1) * (Real.log Pa.N + 1) := by
      have hN'le : (N':ℝ) ≤ 3 * Pa.N := by nlinarith [hN'lt, hN1]
      have hlog3N : Real.log (N':ℝ) ≤ Real.log (3 * Pa.N) := Real.log_le_log hN'pos hN'le
      have hsplit : Real.log (3 * Pa.N) = Real.log 3 + Real.log Pa.N :=
        Real.log_mul (by norm_num) (by linarith)
      rw [hsplit] at hlog3N
      have hlogN0 : 0 ≤ Real.log Pa.N := Real.log_nonneg hN1
      have hprod : 0 ≤ Real.log 3 * Real.log Pa.N :=
        mul_nonneg (Real.log_nonneg (by norm_num)) hlogN0
      nlinarith [hlog3N, hprod]
    have hsq : (Real.log (N':ℝ)) ^ 2 ≤ ((Real.log 3 + 1) * (Real.log Pa.N + 1)) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogN' 2
    calc (∑' ℓ : ℤ, ‖(c ℓ + star (c (-ℓ))) / 2‖)
        ≤ ∑' ℓ : ℤ, ‖c ℓ‖ := hdbd
      _ ≤ C0 * (Real.log (N':ℝ)) ^ 2 := hcbd
      _ ≤ C0 * ((Real.log 3 + 1) * (Real.log Pa.N + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (le_of_lt hC0pos)
      _ = C0 * (Real.log 3 + 1) ^ 2 * (Real.log (Pa.N:ℝ) + 1) ^ 2 := by ring
  · -- the identity on the range `1/N ≤ |α| ≤ 1`
    intro α hα1 hα2
    have h2N' : 2 / (N':ℝ) ≤ 1 / Pa.N := by
      rw [div_le_div_iff₀ hN'pos hNPpos]
      simpa using hN'ge
    rw [hdpt α]
    rw [← hcpt α (le_trans h2N' hα1) hα2]
    push_cast
    ring

end Work.FIArea4.S15red
