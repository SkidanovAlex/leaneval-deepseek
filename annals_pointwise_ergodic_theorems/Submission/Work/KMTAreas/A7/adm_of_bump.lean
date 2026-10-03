/-
# Admissibility of compactly supported `C²` bumps

The predicate `Work.KMTAreas.A7.Adm A φ` (defined in `Tm_randSymb_Adm`) collects the three
analytic properties of a symbol `φ : ℝ → ℂ` which make the exact-height Ionescu–Wainger operator
`Tm ρ l φ = iwConv (diffFreqs ρ l) (periodize φ)` additive in the symbol for bounded input:

1. `∀ x : ℝ, Summable fun j : ℤ => φ (x + j)` — the translates of `φ` are summable, so that
   `periodize` behaves additively;
2. `Integrable (iwSymbolSet A (periodize φ)) circleMeasure` — the IW symbol is integrable, so that
   its Fourier coefficients (the IW kernel) are additive in the symbol;
3. `Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize φ)) j‖` — the kernel is in `ℓ¹`, so
   that a bounded input makes the defining `tsum` of `iwConv` summable.

This module proves that every `C²` function with compact support is admissible at every finite
frequency set `A`:

* for (1): `φ` vanishes outside `[-R, R]` (`exists_abs_le_of_hasCompactSupport`), hence for fixed
  `x` the support of `j ↦ φ (x + j)` is contained in the finite interval `[-N, N]` with
  `N ≥ R + |x|`; a finitely supported sequence is summable;
* for (2): `φ` is continuous with compact support, hence integrable on `ℝ`, and the periodisation
  of an integrable function is integrable on the circle (`IntegrablePeriodize`); a finite sum of
  translates of an integrable function is integrable;
* for (3): the kernel of the IW symbol of a `C²` compactly supported bump decays like `j^{-2}`
  (`iwKernel_decay_of_bump`, whose comparison weight `kmtKernWeight` is summable), hence it is in
  `ℓ¹`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Tm_randSymb_Adm
import Submission.Work.KMTPlan.A6.IntegrablePeriodize

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **The translates of a compactly supported function are summable.**  If `φ` vanishes beyond a
radius `R`, then for a fixed `x` the sequence `j ↦ φ (x + j)` is supported in the finite interval
of integers `[-N, N]`, where `N ≥ R + |x|`, hence it is summable. -/
theorem summable_translate_of_hasCompactSupport {φ : ℝ → ℂ} (hcs : HasCompactSupport φ) (x : ℝ) :
    Summable fun j : ℤ => φ (x + (j : ℝ)) := by
  obtain ⟨R, hR⟩ := exists_abs_le_of_hasCompactSupport hcs
  obtain ⟨N, hN⟩ := exists_nat_ge (R + |x|)
  refine summable_of_hasFiniteSupport ?_
  refine Set.Finite.subset (Set.finite_Icc (-(N : ℤ)) (N : ℤ)) ?_
  intro j hj
  rw [Function.mem_support] at hj
  -- `φ (x + j) ≠ 0` forces `|j| ≤ N`.
  have hle : |(j : ℝ)| ≤ (N : ℝ) := by
    by_contra hcon
    rw [not_le] at hcon
    -- reverse triangle inequality: `|j| - |x| ≤ |j + x|`
    have hrev : |(j : ℝ)| - |x| ≤ |(j : ℝ) + x| := by
      have h := abs_sub_abs_le_abs_sub (j : ℝ) (-x)
      simpa [sub_eq_add_neg, abs_neg] using h
    have hgt : R ≤ |x + (j : ℝ)| := by
      rw [add_comm]
      linarith
    exact hj (hR _ hgt)
  obtain ⟨h1, h2⟩ := abs_le.mp hle
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- **Every `C²` compactly supported bump is admissible at every finite frequency set.** -/
theorem adm_of_bump {A : Finset Work.Analysis.IonescuWainger.Circle} {F : ℝ → ℂ}
    (hcd : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) : Work.KMTAreas.A7.Adm A F := by
  have hcont : Continuous F := hcd.continuous
  have hIntF : Integrable F := hcont.integrable_of_hasCompactSupport hcs
  refine ⟨fun x => summable_translate_of_hasCompactSupport hcs x, ?_, ?_⟩
  · -- (2) integrability of the IW symbol of the periodisation
    have hIntPer : Integrable (periodize F) circleMeasure :=
      Work.KMTPlan.A6.IntegrablePeriodize hIntF
    have hsum : Integrable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
        ∑ α ∈ A, periodize F (ξ - α)) circleMeasure :=
      integrable_finsetSum A (fun α _ => hIntPer.comp_sub_right α)
    exact hsum
  · -- (3) `ℓ¹` summability of the IW kernel
    obtain ⟨S, hS0, hS1, hS2⟩ :
        ∃ S : ℝ, 0 ≤ S ∧ (∫ y, ‖F y‖) ≤ S ∧ (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S :=
      ⟨max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖),
        le_max_of_le_left (integral_nonneg fun y => norm_nonneg _),
        le_max_left _ _, le_max_right _ _⟩
    have hdec : ∀ j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖
        ≤ (4 * ((A.card : ℝ) * S) + 1) * ‖kmtKernWeight j‖ :=
      iwKernel_decay_of_bump A hcd hcs hS0 hS1 hS2
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
      (summable_kmtKernWeight.mul_left (4 * ((A.card : ℝ) * S) + 1))

end

end Work.KMTAreas.A7
