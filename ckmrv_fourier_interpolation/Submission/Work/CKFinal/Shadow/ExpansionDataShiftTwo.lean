import Submission.Work.FunctionalEquations.ExpansionDataShiftTwo
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tsum_shift_one_two)
end Work.FunctionalEquations

/-!
# Shifting the Fourier expansion from `m ≥ 1` to `m ≥ 2`

`Work.FE.ExpansionData n S basis` records the Fourier expansions of `F` and `F̃`
together with their termwise radial derivatives, indexed by `Set.Ici 1`.  If the four
coefficient functions at the index `m = 1` vanish (the case of the Leech lattice,
`k₀ = 2`), then the whole expansion may be re-indexed from `Set.Ici 2`: restricting the
basis to `m ≥ 2` gives the same expansions, because the missing `m = 1` terms are zero.

The only analytic input needed for the re-indexing is that a sum over `Set.Ici 1` of a
sequence extended by `0` at the index `1` equals the sum over `Set.Ici 2`; this is
`tsum_shift_one_two`, proved from `tsum_subtype_eq_of_support_subset` (no summability
hypothesis is required).
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The radial derivative of a function vanishing along the first coordinate axis is
zero there. -/
private lemma radialDeriv_zero_fun {n : ℕ} [NeZero n] (ℓ : ℕ) (x : E n) :
    radialDeriv ℓ (0 : E n → ℂ) x = 0 := by
  simp [Work.FE.radialDeriv]

/-- A sequence on `ℕ` vanishing at `0` and `1` has the same sum over `Set.Ici 1` and
over `Set.Ici 2`.  This is the index-shifting step, stated on `ℕ`; the proof replaces
both sums by the sum over all of `ℕ`, which only sees the support of the sequence. -/
private lemma tsum_Ici_one_eq_two_nat (f : ℕ → ℂ) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    (∑' m : Set.Ici (1:ℕ), f m) = ∑' m : Set.Ici (2:ℕ), f m := by
  have hA : (∑' m : Set.Ici (1:ℕ), f (m:ℕ)) = ∑' n : ℕ, f n := by
    apply tsum_subtype_eq_of_support_subset
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra h
    simp only [Set.mem_Ici, not_le] at h
    have : n = 0 := by omega
    rw [this, h0] at hn
    exact hn rfl
  have hB : (∑' m : Set.Ici (2:ℕ), f (m:ℕ)) = ∑' n : ℕ, f n := by
    apply tsum_subtype_eq_of_support_subset
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra h
    simp only [Set.mem_Ici, not_le] at h
    have : n = 0 ∨ n = 1 := by omega
    rcases this with h' | h'
    · rw [h', h0] at hn; exact hn rfl
    · rw [h', h1] at hn; exact hn rfl
  rw [hA, hB]

theorem ExpansionDataShiftTwo {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) (hExp : ExpansionData n S basis)
    (hv : ∀ (j : Fin 4) (x : E n), (basis (⟨1, by simp⟩, j)).1 x = 0) :
    ∃ basis₂ : SampleIdx 2 → RSch n, ExpansionDataGen n 2 S basis₂ := by
  obtain ⟨hF, hFt, hD, hDt, hG⟩ := hExp
  refine ⟨fun i => basis (⟨i.1.1,
      Set.mem_Ici.mpr (le_trans (by norm_num) (Set.mem_Ici.mp i.1.2))⟩, i.2), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ x hτ
    rw [hF τ x hτ,
      tsum_shift_one_two (c := fun m => (basis (m, 0)).1 x) (hv 0 x) τ,
      tsum_shift_one_two (c := fun m => (rate m.1 : ℂ) * (basis (m, 2)).1 x)
        (by simp [hv 2 x]) τ]
  · intro τ x hτ
    rw [hFt τ x hτ,
      tsum_shift_one_two (c := fun m => (basis (m, 1)).1 x) (hv 1 x) τ,
      tsum_shift_one_two (c := fun m => (rate m.1 : ℂ) * (basis (m, 3)).1 x)
        (by simp [hv 3 x]) τ]
  · intro ℓ τ x hτ
    rw [hD ℓ τ x hτ,
      tsum_shift_one_two (c := fun m => radialDeriv ℓ (⇑(basis (m, 0)).1) x)
        (by
          have : (⇑(basis (⟨1, by simp⟩, 0)).1 : E n → ℂ) = 0 := funext (hv 0)
          rw [this]
          exact radialDeriv_zero_fun ℓ x) τ,
      tsum_shift_one_two
        (c := fun m => (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 2)).1) x)
        (by
          have : (⇑(basis (⟨1, by simp⟩, 2)).1 : E n → ℂ) = 0 := funext (hv 2)
          rw [this, radialDeriv_zero_fun ℓ x, mul_zero]) τ]
  · intro ℓ τ x hτ
    rw [hDt ℓ τ x hτ,
      tsum_shift_one_two (c := fun m => radialDeriv ℓ (⇑(basis (m, 1)).1) x)
        (by
          have : (⇑(basis (⟨1, by simp⟩, 1)).1 : E n → ℂ) = 0 := funext (hv 1)
          rw [this]
          exact radialDeriv_zero_fun ℓ x) τ,
      tsum_shift_one_two
        (c := fun m => (rate m.1 : ℂ) * radialDeriv ℓ (⇑(basis (m, 3)).1) x)
        (by
          have : (⇑(basis (⟨1, by simp⟩, 3)).1 : E n → ℂ) = 0 := funext (hv 3)
          rw [this, radialDeriv_zero_fun ℓ x, mul_zero]) τ]
  · intro k ℓ
    obtain ⟨C, N, hC, h⟩ := hG k ℓ
    exact ⟨C, N, hC, fun m j x =>
      h ⟨m.1, Set.mem_Ici.mpr (le_trans (by norm_num) (Set.mem_Ici.mp m.2))⟩ j x⟩

end Work.FunctionalEquations


end Work.CKFinal.Shadow
