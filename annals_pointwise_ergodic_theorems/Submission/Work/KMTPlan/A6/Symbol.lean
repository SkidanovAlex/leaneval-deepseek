/-
# The symbols of the Ionescu--Wainger projections and of the §5 pieces

This module fixes the vocabulary used by the proof of the "projection vanishing" lemmas
`projVanishingF` / `projVanishingG` of area A6:

* `kmtSym ρ l k` — the symbol of the concrete IW projection `kmtProj ρ l k`, i.e. the circle
  function `ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize η_{≤k})(ξ - α)`;
* `PiEx ρ l k` — the symbol of the exact-height projection `piExact (kmtPj ρ) l k`;
* `Gsym ρ d l₂ k₂ N` — the symbol of the §5 piece `Gpiece (kmtPj ρ) d 0 l₂ k₂ N ·`.

The two facts about the symbols on which the vanishing proof rests are:
* `kmtProj_eq_tsum` — `kmtProj ρ l k` is the convolution with the Fourier coefficients of
  `kmtSym ρ l k` (definitional);
* `PiEx_eq_iwSymbolSet` — `PiEx ρ l k = iwSymbolSet ((ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}) η_{≤k}` for
  `l ≠ 0`.
-/
import Mathlib
import Submission.Work.KMTContract.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Submission.PointwiseErgodicTheorems

noncomputable section

/-- **The symbol of the Ionescu--Wainger projection `kmtProj ρ l k`.** -/
noncomputable def kmtSym (ρ : ℝ) (l : ℕ) (k : ℤ) : AddCircle (1 : ℝ) → ℂ :=
  iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))

theorem kmtSym_apply (ρ : ℝ) (l : ℕ) (k : ℤ) (ξ : AddCircle (1 : ℝ)) :
    kmtSym ρ l k ξ = ∑ α ∈ iwArithFreqs ρ l,
      periodize (etaCut Work.KMTContract.kmtEta k) (ξ - α) := rfl

/-- The projection `kmtProj ρ l k` is the convolution with the Fourier coefficients of its
symbol `kmtSym ρ l k`. -/
theorem kmtProj_eq_tsum (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) (n : ℤ) :
    Work.KMTContract.kmtProj ρ l k f n
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel (kmtSym ρ l k) j * f (n - j) := rfl

/-- The Fourier coefficients of a symbol are the `iwKernel` of that symbol (definitional). -/
theorem iwKernel_eq_fourierCoeff (m : AddCircle (1 : ℝ) → ℂ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel m j = fourierCoeff m j := rfl

/-! ## The zero height -/

theorem iwP_zero (ρ : ℝ) : iwP ρ 0 = {1} := by
  rw [iwP, if_pos (Nat.zero_le _)]
  norm_num

/-- `(ℚ/ℤ)_{≤0} = {0}`. -/
theorem iwArithFreqs_zero (ρ : ℝ) :
    iwArithFreqs ρ 0 = ({(0 : AddCircle (1 : ℝ))} : Finset (AddCircle (1 : ℝ))) := by
  rw [iwArithFreqs, iwP_zero, Finset.singleton_biUnion, Finset.range_one, Finset.image_singleton]
  norm_num

/-! ## The exact-height symbol and the symbol of the §5 piece -/

/-- **The symbol of the exact-height projection** `piExact (kmtPj ρ) l k`. -/
noncomputable def PiEx (ρ : ℝ) (l : ℕ) (k : ℤ) : AddCircle (1 : ℝ) → ℂ :=
  if l = 0 then kmtSym ρ 0 k else kmtSym ρ l k - kmtSym ρ (l - 1) k

/-- **The symbol of the §5 piece** `Gpiece (kmtPj ρ) d u l₂ k₂ N` for `u = 0`. -/
noncomputable def Gsym (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  if k₂ = -((0 : ℕ) : ℤ) then PiEx ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
  else PiEx ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
      - PiEx ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)))

end

end Work.KMTPlan.A6
