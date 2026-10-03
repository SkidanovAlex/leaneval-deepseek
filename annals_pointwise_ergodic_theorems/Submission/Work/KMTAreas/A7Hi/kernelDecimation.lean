import Mathlib
import Submission.Work.KMTAreas.A7Hi.kmtProjHeightSplit
import Submission.Work.KMTAreas.A7.arithChar_eq_iwQ0_mul_KW
import Submission.Work.KMTAreas.A7.fourierPeriodSumZero

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped ENNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

noncomputable section

/-! # The decimation structure of the Ionescu--Wainger projections

Let `T_k = kmtProj ρ l k` be the IW projection of height `≤ l` at scale `2^k`, i.e. the Fourier
multiplier with symbol `iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))`, and let
`κ_k(j) = iwKernel (…) j` be its convolution kernel.  The arithmetic height `l` enters through the
arithmetic character `arithChar ρ l (-j) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(-j α)`:

  `κ_k(j) = arithChar ρ l (-j) · cw (etaCut kmtEta k) j`
  (`Work.KMTAreas.A7Hi.kmtKernel_eq_arithChar_cw`).

In the *deep* regime `iwC0 ρ < l` the arithmetic character has the exact factorisation
`arithChar ρ l z = iwQ0 ρ l · (if iwQ0 ρ l ∣ z then KW ρ l z else 0)`
(`Work.KMTAreas.A7.arithChar_eq_iwQ0_mul_KW`, where `iwQ0 ρ l = (N_0^{(l)}!)^{D_ρ}` is the huge
"small prime" modulus).  The consequences — the content of this file — are:

* **the kernel vanishes off the sublattice `iwQ0 ρ l · ℤ`**: `κ_k(j) = 0` unless `iwQ0 ρ l ∣ j`.
  In particular `T_k` is a *decimated* convolution: it splits as a direct sum of operators on the
  `iwQ0 ρ l` residue classes `x + iwQ0 ρ l · ℤ`;
* **the residue-class locality**: if two functions agree on `x - iwQ0 ρ l · ℤ` then their
  projections agree at `x`.

This is the structural reason why the naive kernel bounds (which only use `|arithChar| ≤ #A`)
lose a factor `#(ℚ/ℤ)_{≤l}`, while the truth is governed by the much smaller "large prime"
character sum `KW`: on the sublattice the kernel is `iwQ0 ρ l · KW ρ l (-j) · cw (etaCut kmtEta k) j`.
In particular, for `l > iwC0 ρ` the operator is *fibrewise* an operator on `ℤ` (one fibre per
residue class), and the maximal/norm estimates for `T_k` can be performed fibre by fibre. -/

/-- **Reindexing over a sublattice.**  A sum over `ℤ` of a family supported on the multiples of
`Q ≠ 0` is a sum over the multiples. -/
theorem tsum_of_dvd (Q : ℕ) (hQ : Q ≠ 0) (F : ℤ → ℂ) :
    (∑' j : ℤ, (if (Q : ℤ) ∣ j then F j else 0)) = ∑' m : ℤ, F ((Q : ℤ) * m) := by
  have h : (∑' j : ℤ, (if (Q : ℤ) ∣ j then F j else 0))
      = ∑' j : ℤ, ({j : ℤ | (Q : ℤ) ∣ j} : Set ℤ).indicator F j := by
    refine tsum_congr fun j => ?_
    rw [Set.indicator_apply]
    by_cases hj : (Q : ℤ) ∣ j <;> simp [hj]
  rw [h, ← tsum_subtype ({j : ℤ | (Q : ℤ) ∣ j} : Set ℤ) F]
  let e : ℤ ≃ {j : ℤ // (Q : ℤ) ∣ j} :=
    { toFun := fun m => ⟨(Q : ℤ) * m, ⟨m, rfl⟩⟩
      invFun := fun j => j.1 / (Q : ℤ)
      left_inv := by
        intro m
        simp only
        rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hQ)]
      right_inv := by
        intro j
        refine Subtype.ext ?_
        simp only
        rw [mul_comm]
        exact Int.ediv_mul_cancel j.2 }
  symm
  exact Equiv.tsum_eq e (fun j : {j : ℤ // (Q : ℤ) ∣ j} => F j.1)

end

end Work.KMTAreas.A7Hi
