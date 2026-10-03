/-
# The Bessel inequality for the §5 frequency pieces: shared vocabulary

This module fixes the vocabulary of the proof of `Work.KMTPlan.A6.besselF`, the Bessel
inequality for the §5 frequency pieces `F^{0,l₁,k₁}_N` of Krause--Mirek--Tao.

The frequency piece of §5 is
`Fpiece (kmtPj ρ) 0 l₁ k₁ N f = Π_{l₁,≤κ} f − Π_{l₁,≤κ−1} f` with `κ = k₁ − Log N`
(`Π_{l,≤k} = piExact (kmtPj ρ) l k`, `Π_{−1,≤k} = 0`), i.e. at the level of the Fourier
multiplier it is the Littlewood--Paley *shell* `η_{≤k₁−Log N} − η_{≤k₁−Log N −1}` spread over
the arithmetic frequencies `(ℚ/ℤ) = (ℚ/ℤ)_{≤l₁} \ (ℚ/ℤ)_{≤l₁−1}` of height exactly `l₁`:

* `kmtSet ρ l = (ℚ/ℤ)_l` — the arithmetic frequencies of height exactly `l`
  (with `kmtSet ρ 0 = (ℚ/ℤ)_{≤0} = {0}`);
* `DiSym ρ l k` — the symbol of that shell, i.e. the IW symbol
  `iwSymbolSet (kmtSet ρ l) (periodize (η_{≤k} − η_{≤k−1}))`.

The two structural facts about `DiSym` (proved elsewhere under `Submission/Work/KMTPlan/A6/`)
are

* `DiSym_support` — a non-zero value of `DiSym ρ l k` at `ξ` forces
  `ξ = α + θ` with `α ∈ kmtSet ρ l` and `2^{k−1} < |θ| ≤ 2^k`;
* `DiSym_memLp`, `DiSym_norm_le` — `DiSym ρ l k` is bounded by `1` on non-aliasing arcs at
  scale `k`.

We also record `pieceEqMultiplier`: for finitely supported `f`, the frequency piece is the
Fourier multiplier with symbol `DiSym ρ l₁ κ`.
-/
import Mathlib
import Submission.Work.KMTContract.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- The arithmetic frequencies of height *exactly* `l`:
`(ℚ/ℤ)_l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l−1}`, with the convention `(ℚ/ℤ)_{≤−1} = ∅`
(so that `kmtSet ρ 0 = (ℚ/ℤ)_{≤0} = {0}`). -/
def kmtSet (ρ : ℝ) (l : ℕ) : Finset (AddCircle (1:ℝ)) :=
  if l = 0 then iwArithFreqs ρ 0 else iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1)

/-- **The Littlewood--Paley shell symbol of the §5 frequency pieces**: the function
`ξ ↦ ∑_{α ∈ (ℚ/ℤ)_l} (periodize (η_{≤k}) − periodize (η_{≤k−1}))(ξ − α)`, i.e. the IW symbol
over `kmtSet ρ l` of the periodised difference of the cutoffs at scales `k` and `k−1`. -/
def DiSym (ρ : ℝ) (l : ℕ) (k : ℤ) : AddCircle (1:ℝ) → ℂ :=
  iwSymbolSet (kmtSet ρ l)
    (periodize (etaCut Work.KMTContract.kmtEta k)
      - periodize (etaCut Work.KMTContract.kmtEta (k - 1)))

theorem kmtSet_subset (ρ : ℝ) (l : ℕ) : kmtSet ρ l ⊆ iwArithFreqs ρ l := by
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h; simp [kmtSet]
  · simp only [kmtSet, if_neg (by omega : ¬ l = 0)]
    exact Finset.sdiff_subset

theorem kmtSet_subset_of_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l l' : ℕ} (h : l' ≤ l) :
    kmtSet ρ l' ⊆ iwArithFreqs ρ l :=
  (kmtSet_subset ρ l').trans ((iwArithFreqs_mono (ρ := ρ) hρ hρ1 h))

/-- The symbol of the frequency piece, unfolded. -/
theorem DiSym_apply (ρ : ℝ) (l : ℕ) (k : ℤ) (ξ : AddCircle (1:ℝ)) :
    DiSym ρ l k ξ =
      ∑ α ∈ kmtSet ρ l,
        (periodize (etaCut Work.KMTContract.kmtEta k) (ξ - α)
          - periodize (etaCut Work.KMTContract.kmtEta (k - 1)) (ξ - α)) :=
  rfl

end

end Work.KMTPlan.A6
