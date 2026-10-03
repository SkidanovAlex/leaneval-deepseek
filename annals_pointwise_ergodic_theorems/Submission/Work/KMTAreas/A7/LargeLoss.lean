/-
# The large-scale part of Theorem `varp` at the exponents `(p₁,p₂) ≠ (2,2)`

This is the area-`A7` lemma `Work.KMTAreas.A7.LargeLoss`: `VarpLossLarge P p₁ p₂`, the regime
`N > splitCut ρ L` of the paper's Theorem `varp` at the exponents `(p₁,p₂) ≠ (2,2)`, from area
`A1` (the Ionescu--Wainger multiplier theorem) alone -- i.e. §8 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

in the "without gain" form in which the A7 development uses it.

The proof is assembled in `Submission.Work.KMTAreas.A7.Large.AssemblyRep` from four estimates.

## The model and its two defects

The §6 model operator is the twisted bilinear multiplier
`∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g) dt` of
`Large/Defs.lean`, and the columns of §5 are compared with it.  Two defects of the *first*
version of that model (`modelTuple` of `Large/Defs.lean`) were found and repaired:

1. **the arithmetic height `l = 0`**: `iwArithFreqsNew ρ 0 = ∅` (truncated subtraction), so
   `Tex ρ 0 = 0` and the model vanishes identically whenever `l₁ = 0` or `l₂ = 0`, while the
   concrete column at height `0` is the non-trivial projection `Π_{0,≤k} = Π_{≤0,≤k}`
   (the paper's `(ℚ/ℤ)_0 = {0}`).  Hence the model-approximation bound is *not* the paper's
   `mod-approx` on the whole range: it splits into the *main* range `1 ≤ l₁ ∧ 1 ≤ l₂` (§6) and
   the complementary `l = 0` range (a direct estimate for the concrete columns).  See
   `NOTES_A7_level0_model_and_LargeLoss.md`;
2. **the free constant `C₂` of the model symbol** `m_* = η_{≤-2u} ⊗ η_{≤-2du}`: the workspace's
   normalisation `u = uScale ρ L = ⌊2^{2ρL}⌋` pins the paper's free constant `C₂` to `1`, which
   makes the plateau `2^{-2u}` *wider* than the separation of the exact-height fibres
   `diffFreqs ρ (max l₁ l₂)` as soon as `max (l₁,l₂)` is large compared with `L`; the model then
   acquires cross-fibre terms of size `O(1)` with no `N^{-1}` gain, and the single-scale content
   of the model approximation is false (`NOTES_A7_HiMassBoundHolds_VERDICT.md`).  The repair
   prescribed there is used here: `modelTupleRep` (`Large/Defs.lean`) has the band
   `uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) (max l₁ l₂ + 3)` -- the
   extra term implements the separation, since distinct fractions `a/q ≠ a'/q'` with
   `q,q' ≤ 2^l` are at distance `≥ 2^{-2l}` -- and the band condition
   `bandCond : k + 1 + 2uRep ≤ Log N` (the window of `φ_{N,t}` inside the plateau of `m_*`) in
   its guard.  Off the band the model is `0`; the off-band scales are `ρ`- and `C₀`-bounded in
   number and are absorbed into the constant `K(Λ)`.

The four inputs of the assembly are then

* `Work.KMTAreas.A7.ModelApproxHiRep` — §6 `mod-approx` ∘ `bn-ident` at exact height
  `1 ≤ l₁ ∧ 1 ≤ l₂`, for the repaired model;
* `Work.KMTAreas.A7.ModelApproxLoRep` — the same for the complementary range
  `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` (`l = 0`), where both tuples are zero and the claim is a direct
  variational estimate for the concrete columns;
* `Work.KMTAreas.A7.ModelLargeHiRep` — §8, the bound for the repaired model tuple itself;
* `Work.KMTAreas.A7.ExceptionalBound` — the exceptional scales (admissible and large, but with
  `Log N < k + 2u`), a bounded contribution; the term `exceptionalPart` is *model-independent*,
  so this estimate survives the repairs unchanged (`ExceptionalBound` is **proved**).

The pointwise splitting `colTuple = model + (mainPartTuple - model) + exceptionalPart`, the case
split on `l₁, l₂ ≥ 1`, the absorption of the polynomial loss `⟨L⟩^{max c₁ c₂}` into one further
exponential factor `2^{ρL}` and the subadditivity of `variationalNorm`/`eLpNorm` are carried out
in `Large/Assembly.lean`, `Large/AssemblyLo.lean` and `Large/AssemblyRep.lean`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.AssemblyRep
import Submission.Work.KMTAreas.A7.ModelApproxHiRep
import Submission.Work.KMTAreas.A7.Large.LoBridge
import Submission.Work.KMTAreas.A7.ModelLargeHiRep

set_option autoImplicit false

namespace Work.KMTAreas.A7

theorem LargeLoss :
    ∀ (P : Polynomial ℤ) (p₁ p₂ : ENNReal), 2 ≤ P.natDegree → 1 < p₁ → p₁ < ⊤ → 1 < p₂ → p₂ < ⊤ →
      p₁⁻¹ + p₂⁻¹ ≤ 1 → (p₁ ≠ 2 ∨ p₂ ≠ 2) → Work.KMTContract.AreaA1 →
      Work.KMTAreas.A7.VarpLossLarge P p₁ p₂ := by
  intro P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum _hneq hA1
  exact largeLoss_of_hi_lo_rep P p₁ p₂ hdeg hsum
    (ModelApproxHiRep P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (ModelApproxLoBridge P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (ModelLargeHiRep P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (ExceptionalBound P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum)

end Work.KMTAreas.A7
