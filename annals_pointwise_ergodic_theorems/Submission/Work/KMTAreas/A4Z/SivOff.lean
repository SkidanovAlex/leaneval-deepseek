
/-
# The remaining inputs for `siv-second`: block form of the off-diagonal decay

This module fixes the two remaining inputs of the proof of `siv-second` from `struct-iii-second`
(paper §5.2), in the vocabulary of `SivGeom`/`SivL2`:

* `OffBlockBd P ρ Cρ₀ Koff` — the blockwise form of the off-diagonal decay `(off-decay)` of
  Lemma `iw-prop`(i), **with the exact exponential gain `2^{-8 d l}` made explicit**: for a
  function `ψ` supported in the window `suppWin P N i`, the Ionescu--Wainger projection
  `Π_{≤l,≤d(l-Log N)}` restricted to a block `I_m` at distance `≥ coeffSum P + 3` from `i`
  decays like `Koff · max(l,1) · 2^{-8 d l} · (1+|m-i|)^{-8}` (for blocks at distance at least
`coeffSum P + 3 + 2^{deg P}`, so that the gap is at least `2^d` block lengths and the factor
`(max 1 (2^k · gap))^{-8}` is genuinely of size `2^{-8dl}`).  The gain `2^{-8dl}` is exactly the
  content of the two inequalities `2^{k}·N^d = 2^{dl}·N^d/2^{d·Log N} ≥ 2^{dl-d}` and
  `2^{Log N} ≤ 2N`.

* `PairingFarBd P ρ Cρ₀ K` — the almost-orthogonality of the minor-arc parts of two different
  blocks: for blocks at distance `≥ coeffSum P + 3`, the pairing of the minor-arc parts decays
  like `(A^2 + K (max l 1)^2 2^{-16 d l}) (1+|i-j|)^{-8} a_i a_j`, where `A` is the constant of the
  local `ℓ²` bound supplied by `struct-iii-second` and `a_i = ‖f·1_{I_i}‖_{ℓ²}`.

Both are *quantitative* in `l`: the constants `Koff`, `K` do not depend on `N`, `l`, `Cρ`, `f`,
`h`, `i`, `j`, `A` (nor on `ρ` for fixed `ρ`).  This is what makes the Schur summation in the
assembly give the `2^{-cl}` decay: an existential constant of unknown size in `l` would not do.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.SivL2

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar

namespace Work.KMTAreas.A4Z

/-- **The minor-arc part of the local second dual function**: the `i`-th local dual function
`dPiece P N f h i` minus its projection `Π_{≤l,≤d(l-Log N)}`. -/
def minorPart (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) (f h : ℤ → ℂ) (i : ℤ) : ℤ → ℂ :=
  fun x => dPiece P N f h i x - projTwo P ρ N l (dPiece P N f h i) x

theorem minorPart_apply (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) (f h : ℤ → ℂ) (i : ℤ) :
    minorPart P ρ N l f h i
      = fun x => dPiece P N f h i x - projTwo P ρ N l (dPiece P N f h i) x := rfl

/-- **The blockwise off-diagonal decay with the explicit gain `2^{-8 d l}`.** -/
def OffBlockBd (P : Polynomial ℤ) (ρ Cρ₀ Koff : ℝ) : Prop :=
  ∀ (N l : ℕ) (Cρ : ℝ), 1 ≤ N → Cρ₀ ≤ Cρ →
    GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
    ∀ (i m : ℤ) (ψ : ℤ → ℂ), MemLp ψ 2 Measure.count →
      (∀ x : ℤ, x ∉ suppWin P N i → ψ x = 0) →
      coeffSum P + 3 + 2 ^ P.natDegree ≤ |m - i| →
      eLpNorm (fun x : ℤ =>
          if x ∈ Finset.Ico (m * blockLen P N) ((m + 1) * blockLen P N) then
            Work.KMTContract.kmtProj ρ l
              ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) ψ x
          else 0) 2 Measure.count
        ≤ ENNReal.ofReal (Koff * max ((l : ℝ)) 1
            * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
            * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
          * eLpNorm ψ 2 Measure.count

/-- **The almost-orthogonality of the minor-arc parts of two blocks**, with the explicit gain. -/
def PairingFarBd (P : Polynomial ℤ) (ρ Cρ₀ K : ℝ) : Prop :=
  ∀ (N l : ℕ) (Cρ : ℝ), 1 ≤ N → Cρ₀ ≤ Cρ →
    GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
    ∀ (f h : ℤ → ℂ) (i j : ℤ) (A : ℝ), MemLp f 2 Measure.count →
      (∀ x : ℤ, ‖h x‖ ≤ 1) → 0 ≤ A →
      2 * coeffSum P + 5 + 2 ^ (P.natDegree + 1) ≤ |i - j| →
      eLpNorm (minorPart P ρ N l f h i) 2 Measure.count
        ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f i)) →
      eLpNorm (minorPart P ρ N l f h j) 2 Measure.count
        ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f j)) →
      ‖∑' x : ℤ, minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
        ≤ (A ^ 2 + K * (max ((l : ℝ)) 1) ^ 2
              * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
          * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))
          * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j)


/-- **The operator `T = (1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(·,h)`** of §5.2. -/
def transOp (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) (f h : ℤ → ℂ) : ℤ → ℂ :=
  fun x => AhalfTranspose₂ N P f h x - projTwo P ρ N l (AhalfTranspose₂ N P f h) x

theorem transOp_apply (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) (f h : ℤ → ℂ) :
    transOp P ρ N l f h
      = fun x => AhalfTranspose₂ N P f h x - projTwo P ρ N l (AhalfTranspose₂ N P f h) x :=
  rfl

end Work.KMTAreas.A4Z
