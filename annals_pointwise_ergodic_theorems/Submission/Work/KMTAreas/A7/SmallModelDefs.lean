/-
# Vocabulary of the small-scale model-tuple estimate (`SmallModelVar`, paper §7)

This module fixes the objects in which the §7 assembly of `Work.KMTAreas.A7.SmallModelVar` is
phrased:

* `randSymb φ ε K` — the *randomised symbol* attached to a family `φ : ℕ → ℝ → ℂ` of bumps and a
  family of coefficients `ε` with `‖ε n‖ ≤ 1`:
  `ξ ↦ ∑_{n < K} ε n • (φ (n+1) ξ - φ n ξ)`.
  This is the symbol appearing on the right-hand side of the two-dimensional
  Rademacher--Menshov inequality for bilinear forms: after the linearity of `Tle` in its symbol,
  `∑_{n<K} ε n • (Tle (φ (n+1)) f - Tle (φ n) f) = Tle (randSymb φ ε K) f`.
* `smallSymbF` / `smallSymbG` — the concrete bump families of the small-scale tuple: the modulated
  bumps `φ_{N,t}`, `φ̃_{N,t}` of §6 at the lacunary scales `N = ⌊a n⌋`, clamped by the small-scale
  condition `smallCond` **and anchored at `n = 0`**
  (`smallSymbF … 0 = 0`, i.e. the family vanishes at the origin).  The anchoring is what lets the
  Rademacher--Menshov inequality -- which anchors its sequences at `0` -- be applied to the
  columns: the tuple at `n = 0` is split off as a single spike and estimated by the
  single-scale bound.

The single-scale input of the assembly is the estimate

  `‖ Btwist (Tle (randSymb (smallSymbF … ) ε K) f) (Tle (randSymb (smallSymbG … ) ε' K) g) ‖_{ℓ^p}
     ≤ C Λ · ⟨L⟩^A 2^{A ρ L} ‖f‖_{p₁} ‖g‖_{p₂}`,

i.e. the paper's Lemma `ssu` (the single-scale estimate for the model operator, valid for *all*
randomised cutoffs, uniformly in `K` and in the signs), combined with the linear estimates
`iw-prop` and Theorem `cz-shift` for the randomised cutoffs.  It is stated as the Prop
`RandBumpSingleScale` below.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.LargeInterface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- **The randomised symbol** attached to a bump family `φ` and coefficients `ε`:
`ξ ↦ ∑_{n < K} ε n • (φ (n+1) ξ - φ n ξ)`. -/
noncomputable def randSymb (φ : ℕ → ℝ → ℂ) (ε : ℕ → ℂ) (K : ℕ) : ℝ → ℂ :=
  fun ξ => ∑ n ∈ Finset.range K, ε n * (φ (n + 1) ξ - φ n ξ)

theorem randSymb_zero (φ : ℕ → ℝ → ℂ) (ε : ℕ → ℂ) : randSymb φ ε 0 = 0 := by
  funext ξ
  simp [randSymb]

/-- **The `f`-side bump family of the small-scale tuple**: on the small-scale condition, the
modulated bump `φ_{N,t}` at the lacunary scale `N = ⌊a n⌋`, and `0` otherwise.  The family is
anchored at `0` (`smallSymbF … 0 = 0`), so that the Rademacher--Menshov inequality (whose sequences
start at `0`) applies. -/
noncomputable def smallSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    ℕ → ℝ → ℂ :=
  fun n ξ =>
    if n = 0 then 0
    else if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then varphiNt (Nat.floor (a n)) k₁ t ξ else 0

/-- **The `g`-side bump family of the small-scale tuple**: the analogue of `smallSymbF` with the
modulated bump `φ̃_{N,t}` of §6 (the `d`-fold rescaled frequency variable). -/
noncomputable def smallSymbG (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n ξ =>
    if n = 0 then 0
    else if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
      varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ
    else 0

/-- **The integrand of the small-scale model tuple at the time `t`**: the twisted bilinear
multiplier `Btwist` applied to the two exact-height modulated pieces, gated by the small-scale
condition `smallCond`.  It is the object whose `t`-integral over `[1/2,1]` is `smallModelTuple`. -/
noncomputable def modelInt (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) (f g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
      smallBtwist ρ P l₁ l₂ (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    else 0

/-- **The truncation index of the lacunary sequence**: beyond this index `n` the small-scale
condition `smallCond` fails, because `a` is `Λ`-lacunary (so `a n ≥ Λ ^ n`) while `smallCond`
requires `⌊a n⌋ ≤ splitCut ρ L`.  It is the index at which the Rademacher--Menshov truncation of
the model tuple is taken. -/
noncomputable def truncIndex (ρ : ℝ) (Λ : ℝ≥0) (L : ℕ) : ℕ :=
  Nat.ceil (Real.log ((splitCut ρ L : ℝ) + 1) / Real.log (Λ : ℝ)) + 2

theorem smallSymbF_zero (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t 0 = 0 := rfl

theorem smallSymbG_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) : smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t 0 = 0 := rfl

/-- **The single-scale input of the small-scale assembly** (paper §7): the model operator applied
to the two *randomised* cut-offs is bounded by the loss weight, uniformly in the number of scales
`K` and in the signs `ε`, `ε'` (this is the paper's Lemma `ssu` combined with the trivial
observation that the randomised cut-offs are supported in the main-regime band, plus the linear
estimates `iw-prop` and Theorem `cz-shift` for them).

**Quantifier order.**  The order of the quantifiers is essential and is the one of the paper:
`ρ₀` (and the exponent `A`) must be allowed to depend on `C₀`, even though `ρ₀, A, C` must not
depend on the data `a, Λ, l₁, …, f, g`.  With `ρ₀` independent of `C₀` the statement is FALSE: the
only route through area `A1` (`IwLqGeneral` + `GoodMajorArcs`) requires `ρ · C₀ ≲ 1` (the paper has
`ρ = 1/C₁` with `C₁ ≫ C₀`); a colleague refuted the wrong order by an elementary scaling
obstruction (taking `C₀ = ⌈10/ρ⌉` and heights `l ≈ L` large makes the arithmetic frequency set
`(ℚ/ℤ)_{≤L}` contain denominators `q ≫ N`, whence the symbol
`iwSymbolSet (iwArithFreqs ρ L) (periodize Φ)` is a non-zero constant on the main-regime band).
The target `Work.KMTAreas.A7.SmallModelVar` has exactly this order (`∀ C₀ r, … → ∃ c, ∃ ρ₀, ∀ ρ ≤ ρ₀,
∃ K, …`), as does `Work.KMTAreas.A7.VarpLossSmall`. -/
def RandBumpSingleScale (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (hdeg : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1), 1 < p₁ → p₁ < ⊤ → 1 < p₂ →
    p₂ < ⊤ → p₁⁻¹ + p₂⁻¹ ≤ 1 →
    ∀ (C₀ : ℕ), 1 ≤ C₀ →
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ A : ℝ, 0 ≤ A ∧
        ∃ C : ℝ≥0 → ℝ≥0,
          ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ)
            (ε ε' : ℕ → ℂ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            (∀ n, ‖ε n‖ ≤ 1) → (∀ n, ‖ε' n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                Btwist ρ P l₁ l₂ (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
                  (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
                  (Tle ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f)
                  (Tle ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g) x)
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) *
                ENNReal.ofReal ((1 + lmaxR l₁ l₂ k₁ k₂) ^ A *
                  (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂)) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

end

end Work.KMTAreas.A7
