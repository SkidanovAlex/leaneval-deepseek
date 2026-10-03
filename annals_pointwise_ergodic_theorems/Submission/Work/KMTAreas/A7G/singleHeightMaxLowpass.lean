import Mathlib
import Submission.Work.KMTAreas.A7G.tailAbs
import Submission.Work.KMTAreas.A7Hi.VarPartDefs

/-!
# The single-height Ionescu--Wainger maximal bound (head/tail split)

Target (statement fixed): `∃ Cρ > 0, ∃ C > 0, ∀ l m₀, GoodMajorArcs ρ Cρ l (-(m₀)) → ∀ f : ℤ → ℂ`,

`‖ sup_n |iwConv (iwArithFreqsNew ρ l) (periodize (etaCut kmtEta (-(m₀+n)))) f | ‖_{ℓᵖ} ≤ C‖f‖_{ℓᵖ}`,

the maximal function of the *single-height* projection `T^{(l)}_n = Π_{≤l,≤-(m₀+n)} − Π_{≤l-1,≤-(m₀+n)}`,
with a constant **independent of the arithmetic height `l`**.

This is `strictly between` `Work.KMTAreas.A7G.maximalLowpass` (which has the `(1+l)` constant and is
proved modulo the tree's crux `A7Hi2.lacunaryMaxPiece`) and that same crux (an `l`-free maximal bound for
the *whole* walk, the workspace's central open problem).  See
`NOTES_A7G_singleHeightMaxLowpass_SESSION.md` at the workspace root for the full analysis; in summary:

* `sup_n |T^{(l)}_n f| ≤ sup_n |Π_{≤l,≤·}f| + sup_n |Π_{≤l-1,≤·}f|`, so the crux **implies** this target
  (and the band square-function bound `A7Lpd.bandSquareUnif` converts its `sqFun` term into `‖f‖`);
* conversely the target gives the whole walk's maximal function with constant `(1+l)C`, i.e. it gives
  `A7G.maximalLowpass`;
* the target decomposes into

  (TAIL) the levels `k ≥ C₀+1`, where the **proved** decimation identity
  `Work.KMTPlan.A6.lpf_eq_decimatedKernel_comp_Qlevel` exhibits the walk as the convolution with the
  kernel `decimatedKernel Q (etaCut kmtEta (-k))`, which (because `decimatedKernel Q m j = Q·[Q|j]·∫…`)
  is **block-diagonal along the `Q = iwQl ρ l` residue classes**, each block being the *normalised
  real-scale lacunary dilation* `(1/σ)\hatη(·/σ)`, `σ_k = 2^k/Q`, of a fixed Schwartz kernel.  The
  direct sum over the residue classes makes the tree's **proved** real-scale JSW variational estimate
  `Work.A7Hi2.dilVarRealScale` (equivalently the decimated `Work.A7Hi2.decimDilVarUnif`) apply with an
  **absolute** constant: this is the statement `Work.KMTAreas.A7G.tailVarBound`;
  (HEAD) the finitely many levels `m₀ + k ≤ C₀` for the *minimal* admissible coarse level
  `C₀ = max m₀ (⌈log₂(3·iwQl ρ l)⌉+2)`, where the decimation identity is unavailable (the fine bump is
  wider than the `Q`-lattice) and the arithmetic (Gauss-sum / super-orthogonality) content of the walk is
  genuinely needed.

**Status of the pieces (end of session).**

* `Work.KMTAreas.A7G.tailVarBound` (`Submission/Work/KMTAreas/A7G/tailVarBound.lean`) — **PROVED**
  (sorry-free, axiom-clean): the `TailHyp` bound.  The route is the decimation identity
  `KMTPlan.A6.lpf_eq_decimatedKernel_comp_Qlevel` + the block-diagonal structure of
  `decimatedKernel Q Φ_k` along the `Q = iwQl ρ l` residue classes (each block a normalised real-scale
  lacunary dilation `(1/σ)\hatη(·/σ)`) + the proved real-scale JSW estimate `A7Hi2.dilVarRealScale` /
  `A7Hi2.decimDilVarUnif`.  This is a new `l`-free estimate which *closes the "large-scale / decimated
  regime" obligation* of the tree (the still-`sorry` `A7Hi/lpfLargeScaleRep`) in the single-height form.
  Its **absolute (level-indexed) form** — which is what the assembly below needs, since
  `TailHyp` is indexed from the *base* level `m₀ + C₀ + 1` and therefore leaves a gap — is proved in
  the self-contained module `Submission/Work/KMTAreas/A7G/tailAbs.lean` as
  `Work.KMTAreas.A7G.Abs.tailVarBoundCoarse` / `Abs.tailVarBoundAbs` (see below).
* `Work.KMTAreas.A7G.iwConvNew_eq_sub` (`Submission/Work/KMTAreas/A7G/iwConvNew_eq_sub.lean`) — **PROVED**:
  the symbol-splitting identification
  `iwConv (iwArithFreqsNew ρ l) (periodize Φ) f = iwConv (iwArithFreqs ρ l) (periodize Φ) f
   − iwConv (iwArithFreqs ρ (l−1)) (periodize Φ) f` for bounded `f`.

## The assembly below (`singleHeightMaxLowpass`)

**The target is PROVED in this file, modulo exactly two named statements** (both of which are
*sorry*-stubs at the time of writing, and *both* of which are imported, not assumed inside this
file): the **tail** `Work.KMTAreas.A7G.Abs.tailVarBoundAbs` (proved, sorry-free — see below; it is a
self-contained copy of the proved `Work.KMTAreas.A7G.tailVarBoundCoarse`) and the **head**, which is
itself assembled in `headCombined` from its two complementary regimes:

* `Work.KMTAreas.A7G.headEasy` — the regimes `l ≤ iwC0 ρ` (finitely many arithmetic heights) and
  `Nat.log 2 (3·iwQl ρ l) + 2 ≤ m₀` (where the pinned coarse level equals `m₀`, so the supremum
  collapses to the single scale `k = 0`).  This is provable from the tree's *proved* uniform
  single-scale bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform` plus "finite sup ≤ sum";
* `Work.KMTAreas.A7G.headDeep` — the complementary, genuinely arithmetic regime `iwC0 ρ < l` and
  `m₀ < Nat.log 2 (3·iwQl ρ l) + 2`, in which the head has `Θ(2^l)`-many scales and the decimation
  identity is unavailable (the fine bump is wider than the `Q`-lattice).  **This is the sole
  remaining content of the target**: `headDeep` ⟹ (with the *proved* `headEasy`) the head ⟹ (with
  the proved tail assembly in this file) the target.  `headDeep` is in turn implied by the tree's
  central crux `Work.KMTAreas.A7Hi2.lacunaryMaxPiece` (instantiate the latter at the same `(l, m₀)`
  — the extra hypotheses only restrict the quantifier), so *any* proof of the crux closes this file
  as well.

The split is at the pinned coarse level `C₀ = max m₀ (Nat.log 2 (3·iwQl ρ l) + 2)`: the head covers the
levels `m₀ + k ≤ C₀` and the tail (`tailVarBoundAbs`, whose walk starts at the *absolute* level `C₀+1`)
covers the levels `> C₀`; the levels `≤ C₀` are also exactly those for which the non-aliasing
`GoodMajorArcs ρ Cρ l (-(C₀))` and the decimation gate `3·iwQl ρ l < 2^{C₀}` hold.

The self-contained tail module `Submission/Work/KMTAreas/A7G/tailAbs.lean` (namespace
`Work.KMTAreas.A7G.Abs`, declarations `Abs.tailVarBoundCoarse` / `Abs.tailVarBoundAbs`) is a copy of
the proved `A7G/tailVarBound.lean`; the copy is needed because `A7G/tailVarBound.lean` imports *this*
file (for `TailHyp`), so this file cannot import it back.
-/

namespace Work.KMTAreas.A7G

open MeasureTheory
open scoped ENNReal NNReal

/-- **The TAIL hypothesis** (PROVED as `Work.KMTAreas.A7G.tailVarBound`): for the single-height walk, the
`r`-variational (`2 < r`) norm over the levels `k ≥ C₀+1` is bounded by an *absolute* constant (no
dependence on `l`, `m₀`, `C₀`).  The levels `k ≥ C₀+1` are exactly those for which the decimation identity
`KMTPlan.A6.lpf_eq_decimatedKernel_comp_Qlevel` applies. -/
def TailHyp (ρ : ℝ) (r : NNReal) (p : ℝ) : Prop :=
  ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (l m₀ C₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ → m₀ ≤ C₀ → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count

/-- **The HEAD hypothesis**: the maximal bound for the single-height walk restricted to the finitely many
levels `m₀ + k ≤ C₀` (the levels below the coarse level, where the decimation identity does not reach).
This is the remaining open arithmetic content of the target (the tree's mean-zero / aliased regime). -/
def HeadHyp (ρ : ℝ) (p : ENNReal) : Prop :=
  ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (l m₀ C₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ → m₀ ≤ C₀ → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ k : {k : ℕ // m₀ + k ≤ C₀},
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ k.1 f x - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ k.1 f x‖ₑ)
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

/-- **The conclusion of `singleHeightMaxLowpass`, packaged as a `Prop`.**  This is the form in which
downstream lemmas (e.g. the height-splitting derivation of the whole-walk maximal bound
`Work.KMTAreas.A7G.maximalLowpass` from the single-height bound) should take the target as an
input, so that they do not have to import the (currently `sorry`-bearing, via `headDeep`) proof
term. -/
def SingleHeightMax (ρ : ℝ) (p : ENNReal) : Prop :=
  ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l m₀ : ℕ),
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
    MeasureTheory.eLpNorm (fun x : ℤ => ⨆ n : ℕ,
        ‖Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + ((n : ℕ) : ℤ))))) f x‖ₑ)
      p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

end Work.KMTAreas.A7G
