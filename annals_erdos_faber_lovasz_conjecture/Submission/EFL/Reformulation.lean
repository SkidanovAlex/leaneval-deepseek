import Submission.EFL.LineGraph
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Reformulations of the Erdős–Faber–Lovász theorem

The main theorem (`theorem_1_1` in `Submission.lean`) states that for all
sufficiently large `n`, every linear hypergraph on `n` vertices has chromatic
index at most `n`.

In this file we record the elementary equivalence between that statement and
its line-graph form: for all sufficiently large `n`, the line graph of every
linear hypergraph on `n` vertices is `n`-colourable.  This is where the actual
proof in the literature operates (one colours the line graph, i.e. finds a
decomposition of the edge set into `≤ n` matchings).

We also record the `∃ N, ∀ n ≥ N, ...` form, which is the natural target of a
finite proof of "for all sufficiently large `n`".
-/

set_option autoImplicit false

open Filter

namespace ErdosFaberLovaszConjecture

/-- The statement of Theorem 1.1: for all sufficiently large `n`, every linear
hypergraph on the `n`-element vertex set `Fin n` has chromatic index at most `n`. -/
def eflStatement : Prop :=
  ∀ᶠ n in atTop, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → 𝓗.chromaticIndex ≤ n

/-- The line-graph form of Theorem 1.1: for all sufficiently large `n`, the line
graph of every linear hypergraph on `n` vertices is `n`-colourable. -/
def eflStatementLineGraph : Prop :=
  ∀ᶠ n in atTop, ∀ 𝓗 : Hypergraph (Fin n),
    𝓗.IsLinear → (𝓗.lineGraph).Colorable n

/-- For hypergraphs on `Fin n`, the chromatic index is at most `n` exactly when
the line graph is `n`-colourable. -/
theorem chromaticIndex_le_iff_lineGraph_colorable_fin (n : ℕ) (𝓗 : Hypergraph (Fin n)) :
    𝓗.chromaticIndex ≤ n ↔ (𝓗.lineGraph).Colorable n := by
  classical
  exact Hypergraph.chromaticIndex_le_iff_lineGraph_colorable_of_finite 𝓗 n

/-- The two formulations of the theorem are equivalent. -/
theorem eflStatement_iff_lineGraph : eflStatement ↔ eflStatementLineGraph := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    intro 𝓗 hlin
    exact (chromaticIndex_le_iff_lineGraph_colorable_fin n 𝓗).1 (hn 𝓗 hlin)
  · intro h
    filter_upwards [h] with n hn
    intro 𝓗 hlin
    exact (chromaticIndex_le_iff_lineGraph_colorable_fin n 𝓗).2 (hn 𝓗 hlin)

/-- "For sufficiently large `n`" on `ℕ` means "there exists `N` such that all
`n ≥ N` have the property". -/
theorem eventually_atTop_iff_exists (p : ℕ → Prop) :
    (∀ᶠ n in atTop, p n) ↔ ∃ N : ℕ, ∀ n ≥ N, p n := by
  exact eventually_atTop

/-- The target statement: there is a threshold `N` beyond which every linear
hypergraph on `n` vertices has chromatic index at most `n`. -/
def eflStatementThreshold : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → 𝓗.chromaticIndex ≤ n

/-- The `∃ N`-form is equivalent to the `∀ᶠ`-form. -/
theorem eflStatement_iff_threshold : eflStatement ↔ eflStatementThreshold := by
  unfold eflStatement eflStatementThreshold
  rw [eventually_atTop]

/-- The `∃ N`-form of the line-graph reformulation. -/
def eflStatementLineGraphThreshold : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ 𝓗 : Hypergraph (Fin n),
    𝓗.IsLinear → (𝓗.lineGraph).Colorable n

/-- The `∃ N`-forms of the two reformulations are equivalent. -/
theorem eflStatementLineGraph_iff_threshold :
    eflStatementLineGraph ↔ eflStatementLineGraphThreshold := by
  unfold eflStatementLineGraph eflStatementLineGraphThreshold
  rw [eventually_atTop]

/-- The chromatic-number form: for all sufficiently large `n`, the line graph of every
linear hypergraph on `n` vertices has chromatic number at most `n`. -/
def eflStatementChromaticNumber : Prop :=
  ∀ᶠ n in atTop, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → (𝓗.lineGraph).chromaticNumber ≤ n

/-- The chromatic-number form of the theorem is equivalent to the original one. -/
theorem eflStatement_iff_chromaticNumber : eflStatement ↔ eflStatementChromaticNumber := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    intro 𝓗 hlin
    exact (chromaticIndex_le_iff_chromaticNumber_fin n 𝓗).1 (hn 𝓗 hlin)
  · intro h
    filter_upwards [h] with n hn
    intro 𝓗 hlin
    exact (chromaticIndex_le_iff_chromaticNumber_fin n 𝓗).2 (hn 𝓗 hlin)

end ErdosFaberLovaszConjecture
