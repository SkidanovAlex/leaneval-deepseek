/-
  WilC5 — **the containment of the value group of a definable closure** (vdDMM (3.9), the
  `ℚ`-rank form).

  Wilkie's valuation inequality (`WilkiesDesign.CG.ValIneq`, the frozen `hVI`) says that at most
  `k` values of elements of `dcl(S ∪ {a₁,…,a_k})` can be `ℤ`-independent modulo the value group
  `v(S^×)` of an elementary substructure `S`.  Equivalently: for every `b` definable from
  `S ∪ {a₁,…,a_k}`, the value `v(b)` lies in the divisible hull of `v(S^×) ∪ ℚ v(a₁) ∪ … ∪ ℚ v(a_k)`
  — the containment half of vdDMM (3.9), i.e. the value-theoretic input of their Lemmas 4.2 and
  4.4.

  **The generators must be value-independent** (`hind`): the containment is FALSE without it.  Take
  `S = ℝ` (elementary), `a₀ = 1 + ε` with `ε` an infinitesimal and `b = ε`: then `b` is definable
  from `S ∪ {a₀}` (as `a₀ - 1`) and `v(a₀) = 0 = v(S^×)`, so `v(b) = v(ε) ∉ v(S^×) + ℚ·v(a₀)`, yet
  `hVI` is not violated (one generator is allowed one independent value).

  `Work.WilC5.valIneq_span` (`valIneq_span.lean`) proves the *new value* case
  (`v(y) ∉ v(S^×)`, one generator, relation with a nonzero exponent on `b`): there it is enough to
  apply `hVI` at `k = 1` to the pair `(b, y)`.  The present lemma removes the hypotheses `hy` and
  `hynew` and allows an arbitrary finite family of generators; the proof is the same application of
  `hVI` with `m = k + 1` elements `(b, a₀, …, a_{k-1})`, together with the observation that if the
  resulting integer relation happens to have coefficient `0` on `b`, then the generators themselves
  are dependent and one of them can be dropped (an induction on `k`).

  The statement is written in the `Un(K)`-language, i.e. with `IsUnitVal`, so that it can be fed
  directly into the `w = u(1+ε)∏ aᵢ^{qᵢ}` decomposition (`Work.WilC5.decomposition_of_same_value`)
  used by the log-closure/log-preservation arguments of vdDMM §4.  The exponent of `b` is its own
  integer `n ≠ 0` (it must *not* be tied to the exponents of the generators): the relation
  `v(c) + n·v(b) + Σ qᵢ v(aᵢ) = 0` reads `v(b) = -v(c)/n - Σ (qᵢ/n) v(aᵢ)`, i.e. the *ℚ*-span
  `v(b) ∈ divhull(v(S^×) ∪ ℚ{v(aᵢ)})`.  Tying `n` to the bracket instead would only give the
  ℤ-span of the generators, which is false (take `S = ℝ`, `b = √ε`, `a₀ = ε` with `ε` an
  infinitesimal: `v(b) = v(a₀)/2 ∉ ℤ·v(a₀)`).

  -/
import Mathlib
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.model_pow_root
import Submission.Work.WilC5.elemSub_pow_root
import Submission.Work.WilC5.SpanValueContain
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.dcl_elementary

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC5

/-- **Value containment for a definable closure** (vdDMM (3.9)).

`S` is an elementary substructure of a model `M ⊨ TR`, `a : Fin k → M` a finite family of
generators, and `b` is an element whose singleton is definable from the parameters `S ∪ range a`.
Then the value of `b` lies in the divisible hull of the value group of `S` together with the
`ℚ`-span of the values of the generators: there are `q : Fin k → ℤ`, `n > 0` and `c ∈ S \ {0}`
with `c * (b * ∏ᵢ aᵢ ^ qᵢ) ^ n` a unit of the standard real valuation.

In value-group notation (`v(x) = 0` for units, bigger elements have smaller value): the relation
`v (c · (b · ∏ aᵢ^{qᵢ})^n) = 0` reads `v(b) = -v(c)/n - Σᵢ qᵢ v(aᵢ)`, i.e.
`v(b) ∈ divhull(v(S^×) ∪ ℚ·span{v(aᵢ)})` since `v(S^×)` is divisible (`S ⊨ TR`). -/
theorem SpanContain {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (hVI : WilkiesDesign.CG.ValIneq) (S : WilkiesDesign.CG.LRc.ElementarySubstructure M)
    {k : ℕ} (a : Fin k → M) {b : M} (hb : b ≠ 0)
    (hbdef : ((S : Set M) ∪ Set.range a).Definable WilkiesDesign.CG.LRc {fun _ : Fin 1 => b})
    (hind : ∀ q : Fin k → ℤ, (∃ c ∈ (S : Set M), c ≠ 0 ∧
      WilkiesDesign.CG.IsUnitVal (c * ∏ i, a i ^ (q i))) → q = 0) :
    ∃ (q : Fin k → ℤ) (n : ℤ), n ≠ 0 ∧ ∃ c ∈ (S : Set M), c ≠ 0 ∧
      WilkiesDesign.CG.IsUnitVal (c * b ^ n * ∏ i, a i ^ (q i)) :=
  SpanValueContain hVI S a hb hbdef hind

end Work.WilC5
