/-
  WilE9 / Sharp — the main construction of the E9 assembly.

  Fix a presentation of the `ψ`-image `Z` of the graph of `f` together with an effective
  stratification of its pieces, recorded as a list `S` of strata `EffStratum n m`
  (`E9Layer`).  From it we build

  * `Tset S L` — the union over the strata of the `ψ`-image of the `L`-th derivative graph
    (`exTset`, which is a `Star`-set by `exTset_star`), and
  * `Eset S L = closure (psiV ⁻¹' Tset S L)`, the corresponding `Gen`-set, whose section is
    `∂_L f` on the `C^{|L|}`-locus (`Eset_spec`, to be proved from `exSemiPf_fst`/`exSemiPf_snd`),
  * `DomSet S k` — the interior of the set of points at which *every* `Eset S L` (`|L| ≤ k`) has
    a defined, unique and continuous section and, for `|L| < k`, a differentiable one whose
    derivative is attained by `Eset S (i :: L)`.  Its interior is exactly the `C^k`-locus of `f`
    (`DomSet_eq`).

  Then `sdSet f k v = {z | Fin.init z ∈ DomSet S k} ∩ Eset S (List.ofFn v)` (`sdSet_eq`):
  the `Gen`-set exhibiting the sharp derivative.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.AE.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The list-indexed iterated directional derivatives, as a set of orders: the lists of length
at most `k`. -/
abbrev Ord (n k : ℕ) : Type := {L : List (Fin n) // L.length ≤ k}

/-- The `ψ`-image of the `L`-th derivative graph over the strata `S`.  Each stratum contributes
only its own component (`exTsetC`), so that the per-stratum hypothesis "the component projects
into `Z`" is available at every point used. -/
def Tset (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) :
    Set (Fin (n + 1) → ℝ) :=
  ⋃ A ∈ S, exTsetC n A.1 A.E A.q L

/-- The `Gen`-set of the E9 construction: the closure of the `psiV`-preimage of `Tset S L`. -/
def Eset (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) :
    Set (Fin (n + 1) → ℝ) :=
  closure (WilkiesDesign.E.psiV ⁻¹' Tset n S L)

/-- The points of a `Gen`-set at which its graph function is continuous (the formula of
`Work.WilE9.Gen.gen_contSet`). -/
def contPart {n : ℕ} (G : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {v | v ∈ G ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Fin n → ℝ,
    (∀ j : Fin n, |x' j - Fin.init v j| < δ) →
    ∀ v' : ℝ, Fin.snoc x' v' ∈ G → |v' - v (Fin.last n)| < ε}

/-- The derivative graph of the graph function of a `Gen`-set, in the coordinate direction `i`
(the formula of `Work.WilE9.Gen.gen_diffSet`). -/
def diffPart {n : ℕ} (G : Set (Fin (n + 1) → ℝ)) (i : Fin n) : Set (Fin (n + 1) → ℝ) :=
  {v | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
    ∀ x' : Fin n → ℝ, (∀ j : Fin n, x' j = Fin.init v j + h * (if j = i then 1 else 0)) →
    ∀ y₀ : ℝ, Fin.snoc (Fin.init v) y₀ ∈ G →
    ∀ v' : ℝ, Fin.snoc x' v' ∈ G → |v (Fin.last n) - (v' - y₀) / h| < ε}

/-- **The domain of the E9 construction.**  The interior of the set of points at which

* `f` itself is continuous (`contPart` of its graph `G`), and
* for every order `L` with `|L| ≤ k`, the set `Eset S L` has a defined, unique and continuous
  section, and — for `|L| < k` — a differentiable one whose derivative is attained by
  `Eset S (i :: L)`.

Its interior is exactly the `C^k`-locus of `f` (`DomSet_eq`). -/
def DomSet (n k : ℕ) (S : List (AEStratum n)) (G : Set (Fin (n + 1) → ℝ)) :
    Set (Fin n → ℝ) :=
  interior (WilkiesDesign.projLast (contPart G) ∩
    ⋂ L : Ord n k,
      (WilkiesDesign.projLast (Eset n S L.1) ∩
        WilkiesDesign.projLast (contPart (Eset n S L.1)) ∩
        (if L.1.length < k then
          ⋂ i : Fin n, WilkiesDesign.projLast
            (diffPart (Eset n S L.1) i ∩ Eset n S (i :: L.1))
         else Set.univ)))

/-- **The section correctness of the family `E_L` on the `C^{|L|}` locus.**  At a point `x` where
`f` is `C^{|L|}`, the set `Eset S L` over `x` is exactly `{(x, ∂_L f x)}`.

(Off the `C^{|L|}` locus the fibre of `Eset S L` may contain limits of `∂_L f` along the good
points, which need not be `glDeriv L f x`; that is why the specification is restricted to the
`C^{|L|}` locus, which is all that `DomSet` and the identification `sdSet_eq` consume.) -/
def SecSpec (n k : ℕ) (S : List (AEStratum n)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ L : List (Fin n), L.length ≤ k → ∀ (x : Fin n → ℝ) (t : ℝ),
    ContDiffAt ℝ L.length f x →
      (Fin.snoc x t ∈ Eset n S L ↔ t = glDeriv L f x)

/-- **The closure property of the family `E_L`.**  Every point of the projection of `Eset S L` is
a limit of points at which `f` is `C^{|L|}`; this is what lets `DomSet` identify the `C^k`-locus
with a *closed* condition on the sections. -/
def LimSpec (n k : ℕ) (S : List (AEStratum n)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ L : List (Fin n), L.length ≤ k → ∀ x : Fin n → ℝ,
    x ∈ WilkiesDesign.projLast (Eset n S L) → x ∈ closure {y | ContDiffAt ℝ L.length f y}

end Work.WilE9.Sharp
