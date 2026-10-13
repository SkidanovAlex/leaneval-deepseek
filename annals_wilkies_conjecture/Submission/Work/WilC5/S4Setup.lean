/-
  WilC5 — shared setup ("glue") for the Zorn assembly `S4OnePoint ⟹ S4SubTE`.

  The assembly is the iteration of vdDMM's one-element step `Work.WilC5.S4OnePoint` over a
  well-ordering of the model `K`, maintaining a `Dcl`-closed (i.e. `TR`-modelling), log-closed
  `LRc`-substructure `F ≤ K` together with a log-preserving `LRc`-embedding `σ : F → L`.

  The Zorn poset of that iteration is `Work.WilC5.S4Pair` below: a partial extension `(F, σ)` of a
  prescribed initial pair `(A₀, σ₀)`, carrying the two invariant properties

  * `Work.WilC5.S4Dom F` — `F` is `Dcl`-closed (so a model of `TR`, by
    `Work.WilC5.model_TR_of_dcl_closed`) and closed under the definable logarithm, and
  * `Work.WilC5.LogPreserving F h σ` — `σ` commutes with the definable logarithm.

  Its underlying data is an element of Mathlib-side `ExtPair` for the *empty* theory, so that the
  chain-gluing lemmas of `Submission/Work/WilC5/ExtChainUnion.lean` and
  `ExtPair_chain_upper.lean` (`chainDom`, `chainEmbFun`, `chainEmbedding`, …) apply verbatim: no
  hypothesis of those lemmas mentions the theory.

  The `rexp`-reduct is registered as a global instance for the duration of this area's work, so
  that everywhere in the following modules the `LRc`-structure of an `LEc`-structure is the
  reduction `Work.WilC5.reductStruct` fixed by `S4Dom`/`LogPreserving`.
-/
import Mathlib
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.ExtPair_chain_upper

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- The `rexp`-reduct of an `LEc`-structure, as a global instance: throughout the §4 layer the
`LRc`-structure of a model of `TE` is its reduct `Work.WilC5.reductStruct`. -/
instance (M : Type) [LEc.Structure M] : LRc.Structure M := reductStruct M

/-- The empty `LRc`-theory.  It is used only to instantiate Mathlib's `ExtPair` (whose `models`
field is irrelevant for the chain-gluing lemmas) with something trivially true; the real invariant
is carried by `S4Pair`. -/
abbrev emptyTheory : LRc.Theory := ∅

theorem emptyTheory_model (M : Type) [LRc.Structure M] : M ⊨ emptyTheory :=
  ⟨fun _ hφ => absurd hφ (Set.notMem_empty _)⟩

/-- **The Zorn poset of the §4 iteration.**  A partial extension of `σ₀ : A₀ → N`: a domain
`F ≤ K` together with a log-preserving `LRc`-embedding `σ : F → N` of the `rexp`-reducts, whose
domain is `Dcl`-closed and log-closed and which extends `σ₀` on `A₀`. -/
structure S4Pair {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (A₀ : LRc.Substructure M) (σ₀ : @Embedding LRc ↥A₀ N _ (reductStruct N)) where
  /-- the domain of the partial extension -/
  dom : LRc.Substructure M
  /-- the embedding of the `rexp`-reducts -/
  emb : @Embedding LRc ↥dom N _ (reductStruct N)
  /-- the invariant: the domain is `Dcl`-closed and log-closed -/
  h4 : S4Dom dom
  /-- the invariant: the embedding commutes with the definable logarithm -/
  logpres : LogPreserving dom h4.log_closed emb
  /-- the domain contains the initial one -/
  le_dom : A₀ ≤ dom
  /-- the embedding extends `σ₀` -/
  agrees : ∀ a : A₀, emb ⟨(a : M), le_dom a.2⟩ = σ₀ a

namespace S4Pair

variable {M N : Type} [LEc.Structure M] [LEc.Structure N]
variable {A₀ : LRc.Substructure M} {σ₀ : @Embedding LRc ↥A₀ N _ (reductStruct N)}

/-- **The underlying Mathlib partial extension** (for the empty theory, so that the theory
hypothesis is vacuous).  It is `@[reducible]` so that the chain-gluing lemmas of `ExtPair`, whose
statements are about `ExtPair`, apply without any unfolding gymnastics. -/
@[reducible] def toExt (p : S4Pair A₀ σ₀) : ExtPair emptyTheory A₀ σ₀ where
  dom := p.dom
  emb := p.emb
  le_dom := p.le_dom
  agrees := p.agrees
  models := emptyTheory_model _

@[simp] theorem toExt_dom (p : S4Pair A₀ σ₀) : p.toExt.dom = p.dom := rfl

@[simp] theorem toExt_emb (p : S4Pair A₀ σ₀) : p.toExt.emb = p.emb := rfl

/-- The order of the poset: larger domain and compatible embeddings. -/
abbrev le (p q : S4Pair A₀ σ₀) : Prop := p.toExt ≤ q.toExt

instance instLE : LE (S4Pair A₀ σ₀) := ⟨le⟩

instance instPreorder : Preorder (S4Pair A₀ σ₀) where
  le := le
  le_refl p := le_refl p.toExt
  le_trans _ _ _ hpq hqr := le_trans hpq hqr
  lt p q := le p q ∧ ¬ le q p
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- The ordering of `S4Pair` is the `ExtPair` ordering of the underlying pairs. -/
theorem le_def (p q : S4Pair A₀ σ₀) : p ≤ q ↔ p.toExt ≤ q.toExt := Iff.rfl

/-- The domain of an extension is larger. -/
theorem dom_le_of_le {p q : S4Pair A₀ σ₀} (h : p ≤ q) : p.dom ≤ q.dom :=
  ExtPair.le_dom_of_le h

/-- The embedding of an extension restricts to the smaller one. -/
theorem emb_agree_of_le {p q : S4Pair A₀ σ₀} (h : p ≤ q) (a : p.dom) (hq : (a : M) ∈ q.dom) :
    q.emb ⟨(a : M), hq⟩ = p.emb a :=
  ExtPair.le_emb h a hq

end S4Pair

end Work.WilC5
