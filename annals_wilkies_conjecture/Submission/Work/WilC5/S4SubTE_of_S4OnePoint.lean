/-
  WilC5 — **`S4OnePoint ⟹ S4SubTE`**: the Zorn assembly of vdDMM's §4 iteration.

  `Work.WilC5.S4OnePoint` (in `S4OnePoint.lean`) is the one-element step of van den
  Dries–Macintyre–Marker's proof of their Theorem 4.1: given a model `K ⊨ TE`, a `κ`-saturated
  model `L ⊨ TE` with `κ > |K|`, an invariant domain `A ≤ K` (`Dcl`-closed in the `rexp`-reduct
  and log-closed, `Work.WilC5.S4Dom`) and a log-preserving `LRc`-embedding `σ : A → L`, the pair
  `(A, σ)` extends past any prescribed `x ∈ K`.

  This module performs the *iteration*: `Work.WilC5.S4Dom` is vdDMM's invariant ("`A ⊨ T_an` and
  log-closed"), and the Zorn poset of the partial extensions `(A, σ)` carrying it is
  `Work.WilC5.S4Pair` (`Submission/Work/WilC5/S4Setup.lean`).  There,

  * `Work.WilC5.S4Pair_chain_upper` — the union of a chain of partial extensions is again one:
    the union of the domains is `Dcl`-closed (`dcl_finite_params` plus the directedness of the
    chain) and log-closed, and the embeddings of the chain glue along it
    (`ExtPair.chainEmbedding`);
  * `Work.WilC5.S4Pair_maximal_step` — a maximal partial extension has domain all of `K`, since
    otherwise `S4OnePoint` would extend it by one point;
  * the resulting total log-preserving `LRc`-embedding `M → N` is the underlying function of an
    `LEc`-embedding (`Work.WilC5.LEcEmbedding_of_top`, through
    `Work.WilC5.LEcEmbedding_of_LRcEmbedding`), which is the conclusion of `S4SubTE`.

  The bottom of the poset is `Work.WilC5.S4Pair_initial`: the carrier of an `LEc`-substructure
  `A ≤ M` with `A ⊨ TE` is `Dcl`-closed (`dcl_substructure_subset`) and log-closed
  (`logFun_mem_of_substructure`), and an `LEc`-embedding `σ : A → N` restricts to a log-preserving
  `LRc`-embedding of the `rexp`-reducts (`ReductEmb`, `LogFunMap`).
-/
import Mathlib
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.S4SubTE
import Submission.Work.WilC5.dcl_iUnion_chain
import Submission.Work.WilC5.dcl_substructure_subset
import Submission.Work.WilC5.logFun_mem_of_substructure
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.LogStructEmbedding
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.S4Setup
import Submission.Work.WilC5.ExtPair_top_embedding
import Submission.Work.WilC5.LEcEmbedding_of_LRcEmbedding
import Submission.Work.WilC5.S4Dom_chainDom
import Submission.Work.WilC5.logPreserving_chainEmbedding
import Submission.Work.WilC5.LEcEmbedding_of_top
import Submission.Work.WilC5.S4Pair_initial

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- Two `LogPreserving` statements for the same domain and embedding agree: they differ only in the
proof of `LogClosed`, which is a proposition.  This is what lets the chain step below pass from the
per-member log-preservation of a chain to the log-preservation of the glued embedding. -/
theorem logPreserving_congr {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (A : LRc.Substructure K) (σ : @Embedding LRc ↥A L _ (reductStruct L))
    (h1 h2 : LogClosed (A : Set K)) : LogPreserving A h1 σ ↔ LogPreserving A h2 σ :=
  iff_of_eq (congrArg (fun h => LogPreserving A h σ) (Subsingleton.elim h1 h2))

/-- **The chain step of the Zorn argument.**  The union of a chain of partial extensions of the
§4 iteration is again a partial extension, and bounds the chain. -/
theorem S4Pair_chain_upper {M N : Type} [LEc.Structure M] [LEc.Structure N]
    {A₀ : LRc.Substructure M} {σ₀ : @Embedding LRc ↥A₀ N _ (reductStruct N)}
    {c : Set (S4Pair A₀ σ₀)} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ ub : S4Pair A₀ σ₀, ∀ a ∈ c, a ≤ ub := by
  classical
  -- the underlying Mathlib partial extensions of the members of the chain
  set c' : Set (ExtPair emptyTheory A₀ σ₀) := S4Pair.toExt '' c with hc'def
  have hc' : IsChain (· ≤ ·) c' := by
    intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    intro hne
    rcases hc hp hq (fun heq => hne (by rw [heq])) with hpq | hqp
    · exact Or.inl hpq
    · exact Or.inr hqp
  have hne' : c'.Nonempty := hne.image _
  -- the union of the domains is `Dcl`-closed and log-closed
  have h4c : S4Dom (ExtPair.chainDom c') :=
    S4Dom_chainDom hc' hne' (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := hp
      exact q.h4)
  have hmem : ∀ p ∈ c', LogClosed (p.dom : Set M) := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := hp
    exact q.h4.log_closed
  have hpres : ∀ (p : ExtPair emptyTheory A₀ σ₀) (hp : p ∈ c'),
      LogPreserving p.dom (hmem p hp) p.emb := fun p hp => by
    obtain ⟨q, hq, rfl⟩ := hp
    exact (logPreserving_congr q.dom q.emb _ _).mpr q.logpres
  -- and the embeddings of the chain glue to an embedding of the union, on which `logFun` is still
  -- preserved
  have hlogpres : LogPreserving (ExtPair.chainDom c') h4c.log_closed
      (ExtPair.chainEmbedding hc' hne') :=
    logPreserving_chainEmbedding hc' hne' hmem hpres h4c.log_closed
  obtain ⟨p₀, hp₀⟩ := hne
  have hle₀ : A₀ ≤ ExtPair.chainDom c' :=
    p₀.le_dom.trans (ExtPair.dom_le_chainDom (Set.mem_image_of_mem S4Pair.toExt hp₀))
  refine ⟨{ dom := ExtPair.chainDom c'
            emb := ExtPair.chainEmbedding hc' hne'
            h4 := h4c
            logpres := hlogpres
            le_dom := hle₀
            agrees := ?_ }, ?_⟩
  · -- the glued embedding extends `σ₀`, as each member of the chain does
    intro a
    have ha : (a : M) ∈ p₀.dom := p₀.le_dom a.2
    have h := ExtPair.chainEmbFun_eq hc' hne' (Set.mem_image_of_mem S4Pair.toExt hp₀)
      (⟨(a : M), hle₀ a.2⟩ : ↥(ExtPair.chainDom c')) ha
    rw [show (ExtPair.chainEmbedding hc' hne') ⟨(a : M), hle₀ a.2⟩
        = ExtPair.chainEmbFun hc' hne' ⟨(a : M), hle₀ a.2⟩ from rfl, h]
    exact p₀.agrees a
  · -- and every member of the chain is below the union
    intro a ha
    refine ⟨ExtPair.dom_le_chainDom (Set.mem_image_of_mem S4Pair.toExt ha), ?_⟩
    intro x
    have h := ExtPair.chainEmbFun_eq hc' hne' (Set.mem_image_of_mem S4Pair.toExt ha)
      (⟨(x : M), ExtPair.dom_le_chainDom (Set.mem_image_of_mem S4Pair.toExt ha) x.2⟩ :
        ↥(ExtPair.chainDom c')) x.2
    rw [show (ExtPair.chainEmbedding hc' hne')
        ⟨(x : M), ExtPair.dom_le_chainDom (Set.mem_image_of_mem S4Pair.toExt ha) x.2⟩
        = ExtPair.chainEmbFun hc' hne'
          ⟨(x : M), ExtPair.dom_le_chainDom (Set.mem_image_of_mem S4Pair.toExt ha) x.2⟩ from rfl, h]

/-- **The maximality step.**  A maximal member of the Zorn poset has domain all of `M`: otherwise
the one-element step `S4OnePoint` would produce a strictly larger partial extension, contradicting
maximality. -/
theorem S4Pair_maximal_step {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (h : S4OnePoint) (hM : M ⊨ TE) (hN : N ⊨ TE) (κ : Cardinal.{0})
    (hκ : Cardinal.mk M < κ) (hsat : @IsSaturated LEc N _ κ)
    {A₀ : LRc.Substructure M} {σ₀ : @Embedding LRc ↥A₀ N _ (reductStruct N)}
    {p : S4Pair A₀ σ₀} (hmax : ∀ q : S4Pair A₀ σ₀, p ≤ q → q ≤ p) :
    ∀ x : M, x ∈ (p.dom : Set M) := by
  intro x
  by_contra hx
  obtain ⟨A', hA', σ', hle, ⟨a', ha'⟩, hag, hlogpres⟩ :=
    h M N hM hN κ hκ hsat p.dom p.h4 p.emb p.logpres x hx
  let q : S4Pair A₀ σ₀ :=
    { dom := A'
      emb := σ'
      h4 := hA'
      logpres := hlogpres
      le_dom := p.le_dom.trans hle
      agrees := fun a => (hag ⟨(a : M), p.le_dom a.2⟩ (hle (p.le_dom a.2))).trans (p.agrees a) }
  have hpq : p ≤ q := ⟨hle, fun a => hag a (hle a.2)⟩
  have hmem : (a' : M) ∈ p.dom := (S4Pair.dom_le_of_le (hmax q hpq)) a'.2
  rw [ha'] at hmem
  exact hx hmem

theorem S4SubTE_of_S4OnePoint (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (h : Work.WilC5.S4OnePoint) :
    Work.WilC5.S4SubTE := by
  unfold S4SubTE HasExtPropSub
  intro M N instM instN hM hN κ hκ hsat A hA σ
  -- the initial pair: the carrier of `A` with the restriction of `σ`
  obtain ⟨F, hF, hFeq, τ, hlogpres, hagree⟩ := S4Pair_initial hMCr hM hN A hA σ
  let base : S4Pair F τ :=
    { dom := F
      emb := τ
      h4 := hF
      logpres := hlogpres
      le_dom := le_refl F
      agrees := fun a => congrArg τ (Subtype.ext rfl) }
  haveI : Nonempty (S4Pair F τ) := ⟨base⟩
  -- Zorn: a maximal partial extension
  obtain ⟨p, hmax⟩ := zorn_le_nonempty (α := S4Pair F τ)
    (fun c hc hne => S4Pair_chain_upper hc hne)
  -- its domain is all of `M`, and its embedding is the underlying function of an `LEc`-embedding
  obtain ⟨g, hg⟩ := LEcEmbedding_of_top hM hN p.toExt
    (S4Pair_maximal_step h hM hN κ hκ hsat hmax) p.h4.log_closed p.logpres
  refine ⟨g, ?_⟩
  intro a
  have hmem : (a : M) ∈ F := by
    change (a : M) ∈ (F : Set M)
    rw [hFeq]
    exact a.2
  calc g a = g ((⟨(a : M), hmem⟩ : F) : M) := rfl
    _ = τ ⟨(a : M), hmem⟩ := hg ⟨(a : M), hmem⟩
    _ = σ a := hagree a hmem

end Work.WilC5
