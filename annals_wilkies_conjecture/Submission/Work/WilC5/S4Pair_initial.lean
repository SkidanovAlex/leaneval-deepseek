/-
  WilC5 — **the initial pair of the §4 Zorn iteration**.

  The Zorn poset `Work.WilC5.S4Pair` of `S4Setup.lean` consists of the invariant partial extensions
  `(F, σ)` of a prescribed initial pair: `F ≤ K` an `LRc`-substructure which is `Dcl`-closed and
  log-closed (`Work.WilC5.S4Dom`), and `σ : F → L` a log-preserving `LRc`-embedding
  (`Work.WilC5.LogPreserving`) extending the prescribed `σ₀` on the prescribed domain `A₀`.

  This module provides the *bottom* element of that poset: given an `LEc`-substructure `A ≤ M` of a
  model of `TE` which is itself a model of `TE`, and any `LEc`-embedding `σ : A → N` into a model
  `N ⊨ TE`, the pair `(A, σ)` already satisfies the invariant.

  There are two points to it.

  * **`A` is the carrier of an `LRc`-substructure of the `rexp`-reduct.**  The carrier `A` is closed
    under the ring operations and the constants because it is an `LEc`-substructure, and under the
    restricted exponential because the restricted exponential is `LEc`-*definable* (it is the value
    of a term, hence in the definable closure of `A`); the `Dcl`-closure of `A` comes from
    `Work.WilC5.dcl_substructure_subset` (model completeness of `TR` plus the elementarity of the
    inclusion `A ↪ M`), and log-closure from `Work.WilC5.logFun_mem_of_substructure`.
  * **`σ` is already an `LRc`-embedding of the `rexp`-reducts** and commutes with `logFun`.  The
    first is `Work.WilC5.ReductEmb` (`σ` preserves the *definable* restricted exponential), the
    second is `Work.WilC5.LogFunMap`.

  The `LRc`-structure on the carrier is the one induced by `M`'s `rexp`-reduct
  (`Substructure.inducedStructure`), *not* the `rexp`-reduct of `M`'s `LEc`-structure restricted to
  `A` — these two `LRc`-structures agree on the nose (see `Work.WilC5.rexpFromExp_reduct_coe`
  below), and it is the structural transport between them that the proof of `S4Pair_initial`
  performs.
-/
import Mathlib
import Submission.Work.WilC5.S4Setup
import Submission.Work.WilC5.dclClosed_substructure

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## The two structural facts about the initial pair -/

/-- **The restricted exponential of the `rexp`-reduct of an `LEc`-substructure is the ambient
one.**

`reductStruct ↥A` computes `rexp x` in the `LEc`-structure of the subtype `↥A` (i.e. as
`if absLeOne x then exp x else 0`, with the `LEc`-structure induced from `M`), whereas the
`LRc`-substructure of `M` carried by `A` computes it as the *ambient* `rexpFromExp`.  This lemma
identifies the two: the inclusion `A ↪ M` is an `LEc`-embedding of models of `TE`, so it preserves
the definable restricted exponential (`Work.WilC5.rexpFromExp_map`). -/
theorem rexpFromExp_reduct_coe {M : Type} [LEc.Structure M] (hM : M ⊨ TE)
    (A : LEc.Substructure M) (hA : (A : Type) ⊨ TE) (xs : Fin 1 → ↥A) :
    ((@Structure.funMap LRc ↥A (reductStruct ↥A) 1 (Sum.inl (Sum.inr rexpFunc.rexp)) xs : ↥A) : M)
      = rexpFromExp ((xs 0 : ↥A) : M) := by
  have h : (A.subtype (rexpFromExp (xs 0 : ↥A)) : M) = rexpFromExp (A.subtype (xs 0)) :=
    rexpFromExp_map (Substructure.subtype A) hA hM (xs 0)
  show (↑(rexpFromExp (xs 0 : ↥A)) : M) = rexpFromExp ((xs 0 : ↥A) : M)
  simpa using h

/-- **An `LEc`-substructure of a model of `TE` which is itself a model of `TE` is the carrier of an
`LRc`-substructure satisfying the §4 invariant.**

The `LRc`-substructure is the carrier `A` itself; its closure under the function symbols of `LRc`
is the `Dcl`-closure of `A` (a function symbol of `LRc` is the term `Functions.term f`, whose value
at a tuple of elements of `A` lies in `Dcl A`, and `Dcl A ⊆ A` by
`Work.WilC5.dcl_substructure_subset`).  The two invariant properties are the same `Dcl`-closure
together with log-closure (`Work.WilC5.logFun_mem_of_substructure`). -/
theorem LRcSubstructure_of_LEcSubstructure (hMCr : ModelComplete TR)
    {M : Type} [LEc.Structure M] (hM : M ⊨ TE)
    (A : LEc.Substructure M) (hA : (A : Type) ⊨ TE) :
    ∃ F : LRc.Substructure M, (F : Set M) = (A : Set M) ∧ S4Dom F := by
  have hdcl : @Work.WilC2.Dcl M (reductStruct M) (A : Set M) ⊆ (A : Set M) :=
    dcl_substructure_subset hMCr hM A hA
  have hlog : LogClosed (A : Set M) := fun x hx => logFun_mem_of_substructure hM A hA hx
  refine ⟨{ carrier := (A : Set M)
            fun_mem := fun {n} f x hx => by
              have h := hdcl (term_realize_mem_dcl (Functions.term f) x hx)
              simpa [Functions.term, Term.realize_func, Term.realize_var] using h }, rfl, ?_⟩
  exact ⟨hdcl, hlog⟩

/-! ## The initial pair -/

/-- **The initial pair of the §4 iteration.**  An `LEc`-substructure `A ≤ M` of a model of `TE`
which is itself a model of `TE`, together with an `LEc`-embedding `σ : A → N` into a model `N ⊨ TE`,
is already an element of the Zorn poset `Work.WilC5.S4Pair A σ`: view `A` as an
`LRc`-substructure of the `rexp`-reduct of `M`, and `σ` as an `LRc`-embedding of the reducts (it is
log-preserving by `Work.WilC5.LogFunMap`). -/
theorem S4Pair_initial (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    (hM : M ⊨ WilkiesDesign.CG.TE) (hN : N ⊨ WilkiesDesign.CG.TE)
    (A : WilkiesDesign.CG.LEc.Substructure M) (hA : (A : Type) ⊨ WilkiesDesign.CG.TE)
    (σ : WilkiesDesign.CG.LEc.Embedding A N) :
    ∃ (F : WilkiesDesign.CG.LRc.Substructure M) (hF : Work.WilC5.S4Dom F),
      (F : Set M) = (A : Set M) ∧
      ∃ τ : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥F N _ (Work.WilC5.reductStruct N),
        Work.WilC5.LogPreserving F hF.log_closed τ ∧
        ∀ (a : A) (h : (a : M) ∈ F), τ ⟨(a : M), h⟩ = σ a := by
  -- `σ` preserves the definable restricted exponential, hence is an `LRc`-embedding of reducts
  obtain ⟨g, hg⟩ := ReductEmb hA hN σ
  have hg' : ∀ v : ↥A, g v = σ v := fun v => congrFun hg v
  -- `A` is the carrier of an `LRc`-substructure satisfying the invariant
  obtain ⟨F, hFc, hFdom⟩ := LRcSubstructure_of_LEcSubstructure hMCr hM A hA
  -- `logFun` is absolute between `↥A` and `M`
  have hlogA : ∀ y : ↥A, ((logFun y : ↥A) : M) = logFun (y : M) := by
    intro y
    simpa using LogFunMap hA hM (Substructure.subtype A) y
  -- the identity map `↥F → ↥A` (the two carriers are the same subset of `M`)
  let i : ↥F → ↥A := fun v => ⟨(v : M), by
    have hv : (v : M) ∈ (F : Set M) := v.2
    exact (Set.ext_iff.mp hFc (v : M)).mp hv⟩
  -- it is an `LRc`-embedding: ring operations and constants are inherited, `rexp` by
  -- `rexpFromExp_reduct_coe`
  have hmap : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → ↥F),
      i (Structure.funMap f x) = Structure.funMap f (i ∘ x) := by
    intro n f x
    rcases f with (f | r) | c
    · rfl
    · rcases r with ⟨⟩
      apply Subtype.ext
      rw [rexpFromExp_reduct_coe hM A hA (i ∘ x)]
      rfl
    · rfl
  let φ : ↥F ↪[LRc] ↥A :=
    { toFun := i
      inj' := fun a b h => Subtype.ext (show (a : M) = (b : M) from
        congrArg (fun v : ↥A => (v : M)) h)
      map_fun' := hmap
      map_rel' := by intro n r x; exact nomatch r }
  -- the transported embedding: `σ` composed with the identification of the carriers
  let τ : @Embedding LRc ↥F N _ (reductStruct N) := g.comp φ
  refine ⟨F, hFdom, hFc, τ, ?_, ?_⟩
  · -- log-preservation: `τ` is `σ` on elements, and `σ` commutes with the definable logarithm
    intro x
    have h1 : i ⟨logFun (x : M), hFdom.log_closed (x : M) x.2⟩ = logFun (i x) := by
      apply Subtype.ext
      rw [hlogA (i x)]
    calc (g.comp φ) ⟨logFun (x : M), hFdom.log_closed (x : M) x.2⟩
        = g (i ⟨logFun (x : M), hFdom.log_closed (x : M) x.2⟩) := rfl
      _ = g (logFun (i x)) := by rw [h1]
      _ = σ (logFun (i x)) := hg' _
      _ = logFun (σ (i x)) := LogFunMap hA hN σ (i x)
      _ = logFun (g (i x)) := by rw [hg' (i x)]
      _ = logFun ((g.comp φ) x) := rfl
  · -- the extension property: `τ` agrees with `σ` on the initial domain `A`
    intro a h
    show g (i ⟨(a : M), h⟩) = σ a
    have h2 : i ⟨(a : M), h⟩ = a := rfl
    rw [h2, hg' a]

end Work.WilC5
