import Mathlib
import Submission.Work.WilC5.S4Setup
import Submission.Work.WilC5.ExtPair_top_embedding
import Submission.Work.WilC5.LEcEmbedding_of_LRcEmbedding

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The top of the §4 iteration is an `LEc`-embedding.**

If a partial extension `p` of `σ₀` (in the sense of `Work.WilC5.ExtPair` for the empty theory)
has domain all of `M`, if that domain is closed under the definable logarithm and `p.emb` preserves
it, then the resulting global `LRc`-embedding of `M` extends to an `LEc`-embedding of `M`, still
agreeing with `σ₀` on `A₀`.

The only content beyond `ExtPair_top_embedding` is the verification that the global `LRc`-embedding
built there commutes with `logFun`: it is `p.emb` composed with the identity-on-elements
equivalence `p.dom ≃[LRc] M`, so on `x ∈ M` it is `p.emb ⟨x, _⟩`, and `LogPreserving p.dom hlog
p.emb` is exactly the commutation with `logFun`.  `LEcEmbedding_of_LRcEmbedding` then upgrades an
`LRc`-embedding of models of `TE` preserving `logFun` to an `LEc`-embedding. -/
theorem LEcEmbedding_of_top {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    (hM : M ⊨ WilkiesDesign.CG.TE) (hN : N ⊨ WilkiesDesign.CG.TE)
    {A₀ : WilkiesDesign.CG.LRc.Substructure M}
    {σ₀ : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥A₀ N _ (Work.WilC5.reductStruct N)}
    (p : Work.WilC5.ExtPair Work.WilC5.emptyTheory A₀ σ₀)
    (htop : ∀ x : M, x ∈ (p.dom : Set M))
    (hlog : Work.WilC5.LogClosed (p.dom : Set M))
    (hpres : Work.WilC5.LogPreserving p.dom hlog p.emb) :
    ∃ g : WilkiesDesign.CG.LEc.Embedding M N, ∀ a : A₀, g a = σ₀ a := by
  -- The identity-on-elements equivalence `p.dom ≃[LRc] M`.
  let e : @FirstOrder.Language.Equiv WilkiesDesign.CG.LRc p.dom M _ _ :=
    { toFun := fun x => (x : M)
      invFun := fun m => ⟨m, htop m⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl
      map_fun' := fun {n} f x => rfl
      map_rel' := fun {n} r x => Iff.rfl }
  -- The global `LRc`-embedding of `M`.
  let g : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc M N _ _ :=
    p.emb.comp e.symm.toEmbedding
  have hgx : ∀ x : M, g x = p.emb ⟨x, htop x⟩ := by
    intro x
    show p.emb (e.symm.toEmbedding x) = p.emb ⟨x, htop x⟩
    congr 1
  -- It commutes with the definable logarithm.
  have hf : ∀ x : M, g (Work.WilC5.logFun x) = Work.WilC5.logFun (g x) := by
    intro x
    calc g (Work.WilC5.logFun x) = p.emb ⟨Work.WilC5.logFun x, htop (Work.WilC5.logFun x)⟩ :=
          hgx (Work.WilC5.logFun x)
      _ = p.emb ⟨Work.WilC5.logFun x, hlog x (htop x)⟩ :=
          congrArg p.emb (Subtype.ext rfl)
      _ = Work.WilC5.logFun (p.emb ⟨x, htop x⟩) := hpres ⟨x, htop x⟩
      _ = Work.WilC5.logFun (g x) := congrArg Work.WilC5.logFun (hgx x).symm
  obtain ⟨g', hg'⟩ := Work.WilC5.LEcEmbedding_of_LRcEmbedding hM hN g hf
  refine ⟨g', ?_⟩
  intro a
  have h1 : (g' : M → N) (a : M) = g (a : M) := congrFun hg' (a : M)
  rw [h1, hgx (a : M)]
  rw [show (⟨(a : M), htop (a : M)⟩ : p.dom) = ⟨(a : M), p.le_dom a.2⟩ from Subtype.ext rfl]
  exact p.agrees a

end Work.WilC5
