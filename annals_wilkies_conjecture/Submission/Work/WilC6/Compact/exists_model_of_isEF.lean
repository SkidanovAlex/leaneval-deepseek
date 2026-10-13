/-
  WilC6 — Compact: the compactness step for the model completeness argument.

  `Work.WilC6.Compact.exists_model_of_isEF` is step 3 of the design
  (`Submission/Work/WilC6/DESIGN.md`): if a tuple `b` in a model `N` of `TE` realizes every `IsEF`
  consequence of `φ`, then there is a model `M` of `TE` and a tuple `a` with `M ⊨ φ(a)` whose
  existential (`IsEF`) type is contained in that of `b`.

  The proof is the standard compactness argument.  Work in the language `LEc[[Fin n]]`, where the
  free variables of `φ` are named by constants, and consider the theory

    `S = TE ∪ {φ} ∪ {¬Ψ : IsEF Ψ, N ⊭ Ψ(b)}`.

  Its finite pieces are the theories `cTheory φ b F` of `Compact/Defs.lean`, indexed by a finite
  set `F` of existential formulas not realized at `b`.  Each of them is satisfiable
  (`Compact/cTheory_isSatisfiable.lean`): modulo `F`, the conjunctions of their negations is the
  negation of the single existential formula `Ψ' = ⋁_{Ψ ∈ F} Ψ`, which is an `IsEF` consequence of
  `φ` exactly if it already holds at `b` — a contradiction — so otherwise a counterexample model
  contains a model of the finite piece, expanded by naming the tuple by constants.

  `S` is the union of these finite pieces over a directed family, so by compactness it is
  satisfiable; a model `N'` of it gives a complete type `p = Th(N') ∈ TE.CompleteType (Fin n)`
  containing `φ` and every `¬Ψ` with `IsEF Ψ`, `N ⊭ Ψ(b)`.  By Mathlib's
  `Theory.exists_modelType_is_realized_in`, that type is realized in a model `M ⊨ TE` by a tuple
  `a`, which is exactly the tuple we were looking for.
-/
import Mathlib
import Submission.Work.WilC6.Compact.Defs
import Submission.Work.WilC6.Compact.cTheory_isSatisfiable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6.Compact

theorem exists_model_of_isEF {n : ℕ} (φ : WilkiesDesign.CG.LEc.Formula (Fin n))
    (N : Type) [WilkiesDesign.CG.LEc.Structure N]
    [FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE] (b : Fin n → N)
    (hΓ : ∀ Ψ : WilkiesDesign.CG.LEc.Formula (Fin n),
      Work.WilC6.IsEF Ψ → Work.WilC6.EFCons φ Ψ → Ψ.Realize b) :
    ∃ (M : Type) (_ : WilkiesDesign.CG.LEc.Structure M)
      (_ : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) (a : Fin n → M),
      φ.Realize a ∧ ∀ Ψ : WilkiesDesign.CG.LEc.Formula (Fin n),
        Work.WilC6.IsEF Ψ → Ψ.Realize a → Ψ.Realize b := by
  classical
  -- The family of finite pieces is directed under inclusion.
  have hdir : Directed (· ⊆ ·) (fun F : Finset (EFIndex b) => cTheory φ b F) := by
    intro F G
    exact ⟨F ∪ G, cTheory_mono Finset.subset_union_left, cTheory_mono Finset.subset_union_right⟩
  -- Every finite piece is satisfiable.
  have hsat : ∀ F : Finset (EFIndex b), (cTheory φ b F).IsSatisfiable :=
    fun F => cTheory_isSatisfiable φ N b hΓ F
  have hunion : Theory.IsSatisfiable (⋃ F : Finset (EFIndex b), cTheory φ b F) :=
    (Theory.isSatisfiable_directed_union_iff hdir).2 hsat
  obtain ⟨N'⟩ := hunion
  -- `N'` satisfies `φ` and the negation of every existential formula not realized at `b`.
  have hφN' : N' ⊨ Formula.equivSentence φ :=
    Theory.realize_sentence_of_mem _ (Set.mem_iUnion.2 ⟨∅, equivSentence_mem_cTheory φ b ∅⟩)
  have hTE : N' ⊨ (LEc.lhomWithConstants (Fin n)).onTheory TE :=
    Theory.Model.mono (inferInstance : N' ⊨ ⋃ F : Finset (EFIndex b), cTheory φ b F) (by
      intro ψ hψ
      exact Set.mem_iUnion.2 ⟨∅, onTheory_subset_cTheory φ b ∅ hψ⟩)
  -- The complete type of `N'`, viewed as a type over `TE` in the variables `Fin n`.
  have hsubset : (LEc.lhomWithConstants (Fin n)).onTheory TE ⊆ (LEc[[Fin n]]).completeTheory N' :=
    fun ψ hψ => mem_completeTheory.2 (hTE.realize_of_mem ψ hψ)
  let p : TE.CompleteType (Fin n) :=
    { toTheory := (LEc[[Fin n]]).completeTheory N'
      subset' := hsubset
      isMaximal' := completeTheory.isMaximal (LEc[[Fin n]]) N' }
  -- Every type is realized in some model of the theory.
  obtain ⟨M, hM⟩ := Theory.exists_modelType_is_realized_in TE p
  obtain ⟨a, ha⟩ := hM
  refine ⟨M, M.struc, M.is_model, a, ?_, ?_⟩
  · -- `φ` holds at `a` because `equivSentence φ ∈ p = TE.typeOf a`.
    have h1 : Formula.equivSentence φ ∈ TE.typeOf a := by
      rw [ha]
      exact mem_completeTheory.2 hφN'
    exact (Theory.CompleteType.formula_mem_typeOf).1 h1
  · -- Every existential formula true at `a` is true at `b`.
    intro Ψ hEF hΨa
    by_contra hnot
    have hmem : (Formula.equivSentence Ψ).not ∈ (⋃ F : Finset (EFIndex b), cTheory φ b F) :=
      Set.mem_iUnion.2
        ⟨{⟨Ψ, hEF, hnot⟩}, not_equivSentence_mem_cTheory (Finset.mem_singleton_self _)⟩
    have hmod : N' ⊨ (Formula.equivSentence Ψ).not := Theory.realize_sentence_of_mem _ hmem
    have hΨN' : N' ⊨ Formula.equivSentence Ψ := by
      have h2 : Formula.equivSentence Ψ ∈ TE.typeOf a :=
        (Theory.CompleteType.formula_mem_typeOf).2 hΨa
      rw [ha] at h2
      exact mem_completeTheory.1 h2
    exact (Sentence.realize_not N').1 hmod hΨN'

end Work.WilC6.Compact
