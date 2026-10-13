import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild

/-!
  WilC5 — the semantics of the type sentences `p.sent F` for *term-parameter* types `SatTyp2`.

  `SatTyp2 L C` is a `Σ`-type and `SatLang L C` is definitionally `L[[C]]`.  Both are ordinary
  `def`s, so the `rw`/`simp` machinery refuses to unfold them while elaborating the implicit
  arguments of the library lemmas (`realize_ex`, `realize_relabel`, …) used below.  Marking them
  implicit-reducible for the duration of this file makes those lemmas applicable; this is a purely
  syntactic device and does not change any statement.
-/
attribute [local implicit_reducible] FirstOrder.Language.withConstants Work.WilC5.SatTyp2

namespace Work.WilC5

/-- `SatTyp2.sent p F` is the sentence `∃y ⋀F` in which the parameters of the type `p` are read
through the corresponding closed terms.  This is the semantic unfolding of that sentence: it holds
in a structure `N` exactly when some element `a` of `N` satisfies every formula of the finite set
`F` simultaneously, the parameters being interpreted by their terms. -/
theorem SatSentRealize {L : FirstOrder.Language.{0, 0}} {C : Type} (N : Type)
    (instN : (SatLang L C).Structure N) (p : SatTyp2 L C)
    (F : Finset ((SatLang L C).Formula (p.1 ⊕ Fin 1))) :
    @FirstOrder.Language.Formula.Realize (SatLang L C) N instN Empty (p.sent F)
        (default : Empty → N) ↔
      ∃ a : N, ∀ φ ∈ F, @FirstOrder.Language.Formula.Realize (SatLang L C) N instN (p.1 ⊕ Fin 1) φ
        (Sum.elim (fun t : p.1 => @FirstOrder.Language.Term.realize (SatLang L C) N instN Empty
          (default : Empty → N) t.1) (fun _ : Fin 1 => a)) := by
  -- Unfold the syntax: the sentence is `(∃y ⋀F).subst`, and evaluate each layer.
  simp only [SatTyp2.sent, SatTyp2.ex, SatTyp2.conj, FirstOrder.Language.Formula.Realize,
    FirstOrder.Language.BoundedFormula.realize_subst,
    FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_relabel]
  refine exists_congr (fun y => ?_)
  -- The remaining conjunction `⋀F` is a `List.foldr` of `⊓` over `F.toList`.
  refine (FirstOrder.Language.BoundedFormula.realize_foldr_inf F.toList _ _).trans ?_
  -- The two assignments agree: the parameter part is by definition, the value part uses that
  -- `Fin.snoc` on an empty tuple is the constant function.
  have hy1 :
      (Sum.elim (fun t : p.1 => @FirstOrder.Language.Term.realize (SatLang L C) N instN Empty
            (default : Empty → N) t.1)
          (Fin.snoc (default : Fin 0 → N) y ∘ Fin.castAdd 0) ∘ id)
        = Sum.elim (fun t : p.1 => @FirstOrder.Language.Term.realize (SatLang L C) N instN Empty
            (default : Empty → N) t.1) (fun _ : Fin 1 => y) := by
    funext x
    rcases x with t | i
    · rfl
    · simp [Fin.snoc_zero]
  have hy2 : (Fin.snoc (default : Fin 0 → N) y ∘ Fin.natAdd 1) = (default : Fin 0 → N) := by
    funext i
    exact Fin.elim0 i
  simp only [hy1, hy2, Finset.mem_toList]

end Work.WilC5
