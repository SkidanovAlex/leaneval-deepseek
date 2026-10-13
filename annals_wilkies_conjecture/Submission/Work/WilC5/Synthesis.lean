/-
  WilC5 — the synthesis of the first (log-language) route: quantifier elimination in `LElog` gives
  model completeness of `TE`.

  This module used to derive `Work.WilC5.ModelComplete_TE` from `HasQE TElog`
  (via `DMM45_QE`, the `LEc`-formula level descent of vdDMM's Corollary 4.5), and hence from the
  residual hole `Work.WilC5.DMM41`.  That route has been **retired**: vdDMM's (4.10) proves
  quantifier elimination for `(𝓡, exp)` only in the language of `𝓡` together with `log` *and a
  symbol for every `∅`-definable function of `𝓡`*.  In the reduced language
  `LEc = ring ⊕ exp ⊕ ℝ` (and hence in `LElog = LEc ⊕ {log, ≤}`) the statement
  `HasQE TElog` is strictly stronger than the source's, and the Sacks test that consumes it cannot
  be expected to apply; the surviving argument is vdDMM Theorem 4.1, carried by
  `Work.WilC5.S4SubTE` (`Submission/Work/WilC5/S4SubTE.lean`), which needs no quantifier
  elimination at all.  See the module comment of `Main.lean`.

  What remains here is the *conditional* statement, which is still useful: vdDMM Theorem 4.1 in
  the log language (arbitrary `LElog`-substructures of models of `TElog`) implies
  `ModelComplete TE`, with no `sorry` in the closure.  The proof is purely formal:

  * if `f : M ↪[LEc] N` is an embedding of models of `TE`, then `f` is an `LElog`-embedding
    (`LogStructEmbedding`, because `log` and `≤` are definable), and quantifier-free
    `LElog`-formulas are absolute for embeddings
    (`FirstOrder.Language.BoundedFormula.IsQF.realize_embedding`);
  * quantifier elimination for `TElog` (`Work.WilC5.HasQEOfExtensionProperty`, Sacks' test applied
    to the hypothesis) makes every formula equivalent to a quantifier-free one,
  * hence `f` is elementary.
-/
import Submission.Work.WilC5.DMM45QEOfHasQE
import Submission.Work.WilC5.LogStructEmbedding
import Submission.Work.WilC5.HasQEOfExtensionProperty

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **Model completeness of `TE`, conditional on vdDMM Theorem 4.1 in the log language alone.**

The hypothesis is the extension property of vdDMM Theorem 4.1 for `TElog` — the statement that was
carried as the hole `Work.WilC5.DMM41`.  With it as an explicit hypothesis, `ModelComplete TE` is
proved with no `sorry` in the closure (Sacks' quantifier-elimination test is
`Work.WilC5.HasQEOfExtensionProperty`). -/
theorem ModelComplete_TE_of_hasExtProp (h : Work.WilC5.HasExtProp LElog TElog) :
    WilkiesDesign.CG.ModelComplete TE := by
  intro M N _instM _instN hM hN f n φ x
  obtain ⟨θ, hθ, hiff⟩ :=
    DMM45QEOfHasQE (Work.WilC5.HasQEOfExtensionProperty TElog h) φ
  obtain ⟨g, hg⟩ := LogStructEmbedding hM hN f
  have hMN := hiff M hM x
  have hNN := hiff N hN ((f : M → N) ∘ x)
  have hq : @BoundedFormula.Realize LElog N (logStruct N) (Fin n) 0 θ
        ((f : M → N) ∘ x) (emptyBnd) ↔
      @BoundedFormula.Realize LElog M (logStruct M) (Fin n) 0 θ x (emptyBnd) := by
    have h' := hθ.realize_embedding g (v := x) (xs := (emptyBnd : Fin 0 → M))
    rw [show (g ∘ x) = ((f : M → N) ∘ x) from funext fun i => hg (x i),
      show (g ∘ (emptyBnd : Fin 0 → M)) = (emptyBnd : Fin 0 → N) from
        funext fun i => i.elim0] at h'
    exact h'
  exact hNN.trans (hq.trans hMN.symm)

end Work.WilC5
