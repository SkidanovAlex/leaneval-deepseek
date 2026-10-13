import Mathlib
import Submission.Work.WilC5.S4Setup

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The one missing symbol.**  The `LEc`-structure on a type is determined by its
`reductStruct` together with the *full* exponential: `LEc = (ring ⊕ exp)[[ℝ]]` is obtained from
`LRc = (ring ⊕ rexp)[[ℝ]]` by replacing the restricted exponential `rexpFromExp` (with which
`reductStruct` interprets `rexp`) by `expE`.  This lemma unfolds the (only) `LEc` function symbol
that is not a symbol of `LRc`, so that the `exp` obligation of an `LEc`-embedding can be stated
in terms of `expE`. -/
theorem funMap_expSym {M : Type} [WilkiesDesign.CG.LEc.Structure M] (xs : Fin 1 → M) :
    @Structure.funMap WilkiesDesign.CG.LEc M _ 1
        (Sum.inl (Sum.inr WilkiesConjecture.expFunc.exp)) xs
      = Work.WilC5.expE (xs 0) := by
  rw [Work.WilC5.expE_def]
  show @Structure.funMap WilkiesDesign.CG.LEc M _ 1
        (Work.WilC5.expSym WilkiesConjecture.expFunc.exp) xs
      = @Structure.funMap WilkiesDesign.CG.LEc M _ 1
        (Work.WilC5.expSym WilkiesConjecture.expFunc.exp) ![xs 0]
  congr 1
  funext i
  fin_cases i
  rfl

/-- **An `LRc`-embedding of the `rexp`-reducts that preserves the logarithm is an `LEc`-embedding.**

`LEc` is the definitional expansion of `LRc` obtained by adjoining the full exponential `exp`
to the data of the `rexp`-reduct (`rexp` itself is recovered as the definable restricted
exponential `rexpFromExp`).  Hence an embedding `f` of the `LRc`-reducts of two models of `TE`
which already commutes with the (definable) logarithm `logFun` is automatically an `LEc`-embedding:
the ring and constant symbols are interpreted identically in `LRc` and `LEc` (`reductStruct`), and
the remaining symbol `exp` is preserved by `f` by
`Work.WilC5.expE_of_logFun_preserving`. -/
theorem LEcEmbedding_of_LRcEmbedding {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (f : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc K L (Work.WilC5.reductStruct K) (Work.WilC5.reductStruct L))
    (hf : ∀ x : K, f (Work.WilC5.logFun x) = Work.WilC5.logFun (f x)) :
    ∃ g : WilkiesDesign.CG.LEc.Embedding K L, (g : K → L) = f := by
  -- `f` preserves the full exponential, the only `LEc`-symbol not already a symbol of `LRc`.
  have hexp : ∀ x : K, f (Work.WilC5.expE x) = Work.WilC5.expE (f x) :=
    Work.WilC5.expE_of_logFun_preserving hK hL f hf
  refine ⟨{ toEmbedding := f.toEmbedding, map_fun' := ?_, map_rel' := ?_ }, rfl⟩
  · intro n g x
    -- `LEc.Functions n = (ring.Functions n ⊕ exp.Functions n) ⊕ (constantsOn ℝ).Functions n`
    rcases g with (g | r) | c
    · -- ring symbol: `reductStruct` interprets it exactly as `LEc` does
      exact f.map_fun (Sum.inl (Sum.inl g)) x
    · -- the exponential symbol: this is `hexp`
      rcases r with ⟨⟩
      rw [funMap_expSym, funMap_expSym]
      exact hexp (x 0)
    · -- constant symbol for a real: again interpreted identically in `LRc` and `LEc`
      exact f.map_fun (Sum.inr c) x
  · -- `LEc` has no relation symbols
    intro n r x
    exact nomatch r

end Work.WilC5
