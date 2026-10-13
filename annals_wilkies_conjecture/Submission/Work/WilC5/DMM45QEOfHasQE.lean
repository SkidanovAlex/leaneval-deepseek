import Mathlib
import Submission.Work.WilC5.QETheory
import Submission.Work.WilC5.LogTranslation

namespace Work.WilC5

theorem DMM45QEOfHasQE (h : Work.WilC5.HasQE Work.WilC5.TElog) {n : ℕ}
    (φ : WilkiesDesign.CG.LEc.Formula (Fin n)) :
    ∃ θ : Work.WilC5.LElog.Formula (Fin n), θ.IsQF ∧
      ∀ (M : Type) [WilkiesDesign.CG.LEc.Structure M],
        FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE → ∀ x : Fin n → M,
          (@FirstOrder.Language.Formula.Realize WilkiesDesign.CG.LEc M _ (Fin n) φ x) ↔
            (@FirstOrder.Language.BoundedFormula.Realize Work.WilC5.LElog M
              (Work.WilC5.logStruct M) (Fin n) 0 θ x (Work.WilC5.emptyBnd)) := by
  -- View the `LEc`-formula `φ` as an `LElog`-formula along the language inclusion
  -- `sumInl : LEc →ᴸ LElog`; the extra symbols (`log`, `≤`) are simply not used.
  obtain ⟨θ, hθqf, hθ⟩ :=
    h ((FirstOrder.Language.LHom.sumInl :
        WilkiesDesign.CG.LEc →ᴸ Work.WilC5.LElog).onFormula φ)
  refine ⟨θ, hθqf, ?_⟩
  intro M instM hM x
  -- Quantifier elimination in `TElog` applies, because the definable expansion of a model of
  -- `TE` is a model of `TElog`.
  have h1 := hθ M (Work.WilC5.logStruct_model_TElog hM) x
  -- Realization of `φ` does not change when passing from `LEc` to `LElog`.
  have h2 := FirstOrder.Language.LHom.realize_onFormula (M := M)
    (φ := (FirstOrder.Language.LHom.sumInl : WilkiesDesign.CG.LEc →ᴸ Work.WilC5.LElog)) φ (v := x)
  have h3 := FirstOrder.Language.Formula.boundedFormula_realize_eq_realize
    (L := Work.WilC5.LElog) (M := M) θ x (Work.WilC5.emptyBnd)
  exact h2.symm.trans (h1.trans h3.symm)

end Work.WilC5
