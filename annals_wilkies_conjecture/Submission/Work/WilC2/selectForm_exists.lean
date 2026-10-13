import Mathlib
import Submission.Work.WilC2.ChoiceDefs
import Submission.Work.WilC2.SelectDefs

set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC2

/-- **The selecting formula realizes the choice condition**: the parametric `LRc`-formula
`selectForm φ` built in `Submission.Work.WilC2.SelectDefs` has, in every ordered field model in
which the nonnegative elements are exactly the squares, the realisation prescribed by
`ChoiceCond φ`. -/
theorem selectForm_realize {n : ℕ} (φ : Work.WilC2.ParamFormula n) {M : Type} [Field M]
    [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin n → M) (y : M) :
    (selectForm φ).Realize (Sum.elim v (fun _ => y)) ↔ Work.WilC2.ChoiceCond φ v y := by
  simp only [selectForm, Formula.realize_iExs, Formula.realize_inf, lcA_realize hsq,
    infA_realize hsq, supA_realize hsq, rrA_realize hsq, midA_realize, ChoiceCond,
    Sum.elim_inl, Sum.elim_inr, exists_fin3', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨m, s, t, h1, h2, h3, h4, h5⟩
    exact ⟨h1, m, s, t, h2, h3, h4, h5⟩
  · rintro ⟨h1, m, s, t, h2, h3, h4, h5⟩
    exact ⟨m, s, t, h1, h2, h3, h4, h5⟩

theorem selectForm_exists {n : ℕ} (φ : Work.WilC2.ParamFormula n) :
    ∃ ψ : Work.WilC2.ParamFormula n,
      ∀ {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
        [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
        [(FirstOrder.Language.constantsOn ℝ).Structure M]
        (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin n → M) (y : M),
        ψ.Realize (Sum.elim v (fun _ => y)) ↔ Work.WilC2.ChoiceCond φ v y :=
  ⟨selectForm φ, fun hsq v y => selectForm_realize φ hsq v y⟩

end Work.WilC2
