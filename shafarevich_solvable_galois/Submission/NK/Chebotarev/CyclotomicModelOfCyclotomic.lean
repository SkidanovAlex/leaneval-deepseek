/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.KroneckerWeber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cyclotomic fields are models for Kronecker–Weber

The conclusion of `NK.Chebotarev.KroneckerWeber` is satisfiable: a cyclotomic field `ℚ(ζ_n)`
is itself a `CyclotomicModel` (with `E = ⊤`).  This records that the `Prop` is not vacuous, and it
is the base case of any attempt at the theorem.
-/

set_option linter.unusedSectionVars false

universe u

namespace NK.Chebotarev

/-- **A cyclotomic field is a model for itself.** -/
theorem nonempty_cyclotomicModel_of_isCyclotomic (n : ℕ) [NeZero n] (L : Type u) [Field L]
    [NumberField L] [IsGalois ℚ L] (h : IsCyclotomicExtension {n} ℚ L) :
    Nonempty (CyclotomicModel L n) :=
  ⟨{ F := L
     fieldF := inferInstance
     numberFieldF := inferInstance
     cyclotomicF := h
     E := ⊤
     galoisE := isGalois_iff_isGalois_top.mpr inferInstance
     equiv := IntermediateField.topEquiv.symm }⟩

/-- **Kronecker–Weber for cyclotomic fields** (the trivial case, and the base case of the
theorem): a field of the form `ℚ(ζ_n)` is its own cyclotomic model.  In particular the `Prop`
`NK.Chebotarev.KroneckerWeber` is not vacuous. -/
theorem kroneckerWeber_cyclotomic {L : Type u} [Field L] [NumberField L] [IsGalois ℚ L]
    {n : ℕ} [NeZero n] (h : IsCyclotomicExtension {n} ℚ L) :
    ∃ (n' : ℕ) (_ : 0 < n'), Nonempty (CyclotomicModel L n') :=
  ⟨n, NeZero.pos n, nonempty_cyclotomicModel_of_isCyclotomic n L h⟩

end NK.Chebotarev
