import Mathlib
import Submission.Work.Tower.Unramified.Basic

/-!
# The maximal elementary abelian unramified `3`-extension

`maxElemAbUnram3 F` is the compositum of all finite everywhere-unramified elementary abelian
`3`-extensions of the number field `F` (inside a fixed algebraic closure), i.e. the fixed field of
`Φ(Gal(F^{ur,3}/F))` in the notation of the paper.  The main API is:

* `Work.Tower.IsElementaryAbelianThreeExtension`: `E/F` is Galois with all Galois elements of
  order dividing `3`;
* `Work.Tower.maxElemAbUnram3`: the compositum;
* `Work.Tower.le_maxElemAbUnram3`: every finite unramified elementary abelian `3`-extension of `F`
  is contained in `maxElemAbUnram3 F`.

Finiteness of `maxElemAbUnram3 F` (equivalently, finiteness of the `3`-class group of `F` in the
class-field-theoretic picture) is *not* proved here; the statements that need it are exposed
with an explicit `FiniteDimensional F (maxElemAbUnram3 F)` hypothesis.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

variable (F : Type*) [Field F] [NumberField F]

/-- `E/F` is an **elementary abelian `3`-extension**: it is Galois and every Galois element has
order dividing `3`.  (For a Galois extension this makes `Gal(E/F)` a subgroup of a product of
`ℤ/3`'s exactly when it is abelian; we keep the weak condition `∀ σ, σ^3 = 1` that the
construction uses.) -/
def IsElementaryAbelianThreeExtension {L : Type*} [Field L] [Algebra F L]
    (E : IntermediateField F L) : Prop :=
  IsGalois F ↥E ∧ ∀ σ : Gal(↥E/F), σ ^ 3 = 1

variable {F}

theorem IsElementaryAbelianThreeExtension.isGalois {L : Type*} [Field L] [Algebra F L]
    {E : IntermediateField F L} (h : IsElementaryAbelianThreeExtension F E) : IsGalois F ↥E :=
  h.1

theorem IsElementaryAbelianThreeExtension.pow_three_eq_one {L : Type*} [Field L] [Algebra F L]
    {E : IntermediateField F L} (h : IsElementaryAbelianThreeExtension F E)
    (σ : Gal(↥E/F)) : σ ^ 3 = 1 :=
  h.2 σ

variable (F)

/-- The **maximal elementary abelian unramified `3`-extension** of `F`: the compositum of all
finite everywhere-unramified elementary abelian `3`-extensions of `F`. -/
noncomputable def maxElemAbUnram3 : IntermediateField F (AlgebraicClosure F) :=
  sSup {E : IntermediateField F (AlgebraicClosure F) |
    FiniteDimensional F E ∧ IsUnramifiedExtension F E ∧ IsElementaryAbelianThreeExtension F E}

variable {F}

/-- Every finite unramified elementary abelian `3`-extension of `F` is contained in
`maxElemAbUnram3 F`. -/
theorem le_maxElemAbUnram3 {E : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F E]
    (h : IsUnramifiedExtension F E) (h2 : IsElementaryAbelianThreeExtension F E) :
    E ≤ maxElemAbUnram3 F :=
  le_sSup ⟨inferInstance, h, h2⟩

/-- `maxElemAbUnram3 F` is itself contained in any extension of `F` that contains every finite
unramified elementary abelian `3`-extension of `F`. -/
theorem maxElemAbUnram3_le {M : IntermediateField F (AlgebraicClosure F)}
    (h : ∀ (E : IntermediateField F (AlgebraicClosure F)), FiniteDimensional F E →
      IsUnramifiedExtension F E → IsElementaryAbelianThreeExtension F E → E ≤ M) :
    maxElemAbUnram3 F ≤ M :=
  sSup_le fun _ hE ↦ h _ hE.1 hE.2.1 hE.2.2

end Tower
end Work
