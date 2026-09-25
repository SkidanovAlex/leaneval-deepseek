import ChallengeDeps
import Submission.CFTLib.Interfaces

/-!
# The Galois correspondence for `F^{un,p}/F`

`E = maximalUnramifiedProPF F p` is the maximal everywhere-unramified pro-`p` extension of the
number field `F` (inside a fixed algebraic closure), and `G = Gal(E/F)` is the trusted
`MaxUnramifiedProPGaloisGroup F p` of the problem statement (`ChallengeDeps.lean`).

Assuming `E/F` is Galois (`Work.CFTLib.ProP.isGalois_maximalUnramifiedProPF`), Mathlib's infinite
Galois theory (`InfiniteGalois`) gives the Galois correspondence between *open normal* subgroups of
`G` and finite Galois intermediate fields of `E/F`, together with the quotient identification
`G ⧸ U ≃* Gal(K/F)`.

## Main results

* `Work.CFTLib.ProP.fixedField_finiteDimensional`
* `Work.CFTLib.ProP.fixedField_isGalois`
* `Work.CFTLib.ProP.quotient_fixedField`
-/

open NumberField

namespace Work.CFTLib.ProP

noncomputable section

variable (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]

/-- The maximal everywhere-unramified pro-`p` extension `F^{un,p}` of `F`. -/
abbrev E : IntermediateField F (AlgebraicClosure F) :=
  LeanEval.NumberTheory.maximalUnramifiedProPF F p

/-- The Galois group `Gal(F^{un,p}/F)`; definitionally the problem statement's
`MaxUnramifiedProPGaloisGroup F p`. -/
abbrev GG : Type := Gal(↥(E F p)/F)

/-- `Gal(F^{un,p}/F)` really is the problem statement's group. -/
theorem GG_eq : GG F p = LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p := rfl

variable {F p}

theorem fixedField_finiteDimensional {U : Subgroup (GG F p)} (hgal : IsGalois F ↥(E F p))
    (hopen : IsOpen (U : Set (GG F p))) :
    FiniteDimensional F (IntermediateField.fixedField U) := by
  haveI := hgal
  have hcl : IsClosed (U : Set (GG F p)) := U.isClosed_of_isOpen hopen
  have hfix : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hcl⟩
  refine (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField U)).mp ?_
  rw [hfix]
  exact hopen

theorem fixedField_isGalois {U : Subgroup (GG F p)} (hgal : IsGalois F ↥(E F p))
    (hU : U.Normal) (hopen : IsOpen (U : Set (GG F p))) :
    IsGalois F (IntermediateField.fixedField U) := by
  haveI := hgal
  have hcl : IsClosed (U : Set (GG F p)) := U.isClosed_of_isOpen hopen
  have hfix : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hcl⟩
  refine (InfiniteGalois.normal_iff_isGalois (IntermediateField.fixedField U)).mp ?_
  rw [hfix]
  exact hU

theorem quotient_fixedField {U : Subgroup (GG F p)} (hgal : IsGalois F ↥(E F p))
    (hU : U.Normal) (hopen : IsOpen (U : Set (GG F p))) :
    Nonempty (GG F p ⧸ U ≃* Gal(↥(IntermediateField.fixedField U)/F)) := by
  haveI := hgal
  have hcl : IsClosed (U : Set (GG F p)) := U.isClosed_of_isOpen hopen
  let Uc : ClosedSubgroup (GG F p) := ⟨U, hcl⟩
  haveI : Uc.Normal := hU
  exact ⟨InfiniteGalois.normalAutEquivQuotient Uc⟩

end

end Work.CFTLib.ProP
