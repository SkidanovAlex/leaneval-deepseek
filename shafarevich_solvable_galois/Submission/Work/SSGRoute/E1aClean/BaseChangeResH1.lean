import Submission.Work.SSGRoute.E1aClean.BaseChangeE1c
import Submission.Work.SSGRoute.PT.akH2Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Piece (1) of the square: the `H¹`-side restriction to the fixing subgroup

`PT.H2Fin.resH1` is the restriction of the `AbsoluteKummer` `H¹` to an arbitrary subgroup (the
`H2Fin` in the name is the *file*, not the degree — see `NOTE_levelChangeRoute.md` §2g).  Here it is
instantiated at the level-change data: `Γ := Ω ≃ₐ[k] Ω`, `N := (LOmega L).fixingSubgroup`,
`P := homCoind k Ω K R`. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **Piece (1) of the level-change square**: the restriction of the `H¹`-side of the global `E1c`
dictionary to the fixing subgroup of `LOmega L` in `Gal(Ω/k)`. -/
noncomputable def resH1_fixing (L : IntermediateField k K)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) →+
      Work.AbsoluteKummer.H1 ↥((LOmega L).fixingSubgroup)
        (Work.SSGRoute.homCoind k Ω K R) :=
  Work.SSGRoute.PT.H2Fin.resH1 (LOmega L).fixingSubgroup (Work.SSGRoute.homCoind k Ω K R)

/-- The computation rule: on the class of a locally constant `1`-cocycle it is the class of the
restricted cocycle. -/
theorem resH1_fixing_H1π (L : IntermediateField k K)
    (f : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Unit)))) :
    resH1_fixing L (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Unit))
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) _ f)
      = Work.AbsoluteKummer.H1π ↥((LOmega L).fixingSubgroup) _
          (Work.SSGRoute.PT.H2Fin.resZ1 (LOmega L).fixingSubgroup _ f) :=
  Work.SSGRoute.PT.H2Fin.resH1_H1π (LOmega L).fixingSubgroup _ f

end

end Work.SSGRoute.E1aClean
