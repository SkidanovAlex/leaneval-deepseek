import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Aut.pglHomInjective

namespace Work.AUTL2.Aut

/-- The permutation representation of `PSL(2,F)` on `ℙ¹(F)` is injective: it is the composite
of the injective map `PSL(2,F) → PGL(2,F)` (`Matrix.ProjectiveSpecialLinearGroup.toPGL`) and
the injective action of `PGL(2,F)` on the projective line
(`Work.AUTL2.Aut.pglHomInjective`). -/
theorem pslHomInjective (F : Type*) [Field F] [DecidableEq F] :
    Function.Injective (Work.AUTL2.pslHom F) := by
  intro x y hxy
  have hxy' : Work.AUTL2.pglHom F (Matrix.ProjectiveSpecialLinearGroup.toPGL x) =
      Work.AUTL2.pglHom F (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := hxy
  exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (pglHomInjective F hxy')

/-- **The images of `PSL(2,q)` and `PGL(2,q)` on `ℙ¹(q)` are abstractly `PSL(2,q)` and
`PGL(2,q)`**: because both permutation representations are faithful, the range of each is
isomorphic to its domain via the range-restriction isomorphism.

This is the identification used when the explicit permutation model `pslImage ⊆ pglImage ⊆
Sym(ℙ¹(q))` is compared with the abstract groups `PSL(2,q)` and `PGL(2,q)` appearing in the
statement of `Work.GW2.AutL2Prop`. -/
theorem images (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    Nonempty (↥(Work.AUTL2.pslImage (GaloisField p k)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧
      Nonempty (↥(Work.AUTL2.pglImage (GaloisField p k)) ≃*
        Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) := by
  have hpsl : Function.Injective (Work.AUTL2.pslHom (GaloisField p k)) :=
    pslHomInjective _
  have hpgl : Function.Injective (Work.AUTL2.pglHom (GaloisField p k)) :=
    pglHomInjective _
  exact ⟨⟨(MonoidHom.ofInjective hpsl).symm⟩, ⟨(MonoidHom.ofInjective hpgl).symm⟩⟩

end Work.AUTL2.Aut
