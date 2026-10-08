import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.fittingPiIn_subgroupOf

namespace Work.DSTR

/-- `F_π` of a subgroup is transported by conjugation.

The relative Fitting subgroup is `fittingPiIn π K = (fittingPi π ↥K).map K.subtype`, so the
left-hand side is `(F_π(↥K)).map (ψ ∘ K.subtype)` where `ψ = MulAut.conj y`.  The conjugation
`ψ` restricts to a group isomorphism `e : ↥K ≃* ↥(K.map ψ)` (`Subgroup.equivMapOfInjective`
applied to the injective map `ψ`), and on `↥K` the two maps `ψ ∘ K.subtype` and
`(K.map ψ).subtype ∘ e` agree as functions.  The transport of `F_π` along the isomorphism `e` is
`fittingPi_map_mulEquiv` (from `Submission.Work.DSTR.fittingPiIn_subgroupOf`). -/
theorem fittingPiIn_map_conj {G : Type*} [Group G] [Finite G]
    (π : Set ℕ) (K : Subgroup G) (y : G) :
    (Work.GW2.fittingPiIn π K).map (MulAut.conj y).toMonoidHom
      = Work.GW2.fittingPiIn π (K.map (MulAut.conj y).toMonoidHom) := by
  have hinj : Function.Injective ((MulAut.conj y).toMonoidHom : G →* G) :=
    fun a b h => (MulAut.conj y).injective h
  let e : ↥K ≃* ↥(K.map (MulAut.conj y).toMonoidHom) :=
    Subgroup.equivMapOfInjective K ((MulAut.conj y).toMonoidHom) hinj
  -- On `↥K`, conjugating by `y` agrees with the isomorphism `e` followed by the inclusion.
  have hone : ∀ k : ↥K,
      ((MulAut.conj y).toMonoidHom) (k : G)
        = ((e k : ↥(K.map (MulAut.conj y).toMonoidHom)) : G) := by
    intro k
    rw [Subgroup.coe_equivMapOfInjective_apply]
  have hcomp : ((MulAut.conj y).toMonoidHom).comp K.subtype
      = (K.map (MulAut.conj y).toMonoidHom).subtype.comp
          (e : ↥K →* ↥(K.map (MulAut.conj y).toMonoidHom)) := by
    ext k
    exact hone k
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPiIn, Subgroup.map_map, hcomp]
  rw [← Subgroup.map_map, fittingPi_map_mulEquiv]

end Work.DSTR
