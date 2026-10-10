import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.e1a_can_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: naturality of the canonical identification `Hom_ℤ(M,Kˣ) ≅ H⁰(Γ, Hom_ℤ(M,Ωˣ))`

`Work.SSGRoute.homRep_unitsK_formula` realises the identification
`Hom_Rep(M,Kˣ) ≅ H⁰(Γ, Hom_ℤ(M,Ωˣ))` (invariants of the conjugation action) as an
`∃`-statement, but its proof is the *canonical* map `Work.SSGRoute.toCoindH0 M`, which is a `def`.
This file records its naturality in `M`, in the form needed by the naturalisation of the `E1c`
dictionary: for `u : M ⟶ N` and `f : N ⟶ unitsK k K`,

`toCoindH0 M (u ≫ f) = mapH0 (precompAddHom u) (toCoindH0 N f)`.

It is the instantiation of `Work.SSGRoute.homRep_unitsK_formula_natural` at the canonical data.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-- **Naturality of `toCoindH0`** under a morphism `u : M ⟶ N` of `Gal(K/k)`-modules. -/
theorem toCoindH0_natural (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M N : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (u : M ⟶ N)
    (h : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom u).toAddMonoidHom))
    (f : N ⟶ SSGRoute.PTExt.unitsK k K) :
    Work.SSGRoute.toCoindH0 M (CategoryTheory.CategoryStruct.comp u f) =
      Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom u).toAddMonoidHom) h
        (Work.SSGRoute.toCoindH0 N f) := by
  have hnat := Work.SSGRoute.homRep_unitsK_formula_natural (k := k) (Ω := Ω) (K := K) u
    (AddEquiv.ofBijective (Work.SSGRoute.toCoindH0 M) (Work.SSGRoute.toCoindH0_bijective M))
    (AddEquiv.ofBijective (Work.SSGRoute.toCoindH0 N) (Work.SSGRoute.toCoindH0_bijective N))
    (fun f x => Work.SSGRoute.toCoindH0_apply M f x)
    (fun f x => Work.SSGRoute.toCoindH0_apply N f x)
    (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom u).toAddMonoidHom) h)
    (fun ψ x => rfl) f
  simpa using hnat

end

end Work.SSGRoute.PT
