import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.homCoindDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the identification `Hom_Rep(M, Kˣ) ≅ (Hom_ℤ(M.V, Ωˣ))^Γ`

Given a morphism `u : M ⟶ N` of `Rep Coeff (K ≃ₐ[k] K)`'s, the two `AddEquiv`'s `ΦM`, `ΦN`
identifying `Hom_Rep(-, Kˣ)` with the `Γ`-invariants of `homCoind` (`Γ = Gal(Ω/k)`) satisfy the
expected naturality square: if `g` acts on invariants by `(g ψ) x = ψ (u x)` and the value of `ΦM f`
(and `ΦN f`) is given by the image of the unit `f x` under `Kˣ → Ωˣ`, then `ΦM (u ≫ f) = g (ΦN f)`.

The proof is a pointwise computation on the underlying `AddMonoidHom`'s, using the composition law
of `Rep` and the three "value" formulas `hM`, `hN`, `hg`.

## Note on the identifier `Additive.ToMul`

The requested statement spells the multiplicative inverse of the tag `Additive` as
`Additive.ToMul`.  Mathlib only provides the lower-case `Additive.toMul` (the `Equiv`
`Additive α ≃ α`), so that identifier is not in scope.  To keep the statement *literally* as
requested we register `Additive.ToMul` here as a transparent alias of `Additive.toMul`; being an
`abbrev`, it is definitionally equal to `Additive.toMul`, so the statement means exactly what the
notation intends.
-/

namespace Additive

/-- Alias of `Additive.toMul`, so that the requested statement (which writes `Additive.ToMul`)
elaborates.  Definitionally equal to `Additive.toMul`. -/
abbrev ToMul {α : Type*} : Additive α → α := toMul

end Additive

namespace Work.SSGRoute

open SSGRoute.PTExt

theorem homRep_unitsK_formula_natural {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {M N : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (u : M ⟶ N) (ΦM : (M ⟶ SSGRoute.PTExt.unitsK k K) ≃+ ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K M))) (ΦN : (N ⟶ SSGRoute.PTExt.unitsK k K) ≃+ ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N))) (hM : ∀ (f : M ⟶ SSGRoute.PTExt.unitsK k K) (x : M.V), (ΦM f : Work.SSGRoute.homCoind k Ω K M) x = Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom (Additive.toMul (Rep.Hom.hom f x)))) (hN : ∀ (f : N ⟶ SSGRoute.PTExt.unitsK k K) (x : N.V), (ΦN f : Work.SSGRoute.homCoind k Ω K N) x = Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom (Additive.ToMul (Rep.Hom.hom f x)))) (g : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N)) →+ ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K M))) (hg : ∀ (ψ : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N))) (x : M.V), Subtype.val (g ψ) x = Subtype.val ψ (Rep.Hom.hom u x)) : ∀ f : N ⟶ SSGRoute.PTExt.unitsK k K, ΦM (CategoryTheory.CategoryStruct.comp u f) = g (ΦN f) := by
  intro f
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  rw [hM (CategoryTheory.CategoryStruct.comp u f) x, hg (ΦN f) x, hN f (Rep.Hom.hom u x),
    Rep.comp_apply u f x]

end Work.SSGRoute
