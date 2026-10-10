import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.PT.br_pTorsion_openSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(D, Hom_ℤ(M, Ωˣ)) = 0` for a closed subgroup `D` fixing `K`

For a finite free `ℤ`-module `M = R.V` (the carrier of a `Rep Coeff Gal(K/k)`) and a *closed*
subgroup `D ≤ Gal(Ω/k)` which acts trivially on `K` — i.e. `D ≤ ker (res k K) = Gal(Ω/K)` — the
`D`-module `homCoind k Ω K R = Hom_ℤ(R.V, Ωˣ)` has vanishing `H¹`.

The point is that `D` acts on `R.V` trivially (it is in the kernel of `res k K`, hence acts
trivially on `K`, so `D` acts through the trivial action on `R.V`), so `Hom_ℤ(R.V, Ωˣ)` is, as a
`D`-module, a finite product of copies of `Ωˣ` (one per element of a `ℤ`-basis of `R.V`), and each
copy has `H¹(D, Ωˣ) = 0` by Hilbert 90 for closed subgroups of an absolute Galois group
(`Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup`).

Concretely, the instance of `DistribMulAction ↥D (R.V →+ Additive Ωˣ)` selected by type class
resolution for the statement is the restriction to `↥D` of the conjugation action
`(σ · φ) x = σ • φ (R.ρ ((res k K) σ)⁻¹ x)`.  Since `D ≤ ker (res k K)`, this restriction agrees
with the pointwise action `(δ • φ) x = δ • φ x`; under it the coordinate isomorphism (evaluation
on a `ℤ`-basis) is an isomorphism of `↥D`-modules, and the target is a finite product of copies of
`Ωˣ`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-! ## The coordinate isomorphism of `Hom_ℤ(R.V, Ωˣ)` -/

/-- **Coordinates in a `ℤ`-basis**: `Hom_ℤ(R.V, Ωˣ) → (ι → Ωˣ)`, `φ ↦ (φ (b i))_i`. -/
def homCoindCoordAddEquiv (R : Rep.{0} Coeff (K ≃ₐ[k] K)) {ι : Type}
    (b : Module.Basis ι ℤ R.V) : (R.V →+ Additive Ωˣ) ≃+ (ι → Additive Ωˣ) where
  toFun φ := fun i => φ (b i)
  invFun g := (b.constr ℤ g).toAddMonoidHom
  left_inv φ := by
    have h : b.constr ℤ (fun i => φ (b i)) = φ.toIntLinearMap :=
      Module.Basis.constr_self (R := ℤ) b (S := ℤ) φ.toIntLinearMap
    show (b.constr ℤ fun i => φ (b i)).toAddMonoidHom = φ
    rw [h]
    rfl
  right_inv g := by
    funext i
    exact Module.Basis.constr_basis b ℤ g i
  map_add' φ ψ := by
    funext i
    rfl

/-! ## The vanishing -/

theorem subsingletonH1_homCoind_of_le_ker
    {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    [Module.Free ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hDcl : IsClosed ((D : Set (Ω ≃ₐ[k] Ω))))
    (hD : D ≤ (SSGRoute.res k K).ker) :
    Subsingleton (Work.AbsoluteKummer.H1 ↥D (Work.SSGRoute.homCoind k Ω K R)) := by
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- a `ℤ`-basis of the (finite, free) carrier `R.V`, and a `Fintype` index for it
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ R.V) ℤ R.V :=
    Module.Free.chooseBasis ℤ R.V
  haveI hfinι : Finite (Module.Free.ChooseBasisIndex ℤ R.V) := Module.Finite.finite_basis b
  haveI : Fintype (Module.Free.ChooseBasisIndex ℤ R.V) := Fintype.ofFinite _
  -- Hilbert 90 at the closed subgroup `D`
  have hA : Subsingleton (Work.AbsoluteKummer.H1 ↥D (Additive Ωˣ)) :=
    Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup (k := k) (Ω := Ω) D hDcl
  -- `H¹` of a finite product of copies of `Ωˣ` vanishes
  have hPi : Subsingleton (Work.AbsoluteKummer.H1 ↥D
      (Module.Free.ChooseBasisIndex ℤ R.V → Additive Ωˣ)) :=
    subsingleton_H1_pi (X := fun _ : Module.Free.ChooseBasisIndex ℤ R.V => Additive Ωˣ)
      (fun _ => hA)
  -- the coordinate isomorphism is `↥D`-equivariant
  refine subsingleton_H1_of_addEquiv
    (homCoindCoordAddEquiv (k := k) (Ω := Ω) (K := K) R b) ?_ hPi
  intro δ φ
  funext i
  rw [Subgroup.smul_def]
  show ((δ : Ω ≃ₐ[k] Ω) • φ) (b i) = ((δ : Ω ≃ₐ[k] Ω) • fun j => φ (b j)) i
  rw [homCoind.smul_apply]
  have h1 : SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω) = 1 := MonoidHom.mem_ker.mp (hD δ.2)
  rw [h1, inv_one, map_one]
  rfl

end

end Work.SSGRoute.ExtChain
