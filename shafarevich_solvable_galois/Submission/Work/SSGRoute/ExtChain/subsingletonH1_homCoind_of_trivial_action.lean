import Mathlib
import Submission.Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker
import Submission.Work.SSGRoute.homCoind_H1_free
import Submission.Work.SSGRoute.PT.br_pTorsion_openSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(D, Hom_ℤ(M, Ωˣ)) = 0` for a closed subgroup `D` acting trivially on `M`

`Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker` proves the vanishing of
`H¹(D, Hom_ℤ(R.V, Ωˣ))` for a closed subgroup `D` of `Gal(Ω/k)` contained in
`ker (res k K) = Gal(Ω/K)`.  Reading its proof shows that the containment is used *only* through
the consequence that `D` acts trivially on the carrier `R.V` (which is what makes the coordinate
isomorphism `Hom_ℤ(R.V,Ωˣ) ≅ (Ωˣ)^{dim}` equivariant for the *pointwise* action); the actual
vanishing input is Hilbert 90 for `Ω / Ω^D`, i.e. `H¹(D, Ωˣ) = 0` for *every* closed `D`, with no
hypothesis.

This file makes that explicit: the vanishing holds for every **closed** subgroup `D` whose action
on `R.V` is trivial — a strictly weaker hypothesis than `D ≤ ker (res k K)`.  The new cases it
covers are exactly the subgroups `D` that fix the *coefficient module* pointwise without fixing
`K`: e.g. an involution `σ` of `Gal(Ω/k)` with `res k K σ ≠ 1` that happens to act trivially on the
carrier `R.V` (for a `Rep` whose carrier carries a trivial `⟨σ⟩`-part).

The statement is used by `Work.SSGRoute.ExtChain.himg_reduction''` (my file) to enlarge the family
of subgroups at which the `E1c` dictionary `e1cMap` is known to restrict to `0` unconditionally.
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

/-- **`H¹(D, Hom_ℤ(R.V, Ωˣ)) = 0` for every closed `D` acting trivially on `R.V`.**

The hypothesis `hact` says exactly that the conjugation action of `D` on `Hom_ℤ(R.V,Ωˣ)` is the
pointwise action on `Ωˣ`, so that evaluation in a `ℤ`-basis is an isomorphism of `↥D`-modules onto a
finite product of copies of `Ωˣ`; each copy has vanishing `H¹` by Hilbert 90 for the closed subgroup
`D` of the absolute Galois group (`Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup`). -/
theorem subsingletonH1_homCoind_of_trivial_action
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    [Module.Free ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hDcl : IsClosed ((D : Set (Ω ≃ₐ[k] Ω))))
    (hact : ∀ δ : ↥D, R.ρ (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) = 1) :
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
  have hcomp : R.ρ ((SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω))⁻¹)
      * R.ρ (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [hact δ, mul_one] at hcomp
  rw [hcomp]
  rfl

end

end Work.SSGRoute.ExtChain
