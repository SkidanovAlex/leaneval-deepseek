import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.ProTwoDefs

/-!
# `Work.ClassFieldTower.ResiduallyFiniteGaloisGroup` -- `G_∅` is residually a finite `2`-group

`ResiduallyFiniteTwoGroup G` (`ProTwoDefs.lean`) is one of the hypotheses of the sound
Golod--Shafarevich interface of this chapter: every nontrivial element of `G` must survive in a
finite `2`-group quotient.  It is needed

* to turn `Finite G` into `IsPGroup 2 G` (so that the finite `p`-group Golod--Shafarevich
  inequality applies), and
* to turn `Infinite G` into finite `2`-quotients of arbitrarily large order (the levels of the
  tower).

**This module proves that for the genuine object `G_∅ = Gal(F_∅/F)` the hypothesis is
automatic** (`residuallyFiniteTwoGroup_galoisGroup`): `F_∅` is the union of its finite
dimensional Galois subextensions, and each of those has pro-`2` Galois group by the `proP`
clause of `MaximalUnramifiedProP`.  Explicitly, for `σ ≠ 1` pick `x` with `σ x ≠ x`, let `L` be
the normal closure of `F⟮x⟯` inside `F_∅`; then `L/F` is finite dimensional and Galois, so
`Gal(L/F)` is a finite `2`-group, and the restriction map `G_∅ →* Gal(L/F)` is surjective
(`AlgEquiv.restrictNormalHom_surjective`) and does not kill `σ`.

## Main results

* `residuallyFiniteTwoGroup_galoisGroup` -- `ResiduallyFiniteTwoGroup G_∅`;
* `exists_quotient_equiv_finite_galois_subfield` -- the general form: the restriction to any
  finite dimensional Galois subextension of `F_∅` exhibits a finite `2`-group quotient of `G_∅`
  isomorphic to its Galois group.  (This is the *provable* half of `DescribesMaximalProTwo` for
  the genuine group; the other half -- that these are all the finite `2`-groups arising -- is
  the content of `DescribesMaximalProTwo`, see `ProTwoGenus.lean`.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

variable {F : Type} [Field F] [NumberField F]

/-- **The restriction to a finite dimensional Galois subextension is a finite `2`-quotient of
`G_∅`.**  For `L : IntermediateField F M.K` finite dimensional and Galois over `F`, the kernel of
`AlgEquiv.restrictNormalHom` is a normal subgroup of `G_∅` with finite `2`-group quotient,
isomorphic to `Gal(L/F)`. -/
theorem exists_quotient_equiv_finite_galois_subfield (M : MaximalUnramifiedProP.{0} F 2)
    (L : IntermediateField F M.K) [NumberField ↥L] (hfd : FiniteDimensional F L)
    (hgal : IsGalois F L) :
    ∃ (N : Subgroup (galoisGroup M)) (_ : N.Normal), Finite (galoisGroup M ⧸ N) ∧
      IsPGroup 2 (galoisGroup M ⧸ N) ∧ Nonempty ((galoisGroup M ⧸ N) ≃* (↥L ≃ₐ[F] ↥L)) := by
  classical
  haveI : FiniteDimensional F L := hfd
  haveI : IsGalois F L := hgal
  haveI : Normal F ↥L := inferInstance
  let φ : galoisGroup M →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := M.K) ↥L
  have hsurj : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective M.K
  refine ⟨φ.ker, MonoidHom.normal_ker φ, ?_, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective φ hsurj⟩⟩
  · haveI : Finite (↥L ≃ₐ[F] ↥L) := Finite.of_fintype _
    exact Finite.of_equiv (↥φ.range) (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  · have hpgL : IsPGroup 2 (↥L ≃ₐ[F] ↥L) := M.proP L hfd hgal
    exact (hpgL.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective).of_equiv
      (QuotientGroup.quotientKerEquivRange φ).symm

/-- **`G_∅ = Gal(F_∅/F)` is residually a finite `2`-group.**  For `σ ≠ 1` in `G_∅` choose `x`
with `σ x ≠ x`; the normal closure of `F⟮x⟯` inside `F_∅` is a finite dimensional Galois
subextension, and `σ` acts nontrivially on it, so restriction to that subextension is a finite
`2`-group quotient separating `σ` from `1`. -/
theorem residuallyFiniteTwoGroup_galoisGroup (M : MaximalUnramifiedProP.{0} F 2) :
    ResiduallyFiniteTwoGroup (galoisGroup M) := by
  classical
  intro σ hσ
  have hne : ∃ x : M.K, σ x ≠ x := by
    by_contra h
    exact hσ (AlgEquiv.ext (fun x => by by_contra hx; exact h ⟨x, hx⟩))
  obtain ⟨x, hx⟩ := hne
  -- the field `F⟮x⟯` is finite dimensional over `F`, since `F_∅/F` is algebraic
  let E : IntermediateField F M.K := IntermediateField.adjoin F ({x} : Set M.K)
  haveI hfdE : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z))
  -- the normal closure of `F⟮x⟯` inside `F_∅` is finite dimensional and Galois over `F`
  let L : IntermediateField F M.K := IntermediateField.normalClosure F E M.K
  haveI hfdL : FiniteDimensional F L := normalClosure.is_finiteDimensional F E M.K
  haveI hgalL : IsGalois F L := IsGalois.normalClosure F E M.K
  haveI hnormL : Normal F L := inferInstance
  let φ : galoisGroup M →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := M.K) ↥L
  -- `σ` does not act trivially on `L`
  have hφσ : φ σ ≠ 1 := by
    intro h
    have hxmem : x ∈ L :=
      (IntermediateField.subset_adjoin F ({x} : Set M.K)).trans
        (IntermediateField.le_normalClosure E) (by simp)
    have h1 : (φ σ) ⟨x, hxmem⟩ = (1 : ↥L ≃ₐ[F] ↥L) ⟨x, hxmem⟩ := by rw [h]
    have h2 : (↑((φ σ) ⟨x, hxmem⟩) : M.K) = (↑(⟨x, hxmem⟩ : ↥L) : M.K) := by rw [h1]; rfl
    rw [AlgEquiv.restrictNormalHom_apply L σ ⟨x, hxmem⟩] at h2
    exact hx h2
  have hpgL : IsPGroup 2 (↥L ≃ₐ[F] ↥L) := M.proP L hfdL hgalL
  let N : Subgroup (galoisGroup M) := φ.ker
  have hN : N.Normal := MonoidHom.normal_ker φ
  haveI : N.Normal := hN
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · haveI : Finite (↥L ≃ₐ[F] ↥L) := Finite.of_fintype _
    exact Finite.of_equiv (↥φ.range) (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  · have hpgrange : IsPGroup 2 ↥(φ.range) :=
      hpgL.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
    exact hpgrange.of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  · intro h
    have hmem : σ ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) σ).mp (by simpa [QuotientGroup.mk'_apply] using h)
    exact hφσ hmem

end Work.ClassFieldTower
