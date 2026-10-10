import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
import Submission.NK.HassePrinciple.LocalUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local step of `brauer_single_place` (E8', piece P4)

`NK.HassePrinciple.locUnits M E ŵ` is the localisation of a class of
`Br(E/M) = H²(Gal(E/M), Eˣ)` at the decomposition group `Γ = Stab_{Gal(E/M)}(ŵ)` of the place
`ŵ` of `E`, landing in `H²(Γ, E_ŵˣ)`.

If `ŵ` is an *infinite* place of `E` and the place of `M` below it is **complex**, then the local
extension `E_ŵ/M_W` is trivial (`[E_ŵ : M_W] = 1`, since `ℂ` has no proper finite extension), so the
decomposition group is trivial, `Nat.card Γ = 1`, and the order `1` annihilates `H²(Γ, E_ŵˣ)`.

This is the archimedean analogue of `Work.SSGRoute.eb_crux`: at a finite place the vanishing of the
localisation is a genuine arithmetic fact (divisibility of local degrees, unramified extensions
split classes of order dividing the degree), while at a complex archimedean place it is the trivial
vanishing of `H²` of a trivial group.

Mathlib's `NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one` supplies the
cardinality statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.SSGRoute

/-- **The archimedean crux (E8', piece P4).**  Let `k ⊆ M ⊆ E` be number fields with `M/k`,
`E/k` and `E/M` Galois and let `ŵ` be an infinite place of `E` whose restriction to `M` is complex.
Then the localisation of *every* class of `H²(Gal(E/M), Eˣ)` at `ŵ` vanishes: the local extension
`E_ŵ/M_W` is trivial, the decomposition group `Stab_{Gal(E/M)}(ŵ)` is trivial
(`InfinitePlace.isUnramified_iff_card_stabilizer_eq_one`), and `H²` of the trivial group is killed
by `Nat.card Γ = 1` (`natCard_cast_smul_H2_eq_zero`). -/
theorem eb_arch_crux {k M E : Type} [Field k] [NumberField k] [Field M] [NumberField M] [Field E]
    [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]
    [FiniteDimensional k M] [FiniteDimensional M E] [FiniteDimensional k E]
    [IsGalois k M] [IsGalois M E]
    (ŵ : NumberField.InfinitePlace E)
    (h : (ŵ.comap (algebraMap M E)).IsComplex) :
    ∀ x : groupCohomology (NK.HassePrinciple.unitsRep M E) 2,
      (NK.HassePrinciple.locUnits M E (NK.GlobalCFT.Place.ofInfinite ŵ)).hom x = 0 := by
  -- the local extension is trivial, so the decomposition group is trivial
  have hcard' : Nat.card (MulAction.stabilizer (E ≃ₐ[M] E) ŵ) = 1 :=
    (NumberField.InfinitePlace.isUnramified_iff_card_stabilizer_eq_one (k := M) (K := E)).mp
      (NumberField.InfinitePlace.isUnramified_iff.mpr (Or.inr h))
  have hcard : Nat.card (MulAction.stabilizer (E ≃ₐ[M] E)
      (NK.GlobalCFT.Place.ofInfinite ŵ)) = 1 := by
    refine (Nat.card_congr (Equiv.subtypeEquivRight (fun δ => ?_))).trans hcard'
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
  haveI hfin : Fintype (MulAction.stabilizer (E ≃ₐ[M] E)
      (NK.GlobalCFT.Place.ofInfinite ŵ)) := Fintype.ofFinite _
  intro x
  have h1 := Commons.RepresentationTheory.GroupCohomology.natCard_cast_smul_H2_eq_zero
    (k := NK.HassePrinciple.CoeffInt)
    (G := MulAction.stabilizer (E ≃ₐ[M] E) (NK.GlobalCFT.Place.ofInfinite ŵ))
    (NK.HassePrinciple.localUnitsRep M E (NK.GlobalCFT.Place.ofInfinite ŵ))
    ((NK.HassePrinciple.locUnits M E (NK.GlobalCFT.Place.ofInfinite ŵ)).hom x)
  rw [hcard] at h1
  simpa using h1

end Work.SSGRoute
