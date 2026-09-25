/-
# Vanishing of the units localisation at an archimedean place

Let `F ⊆ L` be a finite Galois extension of number fields with `F` **totally complex**
(`hF : ∀ v : InfinitePlace F, v.IsComplex`).  Then `L` is totally complex as well: a real place
of `L` would restrict to a real place of `F`, since the completion of `F` at a real place embeds
into the completion of `L`.

For an archimedean place `w` of `L` we consider the localisation
`locUnits F L w : H²(Gal(L/F), Lˣ) ⟶ H²(Γ_w, L_wˣ)`, `Γ_w = stabilizer (L ≃ₐ[F] L) w` the
decomposition group of `w` (see `Work/HassePrinciple/LocalUnits.lean`).

The point of this file is that at a **complex** archimedean place the decomposition group is
*trivial*: `L_w = ℂ = F_v` where `v` is the place of `F` below `w` (a complex place, by `hF`),
and the local Galois group `Gal(ℂ/ℂ)` is trivial, so `Γ_w = 1`.  Equivalently — this is the
formal route taken below — Mathlib's `InfinitePlace.isUnramified_iff` gives
`IsUnramified F w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap F L))`, the second alternative
holds by `hF`, and `IsUnramified.stabilizer_eq_bot` then computes `Γ_w = ⊥`.

Consequently `H²(Γ_w, L_wˣ) = 0` (the cohomology of the trivial group in positive degrees
vanishes, `isZero_groupCohomology_succ_of_subsingleton`), and the localisation is the zero map.
This is the archimedean input of the localisation argument for `H²(Gal(L/F), Lˣ)`
(the relative Hasse–Brauer–Noether theorem only has to be checked at the nonarchimedean places).
-/

import Mathlib
import Submission.NK.HassePrinciple.LocalUnits

open NumberField NK.GlobalCFT
open scoped NumberField

namespace NK.NUV2.LC.RouteB

/-- **The decomposition group of a complex archimedean place is trivial.**

If every infinite place of `F` is complex, then for every archimedean place `w` of `L` the
stabiliser of `w` in `Gal(L/F)` is trivial: `w` is unramified over `F`
(`InfinitePlace.isUnramified_iff`), because the place of `F` below `w` is complex. -/
theorem stabilizer_ofInfinite_eq_bot {F L : Type} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hF : ∀ v : NumberField.InfinitePlace F, v.IsComplex)
    (w : NumberField.InfinitePlace L) :
    MulAction.stabilizer (L ≃ₐ[F] L) (NK.GlobalCFT.Place.ofInfinite w) = ⊥ := by
  -- the place of `F` below `w` is complex, so `w` is unramified over `F`
  have hstab : MulAction.stabilizer (L ≃ₐ[F] L) w = ⊥ := by
    refine NumberField.InfinitePlace.IsUnramified.stabilizer_eq_bot ?_
    rw [NumberField.InfinitePlace.isUnramified_iff]
    exact Or.inr (hF (w.comap (algebraMap F L)))
  -- transport along the equivariant injection `ofInfinite : InfinitePlace L → Place L`
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ
  have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[F] L) w := by
    rw [MulAction.mem_stabilizer_iff]
    exact NK.GlobalCFT.Place.ofInfinite_inj.mp (by simpa using hσ)
  rw [hstab] at hmem
  simpa using hmem

/-- **The target of the units localisation at a complex archimedean place is trivial**:
`H²(Γ_w, L_wˣ)` is a subsingleton, since `Γ_w = 1` and the group cohomology of the trivial group
vanishes in positive degrees. -/
theorem subsingleton_groupCohomology_localUnitsRep_ofInfinite {F L : Type} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hF : ∀ v : NumberField.InfinitePlace F, v.IsComplex)
    (w : NumberField.InfinitePlace L) :
    Subsingleton ↥(groupCohomology
      (NK.HassePrinciple.localUnitsRep F L (NK.GlobalCFT.Place.ofInfinite w)) 2) := by
  have hI : Subsingleton (MulAction.stabilizer (L ≃ₐ[F] L)
      (NK.GlobalCFT.Place.ofInfinite w)) := by
    rw [stabilizer_ofInfinite_eq_bot hF w]
    infer_instance
  exact (ModuleCat.isZero_iff_subsingleton).1
    (isZero_groupCohomology_succ_of_subsingleton
      (NK.HassePrinciple.localUnitsRep F L (NK.GlobalCFT.Place.ofInfinite w)) 1)

/-- **The units localisation vanishes at an archimedean place** of a totally complex extension:
for a totally complex base field `F`, the `w`-component of the localisation
`H²(Gal(L/F), Lˣ) → ∏_w H²(Γ_w, L_wˣ)` is zero at every infinite place `w` of `L`. -/
theorem locUnits_ofInfinite_eq_zero {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hF : ∀ v : NumberField.InfinitePlace F, v.IsComplex)
    (w : NumberField.InfinitePlace L)
    (a : groupCohomology (NK.HassePrinciple.unitsRep F L) 2) :
    (NK.HassePrinciple.locUnits F L (NK.GlobalCFT.Place.ofInfinite w)).hom a = 0 := by
  have hsub := subsingleton_groupCohomology_localUnitsRep_ofInfinite hF w
  exact Subsingleton.elim _ _

end NK.NUV2.LC.RouteB
