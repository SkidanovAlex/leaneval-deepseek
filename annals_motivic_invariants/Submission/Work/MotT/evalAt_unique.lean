import Mathlib
import Submission.Work.MotT.TwistPointKDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- An element of a local ring killed by a ring homomorphism into a field is not a unit, hence
lies in the maximal ideal. -/
lemma ker_le_maximalIdeal_of_field {R : Type*} [CommSemiring R] [IsLocalRing R]
    {L : Type*} [Field L] (f : R →+* L) :
    RingHom.ker f ≤ IsLocalRing.maximalIdeal R := by
  intro x hx
  by_contra hxm
  have hunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hxm
  rw [RingHom.mem_ker] at hx
  exact (hunit.map f).ne_zero hx

/-- **The key claim.**  An `L`-algebra homomorphism `g : Coord E →ₐ[L] L` whose kernel is
contained in the maximal ideal `⟨x - a, y - b⟩` is the evaluation at `(a, b)`. -/
lemma eq_plugHomAt_of_ker_le {L : Type} [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (a b : L) [hns : Work.MotC2.IsNonsingularPoint E a b] (g : Work.MotC2.Coord E →ₐ[L] L)
    (hg : RingHom.ker g.toRingHom ≤ Work.MotC2.affPlaceIdeal E a b) :
    g = plugHomAt E a b hns.nonsingular := by
  have hX : g (Work.MotC2.coordX E) = a := by
    have hm : Work.MotC2.coordX E - algebraMap L (Work.MotC2.Coord E) (g (Work.MotC2.coordX E)) ∈
        RingHom.ker g.toRingHom := by
      rw [RingHom.mem_ker]
      show g (Work.MotC2.coordX E -
        algebraMap L (Work.MotC2.Coord E) (g (Work.MotC2.coordX E))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have hI := hg hm
    rw [← ker_plugHomAt E a b hns.nonsingular] at hI
    have h0 : plugHomAt E a b hns.nonsingular (Work.MotC2.coordX E -
        algebraMap L (Work.MotC2.Coord E) (g (Work.MotC2.coordX E))) = 0 :=
      RingHom.mem_ker.mp hI
    rw [map_sub, plugHomAt_coordX, plugHomAt_algebraMap, sub_eq_zero] at h0
    exact h0.symm
  have hY : g (Work.MotC2.coordY E) = b := by
    have hm : Work.MotC2.coordY E - algebraMap L (Work.MotC2.Coord E) (g (Work.MotC2.coordY E)) ∈
        RingHom.ker g.toRingHom := by
      rw [RingHom.mem_ker]
      show g (Work.MotC2.coordY E -
        algebraMap L (Work.MotC2.Coord E) (g (Work.MotC2.coordY E))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have hI := hg hm
    rw [← ker_plugHomAt E a b hns.nonsingular] at hI
    have h0 : plugHomAt E a b hns.nonsingular (Work.MotC2.coordY E -
        algebraMap L (Work.MotC2.Coord E) (g (Work.MotC2.coordY E))) = 0 :=
      RingHom.mem_ker.mp hI
    rw [map_sub, plugHomAt_coordY, plugHomAt_algebraMap, sub_eq_zero] at h0
    exact h0.symm
  refine AlgHom.ext fun r => ?_
  have hr : r ∈ Algebra.adjoin L
      ({Work.MotC2.coordX E, Work.MotC2.coordY E} : Set (Work.MotC2.Coord E)) := by
    rw [Work.MotC2.adjoin_coordX_coordY E]
    trivial
  refine Algebra.adjoin_induction
    (p := fun r _ => g r = plugHomAt E a b hns.nonsingular r) ?_ ?_ ?_ ?_ hr
  · rintro x (rfl | rfl)
    · simp only [hX, plugHomAt_coordX]
    · simp only [hY, plugHomAt_coordY]
  · intro c
    rw [plugHomAt_algebraMap]
    exact g.commutes c
  · intro x y hx' hy' ihx ihy
    rw [map_add, map_add, ihx, ihy]
  · intro x y hx' hy' ihx ihy
    rw [map_mul, map_mul, ihx, ihy]

/-- **Uniqueness of the residue map at a nonsingular affine point.**

Any two `L`-algebra homomorphisms `↥(affPlaceAt E a b) →ₐ[L] L` from the local ring of a
nonsingular affine point of an elliptic curve to `L` agree.

Route (worked out by the requester; `S := affPlaceAt E a b`, `I := affPlaceIdeal E a b =
⟨x-a, y-b⟩`, `𝔪 := IsLocalRing.maximalIdeal ↥S`):
`↥S` is the localization of `Coord E` at the maximal ideal `I`
(`Work.MotC2.instIsLocalizationAffPlaceAt`), so by `IsLocalization.ringHom_ext` it suffices to
show that the two composites with `algebraMap (Coord E) ↥S` are equal.

Key claim: any `L`-algebra map `g : Coord E →ₐ[L] L` with `Ideal.ker g ≤ I` equals
`Work.MotT.plugHomAt E a b (h.nonsingular)`. Indeed, `Ideal.ker (Work.MotT.plugHomAt E a b _) = I`
(`Work.MotT.ker_plugHomAt`); then
`Work.MotC2.coordX E - algebraMap L (Coord E) (g (coordX E)) ∈ Ideal.ker g ≤ I =
Ideal.ker (plugHomAt ..)` gives `g (coordX E) = a` (use
`Work.MotC2.XClass_eq_coordX_sub`, `Work.MotT.plugHomAt_coordX`,
`Work.MotT.plugHomAt_algebraMap`), likewise `g (coordY E) = b` (via
`Work.MotC2.YClass_eq_coordY_sub`), and two `L`-algebra maps agreeing on `coordX, coordY` agree
everywhere by `Work.MotC2.adjoin_coordX_coordY`.

For a ring hom `φ : ↥S →+* L`: `Ideal.ker φ ⊆ 𝔪` (an element of `↥S` killed by a map into a field
is not a unit, and the non-units of a local ring are `𝔪`), hence
`Ideal.ker (φ.toRingHom.comp (algebraMap (Coord E) ↥S)) ≤ Ideal.under (Coord E) 𝔪 = I` by
`IsLocalization.AtPrime.under_maximalIdeal`. Applying the key claim to both composites and using
`IsLocalization.ringHom_ext` finishes. -/
theorem evalAt_unique {L : Type} [Field L] (E : WeierstrassCurve L) [E.IsElliptic] (a b : L)
    [Work.MotC2.IsNonsingularPoint E a b]
    (φ ψ : ↥(Work.MotC2.affPlaceAt E a b) →ₐ[L] L) : φ = ψ := by
  apply evalAtLoc_ext E a b
  intro r
  have key : ∀ (f : ↥(Work.MotC2.affPlaceAt E a b) →ₐ[L] L),
      f (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) r) =
        plugHomAt E a b
          (inferInstance : Work.MotC2.IsNonsingularPoint E a b).nonsingular r := by
    intro f
    let g : Work.MotC2.Coord E →ₐ[L] L := f.comp (Work.MotC2.affPlaceAtAlgHom E a b)
    have hgle : RingHom.ker g.toRingHom ≤ Work.MotC2.affPlaceIdeal E a b := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hzero : f (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) x) = 0 := hx
      have hmem : algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) x ∈
          IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E a b) := by
        by_contra hcon
        have hunit : IsUnit
            (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) x) :=
          IsLocalRing.notMem_maximalIdeal.mp hcon
        exact (hunit.map f.toRingHom).ne_zero hzero
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Work.MotC2.affPlaceIdeal E a b) x).mp
        hmem
    have hgeq : g = plugHomAt E a b
        (inferInstance : Work.MotC2.IsNonsingularPoint E a b).nonsingular :=
      eq_plugHomAt_of_ker_le E a b g hgle
    have h1 : g r = plugHomAt E a b
        (inferInstance : Work.MotC2.IsNonsingularPoint E a b).nonsingular r :=
      DFunLike.congr_fun hgeq r
    rw [← h1]
    exact (AlgHom.comp_apply f (Work.MotC2.affPlaceAtAlgHom E a b) r).symm
  exact (key φ).trans (key ψ).symm

end Work.MotT
