/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sections over an affine open versus regularity at the places it contains

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let
`W ⊆ C` be a nonempty **affine** open subset.  The restriction map
`Γ(C, W) ⟶ K(C)` is injective, and this file determines its image: a rational function
`f` is a section over `W` if and only if its order of vanishing is nonnegative at every
place of `C` lying in `W`.

The proof of the non-trivial direction is a local-to-global argument for the domain
`A = Γ(C, W)` with fraction field `K = K(C)`.  For `f ∈ K` one considers the ideal
`I = {s : A | s·f ∈ A}` of "candidates for a denominator of `f`".  If `f ∉ A` then `I` is a
proper nonzero ideal, so it is contained in a maximal ideal `m`, and the point of the affine
scheme `W` corresponding to `m` is a point `x` at which the germ map `A → 𝒪_{C,x}` is the
localization at `m`.  If `x` is a place (a closed point), then the fact that `s·f ∈ A` for
some `s ∉ m` contradicts `I ≤ m`; if instead `x` is the generic point of `C`, then `m = ⊥`
and `I ≤ ⊥` again contradicts `I ≠ 0`.  Either way, the existence of a pole at a place of
`W` (equivalently `0 ≤ ord f` at all of them) forces `f ∈ Γ(C, W)`.

## Main results

* `Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff`: at a place `Q`, an element
  of `K(C)` is in the image of the local ring `𝒪_{C,Q} → K(C)` exactly when its order of
  vanishing at `Q` is nonnegative.
* `Work.CurveBasics.BaseChange.mem_range_germ_iff`: the image of `Γ(C, W) → K(C)` for
  `W` affine open is the set of rational functions regular at all places of `W`.
-/
import Mathlib
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.BaseChange.primeIdealOf_eq_bot_of_eq_genericPoint
import Submission.Work.CurveBasics.BaseChange.exists_notMem_mul_mem_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.BaseChange

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

open Work.CurveBasics in
/-- At a place `Q`, an element of the function field is in the image of the local ring at
`Q` if and only if its order of vanishing at `Q` is nonnegative.  Indeed the local ring is a
discrete valuation ring, and its image in the function field is the unit ball of the
associated valuation. -/
theorem mem_range_algebraMap_stalk_iff {k : Type*} [Field k] (C : Curve k) (Q : C.Place)
    (f : C.functionField) :
    f ∈ (algebraMap (C.left.presheaf.stalk Q.point) C.functionField).range ↔
      0 ≤ C.ordAt f Q := by
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := Q.instIsDiscreteValuationRing
  have key : (algebraMap (C.left.presheaf.stalk Q.point) C.functionField).range
      = Q.valuation.valuationSubring.toSubring := by
    rw [RingHom.range_eq_map, IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring]
    rfl
  rw [key, ← Place.mem_valuationSubring_iff]
  exact ValuationSubring.mem_toSubring _ f

open Work.CurveBasics in
theorem mem_range_germ_iff {k : Type*} [Field k] {C : Curve k} (W : C.left.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] (f : C.functionField) :
    f ∈ (C.germToFunctionField W).hom.range ↔ C.RegularOn W f := by
  haveI hFrac : IsFractionRing Γ(C.left, W) C.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen C.left W hW
  haveI hDom : IsDomain Γ(C.left, W) :=
    (IsFractionRing.injective Γ(C.left, W) C.functionField).isDomain
  constructor
  · rintro ⟨a, rfl⟩
    rintro Q hQ
    rw [show (ConcreteCategory.hom (C.germToFunctionField W)) a =
        (algebraMap (C.left.presheaf.stalk Q.point) C.functionField)
          ((C.left.presheaf.germ W Q.point hQ) a) from
      (Scheme.algebraMap_germ_eq_germToFunctionField C.left (U := W) hQ a).symm]
    exact (mem_range_algebraMap_stalk_iff C Q _).mp ⟨_, rfl⟩
  · intro hf
    by_contra hmem
    -- The ideal of sections `s` with `s * f` again a section: the "denominator ideal" of `f`.
    let I : Ideal Γ(C.left, W) :=
      { carrier := {s | ∃ c : Γ(C.left, W),
            algebraMap Γ(C.left, W) C.functionField c
              = algebraMap Γ(C.left, W) C.functionField s * f},
        zero_mem' := ⟨0, by simp⟩,
        add_mem' := by
          rintro a b ⟨a', ha'⟩ ⟨b', hb'⟩
          refine ⟨a' + b', ?_⟩
          rw [map_add, ha', hb', map_add, add_mul],
        smul_mem' := by
          rintro c a ⟨a', ha'⟩
          refine ⟨c * a', ?_⟩
          rw [map_mul, ha', smul_eq_mul, map_mul, mul_assoc] }
    have hmem' : f ∉ (algebraMap Γ(C.left, W) C.functionField).range := hmem
    -- `f ∉ Γ(C, W)`, so `I ≠ ⊤`.
    have hI_ne_top : I ≠ ⊤ := by
      intro h
      apply hmem'
      have h1 : (1 : Γ(C.left, W)) ∈ I := by rw [h]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := h1
      rw [map_one, one_mul] at hc
      exact ⟨c, hc⟩
    -- `f` is a fraction `a / s`, so `I ≠ ⊥`.
    obtain ⟨y, hy⟩ := IsLocalization.surj (nonZeroDivisors Γ(C.left, W)) f
    have hy0 : (y.2 : Γ(C.left, W)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2.2
    have hyI : (y.2 : Γ(C.left, W)) ∈ I := ⟨y.1, by rw [← hy, mul_comm]⟩
    have hI_ne_bot : I ≠ ⊥ := by
      intro h
      have h2 : (y.2 : Γ(C.left, W)) = 0 := by
        rw [h] at hyI
        exact Ideal.mem_bot.mp hyI
      exact hy0 h2
    -- Localize at a maximal ideal containing `I` and pass to the corresponding point of `W`.
    obtain ⟨m, hmax, hIle⟩ := I.exists_le_maximal hI_ne_top
    let mP : PrimeSpectrum Γ(C.left, W) := ⟨m, hmax.isPrime⟩
    let xW : W := hW.isoSpec.inv mP
    have hprimeIdeal : hW.primeIdealOf xW = mP := by
      change hW.isoSpec.hom (hW.isoSpec.inv mP) = mP
      have h := Homeomorph.apply_symm_apply (Scheme.homeoOfIso hW.isoSpec) mP
      simpa using h
    have hloc : IsLocalization.AtPrime (C.left.presheaf.stalk (xW : C.left)) m :=
      hW.isLocalization_stalk' mP xW.2
    -- `f` is *not* in the local ring at `xW`: otherwise its denominator would lie in `I ⊆ m`.
    haveI : IsScalarTower Γ(C.left, W) (C.left.presheaf.stalk (xW : C.left)) C.functionField :=
      AlgebraicGeometry.functionField_isScalarTower C.left W xW
    have hnot : f ∉ (algebraMap (C.left.presheaf.stalk (xW : C.left)) C.functionField).range := by
      intro hf'
      obtain ⟨s, hs, hc⟩ := exists_notMem_mul_mem_range (A := Γ(C.left, W))
        (R := C.left.presheaf.stalk (xW : C.left)) (K := C.functionField) m f hf'
      obtain ⟨c, hc'⟩ := hc
      exact hs (hIle ⟨c, by rw [hc', mul_comm]⟩)
    -- `xW` is a closed point of the curve; if it were the generic point, `m` would be `⊥`.
    have hclosed : IsClosed ({(xW : C.left)} : Set C.left) := by
      rcases Curve.eq_genericPoint_or_isClosed C (xW : C.left) with hgen | hcl
      · exfalso
        have hbot := primeIdealOf_eq_bot_of_eq_genericPoint hW xW hgen
        have hm_bot : m = ⊥ := by
          rw [hprimeIdeal] at hbot
          exact hbot
        exact hI_ne_bot (le_bot_iff.mp (hIle.trans_eq hm_bot))
      · exact hcl
    -- Regularity at that place yields a section after all, a contradiction.
    have hord : 0 ≤ C.ordAt f ⟨(xW : C.left), hclosed⟩ := hf ⟨(xW : C.left), hclosed⟩ xW.2
    exact hnot ((mem_range_algebraMap_stalk_iff C ⟨(xW : C.left), hclosed⟩ f).mpr hord)

end Work.CurveBasics.BaseChange
