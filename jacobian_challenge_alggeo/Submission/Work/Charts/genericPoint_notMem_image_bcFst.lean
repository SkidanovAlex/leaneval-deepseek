import Mathlib
import Submission.Work.Charts.FinBC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

open CategoryTheory Limits AlgebraicGeometry

/-- **B2 (FIBRE-GEN).**  For an irreducible, geometrically irreducible `K`-scheme `X` and a
finite field extension `L/K`, a proper closed subset `Z ⊊ X_L` of the base change never meets
the fibre over the generic point of `X`: the generic point of `X` is not in `fst '' Z`.

The proof is the one of the lead's notes §2: the base change `X_L` is irreducible, so its
generic point `w` has closure `X_L` and therefore lies in no proper closed subset.  A point
`z` of `Z` mapping to the generic point `η` of `X` would force `fst w = η` (as `w ⤳ z`, so
`fst w ⤳ η`, and `η` is generic); both `w` and `z` would then live in the fibre
`fst ⁻¹' {η}`, which is discrete because `fst` is finite, hence locally quasi-finite.  A
discrete subset contains no nontrivial specialization, so `w = z ∈ Z`, a contradiction. -/
theorem genericPoint_notMem_image_bcFst {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    [IrreducibleSpace X.left] [AlgebraicGeometry.GeometricallyIrreducible X.hom]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    (Z : Set (Work.Charts.bcSch X L).left) (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    genericPoint X.left ∉ (Work.Charts.bcFst X L).left.base '' Z := by
  rintro ⟨z, hzZ, hzf⟩
  set w : (Work.Charts.bcSch X L).left := genericPoint (Work.Charts.bcSch X L).left
  -- The generic point `w` of `X_L` lies in no proper closed subset.
  have hwZ : w ∉ Z := by
    intro hw
    have hsub : Set.univ ⊆ Z :=
      ((genericPoint_spec (Work.Charts.bcSch X L).left).mem_closed_set_iff hZ).mp hw
    exact hZne (Set.eq_univ_of_univ_subset hsub)
  -- `w` is mapped to the generic point of `X` (dominance of `bcFst`).
  have hw_base : (Work.Charts.bcFst X L).left.base w = genericPoint X.left := by
    have hsurj := Work.Charts.surjective_bcFst X L
    have himg : IsGenericPoint ((Work.Charts.bcFst X L).left.base w) Set.univ := by
      convert (genericPoint_spec (Work.Charts.bcSch X L).left).image
        (Scheme.Hom.continuous (Work.Charts.bcFst X L).left) using 1
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj, closure_univ]
    exact IsGenericPoint.eq himg (genericPoint_spec X.left)
  -- The fibre over the generic point of `X` is discrete, because `bcFst` is finite.
  have hdisc := Scheme.Hom.isDiscrete_preimage_singleton
    (Work.Charts.bcFst X L).left (genericPoint X.left)
  have hmem_w : w ∈ (Work.Charts.bcFst X L).left.base ⁻¹' {genericPoint X.left} := hw_base
  have hmem_z : z ∈ (Work.Charts.bcFst X L).left.base ⁻¹' {genericPoint X.left} := hzf
  have : w = z := hdisc.eq_of_specializes (genericPoint_specializes z) hmem_w hmem_z
  exact hwZ (this ▸ hzZ)

end Work.Charts
