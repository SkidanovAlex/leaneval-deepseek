import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Chart.Regular

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped Classical

namespace Work.SpecLin.Alt

open Work.CurveBasics

/-- **A rational function of a curve is a section over the open on which it is regular.**

`C` a smooth proper geometrically irreducible curve over a field `K`, `x ∈ K(C)`, and
`W := Work.SpecLin.Chart.regularOpens C x` the complement of the pole set of `x`.  Then `x` is in
the range of the restriction map `Γ(C.left, W) → K(C)`.

Proof: cover `W` by affine opens `V ⊆ C.left` with `V ≤ W` (affine opens form a basis of `C.left`;
a finite subcover exists because `W`, an open of the Noetherian `C.left`, is quasi-compact).  On
each `V`, `x` is regular at every place of `V` (`Work.SpecLin.Chart.regularOn_regularOpens`), so
`x` lies in the range of `Γ(C.left, V) → K(C)` by
`Work.CurveBasics.BaseChange.mem_range_germ_iff`; the sections glue along overlaps
(`TopCat.Sheaf.existsUnique_gluing'`), using injectivity of `Γ(C.left, U) → K(C)` on nonempty
opens (`Scheme.germToFunctionField_injective`) to see that they agree there. -/
theorem exists_section_regularOpens {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (x : C.functionField) [Nonempty (Work.SpecLin.Chart.regularOpens C x)] :
    ∃ s : C.left.presheaf.obj (Opposite.op (Work.SpecLin.Chart.regularOpens C x)),
      (C.germToFunctionField (Work.SpecLin.Chart.regularOpens C x)).hom s = x := by
  -- `W` is the open on which `x` is regular.
  set W : C.left.Opens := Work.SpecLin.Chart.regularOpens C x
  have hWne : Nonempty W := ‹Nonempty (Work.SpecLin.Chart.regularOpens C x)›
  -- Affine opens form a basis of the topology.
  have hbasis : ∀ {V : C.left.Opens} {z : C.left}, z ∈ V →
      ∃ U' ∈ C.left.affineOpens, z ∈ U' ∧ U' ≤ V :=
    Opens.isBasis_iff_nbhd.mp C.left.isBasis_affineOpens
  -- For every point `p ∈ W` choose an affine open `U p ∋ p` contained in `W`.
  let U : W → C.left.Opens := fun p => Classical.choose (hbasis (V := W) p.2)
  have hUaff : ∀ p : W, IsAffineOpen (U p) := fun p =>
    (Classical.choose_spec (hbasis (V := W) p.2)).1
  have hUmem : ∀ p : W, (p : C.left) ∈ U p := fun p =>
    (Classical.choose_spec (hbasis (V := W) p.2)).2.1
  have hUle : ∀ p : W, U p ≤ W := fun p =>
    (Classical.choose_spec (hbasis (V := W) p.2)).2.2
  -- The generic point lies in every nonempty open, in particular in each `U p` (which contains `p`).
  have hgen : ∀ p : W, genericPoint C.left ∈ U p := fun p =>
    ((genericPoint_spec C.left).mem_open_set_iff (U p).isOpen).mpr (by
      have h : Nonempty (U p) := ⟨⟨p, hUmem p⟩⟩
      simpa using h)
  -- `x` is a section over each affine piece `U p`.
  have hmr : ∀ p : W, ∃ s : C.left.presheaf.obj (Opposite.op (U p)),
      (C.left.presheaf.germ (U p) (genericPoint C.left) (hgen p)) s = x := by
    intro p
    haveI : Nonempty (U p) := ⟨⟨p, hUmem p⟩⟩
    obtain ⟨s, hs⟩ :=
      (Work.CurveBasics.BaseChange.mem_range_germ_iff (C := C) (U p) (hUaff p) x).mpr
        (fun Q hQ => Work.SpecLin.Chart.regularOn_regularOpens C x Q (hUle p hQ))
    exact ⟨s, hs⟩
  let sf : ∀ p : W, C.left.presheaf.obj (Opposite.op (U p)) := fun p => Classical.choose (hmr p)
  have hsf : ∀ p : W, (C.left.presheaf.germ (U p) (genericPoint C.left) (hgen p)) (sf p) = x :=
    fun p => Classical.choose_spec (hmr p)
  -- The pieces agree on the overlaps, since both restrict to `x` and the germ at the generic
  -- point is injective.
  have hcompat : TopCat.Presheaf.IsCompatible C.left.presheaf U sf := by
    intro p q
    have hη : genericPoint C.left ∈ U p ⊓ U q := ⟨hgen p, hgen q⟩
    apply germ_injective_of_isIntegral C.left (genericPoint C.left) hη
    rw [TopCat.Presheaf.germ_res_apply C.left.presheaf (Opens.infLELeft (U p) (U q))
          (genericPoint C.left) hη (sf p),
        TopCat.Presheaf.germ_res_apply C.left.presheaf (Opens.infLERight (U p) (U q))
          (genericPoint C.left) hη (sf q)]
    exact (hsf p).trans (hsf q).symm
  -- The `U p` cover `W`: each point lies in its own piece.
  have hcover : W ≤ iSup U := fun z hz => le_iSup U ⟨z, hz⟩ (hUmem ⟨z, hz⟩)
  -- Glue the local sections.
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨C.left.presheaf, C.left.IsSheaf⟩ U W
    (fun p => homOfLE (hUle p)) hcover sf hcompat
  have hWη : genericPoint C.left ∈ W :=
    ((genericPoint_spec C.left).mem_open_set_iff W.isOpen).mpr (by simpa using hWne)
  refine ⟨s, ?_⟩
  obtain ⟨p⟩ := hWne
  -- Evaluate the glued section at the generic point, where it agrees with `x` by construction.
  show (C.left.presheaf.germ W (genericPoint C.left) hWη) s = x
  rw [← TopCat.Presheaf.germ_res_apply C.left.presheaf (homOfLE (hUle p))
        (genericPoint C.left) (hgen p) s, hs p, hsf p]

end Work.SpecLin.Alt
