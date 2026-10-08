import Mathlib

namespace Work.DSTR.layerShapeAux

/-- **Piece of DS7 (`Work.DSTR.layerShape`).** If `φ : E →* Q` has kernel contained in the centre
of `E`, then the central quotient `E ⧸ Z(E)` is a quotient of the range of `φ`, by a central
subgroup, compatibly with the two natural maps.

Route: `f` is `(QuotientGroup.lift φ.ker (QuotientGroup.mk' (Subgroup.center E)) h)` composed with
`(QuotientGroup.quotientKerEquivRange φ).symm`; surjectivity from `Function.Surjective.comp` with
`QuotientGroup.mk'_surjective`; the compatibility clause from the description of
`QuotientGroup.lift` on `QuotientGroup.mk'`-classes; the kernel clause because an element of `ker f`
is `φ.rangeRestrict x` with `x ∈ Z(E)`, hence central in `φ.range`. -/
theorem exists_surj_range_center {E Q : Type*} [Group E] [Group Q] (φ : E →* Q)
    (h : φ.ker ≤ Subgroup.center E) :
    ∃ f : ↥φ.range →* (E ⧸ Subgroup.center E), Function.Surjective f ∧
      f.ker ≤ Subgroup.center ↥φ.range ∧
      ∀ x : E, f (φ.rangeRestrict x) = QuotientGroup.mk' (Subgroup.center E) x := by
  -- First isomorphism theorem: `E ⧸ ker φ ≃* range φ`.
  let e : E ⧸ φ.ker ≃* φ.range := QuotientGroup.quotientKerEquivRange φ
  -- Reduction mod `Z(E)`, which is well defined since `ker φ ≤ Z(E)`.
  let L : E ⧸ φ.ker →* E ⧸ Subgroup.center E :=
    QuotientGroup.lift φ.ker (QuotientGroup.mk' (Subgroup.center E))
      (by rw [QuotientGroup.ker_mk']; exact h)
  let f : φ.range →* E ⧸ Subgroup.center E := L.comp e.symm
  -- Compatibility of `f` with `φ.rangeRestrict`.
  have hcompat : ∀ x : E, f (φ.rangeRestrict x) = QuotientGroup.mk' (Subgroup.center E) x := by
    intro x
    have h1 : e (QuotientGroup.mk' φ.ker x) = φ.rangeRestrict x := by
      simp only [e, QuotientGroup.quotientKerEquivRange, MulEquiv.ofBijective_apply,
        QuotientGroup.rangeKerLift]
      exact QuotientGroup.lift_mk' _ _ x
    show L (e.symm (φ.rangeRestrict x)) = _
    rw [← h1, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk' _ _ x
  refine ⟨f, ?_, ?_, hcompat⟩
  · -- Surjectivity: `L` is a lift of a surjective map and `e.symm` is an equivalence.
    have hL : Function.Surjective L :=
      QuotientGroup.lift_surjective_of_surjective φ.ker (QuotientGroup.mk' (Subgroup.center E))
        (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact h)
    exact hL.comp e.symm.surjective
  · -- `ker f` consists of images of central elements, hence is central in `range φ`.
    intro g hg
    obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective g
    apply Subgroup.map_center_le_center φ.rangeRestrict_surjective
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [← QuotientGroup.ker_mk' (Subgroup.center E), MonoidHom.mem_ker]
    exact (hcompat x).symm.trans (MonoidHom.mem_ker.mp hg)

end Work.DSTR.layerShapeAux
