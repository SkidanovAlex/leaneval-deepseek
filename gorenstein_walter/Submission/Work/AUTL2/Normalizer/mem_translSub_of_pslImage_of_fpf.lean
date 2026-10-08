import Mathlib
import Submission.Work.AUTL2.Normalizer.Defs

namespace Work.AUTL2.Normalizer

open OnePoint

/-- An element of `pslImage F` that fixes `∞` and has no fixed point among the finite points
`F ⊆ ℙ¹(F)` is a translation `x ↦ x + b`.  Indeed, such an element is affine `x ↦ a²x + b`
(`Work.AUTL2.element_fixing_infty`); if `a² ≠ 1` the affine map
`x ↦ a²x + b` has the fixed point `x = -b/(a²-1)`, so `a² = 1` and the map is a translation. -/
theorem mem_translSub_of_pslImage_of_fpf (F : Type*) [Field F] [DecidableEq F]
    (g : Equiv.Perm (Work.AUTL2.P1 F)) (hg : g ∈ Work.AUTL2.pslImage F)
    (hinf : g OnePoint.infty = OnePoint.infty)
    (hfpf : ∀ x : F, g (x : Work.AUTL2.P1 F) ≠ (x : Work.AUTL2.P1 F)) :
    g ∈ Work.AUTL2.Normalizer.translSub F := by
  obtain ⟨a, b, h⟩ := Work.AUTL2.element_fixing_infty F g hg hinf
  -- the multiplier of the affine map must be `1`, otherwise there is a fixed point in `F`
  have hsq : (↑a : F) ^ 2 = 1 := by
    by_contra hne
    have hfix : ∃ x : F, (↑a : F) ^ 2 * x + b = x := by
      refine ⟨-((↑a : F) ^ 2 - 1)⁻¹ * b, ?_⟩
      field_simp
      ring
    obtain ⟨x, hx⟩ := hfix
    exact hfpf x (by rw [h x, hx])
  -- so `g` is the translation `x ↦ x + b`, `∞ ↦ ∞`
  have hg_eq : g = Work.AUTL2.transl F b := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun x => ?_⟩
    · rw [hinf]
      exact (Work.AUTL2.transl_infty F b).symm
    · rw [h x, Work.AUTL2.transl_formula, hsq]
      simp
  rw [hg_eq]
  exact transl_mem_translSub F b

end Work.AUTL2.Normalizer
