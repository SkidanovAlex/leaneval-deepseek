import Mathlib
import Submission.Work.DSMX0U.Cell

namespace Work.DSMX0U

universe a

/-- **The square of the cell construction commutes.**  The differential `Cell.d` of the model,
from degree `q - 1` to degree `q`, followed by the map `Cell.φprev` of the next level up into
`C`, agrees with the map `Cell.φ` of the current level followed by the differential of `C`.

Concretely, on an element `(x, y) ∈ gen × rel` the left hand side is
`φprev (cov y)` and the right hand side is `0 + C.d (β y)`, which is the same because `β` is a
lift of `φprev ∘ cov` along `C.d (q - 1) q` (`Cell.hβ`) and `σ x` is a cycle. -/
theorem cell_d_comm {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0} {q : ℤ}
    (s : Work.DSMX0U.Cell A C c₀ q) :
    CategoryTheory.CategoryStruct.comp (s.d A) s.φprev =
      CategoryTheory.CategoryStruct.comp (s.φ A) (C.d (q - 1) q) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  obtain ⟨x, y⟩ := p
  simp only [ModuleCat.hom_comp, Cell.d, Cell.φ, Cell.dHom, Cell.φHom, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.zero_apply, map_add, map_zero]
  -- the left hand side is `φprev (cov y)`; the right hand side is `0 + C.d (β y)`, and the two
  -- are equal by `Cell.hβ` once the `σ x` term (a cycle) is killed by the differential of `C`.
  rw [zero_add, iCycles_d_apply A (q - 1) q (s.σ.hom x), zero_add, s.hβ y]
  rfl

end Work.DSMX0U
