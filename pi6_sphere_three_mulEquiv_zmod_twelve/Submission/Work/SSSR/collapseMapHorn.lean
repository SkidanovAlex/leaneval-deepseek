import Mathlib
import Submission.Work.SSSR.collapseDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Simplicial
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
/-- The value of the collapse on an `n`-simplex `(a, μ)` of the prism, in coordinates:
`j ↦ if μ j = 0 then a j else s`.  This is the defining formula of `Work.SSSR.collapseMap`,
extracted from its definition through `SSet.stdSimplex.objEquiv`. -/
theorem collapseMap_apply_coe {s n : ℕ}
    (z : (tensorObj (SSet.stdSimplex.obj (SimplexCategory.mk s))
      (SSet.stdSimplex.obj (SimplexCategory.mk 1))).obj (Opposite.op (SimplexCategory.mk n)))
    (j : Fin (n + 1)) :
    ((Work.SSSR.collapseMap s).app (Opposite.op (SimplexCategory.mk n))) z j =
      if ((z.2) j : ℕ) = 0 then (z.1) j else Fin.last s := by
  simp only [Work.SSSR.collapseMap, Work.SSSR.collapseHom]
  rfl

/-- **The collapse of the prism preserves the horn.**
`Work.SSSR.hornSimp s ⊆ Δ[s]` is the horn `⋃_{i<s} d_i Δ[s]` (the union of the faces other than the
last one), i.e. the subcomplex of simplices `a : [n] → [s]` whose image misses some vertex `< s`.
Membership is `Work.SSSR.hornSimp`, `SSet.stdSimplex.mem_face_iff`:
`a ∈ (hornSimp s).obj _ ↔ ∃ i : Fin s, ∀ j, a j ≠ i.castSucc`.

The claim: the collapse `Work.SSSR.collapseMap s : Δ[s] ⊗ Δ[1] ⟶ Δ[s]`, which on an `n`-simplex
`(a, μ)` is `j ↦ if μ j = 0 then a j else s`, sends the part of the prism lying over the horn into
the horn.  Concretely, if `a` misses the vertex `i.castSucc` with `i : Fin s`, then so does
`j ↦ if μ j = 0 then a j else s`, because its values lie in `{a j, s}` and
`i.castSucc ≠ Fin.last s` (as `i : Fin s`).

Useful: `Work.SSSR.hornSimp`, `Work.SSSR.collapseMap`, `Work.SSSR.collapseHom`,
`Subcomplex.prod`, `Subcomplex.preimage`, `SSet.stdSimplex.objEquiv`,
`SSet.stdSimplex.mem_face_iff`, `Subfunctor.iSup_obj`. -/
theorem collapseMapHorn (s : ℕ) :
    (Work.SSSR.hornSimp s).prod (⊤ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet).Subcomplex)
      ≤ (Work.SSSR.hornSimp s).preimage (Work.SSSR.collapseMap s) := by
  rw [Subfunctor.le_def]
  rintro ⟨⟨n⟩⟩ z hz
  rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage]
  rw [SSet.Subcomplex.prod_obj] at hz
  obtain ⟨hz1, _⟩ := hz
  rw [Work.SSSR.hornSimp, Subfunctor.iSup_obj, Set.mem_iUnion] at hz1 ⊢
  obtain ⟨i, hi⟩ := hz1
  rw [SSet.stdSimplex.mem_face_iff] at hi
  refine ⟨i, ?_⟩
  rw [SSet.stdSimplex.mem_face_iff]
  intro j
  simp only [Finset.mem_compl, Finset.mem_singleton] at hi ⊢
  rw [collapseMap_apply_coe z j]
  split_ifs with h
  · exact hi j
  · exact (Fin.castSucc_ne_last i).symm

end Work.SSSR
