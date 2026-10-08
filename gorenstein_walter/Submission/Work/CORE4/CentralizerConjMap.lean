import Mathlib

namespace Work.CORE4

/-- The centralizer of a set of group elements is carried, by a multiplicative
equivalence, to the centralizer of the image set.  (Mathlib only has the
inclusion `Subgroup.map_centralizer_le_centralizer_image`; surjectivity of the
equivalence gives the reverse inclusion.) -/
theorem map_centralizer_eq_centralizer_image {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (s : Set G) :
    (Subgroup.centralizer s).map e.toMonoidHom = Subgroup.centralizer (e '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s e.toMonoidHom) ?_
  intro x hx
  rw [Subgroup.mem_map]
  refine ⟨e.symm x, ?_, by simp⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have h := hx (e y) ⟨y, hy, rfl⟩
  have h2 := congrArg e.symm h
  simpa using h2

/-- Conjugation by `s` carries the centralizer of `{x}` onto the centralizer of
`{s * x * s⁻¹}`. -/
theorem CentralizerConjMap {G : Type*} [Group G] (s x : G) :
    Subgroup.centralizer ({s * x * s⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj s).toMonoidHom := by
  have himg : (MulAut.conj s) '' ({x} : Set G) = {s * x * s⁻¹} := by
    ext y
    simp [MulAut.conj_apply]
  rw [← himg, map_centralizer_eq_centralizer_image]

end Work.CORE4
