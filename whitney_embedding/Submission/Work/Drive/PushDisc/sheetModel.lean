import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# The model plane `sheetA` as a submodule, and the dimension bookkeeping

`Work.Drive.Whitney.sheetA = {ξ | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}` is the model plane of the first sheet of
the Whitney move inside the model space `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k`.  This module packages it as a
`Submodule` (`sheetASub`), computes its dimension (`k + 1`) and the dimension of `Mdl k` (`2 (k+1)`),
and provides the coordinate extensionality of `Mdl k`.  These are the bookkeeping facts needed by
`Work.Drive.PushDisc.sheetOneFlatteningData`.
-/

namespace Work.Drive.PushDisc

/-- The model sheet `sheetA` of the Whitney move, as a submodule of the model space. -/
def sheetASub (k : ℕ) : Submodule ℝ (Work.Drive.Whitney.Mdl k) where
  carrier := Work.Drive.Whitney.sheetA
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by simp [ha.1], by simp [ha.2]⟩

theorem mem_sheetASub {k : ℕ} {ξ : Work.Drive.Whitney.Mdl k} :
    ξ ∈ sheetASub k ↔ ξ ∈ Work.Drive.Whitney.sheetA := Iff.rfl

/-- Coordinate extensionality in the model space. -/
theorem mdl_ext {k : ℕ} {ξ η : Work.Drive.Whitney.Mdl k} (h1 : ξ.1 = η.1)
    (h2 : ξ.2.1 = η.2.1) (h3 : ξ.2.2.1 = η.2.2.1) (h4 : ξ.2.2.2 = η.2.2.2) : ξ = η := by
  obtain ⟨x, y, u, v⟩ := ξ
  obtain ⟨x', y', u', v'⟩ := η
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

/-- The dimension of the model space. -/
theorem finrank_Mdl (k : ℕ) : Module.finrank ℝ (Work.Drive.Whitney.Mdl k) = 2 * (k + 1) := by
  simp only [Work.Drive.Whitney.Mdl, Module.finrank_prod, finrank_euclideanSpace,
    Fintype.card_fin, Module.finrank_self]
  ring

/-- The dimension of the model plane `sheetA`. -/
theorem finrank_sheetASub (k : ℕ) : Module.finrank ℝ (sheetASub k) = k + 1 := by
  let f : sheetASub k →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)) :=
    { toFun := fun ξ => (ξ.1.1, ξ.1.2.2.1)
      map_add' := by intro a b; ext <;> simp
      map_smul' := by intro c a; ext <;> simp }
  have hbij : Function.Bijective f := by
    constructor
    · intro ξ η h
      refine Subtype.ext (mdl_ext ?_ ?_ ?_ ?_)
      · exact congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin k) => z.1) h
      · rw [ξ.2.1, η.2.1]
      · exact congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin k) => z.2) h
      · rw [ξ.2.2, η.2.2]
    · rintro ⟨x, u⟩
      exact ⟨⟨(x, 0, u, 0), ⟨rfl, rfl⟩⟩, rfl⟩
  have hfin := (LinearEquiv.ofBijective f hbij).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace, Fintype.card_fin] at hfin
  rw [hfin]
  omega

end Work.Drive.PushDisc
