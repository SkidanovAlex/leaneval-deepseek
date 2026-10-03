import Mathlib
import Submission.Work.OROneRel.killTree

namespace Work.OROneRel

/-- **Retraction onto the complement of a set of generators.**  For any set `T` of generators of the
free group `F α`, the assignment sending each generator of `T` to itself and every other generator to
`1` extends to a retraction of `F α` onto `F T`: a homomorphism `π : F α →* F T` with
`π (FreeGroup.of e) = 1` for `e ∉ T` and `π (FreeGroup.map Subtype.val x) = x` for all `x : F T`. -/
lemma exists_proj_subtype (α : Type*) (T : Set α) :
    ∃ π : FreeGroup α →* FreeGroup T,
      (∀ e : α, e ∉ T → π (FreeGroup.of e) = 1) ∧
      (∀ x : FreeGroup T, π (FreeGroup.map (Subtype.val : T → α) x) = x) := by
  classical
  let f : α → FreeGroup T := fun e => if h : e ∈ T then FreeGroup.of ⟨e, h⟩ else 1
  refine ⟨FreeGroup.lift f, ?_, ?_⟩
  · intro e he
    rw [FreeGroup.lift_apply_of]
    exact dif_neg he
  · intro x
    have hcomp : (FreeGroup.lift f).comp (FreeGroup.map (Subtype.val : T → α))
        = MonoidHom.id (FreeGroup T) := by
      refine FreeGroup.ext_hom _ _ fun y => ?_
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]
      exact dif_pos y.2
    exact DFunLike.congr_fun hcomp x

/-- The projection of the edge group `F (Fin 2 × ℤ)` onto the alphabet `β = winBeta Wt c lo hi` of the
window: send the generator of a non-tree edge of the window to its `β`-generator, and kill every other
generator (in particular the generators of the tree `treeSet`).  It is a retraction of the inclusion
`F (β) →* F (Fin 2 × ℤ)`. -/
theorem exists_killTree_proj (Wt : ℤ → FreeGroup (Fin 2)) (c : Fin 2 → ℤ) (lo hi : ℤ) :
    ∃ π : FreeGroup (Fin 2 × ℤ) →* FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      (∀ e ∈ Work.OROneRel.treeSet Wt c lo hi, π e = 1) ∧
      (∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
        π (FreeGroup.map (Subtype.val : Work.OROneRel.winBeta Wt c lo hi → Fin 2 × ℤ) x) = x) := by
  classical
  obtain ⟨π, h1, h2⟩ := exists_proj_subtype (Fin 2 × ℤ)
    {e | e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1}
  refine ⟨π, ?_, ?_⟩
  · rintro e ⟨e', he', rfl⟩
    exact h1 e' (fun hmem => hmem.2 he'.2)
  · intro x
    exact h2 x

end Work.OROneRel
