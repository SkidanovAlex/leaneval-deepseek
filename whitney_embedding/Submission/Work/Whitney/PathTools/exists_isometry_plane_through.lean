import Mathlib
import Submission.Work.Whitney.PathTools.compl_totallyDisconnected_pathConnected
import Submission.Work.Whitney.PathTools.RemovabilityAux

namespace Work.Whitney.PathTools

/-- The linear span of two vectors has dimension at most two. -/
private lemma finrank_span_pair_le_two (E : Type*) [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (a b : E) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set E)) ≤ 2 := by
  have hspan : Submodule.span ℝ ({a, b} : Set E) =
      Submodule.span ℝ {a} ⊔ Submodule.span ℝ {b} := by
    rw [show ({a, b} : Set E) = insert a ({b} : Set E) from rfl, Submodule.span_insert]
  rw [hspan]
  have h1 : Module.finrank ℝ (Submodule.span ℝ {a}) ≤ 1 := by
    by_cases ha : a = 0
    · rw [ha, Submodule.span_zero_singleton, finrank_bot]; omega
    · rw [finrank_span_singleton ha]
  have h2 : Module.finrank ℝ (Submodule.span ℝ {b}) ≤ 1 := by
    by_cases hb : b = 0
    · rw [hb, Submodule.span_zero_singleton, finrank_bot]; omega
    · rw [finrank_span_singleton hb]
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span ℝ {a}) (Submodule.span ℝ {b})
  omega

/-- Any subspace of dimension at most two, in a finite-dimensional real vector space of
dimension at least two, is contained in a subspace of dimension exactly two. -/
private lemma exists_submodule_finrank_two_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) (U : Submodule ℝ E)
    (hU : Module.finrank ℝ U ≤ 2) :
    ∃ W : Submodule ℝ E, U ≤ W ∧ Module.finrank ℝ W = 2 := by
  by_cases hU2 : Module.finrank ℝ U = 2
  · exact ⟨U, le_rfl, hU2⟩
  · have hUlt : Module.finrank ℝ U < Module.finrank ℝ E := by omega
    have hne : U ≠ ⊤ := by
      intro h; rw [h, finrank_top] at hUlt; exact lt_irrefl _ hUlt
    obtain ⟨_, m, _, hm⟩ := SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne le_top hne)
    have hfr' : Module.finrank ℝ ↥(U ⊔ Submodule.span ℝ {m}) = Module.finrank ℝ U + 1 :=
      Submodule.finrank_sup_span_singleton hm
    by_cases hU'2 : Module.finrank ℝ ↥(U ⊔ Submodule.span ℝ {m}) = 2
    · exact ⟨U ⊔ Submodule.span ℝ {m}, le_sup_left, hU'2⟩
    · have hlt' : Module.finrank ℝ ↥(U ⊔ Submodule.span ℝ {m}) < Module.finrank ℝ E := by
        omega
      have hne' : (U ⊔ Submodule.span ℝ {m}) ≠ ⊤ := by
        intro h; rw [h, finrank_top] at hlt'; exact lt_irrefl _ hlt'
      obtain ⟨_, m', _, hm'⟩ := SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne le_top hne')
      refine ⟨U ⊔ Submodule.span ℝ {m} ⊔ Submodule.span ℝ {m'}, ?_, ?_⟩
      · exact (le_sup_left : U ≤ U ⊔ Submodule.span ℝ {m}).trans le_sup_left
      · rw [Submodule.finrank_sup_span_singleton hm']
        omega

theorem exists_isometry_plane_through {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : 2 ≤ Module.finrank ℝ E) (c X Y : E) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → E, Isometry f ∧ Continuous f ∧ f 0 = c ∧
      (∃ p : EuclideanSpace ℝ (Fin 2), f p = X) ∧ (∃ q : EuclideanSpace ℝ (Fin 2), f q = Y) := by
  have hle : Module.finrank ℝ (Submodule.span ℝ ({X - c, Y - c} : Set E)) ≤ 2 :=
    finrank_span_pair_le_two E (X - c) (Y - c)
  obtain ⟨W, hUW, hW2⟩ :=
    exists_submodule_finrank_two_of_le hE (Submodule.span ℝ ({X - c, Y - c} : Set E)) hle
  have haW : X - c ∈ W := hUW (Submodule.subset_span (by simp))
  have hbW : Y - c ∈ W := hUW (Submodule.subset_span (by simp))
  -- an orthonormal basis of the plane `W`, indexed by `Fin 2`
  let bW : OrthonormalBasis (Fin 2) ℝ W :=
    (stdOrthonormalBasis ℝ W).reindex (Equiv.cast (congrArg Fin hW2))
  -- the linear isometry from the standard plane onto `W` (inside `E`)
  let g : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E :=
    (Submodule.subtypeₗᵢ W).comp (bW.repr.symm).toLinearIsometry
  refine ⟨fun p => c + g p, ?_, ?_, ?_, ?_, ?_⟩
  · exact Isometry.comp (isometry_add_left c) g.isometry
  · exact (Isometry.comp (isometry_add_left c) g.isometry).continuous
  · show c + g 0 = c
    rw [map_zero, add_zero]
  · refine ⟨bW.repr ⟨X - c, haW⟩, ?_⟩
    show c + g (bW.repr ⟨X - c, haW⟩) = X
    have h1 : bW.repr.symm (bW.repr ⟨X - c, haW⟩) = ⟨X - c, haW⟩ :=
      LinearIsometryEquiv.symm_apply_apply _ _
    have h2 : g (bW.repr ⟨X - c, haW⟩) = X - c := by
      change (Submodule.subtypeₗᵢ W) (bW.repr.symm (bW.repr ⟨X - c, haW⟩)) = X - c
      rw [h1]
      rfl
    rw [h2, add_sub_cancel]
  · refine ⟨bW.repr ⟨Y - c, hbW⟩, ?_⟩
    show c + g (bW.repr ⟨Y - c, hbW⟩) = Y
    have h1 : bW.repr.symm (bW.repr ⟨Y - c, hbW⟩) = ⟨Y - c, hbW⟩ :=
      LinearIsometryEquiv.symm_apply_apply _ _
    have h2 : g (bW.repr ⟨Y - c, hbW⟩) = Y - c := by
      change (Submodule.subtypeₗᵢ W) (bW.repr.symm (bW.repr ⟨Y - c, hbW⟩)) = Y - c
      rw [h1]
      rfl
    rw [h2, add_sub_cancel]

end Work.Whitney.PathTools
