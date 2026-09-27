import Mathlib
import Submission.Work.OneDim.ArcDefs
import Submission.Work.OneDim.interval_surj

/-!
# Reparametrising an arc so that it is defined on all of `ℝ`
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-- An injective local diffeomorphism on an open interval can be reparametrised to a global
injective local diffeomorphism `ℝ → C` with the same image. -/
theorem reparam_arc {γ : ℝ → C} {I : Set ℝ} (hopen : IsOpen I)
    (hconn : IsPreconnected I) (hne : I.Nonempty) (hinj : Set.InjOn γ I)
    (hld : IsLocalDiffeomorphOn (modelWithCornersSelf ℝ ℝ) I1 sm γ I) :
    ∃ γ' : ℝ → C, Function.Injective γ' ∧
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ' ∧
      Set.range γ' = γ '' I := by
  obtain ⟨e, heinj, held, herange⟩ := interval_surj hopen hconn hne
  refine ⟨γ ∘ e, ?_, ?_, ?_⟩
  · intro s t hst
    simp only [Function.comp_apply] at hst
    have hs : e s ∈ I := herange ▸ Set.mem_range_self s
    have ht : e t ∈ I := herange ▸ Set.mem_range_self t
    exact heinj (hinj hs ht hst)
  · intro x
    exact IsLocalDiffeomorphAt.comp (K := I1) (P := C) (held x)
      (hld ⟨e x, herange ▸ Set.mem_range_self x⟩)
  · rw [Set.range_comp, herange]

end Work.OneDim
