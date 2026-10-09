import Mathlib
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **`H¹` of an arbitrary product of coefficient modules is a subsingleton as soon as each
factor is.**  This is the infinite-index version of `Work.SSGRoute.subsingleton_H1_pi` (which
needs `[Fintype ι]`): a locally constant crossed homomorphism `F : Γ → ∏ i, X i` has locally
constant components (`IsLocallyConstant.map` with the projection, no finiteness needed), each
component is a coboundary `σ ↦ σ • a i - a i` because `H¹(Γ, X i)` is a subsingleton, and
`a := fun i => a i` is then a primitive for `F`. -/
theorem subsingleton_H1_pi_inf {Γ : Type} [TopologicalSpace Γ] [Group Γ]
    {ι : Type} {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, DistribMulAction Γ (X i)]
    (h : ∀ i, Subsingleton (Work.AbsoluteKummer.H1 Γ (X i))) :
    Subsingleton (@Work.AbsoluteKummer.H1 Γ (∀ i, X i) _ _
      (Pi.addCommGroup) (Pi.distribMulAction Γ)) := by
  classical
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  -- write `x` as the class of a locally constant crossed homomorphism `F`
  obtain ⟨F, hF⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 Γ (∀ i, X i)).comap
      (Work.AbsoluteKummer.Z1 Γ (∀ i, X i)).subtype) x
  rw [show x = Work.AbsoluteKummer.H1π Γ (∀ i, X i) F from hF.symm,
    Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff]
  -- each component of `F` is a locally constant crossed homomorphism ...
  have key : ∀ i, ∃ a : X i,
      Work.GroupCohomology.d0 Γ (X i) a = fun σ : Γ => (F : Γ → ∀ i, X i) σ i := by
    intro i
    have hsub : Subsingleton (Work.AbsoluteKummer.H1 Γ (X i)) := h i
    have hmem : (fun σ : Γ => (F : Γ → ∀ i, X i) σ i) ∈
        Work.AbsoluteKummer.Z1 Γ (X i) := by
      obtain ⟨hcross, hloc⟩ :=
        (Work.AbsoluteKummer.mem_Z1_iff (G := Γ) (M := ∀ i, X i)
          (f := (F : Γ → ∀ i, X i))).mp F.2
      rw [Work.AbsoluteKummer.mem_Z1_iff]
      exact ⟨fun g hh => by
          have h2 := congrFun (hcross g hh) i
          simpa using h2,
        Work.AbsoluteKummer.IsLocallyConstant.map (fun v : ∀ i, X i => v i) hloc⟩
    -- ... and it is a coboundary, because `H¹(Γ, X i)` is a subsingleton
    have hz : Work.AbsoluteKummer.H1π Γ (X i) ⟨_, hmem⟩ = 0 := Subsingleton.elim _ _
    rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff] at hz
    exact hz
  -- `a := fun i => a i` is a common primitive
  choose a ha using key
  exact ⟨a, by
    funext σ i
    have h2 := congrFun (ha i) σ
    simp only [Work.GroupCohomology.d0_apply] at h2
    show (σ • a - a) i = (F : Γ → ∀ i, X i) σ i
    rw [Pi.sub_apply, Pi.smul_apply]
    exact h2⟩

end Work.SSGRoute
