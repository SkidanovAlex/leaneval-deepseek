import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lifting a linear map along a surjection onto its range

`Work.ThomBordism.exists_comp_eq_of_range_le`: a linear map `Φ : ℝ^k → ℝ^{k+m}` whose range is
contained in the range of `Lv : V → ℝ^{k+m}` factors through `Lv`, i.e. there is a (not necessarily
unique) linear `N : ℝ^k → V` with `Lv ∘ N = Φ`.

This is the linear algebra behind the normal-frame datum of the last mile's tube determinant
(`LeadChapter/chapter_tubeDet`): the Gauss frame `ogFrameCLM (G.gauss p)` of the normal plane has its
range inside the range of the derivative of the level function, so a linear section `N` of the level
function along the Gauss frame exists.  The proof is a basis argument: `N` is defined on the standard
basis by choosing preimages and extended linearly.

No geometry, no new axioms.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism

noncomputable section

/-- **Lifting a linear map along a map whose range contains its range.**

For `Φ : ℝ^k →L ℝ^N` and `Lv : V →L ℝ^N` with `Set.range Φ ⊆ Set.range Lv` there is a linear
`N : ℝ^k →L V` with `Lv ∘ N = Φ`. -/
theorem exists_comp_eq_of_range_le {k N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (Lv : V →L[ℝ] EuclideanSpace ℝ (Fin N))
    (h : Set.range Φ ⊆ Set.range Lv) :
    ∃ N : EuclideanSpace ℝ (Fin k) →L[ℝ] V, Lv.comp N = Φ := by
  classical
  -- a preimage of the `a`-th frame vector
  have hex : ∀ a : Fin k, ∃ w : V, Lv w = Φ (EuclideanSpace.single a 1) := by
    intro a
    refine h ⟨EuclideanSpace.single a 1, rfl⟩
  choose w hw using hex
  refine ⟨∑ a : Fin k, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
    (w a), ?_⟩
  -- both sides are linear, so it suffices to compare them on the standard basis
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ a : Fin k, (v a) • EuclideanSpace.single a 1 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr v]
    exact Finset.sum_congr rfl (fun a _ => by
      rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply])
  calc (Lv.comp (∑ a : Fin k, (EuclideanSpace.proj a :
          EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight (w a))) v
      = Lv ((∑ a : Fin k, (EuclideanSpace.proj a :
          EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight (w a)) v) := rfl
    _ = Lv (∑ a : Fin k, (v a) • w a) := by
          congr 1
          simp
    _ = ∑ a : Fin k, (v a) • Lv (w a) := by
          rw [map_sum]
          exact Finset.sum_congr rfl (fun a _ => (map_smul Lv (v a) (w a)))
    _ = ∑ a : Fin k, (v a) • Φ (EuclideanSpace.single a 1) := by
          exact Finset.sum_congr rfl (fun a _ => by rw [hw a])
    _ = Φ (∑ a : Fin k, (v a) • EuclideanSpace.single a 1) := by
          rw [map_sum]
          exact Finset.sum_congr rfl (fun a _ => (map_smul Φ (v a) _).symm)
    _ = Φ v := congrArg Φ hv.symm

end

end Work.ThomBordism

#print axioms Work.ThomBordism.exists_comp_eq_of_range_le
