import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the `k`-th one-sided time jet of a smooth family

Given a family `H : ℝ × E → Z` which is `C^∞` on the half-open slab `[0,T) × U`
and a natural number `k`, the `k`-th iterated derivative of `H` at `(0,y)` in the
*time* direction `(1,0)` depends smoothly on `y ∈ U`.

This is a direct consequence of the fact that `x ↦ iteratedFDerivWithin ℝ k H s x`
is smooth on `s` (for `s` a set of unique differentiability) and that evaluating a
continuous multilinear map at a fixed vector is a continuous linear operation.
-/

namespace Work.Diff.EXT

open Set

theorem jet_functions_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (H : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U)) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) (0, y) (fun _ => (1, 0)))
      U := by
  intro y hy
  -- `(0, y)` lies in the slab, since `0 < T` and `y ∈ U`.
  have hx₀ : (0, y) ∈ (Set.Ico 0 T) ×ˢ U := ⟨⟨le_refl 0, hT⟩, hy⟩
  -- The slab is a set of unique differentiability.
  have hsd : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) :=
    (uniqueDiffOn_Ico 0 T).prod hU.uniqueDiffOn
  -- The `k`-th iterated derivative is smooth as a function of the base point.
  have hA : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ × E => iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) x)
      ((Set.Ico 0 T) ×ˢ U) (0, y) :=
    (hH.contDiffWithinAt hx₀).iteratedFDerivWithin_right hsd (by simp) hx₀
  -- Evaluating at the fixed direction `(1, 0)` is a continuous linear operation.
  have hcomp : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ × E => iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) x (fun _ => (1, 0)))
      ((Set.Ico 0 T) ×ˢ U) (0, y) :=
    hA.continuousLinearMap_comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z (fun _ => (1, 0)))
  -- The inclusion `y ↦ (0, y)` is smooth and maps `U` into the slab.
  have hφ : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun y : E => ((0 : ℝ), y)) U y :=
    contDiffWithinAt_const.prodMk contDiffWithinAt_id
  have hst : Set.MapsTo (fun y : E => ((0 : ℝ), y)) U ((Set.Ico 0 T) ×ˢ U) :=
    fun _ hy' => ⟨⟨le_refl 0, hT⟩, hy'⟩
  exact ContDiffWithinAt.comp y hcomp hφ hst

end Work.Diff.EXT
