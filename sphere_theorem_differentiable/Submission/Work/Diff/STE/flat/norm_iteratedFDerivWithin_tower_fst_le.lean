import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

theorem norm_iteratedFDerivWithin_tower_fst_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {I : Set ℝ} (hI : UniqueDiffOn ℝ I) (hIY : UniqueDiffOn ℝ (I ×ˢ (Set.univ : Set Y)))
    {c w : ℕ → ℝ → V} {k : ℕ} (hc : ContDiffOn ℝ k (c 0) I)
    (hid : ∀ t ∈ I,
      iteratedFDerivWithin ℝ k (c 0) I t = ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (w k t))
    (p : ℝ × Y) (hp : p ∈ I ×ˢ Set.univ) :
    ‖iteratedFDerivWithin ℝ k (fun p : ℝ × Y => c 0 p.1) (I ×ˢ Set.univ) p‖
      ≤ ‖w k p.1‖ := by
  -- `I ×ˢ univ` is the preimage of `I` under the first projection
  have hset : (I ×ˢ (Set.univ : Set Y)) = Prod.fst ⁻¹' I := by
    ext p; simp
  -- the `k`-th derivative of `p ↦ c 0 p.1` is the `k`-th derivative of `c 0`, composed with
  -- the (linear) first projection
  have hcomp : iteratedFDerivWithin ℝ k (fun p : ℝ × Y => c 0 p.1) (I ×ˢ Set.univ) p
      = (iteratedFDerivWithin ℝ k (c 0) I p.1).compContinuousLinearMap
          (fun _ : Fin k => ContinuousLinearMap.fst ℝ ℝ Y) := by
    rw [hset,
      show (fun p : ℝ × Y => c 0 p.1) = (c 0) ∘ ⇑(ContinuousLinearMap.fst ℝ ℝ Y) from rfl]
    exact ContinuousLinearMap.iteratedFDerivWithin_comp_right _ hc hI (hset ▸ hIY) hp.1 le_rfl
  rw [hcomp, hid p.1 hp.1]
  -- `‖mkPiRing z‖ = ‖z‖` and composing with the projection does not increase the norm
  calc ‖(ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (w k p.1)).compContinuousLinearMap
          (fun _ : Fin k => ContinuousLinearMap.fst ℝ ℝ Y)‖
      ≤ ‖ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (w k p.1)‖ *
          ∏ _ : Fin k, ‖ContinuousLinearMap.fst ℝ ℝ Y‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖w k p.1‖ * ∏ _ : Fin k, ‖ContinuousLinearMap.fst ℝ ℝ Y‖ := by
        rw [ContinuousMultilinearMap.norm_mkPiRing]
    _ ≤ ‖w k p.1‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [show (∏ _ : Fin k, ‖ContinuousLinearMap.fst ℝ ℝ Y‖)
              = ‖ContinuousLinearMap.fst ℝ ℝ Y‖ ^ k by
              rw [Finset.prod_const]; simp]
        exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ Y)
    _ = ‖w k p.1‖ := mul_one _

end Work.Diff.STE.flat
