import Mathlib
import Submission.Work.NAKANE.GreenJoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Metric Set
open scoped Topology

namespace Work.GATE2.D1

/-- **Green comparison near a compactum.**  If the Green function `G_{c₀}` is strictly positive on
a compact set `K ⊆ ℂ`, then the pointwise comparison `(3/4) G_{c₀} w₀ ≤ G_{c₀} z₀` between two
points of `K` is stable, *uniformly over `K`*, under small perturbations of the parameter
(`e` near `c₀`) and of the points (`z` near `z₀`, `w` near `w₀`): close by, `G_e w < 2 G_e z`.

The proof is a Heine–Cantor argument: `G` is jointly continuous
(`Work.NAKANE.GreenJoint.continuous_jointGreen`), the compactness of `K` supplies a positive lower
bound `m > 0` for `G_{c₀}` on `K`
(`IsCompact.exists_forall_le'`), and joint continuity is *uniform* on the compact set
`closedBall c₀ 1 ×ˢ cthickening 1 K`.  With `ε = m/9`, perturbing changes each Green value by less
than `ε`, and the numerical inequality then follows from `G_{c₀} z₀ ≥ m`, which gives the margin
`3 ε < (2/3) G_{c₀} z₀` needed to absorb the factor `4/3`. -/
theorem green_comparison_near_compactum {c₀ : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hpos : ∀ z ∈ K, 0 < Work.Bottcher.green c₀ z) :
    ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ e : ℂ, ‖e - c₀‖ < ρ →
        ∀ z₀ ∈ K, ∀ w₀ ∈ K,
          (3 / 4 : ℝ) * Work.Bottcher.green c₀ w₀ ≤ Work.Bottcher.green c₀ z₀ →
          ∀ z w : ℂ, ‖z - z₀‖ < η → ‖w - w₀‖ < η →
            Work.Bottcher.green e w < 2 * Work.Bottcher.green e z := by
  -- Joint continuity of the Green function, restricted to the parameter `c₀`.
  have hcont : Continuous fun z : ℂ => Work.Bottcher.green c₀ z := by
    have h := Work.NAKANE.GreenJoint.continuous_jointGreen
    have h2 : Continuous fun z : ℂ => Work.NAKANE.jointGreen (c₀, z) :=
      h.comp (continuous_const.prodMk continuous_id)
    simpa only [Work.NAKANE.jointGreen_apply, Work.Bottcher.green_def] using h2
  -- A positive lower bound `m` for `G_{c₀}` on the compact set `K`.
  obtain ⟨m, hm_pos, hm⟩ := hK.exists_forall_le' hcont.continuousOn (fun z hz => hpos z hz)
  -- The accuracy with which we control the Green function.
  set ε : ℝ := m / 9 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- Heine–Cantor on the compact block `closedBall c₀ 1 ×ˢ cthickening 1 K`.
  have hK₁c : IsCompact (cthickening (1:ℝ) K) := hK.cthickening
  have hS : IsCompact (closedBall c₀ (1:ℝ) ×ˢ cthickening (1:ℝ) K) :=
    (isCompact_closedBall c₀ 1).prod hK₁c
  have huc := hS.uniformContinuousOn_of_continuous
    (Work.NAKANE.GreenJoint.continuous_jointGreen.continuousOn)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc ε hεpos
  set r : ℝ := min 1 (δ / 3) with hr
  have hrpos : 0 < r := by rw [hr]; exact lt_min one_pos (by linarith)
  refine ⟨r, hrpos, r, hrpos, ?_⟩
  intro e he z₀ hz₀ w₀ hw₀ hratio z w hz hw
  have her : dist e c₀ < r := by rw [dist_eq_norm]; exact he
  have hzr : dist z z₀ < r := by rw [dist_eq_norm]; exact hz
  have hwr : dist w w₀ < r := by rw [dist_eq_norm]; exact hw
  have hr1 : r ≤ 1 := by rw [hr]; exact min_le_left _ _
  have hr3 : r ≤ δ / 3 := by rw [hr]; exact min_le_right _ _
  have he1 : dist e c₀ < 1 := lt_of_lt_of_le her hr1
  have hz1 : dist z z₀ < 1 := lt_of_lt_of_le hzr hr1
  have hw1 : dist w w₀ < 1 := lt_of_lt_of_le hwr hr1
  have hmK : c₀ ∈ closedBall c₀ (1:ℝ) := by simp
  have hmem_ez : (e, z) ∈ closedBall c₀ (1:ℝ) ×ˢ cthickening (1:ℝ) K :=
    ⟨mem_closedBall.mpr (le_of_lt he1),
     mem_cthickening_of_dist_le z z₀ 1 K hz₀ (le_of_lt hz1)⟩
  have hmem_z0 : (c₀, z₀) ∈ closedBall c₀ (1:ℝ) ×ˢ cthickening (1:ℝ) K :=
    ⟨hmK, self_subset_cthickening K hz₀⟩
  have hmem_ew : (e, w) ∈ closedBall c₀ (1:ℝ) ×ˢ cthickening (1:ℝ) K :=
    ⟨mem_closedBall.mpr (le_of_lt he1),
     mem_cthickening_of_dist_le w w₀ 1 K hw₀ (le_of_lt hw1)⟩
  have hmem_w0 : (c₀, w₀) ∈ closedBall c₀ (1:ℝ) ×ˢ cthickening (1:ℝ) K :=
    ⟨hmK, self_subset_cthickening K hw₀⟩
  have hdist1 : dist (e, z) (c₀, z₀) < δ := by
    rw [Prod.dist_eq]
    refine lt_of_lt_of_le (max_lt (lt_of_lt_of_le her hr3) (lt_of_lt_of_le hzr hr3)) ?_
    linarith
  have hdist2 : dist (e, w) (c₀, w₀) < δ := by
    rw [Prod.dist_eq]
    refine lt_of_lt_of_le (max_lt (lt_of_lt_of_le her hr3) (lt_of_lt_of_le hwr hr3)) ?_
    linarith
  have h1 := hδ (e, z) hmem_ez (c₀, z₀) hmem_z0 hdist1
  have h2 := hδ (e, w) hmem_ew (c₀, w₀) hmem_w0 hdist2
  have hbridge : ∀ a b : ℂ, Work.NAKANE.jointGreen (a, b) = Work.Bottcher.green a b :=
    fun a b => rfl
  rw [hbridge e z, hbridge c₀ z₀, Real.dist_eq] at h1
  rw [hbridge e w, hbridge c₀ w₀, Real.dist_eq] at h2
  obtain ⟨h1lo, h1hi⟩ := abs_lt.mp h1
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp h2
  have hG : m ≤ Work.Bottcher.green c₀ z₀ := hm z₀ hz₀
  linarith [h1lo, h2hi, hratio, hG, hε, hm_pos]

end Work.GATE2.D1
