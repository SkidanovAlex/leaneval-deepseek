import Mathlib.Analysis.Normed.Group.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

-- `hδ` and `hZ` are part of the requested statement but are not needed by the argument
-- (only the *local* data at the base point is used).
set_option linter.unusedVariables false

theorem continuousOn_slab_of_lipschitz {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 ≤ δ)
    {g : ℝ → ℝ × ℝ → E} {Z : Set (ℝ × ℝ)} (hZ : IsOpen Z)
    (hcont : ∀ τ ∈ Set.Icc 0 δ, ContinuousOn (g τ) Z)
    (hlip : ∀ q ∈ Z, ∃ K : ℝ, 0 ≤ K ∧ ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧
      ∀ q' ∈ U, ∀ τ ∈ Set.Icc 0 δ, ∀ τ' ∈ Set.Icc 0 δ, ‖g τ q' - g τ' q'‖ ≤ K * |τ - τ'|) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => g p.2.2 (p.1, p.2.1))
      {p : ℝ × (ℝ × ℝ) | (p.1, p.2.1) ∈ Z ∧ p.2.2 ∈ Set.Icc 0 δ} := by
  -- The function is `p ↦ g p.2.2 (p.1, p.2.1)`.  At a base point `p` of the slab,
  -- it is continuous in the space variable `(p.1, p.2.1)` at the frozen time `p.2.2`
  -- (hypothesis `hcont`), and locally `τ`-Lipschitz with a constant valid on an open
  -- neighbourhood `U` of `(p.1, p.2.1)` (hypothesis `hlip`); an `ε/2`-argument closes
  -- the two pieces.
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro e he
  obtain ⟨hZq, hτp⟩ := hp
  -- the local Lipschitz data at the space-time point `(p.1, p.2.1) ∈ Z`
  obtain ⟨K, hK0, U, hUopen, hqU, hlipU⟩ := hlip (p.1, p.2.1) hZq
  obtain ⟨r, hrpos, hrU⟩ := Metric.isOpen_iff.mp hUopen (p.1, p.2.1) hqU
  -- the per-slice continuity at the frozen time `p.2.2`
  have hcontq : ContinuousWithinAt (g p.2.2) Z (p.1, p.2.1) :=
    (hcont p.2.2 hτp) (p.1, p.2.1) hZq
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp hcontq (e / 2) (by linarith)
  have hcpos : 0 < e / (2 * (K + 1)) := div_pos he (by linarith)
  refine ⟨min δ₁ (min r (e / (2 * (K + 1)))), lt_min hδ₁pos (lt_min hrpos hcpos), ?_⟩
  intro x hx hdist
  obtain ⟨hZx, hτx⟩ := hx
  -- the metric `dist` on `ℝ × (ℝ × ℝ)`, in coordinates
  have hxd : dist x p = max (dist x.1 p.1) (max (dist x.2.1 p.2.1) (dist x.2.2 p.2.2)) := by
    rw [Prod.dist_eq, Prod.dist_eq]
  have hle_inner : dist (x.1, x.2.1) (p.1, p.2.1) ≤ dist x p := by
    rw [hxd, Prod.dist_eq]
    exact max_le (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  -- the time difference is small ...
  have hτsmall : dist x.2.2 p.2.2 < e / (2 * (K + 1)) := by
    have hle : dist x.2.2 p.2.2 ≤ dist x p := by
      rw [hxd]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hle
      (lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- ... the space difference is small ...
  have hspace : dist (x.1, x.2.1) (p.1, p.2.1) < δ₁ :=
    lt_of_le_of_lt hle_inner (lt_of_lt_of_le hdist (min_le_left _ _))
  -- ... and small enough that `(x.1, x.2.1)` lies in the Lipschitz neighbourhood
  have hUmem : (x.1, x.2.1) ∈ U := by
    refine hrU ?_
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hle_inner
      (lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _)))
  -- the frozen-slice continuity
  have hslice : dist (g p.2.2 (x.1, x.2.1)) (g p.2.2 (p.1, p.2.1)) < e / 2 :=
    hδ₁ hZx hspace
  -- the Lipschitz-in-`τ` piece
  have htime : dist (g x.2.2 (x.1, x.2.1)) (g p.2.2 (x.1, x.2.1)) < e / 2 := by
    rw [dist_eq_norm]
    have h1 : ‖g x.2.2 (x.1, x.2.1) - g p.2.2 (x.1, x.2.1)‖ ≤ K * |x.2.2 - p.2.2| :=
      hlipU (x.1, x.2.1) hUmem x.2.2 hτx p.2.2 hτp
    have h2 : |x.2.2 - p.2.2| < e / (2 * (K + 1)) := by
      rw [← Real.dist_eq]
      exact hτsmall
    refine lt_of_le_of_lt h1 ?_
    have h3 : K * |x.2.2 - p.2.2| ≤ K * (e / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left h2.le hK0
    refine lt_of_le_of_lt h3 ?_
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (K + 1))]
    nlinarith [he]
  have htri := dist_triangle (g x.2.2 (x.1, x.2.1)) (g p.2.2 (x.1, x.2.1))
    (g p.2.2 (p.1, p.2.1))
  linarith

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
