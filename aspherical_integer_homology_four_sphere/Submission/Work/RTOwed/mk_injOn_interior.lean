import Mathlib
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.Atlas
import Submission.Work.FoldInst.Polytope

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.RTOwed

open Work.FoldInst

/-- Every side constraint is strict at every interior point of `Q̄`.

If `sideSlack S y = 0` at an interior point `y`, then `y` has `n_S · y = 1`, and moving from `y`
away from the origin along the line `t ↦ t • y` (which crosses the side hyperplane immediately)
produces points of every neighbourhood of `y` that violate the constraint, contradicting that a
small ball around `y` is contained in `Q̄`. -/
theorem sideSlack_pos_of_mem_interior {y : E4} (hy : y ∈ interior Qbar) (S : Fin 24) :
    0 < sideSlack S y := by
  have hyQ : y ∈ Qbar := interior_subset hy
  by_contra hlt
  have h0 : sideSlack S y = 0 := le_antisymm (le_of_not_gt hlt) (hyQ.1 S)
  have hdot : (∑ i, (sideNormal S i : ℝ) * y i) = 1 := by
    have h := h0
    simp only [sideSlack] at h
    linarith
  obtain ⟨ε, hεpos, hεsub⟩ : ∃ ε > 0, Metric.ball y ε ⊆ Qbar := by
    have hmem : Qbar ∈ nhds y := mem_interior_iff_mem_nhds.mp hy
    rwa [Metric.mem_nhds_iff] at hmem
  set t : ℝ := 1 + ε / (2 * (‖y‖ + 1)) with htdef
  have hden : (0 : ℝ) < 2 * (‖y‖ + 1) := by positivity
  have ht1 : 1 < t := by
    have : 0 < ε / (2 * (‖y‖ + 1)) := by positivity
    rw [htdef]; linarith
  have htdiff : t - 1 = ε / (2 * (‖y‖ + 1)) := by rw [htdef]; ring
  have hball : t • y ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : t • y - y = (t - 1) • y := by rw [sub_smul, one_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1), htdiff]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [norm_nonneg y, hεpos]
  have hQ : t • y ∈ Qbar := hεsub hball
  have hslack : sideSlack S (t • y) = 1 - t := by
    simp only [sideSlack]
    have hsum : (∑ i, (sideNormal S i : ℝ) * (t • y) i) =
        t * ∑ i, (sideNormal S i : ℝ) * y i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hsum, hdot]; ring
  have hle : 0 ≤ sideSlack S (t • y) := hQ.1 S
  rw [hslack] at hle
  linarith

/-- The identification group is trivial at an interior point of `Q̄`: no side is tight. -/
theorem Ksub_eq_bot_of_mem_interior {y : E4} (hy : y ∈ interior Qbar) : Ksub y = ⊥ := by
  unfold Ksub
  have hset : {γ : Gg | ∃ S : Fin 24, sideSlack S y = 0 ∧ γ = sideType S} = (∅ : Set Gg) := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro S hS _
    exact (ne_of_gt (sideSlack_pos_of_mem_interior hy S)) hS
  rw [hset, AddSubgroup.closure_empty]

theorem mk_injOn_interior :
    Set.InjOn Work.FoldInst.mk {x : Work.FoldInst.Xbar | x.2.1 ∈ interior Work.FoldInst.Qbar} := by
  intro x hx y hy hxy
  have hrel : rel x y := Quotient.exact hxy
  obtain ⟨γ, hγ, hγx⟩ := hrel
  have hbot : Ksub x.2.1 = ⊥ := Ksub_eq_bot_of_mem_interior hx
  rw [hbot] at hγ
  have hγ0 : γ = 0 := AddSubgroup.mem_bot.mp hγ
  subst hγ0
  rw [actX_zero] at hγx
  exact hγx

end Work.RTOwed
