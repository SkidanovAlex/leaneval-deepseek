/-
# Analyticity of the "Böttcher correction series" `Σ_k 4^{-(k+1)} L(p_c^k z)`

For the monic quartic `p_c(z) = (z^2 + conj c)^2 + c = T_c^2(z)` we consider the series

`bExp z = Σ_{k ≥ 0} 4^{-(k+1)} L (p_c^k z)`,

where `L : ℂ → ℂ` is holomorphic on the escape set `EscapeSet c = {z | G_c z > 0}` and
tends to `0` at infinity.  The goal is `analyticOnNhd_bExp`: `bExp` is analytic (near every
point) of the escape set.

The two structural facts that make this work are

* the escape set is forward invariant and the Green function is multiplicative along the
  orbit: `G_c (p_c z) = 4 G_c z` (`green_pMap`), so that a superlevel set
  `{G_c > δ}` is mapped into itself by every iterate `p_c^k`; and
* `L`, being continuous on the escape set and vanishing at infinity, is bounded on every
  closed superlevel set `{G_c ≥ δ}` (`exists_bound_of_tendsto_cocompact`).

Consequently, near a point `z₀` with `δ = G_c(z₀)/2`, every term
`w ↦ 4^{-(k+1)} L (p_c^k w)` is holomorphic on the common open neighbourhood
`U = {G_c > δ}` and is dominated there by the summable sequence `4^{-(k+1)} M`, where
`M` bounds `‖L‖` on `{G_c ≥ δ}`.  Weierstrass' theorem for series with a summable uniform
bound (`Complex.differentiableOn_tsum_of_summable_norm`) then gives differentiability on
`U`, hence analyticity at `z₀`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Escape.Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Metric
open scoped Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.Bottcher.Contraction

variable {c : ℂ}

/-! ## The Green function and the second iterate -/

/-- The Green function of the tricorn family is continuous (re-exported from the escape
chapter). -/
theorem continuous_green_bottcher (c : ℂ) : Continuous (Work.Bottcher.green c) :=
  Work.Escape.continuous_green_Tantibar c

/-- The second iterate `p_c = T_c ∘ T_c` is differentiable (it is a polynomial). -/
theorem differentiable_pMap (c : ℂ) : Differentiable ℂ (Work.Bottcher.pMap c) := by
  change Differentiable ℂ (fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c)
  fun_prop

/-- **The Green function is multiplied by `4` under `p_c`**: `G_c(p_c z) = 4 G_c z`.
This is `green_comm` applied twice, since `p_c` is the second iterate of `T_c`. -/
theorem green_pMap (c z : ℂ) :
    Work.Bottcher.green c (Work.Bottcher.pMap c z) = 4 * Work.Bottcher.green c z := by
  have hpm : Work.Bottcher.pMap c z = Tantibar c (Tantibar c z) := by
    rw [Work.Bottcher.pMap_eq_iterate_two]
    rfl
  rw [hpm, Work.Bottcher.Green.green_comm, Work.Bottcher.Green.green_comm]
  ring

/-- **Iterated form**: `G_c(p_c^k z) = 4^k G_c z`. -/
theorem green_pMap_iterate (c z : ℂ) (k : ℕ) :
    Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) = 4 ^ k * Work.Bottcher.green c z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', green_pMap, ih, pow_succ]
      ring

/-! ## Forward invariance of the escape set -/

/-- The escape set is forward invariant under `p_c`. -/
theorem pMap_mem_EscapeSet (c : ℂ) {z : ℂ} (hz : z ∈ Work.Bottcher.EscapeSet c) :
    Work.Bottcher.pMap c z ∈ Work.Bottcher.EscapeSet c := by
  rw [Work.Bottcher.mem_EscapeSet] at hz ⊢
  rw [green_pMap]
  linarith

/-- Every iterate of a point of the escape set stays in the escape set. -/
theorem pMap_iterate_mem_EscapeSet (c : ℂ) {z : ℂ} (hz : z ∈ Work.Bottcher.EscapeSet c) (k : ℕ) :
    (Work.Bottcher.pMap c)^[k] z ∈ Work.Bottcher.EscapeSet c := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact pMap_mem_EscapeSet c ih

/-! ## Boundedness of a continuous function vanishing at infinity -/

/-- **A function that is continuous on a closed set and tends to `0` at infinity is bounded on
that set.**  Take a compact `K` outside which `‖L‖ < 1` (from `Tendsto L (cocompact ℂ) (nhds 0)`)
and a ball containing `K`; then `S ∩ closedBall 0 R` is compact, and `L` is continuous on it. -/
theorem exists_bound_of_tendsto_cocompact {L : ℂ → ℂ} {S : Set ℂ}
    (hcont : ContinuousOn L S) (hS : IsClosed S)
    (hLt : Filter.Tendsto L (Filter.cocompact ℂ) (nhds 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ S, ‖L z‖ ≤ M := by
  obtain ⟨K, hKc, hKsub⟩ :=
    Filter.mem_cocompact.mp (by
      have h' := Filter.le_def.mp hLt (Metric.ball (0 : ℂ) 1) (Metric.ball_mem_nhds 0 one_pos)
      rwa [Filter.mem_map] at h')
  have hKsmall : ∀ z, z ∉ K → ‖L z‖ < 1 := by
    intro z hz
    have h := hKsub hz
    simp only [Set.mem_preimage, Metric.mem_ball] at h
    rwa [dist_zero_right] at h
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
  have hT : IsCompact (Metric.closedBall (0 : ℂ) R ∩ S) :=
    (isCompact_closedBall 0 R).inter_right hS
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn (hcont.mono Set.inter_subset_right)
  refine ⟨max C 1, le_trans zero_le_one (le_max_right C 1), fun z hz => ?_⟩
  by_cases hzR : z ∈ Metric.closedBall (0 : ℂ) R
  · exact le_trans (hC z ⟨hzR, hz⟩) (le_max_left C 1)
  · have hzK : z ∉ K := fun h => hzR (hR h)
    exact le_trans (le_of_lt (hKsmall z hzK)) (le_max_right C 1)

/-! ## The main theorem -/

theorem analyticOnNhd_bExp (c : ℂ) {L : ℂ → ℂ}
    (hLan : AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c))
    (hLt : Filter.Tendsto L (Filter.cocompact ℂ) (nhds 0)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))
      (Work.Bottcher.EscapeSet c) := by
  intro z₀ hz₀
  rw [Work.Bottcher.mem_EscapeSet] at hz₀
  have hcontG : Continuous (Work.Bottcher.green c) := continuous_green_bottcher c
  have hLan_cont : ContinuousOn L (Work.Bottcher.EscapeSet c) := hLan.analyticOn.continuousOn
  have hδpos : 0 < Work.Bottcher.green c z₀ / 2 := by linarith
  -- The open neighbourhood of `z₀` on which everything happens
  have hUopen : IsOpen {z : ℂ | Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z} :=
    isOpen_lt continuous_const hcontG
  have hz₀U : z₀ ∈ {z : ℂ | Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z} :=
    show Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z₀ from by linarith
  -- Escape-set membership and forward invariance of the superlevel set
  have hsub : ∀ z : ℂ,
      Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z → z ∈ Work.Bottcher.EscapeSet c := by
    intro z hz
    rw [Work.Bottcher.mem_EscapeSet]
    linarith
  have hiter : ∀ (k : ℕ) (z : ℂ), Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z →
      Work.Bottcher.green c z₀ / 2
        < Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) := by
    intro k z hz
    rw [green_pMap_iterate]
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num) (n := k)
    have h0 : 0 ≤ Work.Bottcher.green c z := by linarith
    have hle : Work.Bottcher.green c z ≤ (4 : ℝ) ^ k * Work.Bottcher.green c z :=
      le_mul_of_one_le_left h0 h4
    linarith
  -- Each term of the series is holomorphic on `U`
  have hterm : ∀ k : ℕ, DifferentiableOn ℂ
      (fun w : ℂ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] w))
      {z : ℂ | Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z} := by
    intro k w hw
    have hwesc : (Work.Bottcher.pMap c)^[k] w ∈ Work.Bottcher.EscapeSet c := hsub _ (hiter k w hw)
    have hLd : DifferentiableAt ℂ L ((Work.Bottcher.pMap c)^[k] w) :=
      (hLan _ hwesc).differentiableAt
    have hpd : DifferentiableAt ℂ ((Work.Bottcher.pMap c)^[k]) w :=
      ((differentiable_pMap c).iterate k).differentiableAt
    exact ((hLd.comp w hpd).const_mul _).differentiableWithinAt
  -- A uniform bound for `L` on the closed superlevel set `{δ ≤ G_c}`
  have hSclosed : IsClosed {z : ℂ | Work.Bottcher.green c z₀ / 2 ≤ Work.Bottcher.green c z} :=
    isClosed_le continuous_const hcontG
  have hScont : ContinuousOn L {z : ℂ | Work.Bottcher.green c z₀ / 2 ≤ Work.Bottcher.green c z} :=
    hLan_cont.mono (fun z hz => by
      have hz' : Work.Bottcher.green c z₀ / 2 ≤ Work.Bottcher.green c z := hz
      rw [Work.Bottcher.mem_EscapeSet]
      linarith)
  obtain ⟨M, -, hM⟩ := exists_bound_of_tendsto_cocompact hScont hSclosed hLt
  -- The dominating summable sequence
  have hu : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1) * M) := by
    have h : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k * ((1 / 4 : ℝ) * M)) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_right ((1 / 4 : ℝ) * M)
    convert h using 1
    funext k
    rw [pow_succ]
    ring
  have hF_le : ∀ (k : ℕ) (w : ℂ),
      w ∈ {z : ℂ | Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z} →
      ‖((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] w)‖
        ≤ (1 / 4 : ℝ) ^ (k + 1) * M := by
    intro k w hw
    have hpk : Work.Bottcher.green c z₀ / 2
        ≤ Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] w) := le_of_lt (hiter k w hw)
    rw [norm_mul]
    have hnorm : ‖(((1 / 4 : ℝ) ^ (k + 1)) : ℂ)‖ = (1 / 4 : ℝ) ^ (k + 1) := by simp
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hM _ hpk) (by positivity)
  have hdiffOn : DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))
      {z : ℂ | Work.Bottcher.green c z₀ / 2 < Work.Bottcher.green c z} :=
    Complex.differentiableOn_tsum_of_summable_norm
      (F := fun k w => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] w))
      hu hterm hUopen hF_le
  exact hdiffOn.analyticAt (hUopen.mem_nhds hz₀U)

end Work.Bottcher.Contraction
