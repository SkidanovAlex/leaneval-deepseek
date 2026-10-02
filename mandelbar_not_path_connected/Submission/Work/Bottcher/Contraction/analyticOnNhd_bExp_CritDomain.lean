/-
# Analyticity of the Böttcher exponent series on the critical domain

`Work.Bottcher.Contraction.analyticOnNhd_bExp` proves that the series

`bExp c L z = Σ_{k ≥ 0} 4^{-(k+1)} L (p_c^k z)`

is analytic on the escape set `EscapeSet c = {z | G_c z > 0}`, assuming `L` is analytic
there and vanishes at infinity.  The present lemma is the same statement with the escape
set replaced by the *critical domain* `CritDomain c = {z | G_c z > G_c(0)}`.

This is genuinely stronger *in its hypothesis* (`CritDomain c ⊆ EscapeSet c`, so
`AnalyticOnNhd ℂ L (CritDomain c)` is weaker than `AnalyticOnNhd ℂ L (EscapeSet c)`),
and the same proof goes through: near a point `z₀ ∈ CritDomain c` we pick
`δ = (G_c(0) + G_c z₀)/2`, so that `G_c(0) < δ < G_c z₀`, and work on the open
neighbourhood

`U = {z | δ < G_c z}`.

Then `U ⊆ CritDomain c` (so `L` is analytic, hence continuous, on the closure
`{δ ≤ G_c z}` and on `U`) and `U` is forward invariant under `p_c` because
`G_c(p_c z) = 4 G_c z > G_c z > δ`.  Each term of the series is holomorphic on `U` and
dominated by a summable geometric sequence, giving the result by Weierstrass' theorem.
-/
import Mathlib
import Submission.Work.Bottcher.Contraction.exists_analyticBottcher_of_mem_mandelbar
import Submission.Work.Bottcher.Contraction.analyticOnNhd_bExp
import Submission.Work.Bottcher.CritBasic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Metric
open scoped Topology

namespace Work.Bottcher.Contraction

theorem analyticOnNhd_bExp_CritDomain (c : ℂ) {L : ℂ → ℂ}
    (hLan : AnalyticOnNhd ℂ L (Work.Bottcher.CritDomain c))
    (hLt : Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ))) :
    AnalyticOnNhd ℂ (Work.Bottcher.Contraction.bExp c L) (Work.Bottcher.CritDomain c) := by
  intro z₀ hz₀
  rw [Work.Bottcher.mem_CritDomain] at hz₀
  -- `hz₀ : greenParam c < green c z₀`
  have hcontG : Continuous (Work.Bottcher.green c) := continuous_green_bottcher c
  set δ : ℝ := (Work.Bottcher.greenParam c + Work.Bottcher.green c z₀) / 2 with hδdef
  have hδgt : Work.Bottcher.greenParam c < δ := by rw [hδdef]; linarith
  have hδlt : δ < Work.Bottcher.green c z₀ := by rw [hδdef]; linarith
  have hδpos : 0 < δ :=
    lt_of_le_of_lt (Work.Bottcher.Green.green_nonneg c 0) hδgt
  -- the neighbourhood `U` and its basic properties
  have hUopen : IsOpen {z : ℂ | δ < Work.Bottcher.green c z} :=
    isOpen_lt continuous_const hcontG
  have hz₀U : z₀ ∈ {z : ℂ | δ < Work.Bottcher.green c z} := hδlt
  have hUsubCrit : {z : ℂ | δ < Work.Bottcher.green c z} ⊆ Work.Bottcher.CritDomain c := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rw [Work.Bottcher.mem_CritDomain]
    exact lt_trans hδgt hz
  -- forward invariance of `U` under `p_c`
  have hiter : ∀ (k : ℕ) (z : ℂ), δ < Work.Bottcher.green c z →
      δ < Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) := by
    intro k z hz
    rw [green_pMap_iterate]
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num) (n := k)
    have h0 : 0 ≤ Work.Bottcher.green c z := by linarith
    exact lt_of_lt_of_le hz (le_mul_of_one_le_left h0 h4)
  -- each term of the series is holomorphic on `U`
  have hterm : ∀ k : ℕ, DifferentiableOn ℂ
      (fun w : ℂ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] w))
      {z : ℂ | δ < Work.Bottcher.green c z} := by
    intro k w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hwcrit : (Work.Bottcher.pMap c)^[k] w ∈ Work.Bottcher.CritDomain c :=
      hUsubCrit (hiter k w hw)
    have hLd : DifferentiableAt ℂ L ((Work.Bottcher.pMap c)^[k] w) :=
      (hLan _ hwcrit).differentiableAt
    have hpd : DifferentiableAt ℂ ((Work.Bottcher.pMap c)^[k]) w :=
      ((differentiable_pMap c).iterate k).differentiableAt
    exact ((hLd.comp w hpd).const_mul _).differentiableWithinAt
  -- a uniform bound for `L` on the closed superlevel set `{δ ≤ G_c}`
  have hSclosed : IsClosed {z : ℂ | δ ≤ Work.Bottcher.green c z} :=
    isClosed_le continuous_const hcontG
  have hScont : ContinuousOn L {z : ℂ | δ ≤ Work.Bottcher.green c z} := by
    refine hLan.analyticOn.continuousOn.mono ?_
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rw [Work.Bottcher.mem_CritDomain]
    exact lt_of_lt_of_le hδgt hz
  obtain ⟨M, -, hM⟩ := exists_bound_of_tendsto_cocompact hScont hSclosed hLt
  -- the dominating summable sequence
  have hu : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1) * M) := by
    have h : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k * ((1 / 4 : ℝ) * M)) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_right ((1 / 4 : ℝ) * M)
    convert h using 1
    funext k
    rw [pow_succ]
    ring
  have hF_le : ∀ (k : ℕ) (w : ℂ),
      w ∈ {z : ℂ | δ < Work.Bottcher.green c z} →
      ‖((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] w)‖
        ≤ (1 / 4 : ℝ) ^ (k + 1) * M := by
    intro k w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hpk : δ ≤ Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] w) :=
      le_of_lt (hiter k w hw)
    rw [norm_mul]
    have hnorm : ‖(((1 / 4 : ℝ) ^ (k + 1)) : ℂ)‖ = (1 / 4 : ℝ) ^ (k + 1) := by simp
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hM _ hpk) (by positivity)
  have hdiffOn : DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z))
      {z : ℂ | δ < Work.Bottcher.green c z} :=
    Complex.differentiableOn_tsum_of_summable_norm
      (F := fun k w => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] w))
      hu hterm hUopen hF_le
  change AnalyticAt ℂ
      (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) z₀
  exact hdiffOn.analyticAt (hUopen.mem_nhds hz₀U)

end Work.Bottcher.Contraction
