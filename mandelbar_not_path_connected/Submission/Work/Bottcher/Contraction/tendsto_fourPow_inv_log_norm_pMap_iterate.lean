/-
# `log ‖p_c^N z‖ / 4^N → G_c(z)` on the escape set

The Green function of the tricorn is defined as the limit
`G_c z = lim_n 2^{-n} log⁺ ‖T_c^[n] z‖` of the *partial* Green functions of the
antiholomorphic map `T_c` (`Work.Escape.green`).  The holomorphic quartic
`p_c = T_c ∘ T_c` (`Work.Bottcher.pMap`) satisfies `p_c^[N] = T_c^[2N]`, so the
sequence `4^{-N} log ‖p_c^[N] z‖` of this file is nothing but the *sub*-sequence
`greenIter (T_c) 2 z (2N)` of the partial Green functions, with `log⁺` replaced by
`log`.

Since `(2^N)^2 = 4^N`, and the `log⁺` and `log` agree once the orbit norm exceeds
`1` — which happens eventually for every point of the escape set — the claim is a
straightforward consequence of `Work.Escape.tendsto_greenIter` (the partial Green
functions converge to `green`) plus the fact that a subsequence of a convergent
sequence converges to the same limit.

This is the "easy half" of the identification of `green` with the logarithm of
the Böttcher coordinate: the modulus of the Böttcher coordinate grows like
`exp (G_c z)` along the `p_c`-orbit.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.green_eq_zero_iff
import Submission.Work.Escape.mem_escapeRegion_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

/-- For `z` in the escape set `{G_c > 0}`, the orbit of `z` under the tricorn map `T_c` is
unbounded, hence some iterate lies in the escaping region `{w | max 2 ‖c‖ < ‖w‖}`; from then on
the orbit norms stay there.  Consequently the *even* iterates `T_c^[2N] z` eventually have norm
`> 1`, which is the only fact about the orbit needed to replace `log⁺` by `log`. -/
private theorem eventually_one_le_norm_Tantibar_iterate_two_mul (c z : ℂ)
    (hz : 0 < Work.Bottcher.green c z) :
    ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ ‖(Tantibar c)^[2 * N] z‖ := by
  have hzg : 0 < Work.Escape.green (Tantibar c) 2 z := hz
  have hMG : Work.Escape.MonicGrowth (Tantibar c) 2 ‖c‖ := Work.Escape.monicGrowth_Tantibar c
  have hzf : z ∉ Work.Escape.filledJulia (Tantibar c) := by
    intro h
    have h1 : Work.Escape.green (Tantibar c) 2 z = 0 :=
      (Work.Escape.green_eq_zero_iff (Tantibar c) 2 ‖c‖ hMG (by norm_num) z).mpr h
    rw [h1] at hzg
    exact lt_irrefl 0 hzg
  have hN0 : ∃ N0 : ℕ, (Tantibar c)^[N0] z ∈ Work.Escape.escapeRegion ‖c‖ := by
    by_contra hc
    exact hzf (Work.Escape.mem_filledJulia_of_norm_le (M := max 2 ‖c‖) fun n =>
      le_of_not_gt fun hlt => hc ⟨n, hlt⟩)
  obtain ⟨N0, hN0⟩ := hN0
  rw [Filter.eventually_atTop]
  refine ⟨N0, fun N hN => ?_⟩
  have hiter : (Tantibar c)^[2 * N - N0] ((Tantibar c)^[N0] z)
      = (Tantibar c)^[2 * N] z := by
    rw [← Function.iterate_add_apply, show 2 * N - N0 + N0 = 2 * N by omega]
  have hin : (Tantibar c)^[2 * N - N0] ((Tantibar c)^[N0] z) ∈ Work.Escape.escapeRegion ‖c‖ :=
    Work.Escape.mem_escapeRegion_iterate (Tantibar c) 2 ‖c‖ hMG (by norm_num) hN0 (2 * N - N0)
  have h2 := Work.Escape.two_lt_norm_of_mem_escapeRegion hin
  rw [← hiter]
  linarith

theorem tendsto_fourPow_inv_log_norm_pMap_iterate (c z : ℂ) (hz : 0 < Work.Bottcher.green c z) :
    Filter.Tendsto (fun N : ℕ => ((4 : ℝ) ^ N)⁻¹ * Real.log ‖(Work.Bottcher.pMap c)^[N] z‖)
      Filter.atTop (nhds (Work.Bottcher.green c z)) := by
  have hMG : Work.Escape.MonicGrowth (Tantibar c) 2 ‖c‖ := Work.Escape.monicGrowth_Tantibar c
  -- `4^N = (2^N)^2`, so the normalising factors agree with those of `greenIter`.
  have h4 : ∀ N : ℕ, ((4 : ℝ) ^ N)⁻¹ = (((2 : ℕ) : ℝ) ^ (2 * N))⁻¹ := by
    intro N
    congr 1
    rw [show (4 : ℝ) = ((2 : ℕ) : ℝ) ^ 2 by norm_num, ← pow_mul]
  -- On the escaping set the orbit norms exceed `1` eventually, so `log⁺ = log` there.
  have hev1 := eventually_one_le_norm_Tantibar_iterate_two_mul c z hz
  have heq : (fun N : ℕ => ((4 : ℝ) ^ N)⁻¹ * Real.log ‖(Work.Bottcher.pMap c)^[N] z‖)
      =ᶠ[Filter.atTop]
      (fun N : ℕ => Work.Escape.greenIter (Tantibar c) 2 z (2 * N)) := by
    filter_upwards [hev1] with N hN
    rw [Work.Escape.greenIter_eq_of_one_le hN, Work.Bottcher.pMap_iterate, h4 N]
  -- the partial Green functions converge; pass to the even subsequence.
  have hconv : Filter.Tendsto (Work.Escape.greenIter (Tantibar c) 2 z) Filter.atTop
      (nhds (Work.Escape.green (Tantibar c) 2 z)) :=
    Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖ hMG (by norm_num) z
  have h2N : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr
      (fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a (by norm_num))⟩)
  exact Filter.Tendsto.congr' heq.symm (hconv.comp h2N)

end Work.Bottcher.Contraction
