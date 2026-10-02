import Mathlib
import Submission.Work.GATE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The whole orbit of a point above the critical potential is in the critical domain.**  If the
`j`-th iterate of `z` under the high return map `F_c = (T_c)^{10}` has Green function exceeding
`1024^j · G_c(0)` (equivalently, since `G_c(F_c^[j] z) = 1024^j G_c z`: `z` itself is in the
critical domain), then every iterate `F_c^[i] z`, `i ≤ j`, is in the critical domain of `c`.

The proof is immediate from the Green functional equation `G_c(F_c^[i] z) = 1024^i G_c z`
(`green_comm_iterate` at `T_c = (F_c)^{1/10}`, i.e. `F_eq_tantibar` followed by
`Function.iterate_mul`) and the monotonicity of `G_c`.

This is item (A3) of the design `NOTES_LEAD_mandelbar_gate2transport.md` §3. -/
theorem mem_critDomain_iterate {c z : ℂ} {j : ℕ}
    (h : (1024 : ℝ) ^ j * Work.Bottcher.green c 0 <
      Work.Bottcher.green c ((Work.EL.F c)^[j] z)) :
    ∀ i ≤ j, (Work.EL.F c)^[i] z ∈ Work.ParamRays.critDomain c := by
  -- The Green function of the `F_c`-orbit: `G_c(F_c^[i] z) = 1024^i · G_c z`.
  have hpow : ∀ i : ℕ, Work.Bottcher.green c ((Work.EL.F c)^[i] z)
      = (1024 : ℝ)^i * Work.Bottcher.green c z := by
    intro i
    rw [Work.EL.F_eq_tantibar, ← Function.iterate_mul,
      Work.Bottcher.Contraction.green_comm_iterate, pow_mul]
    norm_num
  -- The critical potential is nonnegative.
  have hg0 : (0 : ℝ) ≤ Work.Bottcher.green c 0 := Work.Bottcher.Green.green_nonneg c 0
  -- The hypothesis, with the `j`-th iterate expanded, says
  -- `1024^j · G_c 0 < 1024^j · G_c z`, hence `G_c 0 < G_c z` (the factor is positive).
  have hh : (1024 : ℝ)^j * Work.Bottcher.green c 0
      < (1024 : ℝ)^j * Work.Bottcher.green c z := by
    rw [← hpow j]; exact h
  have hpos : (0 : ℝ) < (1024 : ℝ)^j := pow_pos (by norm_num) j
  have hz : Work.Bottcher.green c 0 < Work.Bottcher.green c z :=
    lt_of_mul_lt_mul_left hh hpos.le
  -- Consequently `G_c 0 ≤ 1024^i · G_c z` for every `i`, which is membership in `critDomain c`.
  intro i _
  have hge : Work.Bottcher.green c z ≤ (1024 : ℝ)^i * Work.Bottcher.green c z := by
    have h1 : (1 : ℝ) ≤ (1024 : ℝ)^i := one_le_pow₀ (by norm_num)
    calc Work.Bottcher.green c z = 1 * Work.Bottcher.green c z := (one_mul _).symm
      _ ≤ (1024 : ℝ)^i * Work.Bottcher.green c z :=
          mul_le_mul_of_nonneg_right h1 (le_trans hg0 hz.le)
  rw [← Work.Bottcher.CritBasic.critDomain_eq, Work.Bottcher.mem_CritDomain,
    Work.Bottcher.greenParam_def]
  rw [hpow i]
  linarith

end Work.GATE2.PathTransport
