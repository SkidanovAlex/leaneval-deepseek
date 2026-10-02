import Mathlib
import Submission.Work.SeedLimit.Defs
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedLimit

/-- The critical points of the holomorphic `5`-th return map `(Tsq c)^[5] = T_c^[10]` are exactly
the points whose `T_c`-orbit hits the critical point `0` within `10` steps.  Indeed
`(Tsq c)^[j] = (T_c)^[2j]` and `deriv (Tsq c) w = 4 * w * conj (T_c w)`, so a critical point of the
iterate is a point where some earlier iterate lands either on `0` or on a `T_c`-preimage of `0`.
This identifies the critical points of the return map at a parabolic parameter with the points of
the (single) critical orbit of the tricorn, which is what the petal-count argument (NC2/NC3 of
`NOTES_LEAD_mandelbar_noncusp.md` §5.1, and MNS Lemma "Odd Indifferent Dynamics") counts.

A ready-made chain rule for iterates is available in the workspace:
`Work.ELRig.deriv_iterate_eq_prod : deriv (f^[n]) z = ∏ i ∈ Finset.range n, deriv f (f^[i] z)`
for `f` differentiable, together with `Work.ELRig.deriv_Tsq : deriv (Work.Landing.Tsq c) w =
4 * w * (w^2 + star c)` and `Work.ELRig.star_Tantibar : star (Tantibar c w) = w^2 + star c`. -/
theorem derivTsqIterate (c u : ℂ) :
    deriv ((Work.Landing.Tsq c)^[5]) u = 0 ↔
      ∃ i : ℕ, i < 10 ∧ (LeanEval.ComplexAnalysis.Tantibar c)^[i] u = 0 := by
  -- The critical points of `(Tsq c)^[5]` are the points whose `Tsq`-orbit hits `0` or a
  -- `T_c`-preimage of `0` within `5` `Tsq`-steps.
  rw [Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff]
  constructor
  · -- Forward: a hit at `Tsq`-time `j < 5` is a hit of the `T_c`-orbit at time `2j` or `2j+1`.
    rintro ⟨j, hj, h0 | h0⟩
    · -- `(Tsq c)^[j] u = 0`, i.e. `(T_c)^[2j] u = 0`.
      rw [Finset.mem_range] at hj
      refine ⟨2 * j, by omega, ?_⟩
      rwa [Work.LANDCL.Critical.Tsq_iterate_apply] at h0
    · -- `T_c ((Tsq c)^[j] u) = 0`, i.e. `(T_c)^[2j+1] u = 0`.
      rw [Finset.mem_range] at hj
      refine ⟨2 * j + 1, by omega, ?_⟩
      rw [Work.LANDCL.Critical.Tsq_iterate_apply,
        Work.LANDCL.Critical.Tantibar_iterate_succ] at h0
      exact h0
  · -- Backward: a hit of the `T_c`-orbit at time `i < 10` comes from `Tsq`-time `i / 2`.
    rintro ⟨i, hi, h0⟩
    have hmod := Nat.div_add_mod i 2
    have hlt : i % 2 < 2 := Nat.mod_lt i (by norm_num)
    have hk : i / 2 < 5 := by omega
    rcases (by omega : 2 * (i / 2) = i ∨ 2 * (i / 2) + 1 = i) with he | ho
    · refine ⟨i / 2, Finset.mem_range.mpr hk, Or.inl ?_⟩
      rw [Work.LANDCL.Critical.Tsq_iterate_apply, he]
      exact h0
    · refine ⟨i / 2, Finset.mem_range.mpr hk, Or.inr ?_⟩
      rw [Work.LANDCL.Critical.Tsq_iterate_apply,
        Work.LANDCL.Critical.Tantibar_iterate_succ, ho]
      exact h0

end Work.SeedLimit
