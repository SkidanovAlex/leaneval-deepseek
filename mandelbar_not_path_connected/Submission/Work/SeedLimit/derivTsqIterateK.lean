import Mathlib
import Submission.Work.SeedLimit.Defs
import Submission.Work.SeedLimit.derivTsqIterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedLimit

open LeanEval.ComplexAnalysis (Tantibar)

/-- **Critical points of an iterate.**  For an entire function `f` on `ℂ`, the derivative of the
`n`-th iterate `f^[n]` vanishes at `z` exactly when some point of the orbit
`z, f z, …, f^[n-1] z` is a critical point of `f`.

This is the chain rule `deriv (f^[n]) z = ∏ i ∈ range n, deriv f (f^[i] z)` together with the fact
that `ℂ` is a domain: a finite product in `ℂ` vanishes iff one of its factors does. -/
lemma deriv_iterate_eq_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (z : ℂ) :
    deriv (f^[n]) z = 0 ↔ ∃ j : ℕ, j < n ∧ deriv f (f^[j] z) = 0 := by
  rw [Work.LANDCL.Critical.deriv_iterate_eq_prod hf n z, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hz⟩; exact ⟨j, Finset.mem_range.mp hj, hz⟩
  · rintro ⟨j, hj, hz⟩; exact ⟨j, Finset.mem_range.mpr hj, hz⟩

/-- `(Tsq c)^[5i] = (T_c)^[10i]`: the `i`-th iterate of the holomorphic return map `(Tsq c)^[5]`
is the holomorphic `10i`-th iterate of the tricorn iterator. -/
lemma Tsq_five_iterate_eq (c u : ℂ) (i : ℕ) :
    (((Work.Landing.Tsq c)^[5])^[i]) u = (Tantibar c)^[10 * i] u := by
  rw [show ((Work.Landing.Tsq c)^[5])^[i] = ((Tantibar c)^[10])^[i] from by
        rw [← Tsq_iterate_five_eq], ← Function.iterate_mul]

/-- **The critical points of any iterate of the return map.**  For `k ≥ 1`, the critical points of
`((Tsq c)^[5])^[k] = (T_c)^[10k]` are exactly the points whose `T_c`-orbit meets the critical point
`0` within `10k` steps.  (This is `Work.SeedLimit.derivTsqIterate` iterated: the critical points of
`(Tsq c)^[5]` are the points with `T_c^[j] u = 0` for some `j < 10`, and `(Tsq c)^[5i] = T_c^[10i]`,
so the critical points of the `k`-fold iterate are the union over `i < k` of the `T_c^[10i]`-preimages
of those, i.e. the points with `T_c^[j] u = 0` for some `j < 10k`.)

This is the counting input for the local step NC6 of `NOTES_LEAD_mandelbar_noncusp.md` §5.1: it ties
the critical points of the holomorphic return map to the *single* critical orbit of the tricorn. -/
theorem derivTsqIterateK (c u : ℂ) {k : ℕ} (hk : 0 < k) :
    deriv (((Work.Landing.Tsq c)^[5])^[k]) u = 0 ↔
      ∃ j : ℕ, j < 10 * k ∧ (LeanEval.ComplexAnalysis.Tantibar c)^[j] u = 0 := by
  have _ := hk
  have hdiff : Differentiable ℂ ((Work.Landing.Tsq c)^[5]) :=
    (Work.LANDCL.Critical.differentiable_Tsq c).iterate 5
  rw [deriv_iterate_eq_zero_iff hdiff k u]
  constructor
  · -- A critical point of the `k`-fold iterate is a `T_c^[10i]`-preimage, `i < k`, of a critical
    -- point of the return map `(Tsq c)^[5]`, i.e. of a point hitting `0` within `10` steps.
    rintro ⟨i, hik, hi⟩
    rw [derivTsqIterate] at hi
    obtain ⟨j, hj, h0⟩ := hi
    refine ⟨j + 10 * i, by omega, ?_⟩
    rw [Tsq_five_iterate_eq c u i] at h0
    rwa [← Function.iterate_add_apply] at h0
  · -- Conversely a point whose orbit hits `0` at time `j' < 10k` hits `0` at time `j' % 10 < 10`
    -- after `j' / 10 < k` return steps, hence is critical for the `k`-fold iterate.
    rintro ⟨j', hj', h0⟩
    refine ⟨j' / 10, Nat.div_lt_of_lt_mul hj', ?_⟩
    refine (derivTsqIterate c _).mpr ⟨j' % 10, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [Tsq_five_iterate_eq c u (j' / 10)]
    have hsplit : j' % 10 + 10 * (j' / 10) = j' := by
      have := Nat.div_add_mod j' 10; omega
    rw [← Function.iterate_add_apply, hsplit]
    exact h0

end Work.SeedLimit
