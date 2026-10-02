import Mathlib
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit
import Submission.Work.ELPull.Defs
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Function
open LeanEval.ComplexAnalysis (Tantibar)

/-- The `i`-th iterate of the holomorphic second iterate `Tsq c` is the `2i`-th iterate of the
antiholomorphic quadratic `Tantibar c`. -/
private lemma tsq_iterate_eq (c : ℂ) (i : ℕ) :
    ((Work.Landing.Tsq c)^[i]) = ((Tantibar c)^[2 * i]) := by
  rw [Work.ELRig.Tsq_eq_Tantibar_iterate_two, Function.iterate_mul]

/-- **A point whose `T_c`-orbit avoids the critical point is not a critical point of the holomorphic iterate `(Tsq c)^[k]`.**

`Tsq c = (T_c)^[2]` is the holomorphic second iterate of the tricorn map `T_c z = z̄² + c`, and `deriv ((Tsq c)^[k]) z = ∏_{i<k} deriv (Tsq c) ((Tsq c)^[i] z)` with `deriv (Tsq c) w = 4·w·(w² + c̄) = 4·w·conj (T_c w)` (chain rule, `Work.ELRig.deriv_iterate_eq_prod`, `Work.ELRig.deriv_Tsq`).  Since `Tsq c = (T_c)^[2]`, the factors `(Tsq c)^[i] z` and `T_c ((Tsq c)^[i] z)` are the points `(T_c)^[2i] z` and `(T_c)^[2i+1] z`, so the product vanishes iff some `(T_c)^[m] z` with `m ≤ 2k−1` is `0`.  Hence, if no iterate `(T_c)^[m] z`, `m ≤ 2k−1`, vanishes, then `deriv ((Tsq c)^[k]) z ≠ 0`.

(The sibling statement `Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit` proves the same conclusion under the *different* hypothesis that the value `b = (Tsq c)^[k] z` avoids the critical orbit of `T_c`; that hypothesis is not available in the intended application, which is why this version — in terms of the orbit of `z` — is needed.) -/
theorem deriv_tsqIterate_ne_zero_of_iterate_ne_zero {c z : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ m : ℕ, m ≤ 2 * k - 1 → (LeanEval.ComplexAnalysis.Tantibar c)^[m] z ≠ 0) :
    deriv ((Work.Landing.Tsq c)^[k]) z ≠ 0 := by
  intro hzero
  have hdiff : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
    fun_prop
  rw [Work.ELRig.deriv_iterate_eq_prod hdiff] at hzero
  rw [Finset.prod_eq_zero_iff] at hzero
  obtain ⟨i, hi, hfi⟩ := hzero
  rw [Finset.mem_range] at hi
  set w : ℂ := ((Work.Landing.Tsq c)^[i]) z with hw
  rw [Work.ELRig.deriv_Tsq] at hfi
  -- the two indices `2i` and `2i+1` lie below the iterate bound
  have h1 : 2 * i ≤ 2 * k - 1 := by omega
  have h2 : 2 * i + 1 ≤ 2 * k - 1 := by omega
  -- the `2i`-th iterate of `Tantibar c` at `z` is `w`
  have hiter : ((Tantibar c)^[2 * i]) z = w := by
    rw [hw, tsq_iterate_eq c i]
  rcases mul_eq_zero.mp hfi with h4w | hwc
  · -- the factor `4·w` vanishes, so `w = 0` is the `2i`-th point of the orbit of `z`
    rcases mul_eq_zero.mp h4w with h4 | hw0
    · exact absurd h4 (by norm_num)
    · exact h (2 * i) h1 (by rw [hiter, hw0])
  · -- the factor `w² + c̄ = conj (T_c w)` vanishes, so the `(2i+1)`-st point of the orbit is `0`
    have hTw : Tantibar c w = 0 := by
      have hst : star (Tantibar c w) = 0 := by rw [Work.ELRig.star_Tantibar, hwc]
      exact star_eq_zero.mp hst
    have hz0 : ((Tantibar c)^[2 * i + 1]) z = 0 := by
      rw [show 2 * i + 1 = (2 * i).succ from rfl, Function.iterate_succ_apply', hiter, hTw]
    exact h (2 * i + 1) h2 hz0

end Work.GATE2.PL
