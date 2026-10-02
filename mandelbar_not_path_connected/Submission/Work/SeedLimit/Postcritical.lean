/-
Copyright: subproject `Submission/Work/SeedLimit/`.

# §5.1, step NC6: the postcritical set, and its two Fatou inputs

Step NC6 of `NOTES_LEAD_mandelbar_noncusp.md` §5.1 says: an attracting (or parabolic) point at a
parameter `c'` forces `c'` into the mandelbar, because the closure of the postcritical set of `T_c`
for `c ∉ Mandelbar` is the escaping critical orbit, which is disjoint from the filled Julia set.

This module makes that step a theorem.  The content is:

* `Work.SeedLimit.mem_Mandelbar_of_critical_bounded` — the core: a critical point of the holomorphic
  return map `(Tsq c)^[5] = T_c^[10]` whose orbit under that return map is bounded forces
  `c ∈ Mandelbar`.  Indeed the critical points of `(Tsq c)^[5]` are exactly the `T_c`-preimages of
  `0` within `10` steps (`Work.SeedLimit.derivTsqIterate`), so the return-map orbit of such a point
  is a shifted `T_c`-orbit of `0` along an arithmetic progression of indices; if it is bounded then
  the whole critical orbit of `T_c` is bounded (`Work.SeedLimit.boundedOrbitOfBoundedArith`), i.e.
  `c ∈ Mandelbar`.  This is proved here.
* `Work.SeedLimit.AttractingCycleFatou` — Fatou's theorem on *attracting* cycles (named causal
  input): an attracting fixed point of the degree-`2^10` polynomial `(Tsq c)^[5]` attracts a
  critical point.
* `Work.SeedLimit.mem_Mandelbar_of_attracting` — NC6, attracting case, from that input.
* `Work.SeedLimit.mem_Mandelbar_of_parabolic` — NC6, parabolic case, from `FatouParabolicInput`
  (`Work.FatouParabolic.FatouParabolicInput` is consumed **by name**, applied to the polynomial
  `(Tsq c)^[5]` of degree `1024`, whose degree witness is `Work.SeedLimit.natDegreeIterP`).

With `Work.SeedLimit.IndexParityStep` (NC4–NC5, `LocalRoute.lean`) these close step NC6 of the local
route: the only remaining inputs of the local §5.1 are the petal count (NC1–NC3) and the index/parity
step (NC4–NC5).
-/
import Submission.Work.SeedLimit.Defs
import Submission.Work.SeedLimit.derivTsqIterate
import Submission.Work.SeedLimit.boundedOrbitOfBoundedArith
import Submission.Work.SeedLimit.natDegreeIterP
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FBif.IterPoly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedLimit

open Filter
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The core: a bounded critical orbit of the return map bounds the critical orbit -/

/-- `Tsq c = (T_c)^[2]`, as functions. -/
theorem Tsq_eq_T_iterate_two (c : ℂ) : Tsq c = (Tantibar c)^[2] := by
  funext z
  simpa [Tsq, Work.Landing.Tsq, Function.iterate_succ, Function.iterate_one,
    Function.comp_apply] using Work.ParamRays.orbit_two_eq c z

/-- The return-map orbit of a point is the `T_c`-orbit along an arithmetic progression. -/
theorem iterate_tsq_five_apply (c w : ℂ) (n : ℕ) :
    (((Tsq c)^[5])^[n]) w = (Tantibar c)^[10 * n] w := by
  rw [Tsq_iterate_five_eq c, Function.iterate_mul]

/-- **NC6, core.**  A critical point `w` of the holomorphic return map `(Tsq c)^[5] = T_c^[10]`
whose orbit under that return map is bounded forces `c ∈ Mandelbar`: by
`Work.SeedLimit.derivTsqIterate` some `T_c`-iterate of `w` is the critical point `0`, so a bounded
return-map orbit of `w` is a bounded arithmetic subsequence of the critical orbit of `T_c`, and
`Work.SeedLimit.boundedOrbitOfBoundedArith` then bounds the whole critical orbit. -/
theorem mem_Mandelbar_of_critical_bounded {c w : ℂ} (hcrit : deriv ((Tsq c)^[5]) w = 0)
    (hbdd : ∃ M : ℝ, ∀ n : ℕ, ‖(((Tsq c)^[5])^[n]) w‖ ≤ M) : c ∈ Mandelbar := by
  obtain ⟨j, hj, h0⟩ := (derivTsqIterate c w).mp hcrit
  obtain ⟨M, hM⟩ := hbdd
  -- `w` reaches the critical point `0` after `j < 10` steps of `T_c`
  have hshift : ∀ n : ℕ, j ≤ 10 * n →
      (Tantibar c)^[10 * n - j] 0 = (((Tsq c)^[5])^[n]) w := by
    intro n hn
    rw [iterate_tsq_five_apply]
    have hsplit : (Tantibar c)^[10 * n] w
        = (Tantibar c)^[10 * n - j] ((Tantibar c)^[j] w) := by
      conv_lhs => rw [show 10 * n = (10 * n - j) + j from (Nat.sub_add_cancel hn).symm]
      exact Function.iterate_add_apply (f := Tantibar c) (10 * n - j) j w
    rw [hsplit, h0]
  -- hence the arithmetic subsequence of the critical orbit with indices `10 * n - j` is bounded
  refine boundedOrbitOfBoundedArith c (q := 10) (r := (10 - j) % 10) (by norm_num) ⟨M, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- `j = 0`: the index `10 * n + 0` is one of the shifted indices
    subst hj0
    have h1 : 10 * n + 0 = 10 * n := by omega
    rw [h1]
    have h2 : (Tantibar c)^[10 * n] 0 = (((Tsq c)^[5])^[n]) w := by
      simpa using hshift n (by omega)
    rw [h2]
    exact hM n
  · -- `j > 0`: `(10 - j) % 10 = 10 - j`, and `10 * n + (10 - j) = 10 * (n + 1) - j`
    have hlt : j < 10 := hj
    have hmod : (10 - j) % 10 = 10 - j := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have h1 : 10 * n + (10 - j) = 10 * (n + 1) - j := by omega
    rw [h1, hshift (n + 1) (by omega)]
    exact hM (n + 1)

/-! ## The two Fatou inputs, and NC6 in both cases -/

/-- **Fatou's theorem on attracting cycles** (named classical input; Milnor, *Dynamics in one complex
variable*, §8–9): for the tricorn, an attracting fixed point of the holomorphic return map
`(Tsq c)^[k] = (T_c)^[2k]` — a polynomial of degree `4^k ≥ 2` — attracts a critical point of that
return map.  (`Work.FatouParabolic.FatouParabolicInput` is the corresponding statement for
parabolic points.) -/
def AttractingCycleFatou : Prop :=
  ∀ (c : ℂ) (k : ℕ) (z : ℂ), 0 < k → ((Tsq c)^[k]) z = z →
    ‖deriv (((Tsq c)^[k])) z‖ < 1 →
    ∃ w : ℂ, deriv (((Tsq c)^[k])) w = 0 ∧
      Tendsto (fun n : ℕ => (((Tsq c)^[k])^[n]) w) atTop (𝓝 z)

/-- The return map `(Tsq c)^[5] = (T_c)^[10]` of the period-`5` cycle is the evaluation of the
polynomial `iterP c 10` of degree `1024`, so Fatou's theorems (which are stated for polynomial maps
of degree `≥ 2`) apply to it. -/
theorem isPolynomial_returnMap (c : ℂ) :
    Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo ((Tsq c)^[5]) := by
  refine ⟨Work.FBif.iterP c 10, ?_, ?_⟩
  · rw [natDegreeIterP]; norm_num
  · intro z
    rw [Tsq_iterate_five_apply]
    exact (Work.FBif.iterP_ten_eval c z).symm

/-- A convergent sequence of norms is bounded (the elementary step from Fatou's conclusion to a
bounded orbit). -/
theorem exists_bound_of_tendsto (u : ℕ → ℂ) (z : ℂ) (h : Tendsto u atTop (𝓝 z)) :
    ∃ M : ℝ, ∀ n : ℕ, ‖u n‖ ≤ M := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) 1 zero_lt_one
  refine ⟨max (‖z‖ + 1) (∑ i ∈ Finset.range N, ‖u i‖), fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hn)
  · have h1 : dist (u n) z < 1 := hN n hn
    rw [dist_eq_norm] at h1
    have : ‖u n‖ ≤ ‖z‖ + 1 := by
      have h2 := norm_add_le (u n - z) z
      rw [sub_add_cancel] at h2
      linarith
    exact le_trans this (le_max_left _ _)

/-- **NC6, attracting case.**  If the holomorphic return map `(Tsq c)^[5]` of the period-`5` cycle
has an attracting fixed point, then `c ∈ Mandelbar`. -/
theorem mem_Mandelbar_of_attracting (hFatou : AttractingCycleFatou) {c z : ℂ}
    (hfix : ((Tsq c)^[5]) z = z) (hder : ‖deriv (((Tsq c)^[5])) z‖ < 1) : c ∈ Mandelbar := by
  obtain ⟨w, hcrit, htend⟩ := hFatou c 5 z (by norm_num) hfix hder
  exact mem_Mandelbar_of_critical_bounded hcrit (exists_bound_of_tendsto _ z htend)

/-- **NC6, parabolic case**, from `Work.FatouParabolic.FatouParabolicInput` (consumed by name).  If
the holomorphic return map `(Tsq c)^[5]` of the period-`5` cycle has a parabolic fixed point
(multiplier `1`), then `c ∈ Mandelbar`. -/
theorem mem_Mandelbar_of_parabolic (hFatou : Work.FatouParabolic.FatouParabolicInput) {c z : ℂ}
    (hfix : ((Tsq c)^[5]) z = z) (hder : deriv (((Tsq c)^[5])) z = 1) : c ∈ Mandelbar := by
  have hpol := isPolynomial_returnMap c
  obtain ⟨w, hcrit, hbasin⟩ := hFatou ((Tsq c)^[5]) z hpol hfix hder
  refine mem_Mandelbar_of_critical_bounded hcrit ?_
  rw [Work.FatouParabolic.mem_basin] at hbasin
  exact exists_bound_of_tendsto _ z hbasin

end Work.SeedLimit
