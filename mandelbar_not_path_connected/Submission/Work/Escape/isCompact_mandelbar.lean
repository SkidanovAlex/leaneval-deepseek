import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mandelbar (tricorn) is compact

`Mandelbar` is the connectedness locus of the antiholomorphic quadratic family
`z ↦ z̄² + c`, i.e. the set of parameters `c` whose critical orbit `n ↦ (Tantibar c)^[n] 0`
is bounded.  We prove that it is compact.

The proof identifies `Mandelbar` with the set of parameters all of whose critical iterates lie in
the closed unit ball of radius `2`:

`Mandelbar = {c | ∀ n, ‖(Tantibar c)^[n] 0‖ ≤ 2}`.

The inclusion `⊆` is the sharp escape criterion: as soon as some iterate of the critical point
has norm `> 2` (and, for the first step, as soon as `‖c‖ > 2`), the orbit escapes to infinity, so
a bounded critical orbit forces every iterate into the ball of radius `2`.  The reverse inclusion
is immediate (`M = 2`).

This exhibits `Mandelbar` as an intersection of closed sets — preimages of `closedBall 0 2` under
the continuous parameter maps `c ↦ (Tantibar c)^[n] 0` — and bounds it by the ball of radius `2`,
so it is closed and bounded, hence compact in `ℂ`.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Continuity of the critical orbit in the parameter -/

/-- The `n`-th iterate of the critical point `0`, as a function of the parameter `c`,
`c ↦ (T̄_c^[n]) 0`, is continuous.  This is what makes `Mandelbar` closed. -/
theorem continuous_iterate_zero_Tantibar (n : ℕ) :
    Continuous fun c : ℂ => (Tantibar c)^[n] 0 := by
  induction n with
  | zero => simpa using continuous_const (y := (0 : ℂ))
  | succ n ih =>
      have h : (fun c : ℂ => (Tantibar c)^[n + 1] 0)
          = fun c => (starRingEnd ℂ ((Tantibar c)^[n] 0)) ^ 2 + c := by
        funext c
        rw [Function.iterate_succ_apply']
        rfl
      rw [h]
      exact ((continuous_star.comp ih).pow 2).add continuous_id

/-! ## The escape criterion in the parameter plane -/

/-- **`‖c‖ ≤ 2` for bounded critical orbits.**  If `c ∈ Mandelbar` then `‖c‖ ≤ 2`: otherwise the
second critical iterate `c̄² + c` has norm `≥ ‖c‖² - ‖c‖ > max 2 ‖c‖`, so it lies in the escaping
region of `T̄_c` and the critical orbit is unbounded. -/
theorem norm_le_two_of_mem_mandelbar_aux {c : ℂ} (hc : c ∈ Mandelbar) : ‖c‖ ≤ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨M, hM⟩ := hc
  have hgr : MonicGrowth (Tantibar c) 2 ‖c‖ := monicGrowth_Tantibar c
  have hw : ((Tantibar c)^[2]) 0 = (starRingEnd ℂ c) ^ 2 + c := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
    simp [Tantibar]
  have hwnorm : ‖c‖ < ‖(starRingEnd ℂ c) ^ 2 + c‖ := by
    have hle : ‖c‖ ^ 2 - ‖c‖ ≤ ‖(starRingEnd ℂ c) ^ 2 + c‖ := by
      simpa [Tantibar, Td] using norm_Td_ge 2 c c
    have hpos : ‖c‖ < ‖c‖ ^ 2 - ‖c‖ := by nlinarith [norm_nonneg c]
    linarith
  have hz : ((Tantibar c)^[2]) 0 ∈ escapeRegion ‖c‖ := by
    rw [mem_escapeRegion, max_eq_right hcon.le, hw]
    exact hwnorm
  have hT := tendsto_norm_iterate_atTop (Tantibar c) 2 ‖c‖ hgr le_rfl hz
  have hev : ∀ᶠ m in atTop, M < ‖((Tantibar c)^[m]) (((Tantibar c)^[2]) 0)‖ :=
    hT.eventually (Filter.eventually_gt_atTop M)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hbig := hN N le_rfl
  have hsmall : ‖((Tantibar c)^[N]) (((Tantibar c)^[2]) 0)‖ ≤ M := by
    rw [← Function.iterate_add_apply]
    exact hM (N + 2)
  linarith

/-- **Sharp bound on the critical orbit.**  Every iterate of the critical point of a parameter in
the mandelbar lies in the closed ball of radius `2`. -/
theorem iterate_norm_le_two_of_mem_mandelbar {c : ℂ} (hc : c ∈ Mandelbar) (n : ℕ) :
    ‖((Tantibar c)^[n]) 0‖ ≤ 2 := by
  have hc2 : ‖c‖ ≤ 2 := norm_le_two_of_mem_mandelbar_aux hc
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨M, hM⟩ := hc
  have hgr : MonicGrowth (Tantibar c) 2 ‖c‖ := monicGrowth_Tantibar c
  have hz : ((Tantibar c)^[n]) 0 ∈ escapeRegion ‖c‖ := by
    rw [mem_escapeRegion, max_eq_left hc2]
    exact hcon
  have hT := tendsto_norm_iterate_atTop (Tantibar c) 2 ‖c‖ hgr le_rfl hz
  have hev : ∀ᶠ m in atTop, M < ‖((Tantibar c)^[m]) (((Tantibar c)^[n]) 0)‖ :=
    hT.eventually (Filter.eventually_gt_atTop M)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hbig := hN N le_rfl
  have hsmall : ‖((Tantibar c)^[N]) (((Tantibar c)^[n]) 0)‖ ≤ M := by
    rw [← Function.iterate_add_apply]
    exact hM (N + n)
  linarith

/-! ## The mandelbar as an intersection of closed balls -/

/-- **Characterisation of the mandelbar.**  A parameter lies in the mandelbar if and only if all
iterates of its critical point lie in the closed ball of radius `2`. -/
theorem mem_mandelbar_iff_norm_le_two (c : ℂ) :
    c ∈ Mandelbar ↔ ∀ n : ℕ, ‖((Tantibar c)^[n]) 0‖ ≤ 2 :=
  ⟨fun hc n => iterate_norm_le_two_of_mem_mandelbar hc n, fun h => ⟨2, h⟩⟩

/-- The mandelbar is the intersection over `n` of the preimages of `closedBall 0 2` under the
continuous critical-orbit maps `c ↦ (T̄_c^[n]) 0`. -/
theorem mandelbar_eq_iInter :
    Mandelbar = ⋂ n : ℕ, {c : ℂ | ‖((Tantibar c)^[n]) 0‖ ≤ 2} := by
  ext c
  rw [Set.mem_iInter]
  exact mem_mandelbar_iff_norm_le_two c

theorem isClosed_mandelbar : IsClosed Mandelbar := by
  rw [mandelbar_eq_iInter]
  exact isClosed_iInter fun n =>
    isClosed_le (continuous_iterate_zero_Tantibar n).norm continuous_const

theorem isBounded_mandelbar : Bornology.IsBounded Mandelbar :=
  Metric.isBounded_closedBall.subset fun c hc => by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := iterate_norm_le_two_of_mem_mandelbar hc 1
    simpa [Function.iterate_one, Tantibar] using h

/-! ## Compactness -/

theorem isCompact_mandelbar : IsCompact LeanEval.ComplexAnalysis.Mandelbar :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_mandelbar, isBounded_mandelbar⟩

end Work.Escape
