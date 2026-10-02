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
# The escape dichotomy for the tricorn

The mandelbar (tricorn) set is the connectedness locus of the antiholomorphic family
`Tantibar c z = z̄² + c`, i.e. the set of parameters `c` whose critical orbit `n ↦ (Tantibar c)^[n] 0`
is bounded.  This file identifies it with the *closed disk of radius `2`* on the orbit side:

`c ∈ Mandelbar ↔ ∀ n, ‖(Tantibar c)^[n] 0‖ ≤ 2`.

This is the classical escape criterion for the quadratic unicritical family, in its exact sharp
form: the escaping region of a degree-`2` monic map with constant `A = ‖c‖` is
`{z | max 2 ‖c‖ < ‖z‖}`, and for the critical orbit `0 ↦ c ↦ c̄² + c ↦ …` any point of norm
exceeding `2` already forces escape (either it is itself in the escaping region, when `‖c‖ ≤ 2`,
or its second iterate is, when `‖c‖ > 2`).

## Main results

* `not_isBounded_range_of_mem_escapeRegion`: a point of the escaping region has unbounded orbit.
* `not_isBounded_of_eq_iterate`: unboundedness is inherited from any point of an orbit.
* `iterate_two_mem_escapeRegion`: if `‖c‖ > 2` then the second iterate of `0` escapes.
* `mem_mandelbar_iff`: the escape dichotomy for the mandelbar set.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-- **A point of the escaping region has unbounded orbit.**  If `z ∈ escapeRegion A` for a
`MonicGrowth f d A` map with `d ≥ 2`, then the orbit of `z` is not bounded.  Indeed
`tendsto_norm_iterate_atTop` shows the orbit norms diverge to `+∞`, which no bounded set of the
plane can contain. -/
theorem not_isBounded_range_of_mem_escapeRegion {f : ℂ → ℂ} {d : ℕ} {A : ℝ}
    (h : MonicGrowth f d A) (hd : 2 ≤ d) {z : ℂ} (hz : z ∈ escapeRegion A) :
    ¬ Bornology.IsBounded (range fun k : ℕ => (f^[k]) z) := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  have ht : Tendsto (fun k : ℕ => ‖(f^[k]) z‖) atTop atTop :=
    tendsto_norm_iterate_atTop f d A h hd hz
  have hev : ∀ᶠ k : ℕ in atTop, C + 1 ≤ ‖(f^[k]) z‖ :=
    Filter.tendsto_atTop.mp ht (C + 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have h1 := hN N le_rfl
  have h2 := hC _ ⟨N, rfl⟩
  linarith

/-- **Unboundedness is inherited from any point of an orbit.**  If `z = (f^[n]) z₀` and the orbit
of `z` is unbounded, then so is the orbit of `z₀`: the former is the tail of the latter, and a
subset of a bounded set is bounded. -/
theorem not_isBounded_of_eq_iterate {f : ℂ → ℂ} {z z₀ : ℂ} {n : ℕ}
    (h : z = (f^[n]) z₀)
    (hz : ¬ Bornology.IsBounded (range fun k : ℕ => (f^[k]) z)) :
    ¬ Bornology.IsBounded (range fun k : ℕ => (f^[k]) z₀) := by
  intro hb
  refine hz (hb.subset ?_)
  rintro w ⟨k, rfl⟩
  exact ⟨n + k, by rw [h]; simp only [Nat.add_comm n k, Function.iterate_add_apply]⟩

/-- **If `‖c‖ > 2` then the second iterate of the critical point escapes.**  Since
`(Tantibar c) 0 = c` and `(Tantibar c) c = c̄² + c`, and `‖c̄² + c‖ ≥ ‖c‖² - ‖c‖ > ‖c‖ = max 2 ‖c‖`
as soon as `‖c‖ > 2`, the critical orbit enters the escaping region at time `2`. -/
theorem iterate_two_mem_escapeRegion {c : ℂ} (hc : 2 < ‖c‖) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2] 0 ∈ escapeRegion ‖c‖ := by
  rw [mem_escapeRegion, max_eq_right hc.le]
  have hge := norm_Td_ge 2 c c
  have hlt : ‖c‖ < ‖c‖ ^ 2 - ‖c‖ := by nlinarith [norm_nonneg c]
  have hfin : ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2] 0‖ = ‖Td 2 c c‖ := by
    congr 1
    simp [Function.iterate_succ_apply, LeanEval.ComplexAnalysis.Tantibar, Td]
  rw [hfin]
  linarith

/-- **Escape dichotomy for the mandelbar set.**  A parameter `c` lies in the mandelbar (tricorn)
set — i.e. its critical orbit is bounded — exactly when the whole critical orbit stays inside the
closed disk of radius `2`. -/
theorem mem_mandelbar_iff (c : ℂ) :
    c ∈ LeanEval.ComplexAnalysis.Mandelbar ↔
      ∀ n : ℕ, ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] 0‖ ≤ 2 := by
  constructor
  · intro hc
    obtain ⟨M, hM⟩ := hc
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := hcon
    have hbdd : Bornology.IsBounded
        (range fun k : ℕ => (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0) :=
      isBounded_iff_forall_norm_le.mpr ⟨M, fun x hx => by
        obtain ⟨k, rfl⟩ := hx; exact hM k⟩
    obtain hcontra : ¬ Bornology.IsBounded
        (range fun k : ℕ => (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0) := by
      rcases le_or_gt ‖c‖ 2 with hc2 | hc2
      · -- `‖c‖ ≤ 2`: the point `(Tantibar c)^[n] 0` of norm `> 2` is itself in the escaping region.
        have hz : (LeanEval.ComplexAnalysis.Tantibar c)^[n] 0 ∈ escapeRegion ‖c‖ := by
          rw [mem_escapeRegion, max_eq_left hc2]; exact hn
        exact not_isBounded_of_eq_iterate (f := LeanEval.ComplexAnalysis.Tantibar c)
          (n := n) rfl
          (not_isBounded_range_of_mem_escapeRegion (monicGrowth_Tantibar c) (le_refl 2) hz)
      · -- `‖c‖ > 2`: the second iterate of `0` is already in the escaping region.
        have hz : (LeanEval.ComplexAnalysis.Tantibar c)^[2] 0 ∈ escapeRegion ‖c‖ :=
          iterate_two_mem_escapeRegion hc2
        exact not_isBounded_of_eq_iterate (f := LeanEval.ComplexAnalysis.Tantibar c)
          (n := 2) rfl
          (not_isBounded_range_of_mem_escapeRegion (monicGrowth_Tantibar c) (le_refl 2) hz)
    exact hcontra hbdd
  · intro h
    exact ⟨2, h⟩

end Work.Escape
