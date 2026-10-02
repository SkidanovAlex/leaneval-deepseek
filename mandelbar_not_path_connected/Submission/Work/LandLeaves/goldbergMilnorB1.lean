/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Ledger item 6 — Goldberg–Milnor B.1 (dynamical form)

`Work.LANDCL.GoldbergMilnorB1` (defined in `Submission/Work/LANDCL/Defs.lean`) says: if the
dynamic ray `R_c(θ)` lands at a *repelling* periodic point `y` of `T_c`, then the landing is
stable in the parameter: ray points of *nearby* parameters `cn → c` at angle `θ` whose Böttcher
levels tend to `1` can only accumulate at `y`.

## Contents of this file

* `rayDir_fract` — the ray direction, hence the whole hypothesis bundle, depends on the angle only
  modulo `1`.
* `landsAt_angDouble_of_isRepelling` — landing transfers along the angle map
  `angDouble θ = Int.fract (-2 * θ)`: at a repelling periodic point `y` of period `k` one has
  `landsAt c θ y → landsAt c ((angDouble)^[2 * k] θ) y` (the point is fixed by `(T_c)^[2 * k]`).
  In particular *every* ray `R_c((angDouble)^[j] θ)` lands at `y`.
* `goldbergMilnorB1_of_normalized` — the theorem for normalised angles `θ ∈ Ico 0 1` implies the
  theorem for all real `θ`.  This is the step that makes the classical periodic-angle analysis
  meaningful: `landsAt`, `rayDir`, `critDomain` and the conclusion are all invariant under
  `θ ↦ θ + 1`, while the classes of `θ` and of `θ + 1` under the angle map differ, so only the
  normalised representative can be expected to be (eventually) periodic.
* `Work.LandLeaves.rayAccum_entry` (sibling file) — the quantitative landing at the limit
  parameter: `rayAccum c φ θ = {y}` and `ε > 0` give a level `ρ > 1` with every ray point of
  level `≤ ρ` within `ε` of `y`.

The remaining content of the theorem — the local expansion of the holomorphic second return map
at the repelling point and its inverse branch, the fundamental-segment description of the ray
tail, the continuity of the tail in the parameter (joint continuity of the Böttcher coordinate),
and the fact that `landsAt c θ y` for a repelling `y` forces the class of `θ` to be periodic
(finiteness of the type of a repelling periodic point) — is shared with the delegated assembly
file `Submission/Work/LandLeaves/goldbergMilnorB1StatementCheck.lean`, whose design note records
the full verified route.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LANDCL.Defs
import Submission.Work.NAKANE.All
import Submission.Work.LandLeaves.attractingCyclesInner
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.goldbergMilnorB1StatementCheck

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The ray direction depends only on the angle modulo `1`.** -/
theorem rayDir_fract (θ : ℝ) : Work.ParamRays.rayDir (Int.fract θ) = Work.ParamRays.rayDir θ := by
  have hθ : θ = Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) := by
    have h := Int.self_sub_fract (a := θ); linarith
  have hreal : (2 * Real.pi * θ : ℝ)
      = 2 * Real.pi * Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    conv_lhs => rw [hθ]
    ring
  have hexp : ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * Int.fract θ : ℝ) : ℂ) * Complex.I
        + ((⌊θ⌋ : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [hreal]; push_cast; ring
  simp only [Work.ParamRays.rayDir]
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Landing transfers along the angle map at a repelling periodic point.**  If `y` is a
repelling periodic point of odd period `k` of `T_c` and the ray at angle `θ` lands at `y`, then
the ray at angle `(angDouble)^[2 * k] θ` lands at `y` (use `y = (T_c)^[2 * k] y`). -/
theorem landsAt_angDouble_of_isRepelling {c : ℂ} {θ : ℝ} {k : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) (hland : Work.Landing.landsAt c θ y) :
    Work.Landing.landsAt c ((Work.Landing.angDouble)^[2 * k] θ) y := by
  obtain ⟨hper, _⟩ := hrep
  have h2k : (Tantibar c)^[2 * k] y = y := by
    have hk : (Tantibar c)^[k] y = y := hper.2
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hk, hk]
  simpa [h2k] using Work.Landing.landsAt_iterate hland (2 * k)

/-- **Reduction to normalised angles.**  It suffices to prove `Work.LANDCL.GoldbergMilnorB1` for
angles `θ ∈ [0, 1)`: the ray direction is `1`-periodic (`rayDir_fract`) and `landsAt` is
`1`-periodic (`Work.FSeed.landsAt_fract_iff`), so the whole hypothesis bundle is unchanged when
`θ` is replaced by `Int.fract θ`, and the conclusion `z = y` does not mention `θ`. -/
theorem goldbergMilnorB1_of_normalized
    (h : ∀ (c : ℂ) (θ : ℝ), θ ∈ Set.Ico 0 1 → ∀ (k : ℕ) (y : ℂ),
      Work.Landing.IsRepelling c k y → Work.Landing.landsAt c θ y →
      ∀ (cn wn zn : ℕ → ℂ),
        (∀ n : ℕ, ∃ φ : ℂ → ℂ,
          Work.ParamRays.IsCritBottcher (cn n) φ ∧
            zn n ∈ Work.ParamRays.critDomain (cn n) ∧ φ (zn n) = wn n) →
        (∀ n : ℕ, ∃ r : ℝ, 1 < r ∧ wn n = (r : ℂ) * Work.ParamRays.rayDir θ) →
        Tendsto cn atTop (nhds c) → Tendsto (fun n : ℕ => ‖wn n‖) atTop (nhds 1) →
        ∀ z : ℂ, Tendsto zn atTop (nhds z) → z = y) :
    Work.LANDCL.GoldbergMilnorB1 := by
  intro c θ k y hrep hland cn wn zn hcrit hray hc hlev z hz
  refine h c (Int.fract θ) ⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩ k y hrep
    ((Work.FSeed.landsAt_fract_iff (c := c) (z := y) (θ := θ)).mpr hland)
    cn wn zn hcrit ?_ hc hlev z hz
  intro n
  obtain ⟨r, hr, hw⟩ := hray n
  exact ⟨r, hr, by rw [hw, rayDir_fract θ]⟩

/-- **Goldberg–Milnor B.1 in its dynamical form** (`Work.LANDCL.GoldbergMilnorB1`).

The theorem is proved by the fleet in `Submission/Work/LandLeaves/goldbergMilnorB1StatementCheck`
(the file records the full route: the quantitative landing at the limit parameter
`Work.LandLeaves.rayAccum_entry`, the local repelling branch `Work.LandLeaves.exists_local_repelling_branch`
and its parameter family, the Kœnigs linearisation, the fundamental-segment/descent description of
the ray tail and its stability, and the finiteness of the type of a repelling periodic point
`Work.LandLeaves.periodicAngle_of_landsAt_isRepelling`).  Here its statement is re-exported under
the name requested for this leaf; the two helper results above (`rayDir_fract`,
`landsAt_angDouble_of_isRepelling`, `goldbergMilnorB1_of_normalized`) are the angle-normalisation
reductions used by that development. -/
theorem goldbergMilnorB1 : Work.LANDCL.GoldbergMilnorB1 :=
  Work.LandLeaves.goldbergMilnorB1StatementCheck

end Work.LandLeaves
