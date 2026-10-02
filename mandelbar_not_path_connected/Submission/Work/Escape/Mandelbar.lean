import Submission.Work.Escape.Basic
import Submission.Work.Escape.mem_mandelbar_iff
import Submission.Work.Escape.isCompact_mandelbar
import Submission.Work.Escape.norm_le_two_of_mem_mandelbar
import Submission.Work.Escape.tendsto_norm_Tantibar_iterate_atTop
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.green_comp
import Submission.Work.Escape.green_nonneg
import Submission.Work.Escape.green_le_log
import Submission.Work.Escape.log_half_le_green
import Submission.Work.Escape.green_eq_zero_iff
import Submission.Work.Escape.continuous_green
import Submission.Work.Escape.GreenHarmonicExamples

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The mandelbar: escape criterion, compactness, and the Green function of the tricorn

This is the application layer of the escape/Green chapter: everything here is stated for the
tricorn (mandelbar) family `T_c(z) = z̄² + c` of the challenge file.

* `Work.Escape.mem_mandelbar_iff` — `M = {c | ∀ n, ‖T_c^[n] 0‖ ≤ 2}` (escape criterion).
* `Work.Escape.isCompact_mandelbar` — the mandelbar is compact.
* `Work.Escape.norm_le_two_of_mem_mandelbar` — `M ⊆ closedBall 0 2`.
* `Work.Escape.greenParam` — the Green function of the critical orbit, `c ↦ G_c(0)`.
* `Work.Escape.greenParam_eq_zero_iff_mem_mandelbar` — `M = {c | G_c(0) = 0}`.
* `Work.Escape.green_Tantibar_comp` — `G_c ∘ T_c = 2 G_c`.
* `Work.Escape.filledTricorn_eq_green_eq_zero` — `K_c = {z | G_c z = 0}`.
-/

open Filter Function Metric Set InnerProductSpace
open scoped Topology

noncomputable section

namespace Work.Escape

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The Green function is equivariant under the dynamics -/

/-- `G_c (T_c z) = 2 G_c z`: the tricorn Green function is doubled by the map. -/
theorem green_Tantibar_comp (c z : ℂ) :
    green (Tantibar c) 2 (Tantibar c z) = 2 * green (Tantibar c) 2 z :=
  green_comp (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl z

/-- Iterated form: `G_c (T_c^[n] z) = 2^n G_c z`. -/
theorem green_Tantibar_iterate_comp (c z : ℂ) (n : ℕ) :
    green (Tantibar c) 2 ((Tantibar c)^[n] z) = 2 ^ n * green (Tantibar c) 2 z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', green_Tantibar_comp, ih, pow_succ]
      ring

/-- The Green function of the tricorn family is harmonic off the filled Julia set `K_c`. -/
theorem harmonicOnNhd_green_Tantibar' (c : ℂ) :
    HarmonicOnNhd (green (Tantibar c) 2) {z : ℂ | 0 < green (Tantibar c) 2 z} :=
  harmonicOnNhd_green_Tantibar c

/-- The Green function of the tricorn family is continuous. -/
theorem continuous_green_Tantibar (c : ℂ) : Continuous (green (Tantibar c) 2) :=
  continuous_green (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl

/-- `K_c = {z | G_c z = 0}`: the filled tricorn is the zero set of the Green function. -/
theorem filledTricorn_eq_green_eq_zero (c : ℂ) :
    filledTricorn c = {z : ℂ | green (Tantibar c) 2 z = 0} := by
  ext z
  exact (green_eq_zero_iff (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl z).symm

/-! ## The parameter potential `c ↦ G_c(0)` -/

theorem greenParam_eq (c : ℂ) : greenParam c = green (Tantibar c) 2 0 := rfl

/-- The parameter potential is nonnegative. -/
theorem greenParam_nonneg (c : ℂ) : 0 ≤ greenParam c :=
  green_nonneg (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl 0

/-- The parameter potential vanishes exactly on the mandelbar. -/
theorem greenParam_eq_zero_iff_mem_mandelbar (c : ℂ) : greenParam c = 0 ↔ c ∈ Mandelbar := by
  rw [greenParam,
    green_eq_zero_iff (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl 0]
  rw [mem_filledJulia]
  constructor
  · intro h
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp h
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  · rintro ⟨C, hC⟩
    exact isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx => by
      obtain ⟨n, rfl⟩ := hx
      exact hC n⟩

/-- The mandelbar is the zero set of the parameter potential. -/
theorem mandelbar_eq_greenParam_eq_zero : Mandelbar = {c : ℂ | greenParam c = 0} := by
  ext c
  exact (greenParam_eq_zero_iff_mem_mandelbar c).symm


/-! ## Positivity characterisations -/

/-- The Green function is positive exactly off the filled Julia set. -/
theorem green_pos_iff_not_mem_filledJulia (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) (z : ℂ) : 0 < green f d z ↔ z ∉ filledJulia f := by
  constructor
  · intro hz hmem
    exact absurd ((green_eq_zero_iff f d A h hd z).mpr hmem) (ne_of_gt hz)
  · intro hz
    rcases (green_nonneg f d A h hd z).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd ((green_eq_zero_iff f d A h hd z).mp heq.symm) hz

/-- The parameter potential is positive exactly off the mandelbar. -/
theorem greenParam_pos_iff_not_mem_mandelbar (c : ℂ) :
    0 < greenParam c ↔ c ∉ Mandelbar := by
  have hmem : 0 ∈ filledJulia (Tantibar c) ↔ c ∈ Mandelbar := by
    rw [mem_filledJulia]
    constructor
    · intro hb
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
    · rintro ⟨C, hC⟩
      exact isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx => by
        obtain ⟨n, rfl⟩ := hx
        exact hC n⟩
  rw [greenParam,
    green_pos_iff_not_mem_filledJulia (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl 0]
  exact not_iff_not.mpr hmem

/-- The Green function of the tricorn family is positive exactly on the complement of `K_c`. -/
theorem green_Tantibar_pos_iff (c z : ℂ) :
    0 < green (Tantibar c) 2 z ↔ z ∉ filledTricorn c :=
  green_pos_iff_not_mem_filledJulia (Tantibar c) 2 ‖c‖ (monicGrowth_Tantibar c) le_rfl z

end Work.Escape
