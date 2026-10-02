import Mathlib
import Submission.Work.FatouParabolic.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The critical orbit of the tricorn map `T_{1/4}` at the critical value `1/4`

The map `T_c z = conj z ^ 2 + c` (the *tricorn* / Mandelbar family).  At `c = 1/4` the starting
point `1/4` is real, and since `conj` fixes the reals the whole orbit stays real and follows the
real quadratic `x ↦ x² + 1/4`.  That quadratic has a parabolic fixed point at `1/2` (double root
of `x² - x + 1/4`), and the orbit starting at `1/4` increases monotonically to `1/2`.

This file proves that convergence, and lifts it to the complex orbit: `T_{1/4}^[n](1/4) → 1/2`.
-/

open Filter

namespace Work.FatouParabolic.Quarter

noncomputable section

/-- The real quadratic `x ↦ x² + 1/4`, the real slice of `T_{1/4}`. -/
def quarterMap (x : ℝ) : ℝ := x ^ 2 + 1 / 4

/-- The real critical orbit of `x ↦ x² + 1/4` starting at the critical value `1/4`. -/
def quarterOrbit (n : ℕ) : ℝ := quarterMap^[n] (1 / 4)

@[simp] lemma quarterOrbit_zero : quarterOrbit 0 = 1 / 4 := by
  simp [quarterOrbit, Function.iterate_zero_apply]

lemma quarterOrbit_succ (n : ℕ) : quarterOrbit (n + 1) = quarterMap (quarterOrbit n) := by
  simp [quarterOrbit, Function.iterate_succ_apply']

lemma continuous_quarterMap : Continuous quarterMap := by
  unfold quarterMap; continuity

lemma quarterOrbit_ge (n : ℕ) : 1 / 4 ≤ quarterOrbit n := by
  induction n with
  | zero => rw [quarterOrbit_zero]
  | succ n ih =>
    rw [quarterOrbit_succ]; unfold quarterMap
    nlinarith [sq_nonneg (quarterOrbit n)]

lemma quarterOrbit_le (n : ℕ) : quarterOrbit n ≤ 1 / 2 := by
  induction n with
  | zero => rw [quarterOrbit_zero]; norm_num
  | succ n ih =>
    rw [quarterOrbit_succ]; unfold quarterMap
    have h0 : 0 ≤ quarterOrbit n := le_trans (by norm_num) (quarterOrbit_ge n)
    have hsq : quarterOrbit n ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ h0 ih 2
    nlinarith

lemma quarterOrbit_mono : Monotone quarterOrbit := by
  apply monotone_nat_of_le_succ
  intro n
  rw [quarterOrbit_succ]; unfold quarterMap
  nlinarith [sq_nonneg (quarterOrbit n - 1 / 2)]

/-- The real critical orbit increases to the parabolic fixed point `1/2`. -/
lemma tendsto_quarterOrbit : Tendsto quarterOrbit atTop (nhds (1 / 2 : ℝ)) := by
  have hbdd : BddAbove (Set.range quarterOrbit) :=
    ⟨1 / 2, by rintro _ ⟨n, rfl⟩; exact quarterOrbit_le n⟩
  have hlim : Tendsto quarterOrbit atTop (nhds (⨆ n, quarterOrbit n)) :=
    tendsto_atTop_ciSup quarterOrbit_mono hbdd
  have hflim : Tendsto (fun n => quarterMap (quarterOrbit n)) atTop
      (nhds (quarterMap (⨆ n, quarterOrbit n))) :=
    (continuous_quarterMap.tendsto _).comp hlim
  have hshift : Tendsto (fun n => quarterOrbit (n + 1)) atTop (nhds (⨆ n, quarterOrbit n)) :=
    (Filter.tendsto_add_atTop_iff_nat (f := quarterOrbit) 1).2 hlim
  have heq : (fun n => quarterMap (quarterOrbit n)) = (fun n => quarterOrbit (n + 1)) := by
    funext n; rw [quarterOrbit_succ]
  rw [heq] at hflim
  have hfix : quarterMap (⨆ n, quarterOrbit n) = ⨆ n, quarterOrbit n :=
    tendsto_nhds_unique hflim hshift
  have hgoal : (⨆ n, quarterOrbit n) = 1 / 2 := by
    unfold quarterMap at hfix
    nlinarith [sq_nonneg ((⨆ n, quarterOrbit n) - 1 / 2)]
  rwa [hgoal] at hlim

open LeanEval.ComplexAnalysis (Tantibar)

/-- On real arguments `T_{1/4}` agrees with the real quadratic `x ↦ x² + 1/4`
(complex conjugation fixes the reals). -/
lemma tantibar_quarter_ofReal (x : ℝ) :
    Tantibar (1 / 4 : ℂ) (x : ℂ) = ((quarterMap x : ℝ) : ℂ) := by
  unfold Tantibar quarterMap
  rw [Complex.conj_ofReal, Complex.ofReal_add, Complex.ofReal_pow]
  norm_num

/-- The full complex critical orbit of `T_{1/4}` is the image of the real one. -/
lemma tantibar_iterate_quarterOrbit (n : ℕ) :
    (Tantibar (1 / 4 : ℂ))^[n] (1 / 4 : ℂ) = ((quarterOrbit n : ℝ) : ℂ) := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, quarterOrbit_zero]; norm_num
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, tantibar_quarter_ofReal, ← quarterOrbit_succ]

theorem tendsto_quarter_criticalOrbit :
    Filter.Tendsto (fun n : ℕ => (LeanEval.ComplexAnalysis.Tantibar (1 / 4 : ℂ))^[n] (1 / 4 : ℂ))
      Filter.atTop (nhds (1 / 2 : ℂ)) := by
  have h1 : Filter.Tendsto (fun n : ℕ => ((quarterOrbit n : ℝ) : ℂ)) Filter.atTop
      (nhds ((1 / 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_quarterOrbit
  have h2 : (fun n : ℕ => (LeanEval.ComplexAnalysis.Tantibar (1 / 4 : ℂ))^[n] (1 / 4 : ℂ))
      = fun n : ℕ => ((quarterOrbit n : ℝ) : ℂ) := by
    funext n; exact tantibar_iterate_quarterOrbit n
  rw [h2]
  simpa using h1

end

end Work.FatouParabolic.Quarter
