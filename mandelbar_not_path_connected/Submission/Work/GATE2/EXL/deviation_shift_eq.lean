/-
# GATE2 / EXL — the one-step shift of the `α`-relative Böttcher deviation

The `exit loop` construction of `Submission/Work/GATE2/EXL/` runs along the critical orbit
`z, F z, F² z, …` (`F c = (T_c)^{10}`, degree `1024`) and needs the *refining* form of the
`α`-Böttcher branch: in the `α`-relative Böttcher argument `Work.GATE.deviation (varphiCrit c) α`
a point and its image under the high return map `F c` differ exactly by the factor `1024`,

```
deviation α (F c z) = 1024 · deviation α z,
```

**provided** the deviation at `z` is small (`< 1/2048`, i.e. inside the `1024`-th part of the
window `(-1/2, 1/2]`) and the root angle `α` has integral `1023 α ∈ ℤ`.

## The mathematics

The critical Böttcher coordinate satisfies `(φ_c z)^{1024} = φ_c (F_c z)`
(`Work.GATE2.varphiCrit_F_iterate`), so the *normalised* Böttcher arguments `bAngle` are related by
`bAngle (F_c z) ≡ 1024 · bAngle z` modulo `1`.  Writing `repPhase` for the representative of a real
in `(-1/2, 1/2]`, the phase-gap step
`Work.GATE2.PhaseGap.exists_int_repPhase_comb` (ingredient of `phase_gap_integrality`) then gives

```
deviation α (F c z) = 1024 · deviation α z + j,        j ∈ ℤ,
```

because `(1024 - 1) α = 1023 α ∈ ℤ` by hypothesis.  The integer `j` is killed by the window: the
deviation of *any* point lies in `(-1/2, 1/2]` (`Work.GATE.deviation_mem`) while the hypothesis puts
`1024 · deviation α z` in `(-1/2, 1/2)`; hence `|j| < 1`, so `j = 0`.  This is exactly the
hypothesis `< 1/2048` of the statement — the bound is `1/2 / 1024 = 1/2048`, the width at which the
`1024`-fold image of the window still fits in the fundamental window and no integer can appear.
-/
import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.PathTransport.angle_F_iterate
import Submission.Work.GATE2.phase_gap_integrality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

/-- **The one-step phase gap for the critical Böttcher coordinate**: if the Böttcher equation
`φ (F c z) = (φ z)^1024` holds at `z` and `1023 α ∈ ℤ`, then the `α`-relative deviation of `F c z`
is `1024` times that of `z`, up to an integer.  (The integer is killed by the window in
`deviation_shift_eq` below.) -/
private theorem deviation_F_step {c z : ℂ} {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ))
    (hfun : Work.Bottcher.varphiCrit c (Work.EL.F c z) =
      (Work.Bottcher.varphiCrit c z) ^ (1024 : ℕ)) :
    ∃ j : ℤ, Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.F c z) =
      1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α z + (j : ℝ) := by
  -- the arguments of the Böttcher coordinates are related by the factor `1024`
  have hArg : (Complex.arg (Work.Bottcher.varphiCrit c (Work.EL.F c z)) : Real.Angle)
      = (1024 : ℕ) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle) := by
    rw [hfun]; exact Complex.arg_pow_coe_angle _ _
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hArg
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hk
  -- hence the same for the normalised Böttcher arguments, modulo the period `1`
  have hb : ∃ k : ℤ, Work.GATE.bAngle (Work.Bottcher.varphiCrit c) (Work.EL.F c z) =
      1024 * Work.GATE.bAngle (Work.Bottcher.varphiCrit c) z + (k : ℝ) := by
    refine ⟨k, ?_⟩
    rw [Work.GATE.bAngle, Work.GATE.bAngle]
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
    field_simp
    linarith [hk]
  -- the arithmetic of the root angle: `(1024 - 1) α = 1023 α ∈ ℤ`
  obtain ⟨s, hs⟩ := hα
  have hαint : ∃ t : ℤ, ((1024 : ℝ) - 1) * α = (t : ℝ) := by
    refine ⟨s, ?_⟩
    have h1 : ((1024 : ℝ) - 1) * α = 1023 * α := by norm_num
    rw [h1, hs]
  -- the phase-gap step
  obtain ⟨j, hj⟩ := Work.GATE2.PhaseGap.exists_int_repPhase_comb (α := α)
    (bw := Work.GATE.bAngle (Work.Bottcher.varphiCrit c) (Work.EL.F c z))
    (bz := Work.GATE.bAngle (Work.Bottcher.varphiCrit c) z) (n := 1024) hb hαint
  refine ⟨j, ?_⟩
  rw [Work.GATE2.PhaseGap.deviation_eq_repPhase (Work.Bottcher.varphiCrit c) α (Work.EL.F c z),
    Work.GATE2.PhaseGap.deviation_eq_repPhase (Work.Bottcher.varphiCrit c) α z]
  simpa using hj

theorem deviation_shift_eq {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = s) {z : ℂ}
    (hz : z ∈ Work.ParamRays.critDomain c)
    (hFz : Work.EL.F c z ∈ Work.ParamRays.critDomain c)
    (hwin : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) α z| < 1 / 2048) :
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.F c z) =
      1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α z := by
  -- the functional equation of the critical Böttcher coordinate along the high return map
  have hfun : Work.Bottcher.varphiCrit c (Work.EL.F c z) =
      (Work.Bottcher.varphiCrit c z) ^ (1024 : ℕ) := by
    have h := Work.GATE2.varphiCrit_F_iterate (c := c) hz 1
    rw [Function.iterate_one, pow_one] at h
    exact h.symm
  obtain ⟨j, hj⟩ := deviation_F_step (c := c) (z := z) hα hfun
  -- the window kills the integer: `|deviation (F c z)| ≤ 1/2` and `|1024 · deviation z| < 1/2`
  have hmem := Work.GATE.deviation_mem (Work.Bottcher.varphiCrit c) α (Work.EL.F c z)
  have hzw := abs_lt.mp hwin
  have hj0 : j = 0 := by
    have hlo : (-1 : ℝ) < (j : ℝ) := by
      have h1 := hmem.1; have h2 := hzw.2; rw [hj] at h1; linarith
    have hhi : (j : ℝ) < 1 := by
      have h1 := hmem.2; have h2 := hzw.1; rw [hj] at h1; linarith
    have hjlo : (-1 : ℤ) < j := by exact_mod_cast hlo
    have hjhi : j < 1 := by exact_mod_cast hhi
    omega
  rw [hj0, Int.cast_zero, add_zero] at hj
  exact hj

end Work.GATE2.EXL
