/-
# GATE2 / EXL — the deviation window of the backwards leg

`Work.GATE2.EXL.deviation_shift_eq` is the *forward* step of the `1024`-fold Böttcher branch:
for `z` in the critical domain whose `α`-deviation is smaller than `1/2048`,

    deviation α (F c z) = 1024 · deviation α z.

The present module is the *backwards* reading of the same identity, in the form the consumers of
the exit loop use (the leg `A r - 1` of the curve `A`): along a continuous curve `A` of the
`Ψ`-plane — with `F c (Ψ (A r - 1)) = Ψ (A r)` by the equivariance `Ψ (w + 1) = F c (Ψ w)` of the
flower — the deviation of the *back* leg is controlled by the deviation of the front leg,

    |deviation α (Ψ (A r - 1))| < 1/2048    whenever    |deviation α (Ψ (A r))| < 1/16384.

## Mathematics

By `Work.GATE2.varphiCrit_F_iterate` the critical Böttcher coordinate satisfies
`(φ z)^1024 = φ (F c z)` on `critDomain c`; hence the Böttcher arguments are related by
`bAngle (F c z) ≡ 1024 · bAngle z (mod 1)`, and the phase-gap step
(`Work.GATE2.PhaseGap.exists_int_repPhase_comb`) converts this into the integral relation

    deviation α (F c z) = 1024 · deviation α z + j,        j ∈ ℤ,

because `(1024 - 1) α = 1023 α ∈ ℤ` (hypothesis `hα`).  With `z = Ψ (A r - 1)` and
`F c z = Ψ (A r)` this reads

    f r := deviation α (Ψ (A r)) - 1024 · deviation α (Ψ (A r - 1)) ∈ ℤ.

* `f` is **continuous**: both legs lie in `critDomain c` (`hcrit`, `hcrit1`), so the deviation is
  continuous along them.  The library continuity lemma requires `|deviation| < 1/4`; the sharp
  bound is `|deviation| < 1/2` (the only discontinuity of `Real.Angle.toReal` is at the
  representative `π`, i.e. at `deviation = 1/2`), and that sharp form is proved here.
* `f 1 = 0`: the base conditions `hbase`, `hbase1` put both base deviations at `0`.
* the unit interval is connected, so an integer-valued continuous `f` is locally constant; hence
  `f ≡ f 1 = 0`, i.e. the deviation is *divided by* `1024` under the shift `A r ↦ A r - 1`.

The only point where the sharp continuity bound is needed is `deviation = 1/2`.  That case is
excluded by `hzero`: a vanishing front deviation forces `r = 1`, where `hbase` puts the back
deviation at `0`.

Since `|deviation α (Ψ (A r - 1))| = |deviation α (Ψ (A r))| / 1024 < 1/16384 / 1024`, the
requested bound `1/2048` is comfortably met.
-/
import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.EXL.deviation_shift_eq
import Submission.Work.GATE2.EXL.MinCrossing
import Submission.Work.GATE2.deviation_continuousAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Filter Set

namespace Work.GATE2.EXL

/-! ## Two continuity lemmas for the deviation, sharpened to `|deviation| < 1/2` -/

/-- `Real.Angle.toReal` is continuous at `θ` unless the representative is `π`, its only jump. -/
theorem continuousAt_toReal_angle_of_ne_pi {θ : Real.Angle} (hθ : θ.toReal ≠ Real.pi) :
    ContinuousAt Real.Angle.toReal θ := by
  have hslit : ((Real.Angle.cos θ : ℂ) + (Real.Angle.sin θ : ℂ) * Complex.I)
      ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    have hre : ((Real.Angle.cos θ : ℂ) + (Real.Angle.sin θ : ℂ) * Complex.I).re
        = Real.Angle.cos θ := by simp
    have him : ((Real.Angle.cos θ : ℂ) + (Real.Angle.sin θ : ℂ) * Complex.I).im
        = Real.Angle.sin θ := by simp
    rw [hre, him]
    by_cases hc : 0 < Real.Angle.cos θ
    · exact Or.inl hc
    · refine Or.inr fun hsin => ?_
      have hsq : Real.Angle.cos θ ^ 2 = 1 := by
        have h := Real.Angle.cos_sq_add_sin_sq θ
        rw [hsin] at h
        nlinarith
      rcases sq_eq_one_iff.mp hsq with h1 | h1
      · rw [h1] at hc; norm_num at hc
      · rcases Real.Angle.sin_eq_zero_iff.mp hsin with h2 | h2
        · rw [h2] at h1; rw [Real.Angle.cos_zero] at h1; norm_num at h1
        · rw [h2] at hθ; rw [Real.Angle.toReal_pi] at hθ; exact hθ rfl
  have hmap : Continuous (fun ψ : Real.Angle =>
      (Real.Angle.cos ψ : ℂ) + (Real.Angle.sin ψ : ℂ) * Complex.I) := by
    have h1 : Continuous fun ψ : Real.Angle => ((Real.Angle.cos ψ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp Real.Angle.continuous_cos
    have h2 : Continuous fun ψ : Real.Angle => ((Real.Angle.sin ψ : ℝ) : ℂ) * Complex.I :=
      (Complex.continuous_ofReal.comp Real.Angle.continuous_sin).mul continuous_const
    exact h1.add h2
  have hcont : ContinuousAt (fun ψ : Real.Angle =>
      Complex.arg ((Real.Angle.cos ψ : ℂ) + (Real.Angle.sin ψ : ℂ) * Complex.I)) θ :=
    ContinuousAt.comp (g := Complex.arg)
      (f := fun ψ : Real.Angle =>
        (Real.Angle.cos ψ : ℂ) + (Real.Angle.sin ψ : ℂ) * Complex.I)
      (Complex.continuousAt_arg hslit) hmap.continuousAt
  exact hcont.congr (Eventually.of_forall fun ψ => (toReal_eq_arg_cos_add_sin_mul_I ψ).symm)

/-- **Continuity of the deviation read off a value, at the sharp bound `|deviation| < 1/2`.** -/
theorem continuousAt_devOfValue_of_abs_lt_half {w : ℂ} {α : ℝ} (hw : w ≠ 0)
    (h : |devOfValue α w| < 1 / 2) : ContinuousAt (devOfValue α) w := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hAw : ((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal
      = 2 * Real.pi * devOfValue α w := by
    rw [devOfValue]
    exact (mul_div_cancel₀ _ (ne_of_gt h2π)).symm
  have hne : ((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal
      ≠ Real.pi := by
    intro hpi
    have hlt : |((Complex.arg w : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal| < Real.pi := by
      rw [hAw, abs_mul, abs_of_pos h2π]
      nlinarith [h, Real.pi_pos]
    rw [hpi, abs_of_pos Real.pi_pos] at hlt
    linarith [Real.pi_pos]
  have hcone : ContinuousAt (fun x : ℂ => (Complex.arg x : Real.Angle)) w :=
    Complex.continuousAt_arg_coe_angle hw
  have harg : ContinuousAt (fun x : ℂ =>
      (Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)) w :=
    ContinuousAt.sub hcone
      (continuousAt_const : ContinuousAt (fun _ : ℂ => ((2 * Real.pi * α : ℝ) : Real.Angle)) w)
  have htr : ContinuousAt Real.Angle.toReal
      ((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)) :=
    continuousAt_toReal_angle_of_ne_pi hne
  have hcomp : ContinuousAt (fun x : ℂ =>
      ((Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal) w :=
    ContinuousAt.comp (g := Real.Angle.toReal)
      (f := fun x : ℂ => (Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle))
      htr harg
  change ContinuousAt (fun x : ℂ =>
    ((Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal
      / (2 * Real.pi)) w
  exact hcomp.div_const (2 * Real.pi)

/-- **The `α`-deviation of the critical Böttcher coordinate is continuous at every point of the
critical domain at which it is different from `1/2`**, i.e. throughout the interval
`|deviation| < 1/2` in which the representative `Real.Angle.toReal` is continuous. -/
theorem continuousAt_deviation_varphiCrit_of_abs_lt_half {c z : ℂ}
    (hz : z ∈ Work.ParamRays.critDomain c) {α : ℝ}
    (h : |Work.GATE.deviation (Work.Bottcher.varphiCrit c) α z| < 1 / 2) :
    ContinuousAt (Work.GATE.deviation (Work.Bottcher.varphiCrit c) α) z := by
  have hφ : ContinuousAt (Work.Bottcher.varphiCrit c) z :=
    (Work.Bottcher.varphiCrit_continuousOn c).continuousAt
      ((Work.ParamRays.isOpen_critDomain c).mem_nhds hz)
  have hw0 : Work.Bottcher.varphiCrit c z ≠ 0 := Work.Bottcher.varphiCrit_ne_zero hz
  have hs : |devOfValue α (Work.Bottcher.varphiCrit c z)| < 1 / 2 := by
    rwa [← Work.GATE2.deviation_eq_devOfValue]
  have hfun : Work.GATE.deviation (Work.Bottcher.varphiCrit c) α
      = fun z => devOfValue α (Work.Bottcher.varphiCrit c z) := by
    funext z
    exact Work.GATE2.deviation_eq_devOfValue _ _ _
  rw [hfun]
  exact (continuousAt_devOfValue_of_abs_lt_half hw0 hs).comp
    (f := fun w : ℂ => Work.Bottcher.varphiCrit c w) hφ

/-! ## The integral one-step relation of the deviation along the high return map -/

/-- **The one-step phase gap for the critical Böttcher coordinate** (the public form of the
private step of `Work.GATE2.EXL.deviation_shift_eq`): if the Böttcher equation
`φ (F c z) = (φ z)^1024` holds at `z` and `1023 α ∈ ℤ`, then the `α`-relative deviation of
`F c z` is `1024` times that of `z`, up to an integer. -/
private theorem deviation_F_step {c z : ℂ} {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ))
    (hfun : Work.Bottcher.varphiCrit c (Work.EL.F c z) =
      (Work.Bottcher.varphiCrit c z) ^ (1024 : ℕ)) :
    ∃ j : ℤ, Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.F c z) =
      1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α z + (j : ℝ) := by
  have hArg : (Complex.arg (Work.Bottcher.varphiCrit c (Work.EL.F c z)) : Real.Angle)
      = (1024 : ℕ) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle) := by
    rw [hfun]; exact Complex.arg_pow_coe_angle _ _
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hArg
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hk
  have hb : ∃ k : ℤ, Work.GATE.bAngle (Work.Bottcher.varphiCrit c) (Work.EL.F c z) =
      1024 * Work.GATE.bAngle (Work.Bottcher.varphiCrit c) z + (k : ℝ) := by
    refine ⟨k, ?_⟩
    rw [Work.GATE.bAngle, Work.GATE.bAngle]
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
    field_simp
    linarith [hk]
  obtain ⟨s, hs⟩ := hα
  have hαint : ∃ t : ℤ, ((1024 : ℝ) - 1) * α = (t : ℝ) := by
    refine ⟨s, ?_⟩
    have h1 : ((1024 : ℝ) - 1) * α = 1023 * α := by norm_num
    rw [h1, hs]
  obtain ⟨j, hj⟩ := Work.GATE2.PhaseGap.exists_int_repPhase_comb (α := α)
    (bw := Work.GATE.bAngle (Work.Bottcher.varphiCrit c) (Work.EL.F c z))
    (bz := Work.GATE.bAngle (Work.Bottcher.varphiCrit c) z) (n := 1024) hb hαint
  refine ⟨j, ?_⟩
  rw [Work.GATE2.PhaseGap.deviation_eq_repPhase (Work.Bottcher.varphiCrit c) α (Work.EL.F c z),
    Work.GATE2.PhaseGap.deviation_eq_repPhase (Work.Bottcher.varphiCrit c) α z]
  simpa using hj

/-! ## The window of the backwards leg -/

theorem deviation_shift_window {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = s) (A : C(unitInterval, ℂ))
    (hcrit : ∀ r : unitInterval, fl.Ψ (A r - 1) ∈ Work.ParamRays.critDomain c)
    (hcrit1 : ∀ r : unitInterval, fl.Ψ (A r) ∈ Work.ParamRays.critDomain c)
    (hsmall : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r))| < 1 / 16384)
    (hzero : ∀ r : unitInterval,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) = 0 → r = 1)
    (hbase : Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A 1 - 1)) = 0)
    (hbase1 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A 1)) = 0) :
    ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1))| < 1 / 2048 := by
  -- the equivariance of `Ψ` turns the shift `A r - 1 ↦ A r` into the high return map `F c`
  have hsh : ∀ r : unitInterval, fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)) := by
    intro r
    have h := fl.Ψ_shift (A r - 1)
    rwa [sub_add_cancel] at h
  -- the one-step relation, with an integral error
  have hstep : ∀ r : unitInterval, ∃ j : ℤ,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) =
        1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1))
          + (j : ℝ) := by
    intro r
    have hz : fl.Ψ (A r - 1) ∈ Work.ParamRays.critDomain c := hcrit r
    have hfun : Work.Bottcher.varphiCrit c (Work.EL.F c (fl.Ψ (A r - 1))) =
        (Work.Bottcher.varphiCrit c (fl.Ψ (A r - 1))) ^ (1024 : ℕ) := by
      have h := Work.GATE2.varphiCrit_F_iterate (c := c) (z := fl.Ψ (A r - 1)) hz 1
      simp only [pow_one, Function.iterate_one] at h
      exact h.symm
    obtain ⟨j, hj⟩ := deviation_F_step (c := c) (z := fl.Ψ (A r - 1)) hα hfun
    exact ⟨j, by rw [hsh r]; exact hj⟩
  -- the error is an integer, i.e. `f r := deviation (A r) - 1024 · deviation (A r - 1) ∈ ℤ`
  have hfint : ∀ r : unitInterval, ∃ j : ℤ,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) -
        1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1))
          = (j : ℝ) := by
    intro r
    obtain ⟨j, hj⟩ := hstep r
    exact ⟨j, by linarith⟩
  -- the sharp continuity bound `deviation ≠ 1/2` on the back leg
  have hne_half : ∀ r : unitInterval,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1)) ≠ 1 / 2 := by
    intro r hdev
    obtain ⟨j, hj⟩ := hstep r
    -- a vanishing front deviation forces `r = 1`
    have h0 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) = 0 := by
      have hb := hsmall r
      rw [hdev] at hj
      have hj512 : j + 512 = 0 := by
        have hcast : ((j + 512 : ℤ) : ℝ) = 512 + (j : ℝ) := by push_cast; ring
        have habs : |((j + 512 : ℤ) : ℝ)| < 1 := by
          rw [hcast]
          have h512 : (512 : ℝ) + (j : ℝ) = 1024 * (1 / 2) + (j : ℝ) := by norm_num
          rw [h512, ← hj]
          linarith [hb, (by norm_num : (1 : ℝ) / 16384 < 1)]
        rw [← Int.cast_abs] at habs
        exact Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
      have hji : (j : ℝ) = -512 := by
        have hcast : ((j + 512 : ℤ) : ℝ) = 0 := by rw [hj512]; norm_num
        push_cast at hcast
        linarith
      rw [hji] at hj
      rw [hj]; norm_num
    have hr1 : r = 1 := hzero r h0
    rw [hr1] at hdev
    have hb := hbase
    rw [hdev] at hb
    norm_num at hb
  have hback_half : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1))| < 1 / 2 := by
    intro r
    obtain ⟨h1, h2⟩ := Work.GATE.deviation_mem (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1))
    exact abs_lt.mpr ⟨h1, lt_of_le_of_ne h2 (hne_half r)⟩
  -- continuity of the two legs
  have hcurve1 : Continuous fun r : unitInterval => fl.Ψ (A r) :=
    fl.Ψ_diff.continuous.comp A.continuous
  have hcurve2 : Continuous fun r : unitInterval => fl.Ψ (A r - 1) :=
    fl.Ψ_diff.continuous.comp (A.continuous.sub continuous_const)
  have hcont1 : Continuous fun r : unitInterval =>
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) := by
    rw [continuous_iff_continuousAt]
    intro r
    have hpt : ContinuousAt (Work.GATE.deviation (Work.Bottcher.varphiCrit c) α) (fl.Ψ (A r)) :=
      continuousAt_deviation_varphiCrit_of_abs_lt_half (hcrit1 r)
        (by linarith [hsmall r, (by norm_num : (1 : ℝ) / 16384 < 1 / 2)])
    exact hpt.comp (f := fun r : unitInterval => fl.Ψ (A r)) hcurve1.continuousAt
  have hcont2 : Continuous fun r : unitInterval =>
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1)) := by
    rw [continuous_iff_continuousAt]
    intro r
    have hpt : ContinuousAt (Work.GATE.deviation (Work.Bottcher.varphiCrit c) α)
        (fl.Ψ (A r - 1)) :=
      continuousAt_deviation_varphiCrit_of_abs_lt_half (hcrit r) (hback_half r)
    exact hpt.comp (f := fun r : unitInterval => fl.Ψ (A r - 1)) hcurve2.continuousAt
  -- `f` is continuous and integer valued, hence locally constant on the connected unit interval
  set f : unitInterval → ℝ := fun r =>
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) -
      1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1)) with hfdef
  have hfcont : Continuous f := hcont1.sub (hcont2.const_mul 1024)
  have hfint' : ∀ r : unitInterval, ∃ j : ℤ, f r = (j : ℝ) := by
    intro r
    obtain ⟨j, hj⟩ := hfint r
    exact ⟨j, by rw [hfdef]; exact hj⟩
  have hfzero : f 1 = 0 := by
    show Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A 1)) -
        1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A 1 - 1)) = 0
    rw [hbase1, hbase]
    ring
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro r
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hfcont.continuousAt (1 / 2) (by norm_num)
    refine ⟨Metric.ball r δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun r' hr' => ?_⟩
    obtain ⟨j, hj⟩ := hfint' r
    obtain ⟨j', hj'⟩ := hfint' r'
    have hdist : dist (f r') (f r) < 1 / 2 := hδ' hr'
    rw [Real.dist_eq, hj, hj'] at hdist
    have hlt : |((j' - j : ℤ) : ℝ)| < 1 := by
      rw [Int.cast_sub]
      rw [abs_lt]
      rw [abs_lt] at hdist
      constructor <;> linarith [hdist.1, hdist.2]
    rw [← Int.cast_abs] at hlt
    have hjj : j' - j = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
    have : j' = j := by omega
    simp [hj, hj', this]
  have hfeq : ∀ r : unitInterval, f r = 0 := by
    intro r
    have h := hloc.apply_eq_of_preconnectedSpace r (1 : unitInterval)
    rw [h, hfzero]
  -- conclusion
  intro r
  have hzero' : Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) -
      1024 * Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1)) = 0 :=
    hfeq r
  have hdev : Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r - 1)) =
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (fl.Ψ (A r)) / 1024 := by
    linarith
  rw [hdev, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
  linarith [hsmall r]

end Work.GATE2.EXL
