/-
# GATE2 — joint continuity of the `α`-relative Böttcher deviation

The `α`-relative deviation `Work.GATE.deviation φ α z` (`Submission/Work/GATE/Gate/Defs.lean`) is
the representative of the Böttcher argument of `φ z`, shifted by `α`, in the window
`(-1/2, 1/2]`.  The point of this module is that this *is* a continuous function of the pair
`(c, z)`, in the form in which the `G3`-window of the gate needs it
(`Submission/Work/GATE2/Window.lean`, field `hdev`).

## Why this is not `ContinuousOn.comp`

`Complex.arg` is *discontinuous* across the negative real axis: for `w → w₀ ∈ (-∞,0)` the limit of
`arg w` is `π` from one side and `-π` from the other, while `arg w₀ = π`.  The deviation repairs
exactly this: the lift `bAngle φ z + ⌊α - bAngle φ z + 1/2⌋` (= `α + deviation φ α z`) is
*continuous* even where `arg` jumps, because the integer shift changes by `1` at the same moment
that the branch of `arg` changes by `2π`.

The clean way to see this is to read the deviation off the **`Real.Angle`-valued argument**
`(Complex.arg w : Real.Angle)`, which Mathlib knows to be continuous wherever `w ≠ 0`
(`Complex.continuousAt_arg_coe_angle`) — the jump of `arg` by `2π` is absorbed by the quotient
`ℝ ⧸ 2πℤ`.  The deviation is then

`deviation φ α z = ((arg (φ z) : Real.Angle) - (2πα : Real.Angle)).toReal / (2π)`

(`deviation_eq_devOfValue`), i.e. the composite of the continuous angle-valued map with
`Real.Angle.toReal`, the representative in `(-π, π]`; and `toReal` is continuous at every angle
whose representative is not `±π`, in particular wherever its representative lies in
`(-π/2, π/2)` (`continuousAt_toReal_angle`).  The hypothesis `|deviation φ α z₀| < 1/4` forces
the representative `2π · deviation φ α z₀` into `(-π/2, π/2)`.

## Main results

* `Work.GATE2.devOfValue`, `Work.GATE2.deviation_eq_devOfValue`,
  `Work.GATE2.toIocMod_scaleReal`;
* `Work.GATE2.continuousAt_toReal_angle`, `Work.GATE2.continuousAt_devOfValue`;
* `Work.GATE2.deviation_continuousAt` — the requested lemma.
-/
import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.NAKANE.BottcherJoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar)

/-! ## The deviation as a function of the Böttcher argument -/

/-- The `α`-deviation read off a **value** `w` of the Böttcher coordinate: the representative in
`(-1/2, 1/2]` of `arg w / (2π) - α`, expressed through the `Real.Angle`-valued argument of `w`.

This is `Work.GATE.deviation φ α z` at `w = φ z` (`deviation_eq_devOfValue`), but written entirely
in terms of the continuous angle map `ℂ → Real.Angle` and the representative `toReal`. -/
noncomputable def devOfValue (α : ℝ) (w : ℂ) : ℝ :=
  ((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal / (2 * Real.pi)

/-- **Scaling of the interval representative.**  The representative of `x` in `(-1/2, 1/2]` is
the representative of `2πx` in `(-π, π]` divided by `2π`.  (Both are the unique element of the
corresponding interval congruent to the argument modulo the period.) -/
theorem toIocMod_scaleReal (x : ℝ) :
    toIocMod (p := 1) one_pos (-1 / 2) x =
      toIocMod (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi) (2 * Real.pi * x) / (2 * Real.pi) := by
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
  refine (toIocMod_eq_iff (p := 1) one_pos (a := -1 / 2) (b := x)).mpr ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ :=
      toIocMod_mem_Ioc (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi) (2 * Real.pi * x)
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ Real.two_pi_pos]
      rw [show (-1 / 2 : ℝ) * (2 * Real.pi) = -Real.pi by ring]
      linarith
    · rw [div_le_iff₀ Real.two_pi_pos]
      rw [show (-1 / 2 + 1 : ℝ) * (2 * Real.pi) = Real.pi by ring]
      linarith
  · refine ⟨toIocDiv (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi) (2 * Real.pi * x), ?_⟩
    have h := toIocMod_add_toIocDiv_zsmul (p := 2 * Real.pi) Real.two_pi_pos (-Real.pi)
      (2 * Real.pi * x)
    rw [zsmul_eq_mul] at h
    rw [zsmul_eq_mul, mul_one]
    refine mul_left_cancel₀ h2π ?_
    conv_lhs => rw [← h]
    rw [mul_add, mul_div_cancel₀ _ h2π]
    ring

/-- **The deviation is a function of the Böttcher coordinate only**: in the `Real.Angle` form
`devOfValue`. -/
theorem deviation_eq_devOfValue (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    Work.GATE.deviation φ α z = devOfValue α (φ z) := by
  -- the deviation is the representative of `bAngle φ z - α` in `(-1/2, 1/2]`
  have h1 : Work.GATE.deviation φ α z =
      toIocMod (p := 1) one_pos (-1 / 2) (Work.GATE.bAngle φ z - α) := by
    symm
    refine (toIocMod_eq_iff (p := 1) one_pos (a := -1 / 2)
      (b := Work.GATE.bAngle φ z - α)).mpr ⟨?_, ?_⟩
    · obtain ⟨hlo, hhi⟩ := Work.GATE.deviation_mem φ α z
      refine ⟨by linarith, ?_⟩
      rw [show (-1 / 2 + 1 : ℝ) = 1 / 2 by norm_num]
      exact hhi
    · refine ⟨-⌊α - Work.GATE.bAngle φ z + 1 / 2⌋, ?_⟩
      rw [zsmul_eq_mul, mul_one, Work.GATE.deviation_def, Work.GATE.liftAngle]
      push_cast
      ring
  rw [h1, toIocMod_scaleReal]
  have hy : 2 * Real.pi * (Work.GATE.bAngle φ z - α)
      = Complex.arg (φ z) - 2 * Real.pi * α := by
    rw [Work.GATE.bAngle]
    field_simp
  rw [hy, devOfValue, ← Real.Angle.coe_sub, Real.Angle.toReal_coe]

/-! ## Continuity of the angle representative -/

/-- `Real.Angle.toReal` is the argument of `cos + i sin` of the angle. -/
theorem toReal_eq_arg_cos_add_sin_mul_I (ψ : Real.Angle) :
    ψ.toReal = Complex.arg ((Real.Angle.cos ψ : ℂ) + (Real.Angle.sin ψ : ℂ) * Complex.I) := by
  rw [← Real.Angle.cos_toReal ψ, ← Real.Angle.sin_toReal ψ, Complex.ofReal_cos,
    Complex.ofReal_sin]
  exact (Complex.arg_cos_add_sin_mul_I ψ.toReal_mem_Ioc).symm

/-- **Continuity of the representative `Real.Angle.toReal`** whenever the representative lies in
the open interval `(-π/2, π/2)` (in particular it is not `±π`, where `toReal` jumps). -/
theorem continuousAt_toReal_angle {θ : Real.Angle} (hθ : |θ.toReal| < Real.pi / 2) :
    ContinuousAt Real.Angle.toReal θ := by
  rw [abs_lt] at hθ
  have hslit : ((Real.Angle.cos θ : ℂ) + (Real.Angle.sin θ : ℂ) * Complex.I)
      ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hcos : 0 < Real.Angle.cos θ := by
      rw [← Real.Angle.cos_toReal θ]
      exact Real.cos_pos_of_mem_Ioo ⟨hθ.1, hθ.2⟩
    simpa using hcos
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

/-- **Continuity of the deviation read off a value**, at a non-zero value whose deviation is
smaller than `1/4` in absolute value (so that the representative is `2π d` with
`|2π d| < π/2`, well inside the interval of continuity of `Real.Angle.toReal`). -/
theorem continuousAt_devOfValue {w : ℂ} {α : ℝ} (hw : w ≠ 0)
    (h : |devOfValue α w| < 1 / 4) : ContinuousAt (devOfValue α) w := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hAw : ((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal
      = 2 * Real.pi * devOfValue α w := by
    rw [devOfValue]
    exact (mul_div_cancel₀ _ (ne_of_gt h2π)).symm
  have hθ : |((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal|
      < Real.pi / 2 := by
    rw [hAw, abs_mul, abs_of_pos h2π]
    nlinarith [h, Real.pi_pos]
  have hcone : ContinuousAt (fun x : ℂ => (Complex.arg x : Real.Angle)) w :=
    Complex.continuousAt_arg_coe_angle hw
  have harg : ContinuousAt (fun x : ℂ =>
      (Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)) w :=
    ContinuousAt.sub hcone
      (continuousAt_const : ContinuousAt (fun _ : ℂ => ((2 * Real.pi * α : ℝ) : Real.Angle)) w)
  have htr : ContinuousAt Real.Angle.toReal
      ((Complex.arg w : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)) :=
    continuousAt_toReal_angle hθ
  have hcomp : ContinuousAt (fun x : ℂ =>
      ((Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal) w :=
    ContinuousAt.comp (g := Real.Angle.toReal)
      (f := fun x : ℂ => (Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle))
      htr harg
  change ContinuousAt (fun x : ℂ =>
    ((Complex.arg x : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal
      / (2 * Real.pi)) w
  exact hcomp.div_const (2 * Real.pi)

/-! ## The requested continuity -/

/-- **The `α`-relative Böttcher deviation is jointly continuous** at the parameter/point pair
`(c₀, z₀)`, as long as `z₀` is in the critical domain of `T_{c₀}` (so that `(c,z) ↦ φ_c(z)` is
jointly continuous there and `φ_{c₀}(z₀) ≠ 0`) and the deviation of `z₀` is smaller than `1/4`
in absolute value, so that its representative is away from the branch points `±π` of
`Real.Angle.toReal`. -/
theorem deviation_continuousAt {c₀ z₀ : ℂ} (hz : z₀ ∈ Work.ParamRays.critDomain c₀) {α : ℝ}
    (h : |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z₀| < 1 / 4) :
    ∀ ε > 0, ∃ ρ > 0, ∀ e : ℂ, ‖e - c₀‖ < ρ → ∀ z : ℂ, ‖z - z₀‖ < ρ →
      |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α z -
        Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α z₀| < ε := by
  have hne : Work.Bottcher.varphiCrit c₀ z₀ ≠ 0 := Work.Bottcher.varphiCrit_ne_zero hz
  have hsmall : |devOfValue α (Work.Bottcher.varphiCrit c₀ z₀)| < 1 / 4 := by
    rwa [← deviation_eq_devOfValue]
  have hD : ContinuousAt (devOfValue α) (Work.Bottcher.varphiCrit c₀ z₀) :=
    continuousAt_devOfValue hne hsmall
  have hΦ : ContinuousAt (fun p : ℂ × ℂ => Work.Bottcher.varphiCrit p.1 p.2) (c₀, z₀) :=
    Work.NAKANE.continuousAt_jointVarphi hz
  have hG : ContinuousAt
      (fun p : ℂ × ℂ => devOfValue α (Work.Bottcher.varphiCrit p.1 p.2)) (c₀, z₀) :=
    ContinuousAt.comp (g := devOfValue α)
      (f := fun p : ℂ × ℂ => Work.Bottcher.varphiCrit p.1 p.2) hD hΦ
  rw [Metric.continuousAt_iff] at hG
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hG ε hε
  refine ⟨δ, hδ, fun e he z hz' => ?_⟩
  have hmem : dist (e, z) (c₀, z₀) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by rwa [dist_eq_norm], by rwa [dist_eq_norm]⟩
  have hres : dist (devOfValue α (Work.Bottcher.varphiCrit e z))
      (devOfValue α (Work.Bottcher.varphiCrit c₀ z₀)) < ε := hδ' (x := (e, z)) hmem
  rw [Real.dist_eq] at hres
  simpa only [deviation_eq_devOfValue] using hres

end Work.GATE2
