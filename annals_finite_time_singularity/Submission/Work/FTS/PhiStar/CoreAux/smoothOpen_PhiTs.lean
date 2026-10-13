import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs`

The `C^∞`-on-the-open-quadrant regularity of the three objects of the `StarCore` witness that
are built out of the datum `Φ_s` and the singular part `Θ_*(α) = Θ α (F_*)`:

* `Φ̃_* = PhiTs α Φs = Φs - Θ_*(α)`,
* `Φ̃_*/sin 2θ`,
* `Ŷ = Ycheck α Φs = ((z+1)/z)·(Φ̃_*/sin 2θ)`.

The only input about `Θ_*(α)` is the profile identity `L₁₂(F_*)(z) = 2α/(1+z)` (`α ≤ 1` is
carried along by `Work.FTS.PhiStar.L12_profile_eq`), which turns it into the explicit function
`(z,θ) ↦ sin(2θ)/(2(1+z))`, `C^∞` on the open quadrant `(0,∞) × (0,π/2)` because `1 + z > 0`
there.  The remaining two conjuncts are closure of `SmoothOpen` under multiplication and under
division by `sin 2θ ≠ 0` (and by `z ≠ 0`), both legitimate on the *open* quadrant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false

/-! ## Closure of `SmoothOpen` under the pointwise algebra (on the open quadrant) -/

/-- `SmoothOpen` is closed under subtraction. -/
private theorem smoothOpen_sub' {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).sub (hg.forall n)

/-- `SmoothOpen` is closed under multiplication. -/
private theorem smoothOpen_mul' {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).mul (hg.forall n)

/-- The quotient by `sin 2θ` of a `C^∞`-on-the-open-quadrant function is again `C^∞` there:
`sin 2θ > 0` for `0 < θ < π/2`. -/
private theorem smoothOpen_div_sin2' {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / Work.Construction.s2 θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf.forall n
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact h1.div h2 (fun p hp => by
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

/-- The radial factor `(z+1)/z` is `C^∞` on the open quadrant (its only singularity, `z = 0`,
is outside `Q0`). -/
private theorem smoothOpen_zPlusOne_div_z' :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => (p.1 + 1) / p.1)
    Work.FTS.EllipticEst.Q0
  exact ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst
    (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-! ## The singular part `Θ_*(α) = sin(2θ)/(2(1+z))` -/

/-- **`Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant**: by
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for `z > 0`) it is the explicit function
`(z,θ) ↦ sin(2θ)/(2(1+z))`. -/
private theorem smoothOpen_ThetaFstar' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hbase : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1)))
      Work.FTS.EllipticEst.Q0 := by
    have hnum : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => 2 * (1 + p.1))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    exact hnum.div hden (fun p hp => by
      have hz : (0 : ℝ) < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      positivity)
  refine (hbase.of_le le_top).congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  show Work.Construction.Theta α (Work.Construction.Fstar α) z θ
      = Real.sin (2 * θ) / (2 * (1 + z))
  rw [Work.FTS.PhiStar.Theta_eq_thetaProfile hα hα1 hz.le θ, Work.FTS.PhiStar.ThetaProfile]
  ring

/-! ## The target -/

theorem smoothOpen_PhiTs {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen Φs) : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.VocabO2.PhiTs α Φs z θ / Work.Construction.s2 θ) ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs) := by
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothOpen_ThetaFstar' hα hα1
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ) :=
    smoothOpen_sub' hsm hΘ
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
        / Work.Construction.s2 θ) :=
    smoothOpen_div_sin2' h1
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * ((Φs z θ
        - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
          / Work.Construction.s2 θ)) :=
    smoothOpen_mul' smoothOpen_zPlusOne_div_z' h2
  refine ⟨?_, ?_, ?_⟩
  · show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact h1
  · show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
        / Work.Construction.s2 θ)
    exact h2
  · show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * ((Φs z θ
        - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
          / Work.Construction.s2 θ))
    exact h3

end Work.FTS.PhiStar.CoreAux
