/-
# `FTS/PhiStar/CoreAux/fields_smooth.lean` — `C^∞`-on-the-open-quadrant regularity of the
`Φ̃_*`-fields of the `StarPkgo2` witness

`VocabO2.StarCore α Cs Φs` supplies the flat bounds `FlatW 7 (Ycheck α Φs) (Cs·α)` for the
single object `Ŷ = ((z+1)/z)·(Φ̃_*/σ)`, `Φ̃_* = PhiTs α Φs`, `σ = sin 2θ`.  The eleven fields
of `StarPkgo2` are *algebraic* combinations of `Ŷ` and its first two blocks (`D_zŶ`, `D_θŶ`),
so once `Ŷ` is `C^∞` on the open quadrant `Q0 = (0,∞)×(0,π/2)` so is every field.

This file proves that directly, by *flat calculus on `Q0`*: the transport coefficients of
`Work.Construction`,

* `ℛ(Ψ) = (2 sinθ·Ψ + α sinθ·(z∂_zΨ) + cosθ·∂_θΨ)/cos θ`,
* `𝒱(Ψ) = ∂_θΨ - tan θ·Ψ`,
* `𝒰(Ψ) = -3Ψ - α(z∂_zΨ)`,

together with the two multipliers `(z+1)/z` and `1/sin 2θ` occurring in the witness, are all
`C^∞` on `Q0` as soon as `Ψ` is: the only denominators are `cos θ` (`θ < π/2`) and `sin 2θ`
(`θ > 0`), and `tan θ = sin θ / cos θ`.  The starting point is
`CoreAux/smoothOpen_PhiTs`, which gives `SmoothOpen (PhiTs α Φs)` together with `Φ̃_*/σ` and
`Ŷ` — the latter being exactly the `(z+1)/z`-multiple of `Φ̃_*/σ`.

Since `SmoothOpen` is `ContDiffOn ℝ smoothOrder (uncurry ·) Q0`, everything reduces to the
`ContDiffOn` closure rules (`ContDiffOn.add/sub/mul/div`) transferred to the curried two
variable setting; the transfer lemmas `soAdd`/`soSub`/`soMul`/`soDiv` are stated with the
*exact* shape `fun z θ => f z θ ⋆ g z θ` so that no higher-order unification (which would
have to guess the split of a product into its two factors) is needed at the point of use.

Everything here is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Closure of `SmoothOpen` under the pointwise operations

The curried forms of `ContDiffOn.add`, `ContDiffOn.sub`, `ContDiffOn.mul` and
`ContDiffOn.div`. -/

private theorem soMul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact hf.mul hg

private theorem soAdd {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact hf.add hg

private theorem soSub {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact hf.sub hg

/-- Division is legitimate on `Q0` as soon as the denominator does not vanish there. -/
private theorem soDiv {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hne : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ ≠ 0) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  refine hf.div hg ?_
  intro p hp
  obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact hne p.1 p.2 hz hθ hθ'

private theorem soConstMul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-- A function of `θ` alone, globally `C^∞` on `ℝ`, is `C^∞` on the open quadrant. -/
private theorem soThetaOnly {a : ℝ → ℝ} (ha : ContDiff ℝ Work.Stability.smoothOrder a) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => a θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2) _
  exact (ha.comp contDiff_snd).contDiffOn

/-- `SmoothOpen` only sees the open quadrant: agreement there transfers the property. -/
private theorem soCongr {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  refine ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n).congr ?_
  intro p hp
  obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ hθ').symm

/-! ## The elementary factors -/

/-- The radius `(z, θ) ↦ z`. -/
private theorem soZ : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1) _
  exact contDiffOn_fst

/-- The multiplier `(z+1)/z` of the witness; its only singularity `z = 0` is outside `Q0`. -/
private theorem soZp1divZ : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1) / z) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (p.1 + 1) / p.1) _
  refine ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

private theorem soSin : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin θ) :=
  soThetaOnly Real.contDiff_sin

private theorem soCos : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos θ) :=
  soThetaOnly Real.contDiff_cos

/-- `tan θ = sin θ / cos θ` on the open quadrant, where `cos θ > 0`. -/
private theorem soTan : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.tan θ) := by
  refine soCongr (soDiv soSin soCos ?_) ?_
  · intro z θ _ _ hθ'
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ'⟩)
  · intro z θ _ _ _
    exact (Real.tan_eq_sin_div_cos θ).symm

private theorem soS2 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) :=
  soThetaOnly (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

/-- `cos θ ≠ 0` on the open quadrant. -/
private theorem so_C_ne (z θ : ℝ) (_ : 0 < z) (_ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ'⟩)

/-- `sin 2θ ≠ 0` on the open quadrant. -/
private theorem so_S_ne (z θ : ℝ) (_ : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ']))

/-! ## The three transport coefficients -/

/-- **`ℛ` is `C^∞` on the open quadrant** for a `C^∞` datum: `ℛ(Ψ)` is a sum of the three
terms `2 sinθ·Ψ`, `α sinθ·z∂_zΨ`, `cosθ·∂_θΨ` divided by `cos θ`, which is nonzero on `Q0`. -/
private theorem soRop {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * Real.sin θ * Ψ z θ) :=
    soMul (f := fun z θ : ℝ => 2 * Real.sin θ) (g := Ψ) (soConstMul 2 soSin) hΨ
  have h2a : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Real.sin θ * z) :=
    soMul (f := fun z θ : ℝ => α * Real.sin θ) (g := fun z θ : ℝ => z)
      (soConstMul α soSin) soZ
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * Real.sin θ * z * Work.Spaces.pz Ψ z θ) :=
    soMul (f := fun z θ : ℝ => α * Real.sin θ * z) (g := Work.Spaces.pz Ψ) h2a hΨ.pz
  have h3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.cos θ * Work.Spaces.pth Ψ z θ) :=
    soMul (f := fun z θ : ℝ => Real.cos θ) (g := Work.Spaces.pth Ψ) soCos hΨ.pth
  have h12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ) :=
    soAdd (f := fun z θ : ℝ => 2 * Real.sin θ * Ψ z θ)
      (g := fun z θ : ℝ => α * Real.sin θ * z * Work.Spaces.pz Ψ z θ) h1 h2
  have h123 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
        + Real.cos θ * Work.Spaces.pth Ψ z θ)) :=
    soAdd (f := fun z θ : ℝ => 2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ)
      (g := fun z θ : ℝ => Real.cos θ * Work.Spaces.pth Ψ z θ) h12 h3
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
        + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ) :=
    soDiv (f := fun z θ : ℝ => 2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
        + Real.cos θ * Work.Spaces.pth Ψ z θ)
      (g := fun z θ : ℝ => Real.cos θ) h123 soCos so_C_ne
  unfold Work.Construction.Rop
  exact hfin

/-- **`𝒱` is `C^∞` on the open quadrant**: `𝒱(Ψ) = ∂_θΨ - tan θ·Ψ`. -/
private theorem soVop {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    soMul (f := fun z θ : ℝ => Real.tan θ) (g := Ψ) soTan hΨ
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ) :=
    soSub (f := Work.Spaces.pth Ψ) (g := fun z θ : ℝ => Real.tan θ * Ψ z θ) hΨ.pth h2
  unfold Work.Construction.Vop
  exact hfin

/-- **`𝒰` is `C^∞` on the open quadrant**: `𝒰(Ψ) = -3Ψ - α(z∂_zΨ)`. -/
private theorem soUop (α : ℝ) {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -3 * Ψ z θ) := soConstMul (-3) hΨ
  have h2a : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * z) :=
    soConstMul (f := fun z θ : ℝ => z) α soZ
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * z * Work.Spaces.pz Ψ z θ) :=
    soMul (f := fun z θ : ℝ => α * z) (g := Work.Spaces.pz Ψ) h2a hΨ.pz
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ) :=
    soSub (f := fun z θ : ℝ => -3 * Ψ z θ) (g := fun z θ : ℝ => α * z * Work.Spaces.pz Ψ z θ)
      h1 h2
  unfold Work.Construction.Uop
  exact hfin

/-! ## The target -/

theorem fields_smooth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen Φs) : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)) ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) :=
    (smoothOpen_PhiTs hα hα1 hsm).1
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) :=
    soRop hΨ
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) :=
    soVop hΨ
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) :=
    soUop α hΨ
  have hU2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) :=
    soDiv (f := Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))
      (g := fun z θ : ℝ => Real.sin (2 * θ)) hU soS2 so_S_ne
  refine ⟨hΨ, ?_, hV, ?_, ?_, ?_, ?_⟩
  · exact soMul (f := fun z θ : ℝ => (z + 1) / z)
      (g := Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) soZp1divZ hR
  · exact soMul (f := fun z θ : ℝ => (z + 1) / z)
      (g := Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) soZp1divZ hV
  · exact hU2
  · exact soMul (f := fun z θ : ℝ => (z + 1) / z)
      (g := fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) soZp1divZ hU2
  · exact hU.pth

end Work.FTS.PhiStar.CoreAux
