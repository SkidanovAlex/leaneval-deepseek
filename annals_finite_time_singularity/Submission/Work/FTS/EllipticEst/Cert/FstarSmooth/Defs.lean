/-
# Smoothness of the angular moment `F_*`: definitions and toolkit

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

The angular moment of the elliptic estimates is

  `F_*(z) = ∫_θ F(z,θ) · sin θ cos²θ dθ`  (`Work.Elliptic.Fstar`),

an integral over the fixed interval `Iθ = [0,π/2]`.  The class `Work.FTS.EllipticEst.EllHyp`
gives *no* smoothness of `F` itself: it only says that `F` agrees with `bslOp α Ψ` on the
**open** quadrant, where `Ψ` is smooth on a neighbourhood of the closed quadrant.  The
point is that `bslOp α Ψ` is *not* smooth on a neighbourhood of the closed quadrant — the
term `∂_θ(tan θ · Ψ)` has a jump at `θ = π/2` (Lean's `Real.tan (π/2) = 0` by totalised
division, while `tan θ · Ψ z θ → -∂_θΨ z (π/2)` as `θ → π/2⁻`) — but after multiplication
by the angular weight `sin θ cos²θ` everything is smooth:

  `∂_θ(tan θ Ψ)·sinθcos²θ = (Ψ/cos²θ + tanθ ∂_θΨ)·sinθcos²θ
                          = Ψ sinθ + sin²θ cosθ ∂_θΨ`,

which is manifestly smooth.

This file introduces the resulting *smooth* integrand `FstarInt α Ψ` — the `bslOp` bracket
minus the `tan`-term, times the weight, plus the weight-cancelled `tan`-term — together with
the elementary facts used by the certificate:

* the `SmoothNbhd` toolkit (`+`, `-`, `*`, constants, `z ↦ z^n`, functions of `θ` alone,
  iterated `∂_θ`);
* the derivative identity `∂_θ(tan θ · Ψ) = Ψ/cos²θ + tan θ · ∂_θΨ` away from `cos θ = 0`;
* the pointwise cancellation of the `tan`-pole by the weight (`tan_weight_cancel`), and the
  resulting pointwise identity `bslOp α Ψ z θ · sinθcos²θ = FstarInt α Ψ z θ`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.HProductRule_Msummand
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-! ## The `SmoothNbhd` toolkit -/

/-- `SmoothNbhd` only depends on the values of the function. -/
theorem SmoothNbhd_congr {f g : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f)
    (hfg : ∀ z θ : ℝ, f z θ = g z θ) : Work.Spaces.SmoothNbhd g := by
  change ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.nbhU at h
  change ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU
  exact h.congr fun p _ => (hfg p.1 p.2).symm

/-- Constants are smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_const (c : ℝ) : Work.Spaces.SmoothNbhd (fun _ _ : ℝ => c) :=
  contDiffOn_const

/-- The first coordinate is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_fst : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z _ : ℝ => z) Work.Spaces.nbhU
  have h : (Function.uncurry fun z _ : ℝ => z) = fun p : ℝ × ℝ => p.1 := rfl
  rw [h]
  exact contDiffOn_fst

/-- Powers of the first coordinate are smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_pow_fst (n : ℕ) : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z ^ n) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z _ : ℝ => z ^ n) Work.Spaces.nbhU
  have h : (Function.uncurry fun z _ : ℝ => z ^ n) = fun p : ℝ × ℝ => p.1 ^ n := rfl
  rw [h]
  exact (contDiffOn_fst (𝕜 := ℝ) (s := Work.Spaces.nbhU)).pow n

/-- A function of `θ` alone which is smooth on all of `ℝ` is smooth on a neighbourhood of
the closed quadrant. -/
theorem smoothNbhd_snd_comp (g : ℝ → ℝ) (hg : ContDiff ℝ ⊤ g) :
    Work.Spaces.SmoothNbhd (fun _ θ : ℝ => g θ) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun _ θ : ℝ => g θ) Work.Spaces.nbhU
  have h : (Function.uncurry fun _ θ : ℝ => g θ) = fun p : ℝ × ℝ => g p.2 := rfl
  rw [h]
  exact hg.comp_contDiffOn contDiffOn_snd

/-- Iterated `∂_θ` preserves `SmoothNbhd`. -/
theorem smoothNbhd_pthIter {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    ∀ n : ℕ, Work.Spaces.SmoothNbhd (Work.Spaces.pthIter n f)
  | 0 => h
  | n + 1 => (smoothNbhd_pthIter h n).pth

/-- `SmoothNbhd` is closed under addition. -/
theorem smoothNbhd_add {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothNbhd (fun z θ => f z θ + g z θ) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z θ : ℝ => f z θ + g z θ) Work.Spaces.nbhU
  have h : (Function.uncurry fun z θ : ℝ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := rfl
  rw [h]
  change ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.nbhU at hf
  change ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU at hg
  exact hf.add hg

/-- `SmoothNbhd` is closed under subtraction. -/
theorem smoothNbhd_sub {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothNbhd (fun z θ => f z θ - g z θ) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z θ : ℝ => f z θ - g z θ) Work.Spaces.nbhU
  have h : (Function.uncurry fun z θ : ℝ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := rfl
  rw [h]
  change ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.nbhU at hf
  change ContDiffOn ℝ ⊤ (Function.uncurry g) Work.Spaces.nbhU at hg
  exact hf.sub hg

/-- `SmoothNbhd` is closed under negation. -/
theorem smoothNbhd_neg {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothNbhd (fun z θ => -f z θ) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z θ : ℝ => -f z θ) Work.Spaces.nbhU
  have h : (Function.uncurry fun z θ : ℝ => -f z θ) = -Function.uncurry f := rfl
  rw [h]
  change ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.nbhU at hf
  exact hf.neg

/-- `SmoothNbhd` is closed under multiplication by a scalar. -/
theorem smoothNbhd_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothNbhd (fun z θ => c * f z θ) := by
  change ContDiffOn ℝ ⊤ (Function.uncurry fun z θ : ℝ => c * f z θ) Work.Spaces.nbhU
  have h : (Function.uncurry fun z θ : ℝ => c * f z θ) = c • Function.uncurry f := rfl
  rw [h]
  change ContDiffOn ℝ ⊤ (Function.uncurry f) Work.Spaces.nbhU at hf
  exact hf.const_smul c

/-- `SmoothNbhd` is closed under pointwise multiplication. -/
theorem smoothNbhd_mul' {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothNbhd (fun z θ => f z θ * g z θ) :=
  Work.Spaces.smoothNbhd_mul hf hg

/-! ## The smooth integrand -/

/-- **The smooth form of the integrand of the angular moment.**  On the open quadrant this
equals `bslOp α Ψ z θ · sinθcos²θ`: the `tan`-term of `bslOp` is moved out of the bracket and
replaced by its weight-cancelled form `sin θ · Ψ + sin θ · (sin θ cos θ) · ∂_θΨ`.  Unlike
`bslOp α Ψ`, this is smooth on a neighbourhood of the closed quadrant whenever `Ψ` is. -/
def FstarInt (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (-(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        - Work.Spaces.pthIter 2 Ψ z θ
        - 6 * Ψ z θ)
      * Work.Elliptic.sinCos2 θ
    + (Real.sin θ * Ψ z θ
        + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ)

theorem FstarInt_apply (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    FstarInt α Ψ z θ =
      (-(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
          - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
          - Work.Spaces.pthIter 2 Ψ z θ
          - 6 * Ψ z θ)
        * Work.Elliptic.sinCos2 θ
      + (Real.sin θ * Ψ z θ
          + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ) := rfl

/-! ## The `tan`-derivative away from the pole, and its cancellation by the weight -/

/-- `∂_θ(tan θ · Ψ) = Ψ/cos²θ + tan θ · ∂_θΨ` for `cos θ ≠ 0`. -/
theorem pth_tan_mul (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (fun z θ : ℝ => Real.tan θ * Ψ z θ) z θ
      = (1 / Real.cos θ ^ 2) * Ψ z θ
        + Real.tan θ * Work.Spaces.pth Ψ z θ := by
  have h1 : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have h2 : HasDerivAt (fun θ' : ℝ => Ψ z θ') (Work.Spaces.pth Ψ z θ) θ := hd.hasDerivAt
  have h3 := h1.mul h2
  have hfun : (Real.tan * fun θ' : ℝ => Ψ z θ') = fun θ' : ℝ => Real.tan θ' * Ψ z θ' := by
    funext θ'; rw [Pi.mul_apply]
  rw [hfun] at h3
  simpa only [Work.Spaces.pth] using h3.deriv

/-- **Cancellation of the `tan`-pole by the angular weight:**
`(Ψ/cos²θ + tan θ · ∂_θΨ)·sinθcos²θ = sinθ·Ψ + sinθ·(sinθ cosθ)·∂_θΨ` for `cos θ ≠ 0`. -/
theorem tan_weight_cancel {Ψz Q1 θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    ((1 / Real.cos θ ^ 2) * Ψz + Real.tan θ * Q1) * (Real.sin θ * Real.cos θ ^ 2)
      = Real.sin θ * Ψz + Real.sin θ * (Real.sin θ * Real.cos θ) * Q1 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- The pointwise identity between `bslOp` times the angular weight and the smooth integrand.
It is pure calculus and algebra: the derivative identity `pth_tan_mul` for the `tan`-term,
followed by the cancellation `tan_weight_cancel`. -/
theorem bslOp_mul_sinCos2_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hcos : Real.cos θ ≠ 0) (hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ = FstarInt α Ψ z θ := by
  have hT : Work.Spaces.pth (fun z θ : ℝ => Real.tan θ * Ψ z θ) z θ
        * Work.Elliptic.sinCos2 θ
      = Real.sin θ * Ψ z θ
        + Real.sin θ * (Real.sin θ * Real.cos θ) * Work.Spaces.pth Ψ z θ := by
    rw [Work.Elliptic.sinCos2, pth_tan_mul Ψ hcos hd]
    exact tan_weight_cancel (Ψz := Ψ z θ) (Q1 := Work.Spaces.pth Ψ z θ) hcos
  rw [FstarInt_apply, Work.Elliptic.bslOp, Work.Elliptic.Lzero]
  linear_combination hT

end Work.FTS.EllipticEst.Cert
