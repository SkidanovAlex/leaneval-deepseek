/-
Copyright: work module for the Elgindi finite-time singularity project.

# Additivity of the elliptic operator `L` of (PolarBSL)

`bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` with
`L₀Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (see `Submission/Work/Elliptic/Defs.lean`)
is a second order linear differential operator.  This module proves that it is additive,

  `bslOp α (Ψ + Φ) = bslOp α Ψ + bslOp α Φ`

pointwise at `(z,θ)`, under the standing hypothesis that `Ψ` and `Φ` are `C²` (as functions of
`(z,θ)`) near that point.  The `C²` hypothesis is not decoration: `deriv` in Mathlib is the
totalised derivative, so `deriv (f + g) = deriv f + deriv g` genuinely needs differentiability
of the two summands (without it, `f = |·|` and `g = id - |·|` give a counterexample).

The proof reduces the two-variable statements to one-variable ones through the fact that the
slices `z' ↦ Ψ z' θ` and `θ' ↦ Ψ z θ'` of a `C^n` function are `C^n`, and then uses additivity
of `iteratedDeriv` on `C^n` functions.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Slices of a `C^n` function are `C^n` -/

/-- The `z`-slice `z' ↦ Ψ z' θ` of a function which is `C^n` at `(z,θ)` is `C^n` at `z`. -/
lemma contDiffAt_uncurry_slice_fst (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) {n : WithTop ℕ∞}
    (h : ContDiffAt ℝ n (Function.uncurry Ψ) (z, θ)) :
    ContDiffAt ℝ n (fun z' => Ψ z' θ) z := by
  have hg : ContDiffAt ℝ n (fun z' : ℝ => (z', θ)) z := by
    have h1 : ContDiffAt ℝ n (fun z' : ℝ => (ContinuousLinearMap.inl ℝ ℝ ℝ) z') z :=
      ((ContinuousLinearMap.inl ℝ ℝ ℝ).contDiff (n := n)).contDiffAt
    have h2 : ContDiffAt ℝ n (fun _ : ℝ => (((0 : ℝ), θ) : ℝ × ℝ)) z := contDiffAt_const
    have h3 := h1.add h2
    convert h3 using 2
    simp [ContinuousLinearMap.inl_apply]
  exact h.comp z hg

/-- The `θ`-slice `θ' ↦ Ψ z θ'` of a function which is `C^n` at `(z,θ)` is `C^n` at `θ`. -/
lemma contDiffAt_uncurry_slice_snd (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) {n : WithTop ℕ∞}
    (h : ContDiffAt ℝ n (Function.uncurry Ψ) (z, θ)) :
    ContDiffAt ℝ n (fun θ' => Ψ z θ') θ := by
  have hg : ContDiffAt ℝ n (fun θ' : ℝ => (z, θ')) θ := by
    have h1 : ContDiffAt ℝ n (fun θ' : ℝ => (ContinuousLinearMap.inr ℝ ℝ ℝ) θ') θ :=
      ((ContinuousLinearMap.inr ℝ ℝ ℝ).contDiff (n := n)).contDiffAt
    have h2 : ContDiffAt ℝ n (fun _ : ℝ => (((z : ℝ), (0 : ℝ)) : ℝ × ℝ)) θ := contDiffAt_const
    have h3 := h1.add h2
    convert h3 using 2
    simp [ContinuousLinearMap.inr_apply]
  exact h.comp θ hg

/-! ## Additivity of the one-variable first and second derivatives -/

/-- `iteratedDeriv 1` is additive on functions differentiable at the point. -/
lemma iteratedDeriv_one_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (f + g) x = iteratedDeriv 1 f x + iteratedDeriv 1 g x := by
  simp only [iteratedDeriv_one]
  exact deriv_add (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))

/-- `iteratedDeriv 2 f = (deriv ∘ deriv) f`. -/
lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- `iteratedDeriv 2` is additive on functions which are `C²` at the point. -/
lemma iteratedDeriv_two_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (f + g) x = iteratedDeriv 2 f x + iteratedDeriv 2 g x := by
  rw [iteratedDeriv_two_eq, iteratedDeriv_two_eq, iteratedDeriv_two_eq]
  have hfeq : deriv (f + g) =ᶠ[nhds x] deriv f + deriv g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    rw [deriv_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))]
    rfl
  rw [Filter.EventuallyEq.deriv_eq hfeq]
  rw [deriv_add]
  · exact (ContDiffAt.derivWithin hf (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · exact (ContDiffAt.derivWithin hg (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-! ## The curried iterated partials as one-variable iterated derivatives -/

/-- `∂_z^k Ψ z θ` is the `k`-th iterated derivative of the `z`-slice. -/
lemma pzIter_eq_iteratedDeriv (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter k Ψ z θ = iteratedDeriv k (fun z' => Ψ z' θ) z := by
  induction k generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, iteratedDeriv_succ]
    simp only [Work.Spaces.pz]
    congr 1
    funext z'
    exact ih z'

/-- `∂_θ^k Ψ z θ` is the `k`-th iterated derivative of the `θ`-slice. -/
lemma pthIter_eq_iteratedDeriv (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter k Ψ z θ = iteratedDeriv k (fun θ' => Ψ z θ') θ := by
  induction k generalizing θ with
  | zero => simp
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, iteratedDeriv_succ]
    simp only [Work.Spaces.pth]
    congr 1
    funext θ'
    exact ih θ'

/-- `∂_z Ψ z θ` is the first iterated derivative of the `z`-slice. -/
lemma pz_eq_iteratedDeriv_one (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz F z θ = iteratedDeriv 1 (fun z' => F z' θ) z := by
  have h := pzIter_eq_iteratedDeriv 1 F z θ
  simpa using h

/-! ## Additivity of the individual derivatives appearing in `bslOp` -/

/-- `∂_z` is additive on `C²` functions. -/
lemma pz_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pz (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Spaces.pz Ψ z θ + Work.Spaces.pz Φ z θ := by
  rw [pz_eq_iteratedDeriv_one (fun z θ => Ψ z θ + Φ z θ) z θ,
      pz_eq_iteratedDeriv_one Ψ z θ, pz_eq_iteratedDeriv_one Φ z θ]
  exact iteratedDeriv_one_add (contDiffAt_uncurry_slice_fst Ψ z θ (hΨ.of_le (m := 1) (by norm_num)))
    (contDiffAt_uncurry_slice_fst Φ z θ (hΦ.of_le (m := 1) (by norm_num)))

/-- `∂_zz` is additive on `C²` functions. -/
lemma pzIter_two_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Spaces.pzIter 2 Ψ z θ + Work.Spaces.pzIter 2 Φ z θ := by
  rw [pzIter_eq_iteratedDeriv 2 (fun z θ => Ψ z θ + Φ z θ) z θ,
      pzIter_eq_iteratedDeriv 2 Ψ z θ, pzIter_eq_iteratedDeriv 2 Φ z θ]
  exact iteratedDeriv_two_add (contDiffAt_uncurry_slice_fst Ψ z θ hΨ)
    (contDiffAt_uncurry_slice_fst Φ z θ hΦ)

/-- `∂_θθ` is additive on `C²` functions. -/
lemma pthIter_two_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pthIter 2 Φ z θ := by
  rw [pthIter_eq_iteratedDeriv 2 (fun z θ => Ψ z θ + Φ z θ) z θ,
      pthIter_eq_iteratedDeriv 2 Ψ z θ, pthIter_eq_iteratedDeriv 2 Φ z θ]
  exact iteratedDeriv_two_add (contDiffAt_uncurry_slice_snd Ψ z θ hΨ)
    (contDiffAt_uncurry_slice_snd Φ z θ hΦ)

/-- `∂_θ(tan θ · ·)` is additive on `C²` functions (at `θ` with `cos θ ≠ 0`). -/
lemma pth_tan_mul_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pth (fun z θ => Real.tan θ * (Ψ z θ + Φ z θ)) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Φ z θ) z θ := by
  have h1 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * Ψ z θ') θ :=
    ((Real.contDiffAt_tan.mpr hθ).mul
      (contDiffAt_uncurry_slice_snd Ψ z θ (hΨ.of_le (m := 1) (by norm_num)))).differentiableAt
        (by norm_num)
  have h2 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * Φ z θ') θ :=
    ((Real.contDiffAt_tan.mpr hθ).mul
      (contDiffAt_uncurry_slice_snd Φ z θ (hΦ.of_le (m := 1) (by norm_num)))).differentiableAt
        (by norm_num)
  simp only [Work.Spaces.pth]
  have key : (fun θ' : ℝ => Real.tan θ' * (Ψ z θ' + Φ z θ'))
      = (fun θ' : ℝ => Real.tan θ' * Ψ z θ' + Real.tan θ' * Φ z θ') := by
    funext θ'; ring
  rw [key]
  exact deriv_add h1 h2

/-! ## Additivity of `L₀` and of `bslOp` -/

/-- `L₀` is additive: `L₀(Ψ + Φ) = L₀Ψ + L₀Φ` at every `(z,θ)` with `cos θ ≠ 0`. -/
lemma Lzero_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Lzero (fun z θ => Ψ z θ + Φ z θ) z θ = Lzero Ψ z θ + Lzero Φ z θ := by
  have h2 := pthIter_two_add Ψ Φ z θ hΨ hΦ
  have ht := pth_tan_mul_add Ψ Φ z θ hθ hΨ hΦ
  simp only [Lzero, h2, ht]
  ring

/-- `bslOp α` is additive. -/
lemma bslOp_add (α : ℝ) (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    bslOp α (fun z θ => Ψ z θ + Φ z θ) z θ = bslOp α Ψ z θ + bslOp α Φ z θ := by
  have h2 := pzIter_two_add Ψ Φ z θ hΨ hΦ
  have h1 := pz_add Ψ Φ z θ hΨ hΦ
  have hL := Lzero_add Ψ Φ z θ hθ hΨ hΦ
  simp only [bslOp_apply, h2, h1, hL]
  ring

end Work.Elliptic
