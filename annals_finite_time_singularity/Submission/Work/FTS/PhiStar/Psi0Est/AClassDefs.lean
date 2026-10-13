/-
# `Work.FTS.PhiStar.Psi0Est.AClassDefs` — the coefficient family `cVec` of the `A`-class estimate

This file fixes the (α-independent) data used to pass from the `ZClass` bounds on the
iterated angular derivatives of `P = Pfun α` to the `AClass` bounds on `psiSol α`.

Writing `A_j := D_θ^j ψ`, `Z_j := D_θ^j P` (with `D_θ = sin(2θ)·d/dθ = dthU`), and
`s = sin θ`, `c = cos θ`, the key identity is

  `A_{j+1} = 4 cos²θ · Z_j + ∑_{r ≤ j} c_{j,r} · A_r`,

where the coefficients `c_{j,r} = cVec j r` are defined by the recursion

  `c_{0,0} = 2 cos 2θ`,   `c_{j+1,j+1} = c_{j,j} - 4 sin²θ`,
  `c_{j+1,0} = D_θ (c_{j,0}) + 4 sin²θ · c_{j,0}`,
  `c_{j+1,r} = D_θ (c_{j,r}) + 4 sin²θ · c_{j,r} + c_{j,r-1}`  (`1 ≤ r ≤ j`).

Every `c_{j,r}` is a function of the shape `A(sin θ) + cos θ · B(sin θ)` with
`A, B : ℝ[X]` (see `IsCoef`); this class is closed under `+`, `·`, multiplication by fixed
trigonometric polynomials and under `D_θ`:

* `D_θ (A(sin ·) + cos · B(sin ·)) = (2X(1-X²)A')'(sin ·) + cos θ · (2X(1-X²)B' - 2X²B)(sin ·)`,
* `(A₁ + cB₁)(A₂ + cB₂) = A₁A₂ + (1-X²)B₁B₂ + c·(A₁B₂ + A₂B₁)`

(using `c² = 1 - s²`).  Hence every `c_{j,r}` is bounded, and the `c`-bounds are uniform in
`α ∈ (0, 1/4]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Polynomial
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Polynomial

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

/-- The coefficient family `c_{j,r}` of the recursion
`D_θ^{j+1}ψ = 4 cos²θ · D_θ^j P + ∑_{r ≤ j} c_{j,r} · D_θ^r ψ`.
For `r > j` the value is irrelevant (it is never used). -/
noncomputable def cVec : ℕ → ℕ → (ℝ → ℝ)
  | 0 => fun r => if r = 0 then (fun θ => 2 * Real.cos (2 * θ)) else 0
  | (j + 1) => fun r =>
      if r = j + 1 then (fun θ => cVec j j θ - 4 * Real.sin θ ^ 2)
      else if r = 0 then
        (fun θ => Work.Spaces.dthU (cVec j 0) θ + 4 * Real.sin θ ^ 2 * cVec j 0 θ)
      else
        (fun θ => Work.Spaces.dthU (cVec j r) θ + 4 * Real.sin θ ^ 2 * cVec j r θ
          + cVec j (r - 1) θ)

@[simp] theorem cVec_zero_zero : cVec 0 0 = fun θ => 2 * Real.cos (2 * θ) := by
  simp only [cVec]
  norm_num

theorem cVec_zero_of_ne (r : ℕ) (hr : r ≠ 0) : cVec 0 r = 0 := by
  simp only [cVec]
  rw [if_neg hr]

theorem cVec_succ_self (j : ℕ) :
    cVec (j + 1) (j + 1) = fun θ => cVec j j θ - 4 * Real.sin θ ^ 2 := by
  simp only [cVec]
  norm_num

theorem cVec_succ_zero (j : ℕ) :
    cVec (j + 1) 0 = fun θ => Work.Spaces.dthU (cVec j 0) θ
      + 4 * Real.sin θ ^ 2 * cVec j 0 θ := by
  cases j with
  | zero => simp only [cVec]; norm_num
  | succ j => simp only [cVec]; norm_num

theorem cVec_succ_of_ne (j r : ℕ) (h1 : r ≠ j + 1) (h0 : r ≠ 0) :
    cVec (j + 1) r = fun θ => Work.Spaces.dthU (cVec j r) θ
      + 4 * Real.sin θ ^ 2 * cVec j r θ + cVec j (r - 1) θ := by
  simp only [cVec]
  rw [if_neg h1, if_neg h0]

/-- A function of the shape `A(sin θ) + cos θ · B(sin θ)` with `A, B` polynomials.  The class is
closed under `+`, `·`, multiplication by a fixed trigonometric polynomial, and under
`D_θ = dthU`; every element is bounded (uniformly on `ℝ`). -/
def IsCoef (f : ℝ → ℝ) : Prop :=
  ∃ A B : Polynomial ℝ, ∀ θ : ℝ,
    f θ = A.eval (Real.sin θ) + Real.cos θ * B.eval (Real.sin θ)

/-! ## Closure properties of `IsCoef` -/

theorem IsCoef_zero : IsCoef (0 : ℝ → ℝ) :=
  ⟨0, 0, fun θ => by simp⟩

theorem IsCoef_add {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f + g) := by
  obtain ⟨A₁, B₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, h₂⟩ := hg
  refine ⟨A₁ + A₂, B₁ + B₂, fun θ => ?_⟩
  rw [Pi.add_apply, h₁ θ, h₂ θ]
  simp only [Polynomial.eval_add]
  ring

theorem IsCoef_neg {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (-f) := by
  obtain ⟨A, B, h⟩ := hf
  refine ⟨-A, -B, fun θ => ?_⟩
  rw [Pi.neg_apply, h θ]
  simp only [Polynomial.eval_neg]
  ring

theorem IsCoef_sub {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f - g) := by
  obtain ⟨A₁, B₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, h₂⟩ := hg
  refine ⟨A₁ - A₂, B₁ - B₂, fun θ => ?_⟩
  rw [Pi.sub_apply, h₁ θ, h₂ θ]
  simp only [Polynomial.eval_sub]
  ring

theorem IsCoef_const_mul (c : ℝ) {f : ℝ → ℝ} (hf : IsCoef f) :
    IsCoef (fun θ => c * f θ) := by
  obtain ⟨A, B, h⟩ := hf
  refine ⟨Polynomial.C c * A, Polynomial.C c * B, fun θ => ?_⟩
  change c * f θ = Polynomial.eval (Real.sin θ) (Polynomial.C c * A)
    + Real.cos θ * Polynomial.eval (Real.sin θ) (Polynomial.C c * B)
  rw [h θ]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem IsCoef_mul {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f * g) := by
  obtain ⟨A₁, B₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, h₂⟩ := hg
  refine ⟨A₁ * A₂ + (1 - Polynomial.X ^ 2) * (B₁ * B₂), A₁ * B₂ + A₂ * B₁, fun θ => ?_⟩
  rw [Pi.mul_apply, h₁ θ, h₂ θ]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring_nf
  linear_combination (B₁.eval (Real.sin θ) * B₂.eval (Real.sin θ)) * Real.sin_sq_add_cos_sq θ

theorem IsCoef_two_cos_two : IsCoef (fun θ : ℝ => 2 * Real.cos (2 * θ)) := by
  refine ⟨Polynomial.C 2 - Polynomial.C 4 * Polynomial.X ^ 2, 0, fun θ => ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]
  rw [Real.cos_two_mul, Real.cos_sq']
  ring

theorem IsCoef_four_sin_sq : IsCoef (fun θ : ℝ => 4 * Real.sin θ ^ 2) :=
  ⟨Polynomial.C 4 * Polynomial.X ^ 2, 0, fun θ => by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_zero, mul_zero, add_zero]⟩

theorem IsCoef_four_cos_sq : IsCoef (fun θ : ℝ => 4 * Real.cos θ ^ 2) := by
  refine ⟨Polynomial.C 4 * (1 - Polynomial.X ^ 2), 0, fun θ => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]
  ring_nf
  linear_combination (4 : ℝ) * Real.sin_sq_add_cos_sq θ

/-- `dthU` preserves the class `IsCoef` (note the extra `cos θ`-factor coming from
`d/dθ (cos θ · B(sin θ)) = - sin θ · B + cos θ · B' · cos θ`). -/
theorem IsCoef_dthU {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (Work.Spaces.dthU f) := by
  obtain ⟨A, B, h⟩ := hf
  refine ⟨Polynomial.C 2 * Polynomial.X * (1 - Polynomial.X ^ 2) * Polynomial.derivative A,
    Polynomial.C 2 * Polynomial.X * (1 - Polynomial.X ^ 2) * Polynomial.derivative B
      - Polynomial.C 2 * Polynomial.X ^ 2 * B, fun θ => ?_⟩
  have hfun : f = fun φ : ℝ => A.eval (Real.sin φ) + Real.cos φ * B.eval (Real.sin φ) :=
    funext h
  rw [hfun]
  have hsin : HasDerivAt (fun φ : ℝ => Real.sin φ) (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hcos : HasDerivAt (fun φ : ℝ => Real.cos φ) (-(Real.sin θ)) θ := Real.hasDerivAt_cos θ
  have hA : HasDerivAt (fun φ : ℝ => A.eval (Real.sin φ))
      (A.derivative.eval (Real.sin θ) * Real.cos θ) θ :=
    (Polynomial.hasDerivAt A (Real.sin θ)).comp θ hsin
  have hB : HasDerivAt (fun φ : ℝ => B.eval (Real.sin φ))
      (B.derivative.eval (Real.sin θ) * Real.cos θ) θ :=
    (Polynomial.hasDerivAt B (Real.sin θ)).comp θ hsin
  have hcB : HasDerivAt (fun φ : ℝ => Real.cos φ * B.eval (Real.sin φ))
      ((-(Real.sin θ)) * B.eval (Real.sin θ)
        + Real.cos θ * (B.derivative.eval (Real.sin θ) * Real.cos θ)) θ := hcos.mul hB
  have hfd : HasDerivAt (fun φ : ℝ => A.eval (Real.sin φ) + Real.cos φ * B.eval (Real.sin φ))
      (A.derivative.eval (Real.sin θ) * Real.cos θ
        + ((-(Real.sin θ)) * B.eval (Real.sin θ)
          + Real.cos θ * (B.derivative.eval (Real.sin θ) * Real.cos θ))) θ := hA.add hcB
  rw [Work.Spaces.dthU_apply, hfd.deriv]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_pow, Real.sin_two_mul]
  ring_nf
  linear_combination (2 * Real.sin θ * A.derivative.eval (Real.sin θ)
    + 2 * Real.sin θ * Real.cos θ * B.derivative.eval (Real.sin θ))
    * Real.sin_sq_add_cos_sq θ

theorem IsCoef_differentiableAt {f : ℝ → ℝ} (hf : IsCoef f) (θ : ℝ) :
    DifferentiableAt ℝ f θ := by
  obtain ⟨A, B, h⟩ := hf
  rw [show f = fun θ => A.eval (Real.sin θ) + Real.cos θ * B.eval (Real.sin θ) from funext h]
  exact (((Polynomial.hasDerivAt A (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)).add
    ((Real.hasDerivAt_cos θ).mul
      ((Polynomial.hasDerivAt B (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)))).differentiableAt

theorem IsCoef_bounded {f : ℝ → ℝ} (hf : IsCoef f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : ℝ, |f θ| ≤ M := by
  obtain ⟨A, B, h⟩ := hf
  obtain ⟨MA, hMA⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (Polynomial.continuous A).continuousOn
  obtain ⟨MB, hMB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (Polynomial.continuous B).continuousOn
  refine ⟨max MA 0 + max MB 0, add_nonneg (le_max_right _ _) (le_max_right _ _), fun θ => ?_⟩
  rw [h θ]
  have hsin : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hA : |A.eval (Real.sin θ)| ≤ max MA 0 :=
    le_trans (by simpa [Real.norm_eq_abs] using hMA _ hsin) (le_max_left _ _)
  have hB : |Real.cos θ * B.eval (Real.sin θ)| ≤ max MB 0 := by
    rw [abs_mul]
    calc |Real.cos θ| * |B.eval (Real.sin θ)|
        ≤ 1 * max MB 0 :=
          mul_le_mul (Real.abs_cos_le_one θ)
            (le_trans (by simpa [Real.norm_eq_abs] using hMB _ hsin) (le_max_left _ _))
            (abs_nonneg _) (by norm_num)
      _ = max MB 0 := one_mul _
  calc |A.eval (Real.sin θ) + Real.cos θ * B.eval (Real.sin θ)|
      ≤ |A.eval (Real.sin θ)| + |Real.cos θ * B.eval (Real.sin θ)| := abs_add_le _ _
    _ ≤ max MA 0 + max MB 0 := add_le_add hA hB

/-! ## The coefficients `cVec j r` are in the class -/

theorem cVec_isCoef : ∀ j r : ℕ, IsCoef (cVec j r) := by
  intro j
  induction j with
  | zero =>
      intro r
      rcases eq_or_ne r 0 with h | h
      · subst h; exact IsCoef_two_cos_two
      · rw [cVec_zero_of_ne r h]; exact IsCoef_zero
  | succ j ih =>
      intro r
      rcases eq_or_ne r (j + 1) with h | h
      · rw [h, cVec_succ_self]
        exact IsCoef_sub (ih j) IsCoef_four_sin_sq
      · rcases eq_or_ne r 0 with h0 | h0
        · subst h0
          rw [cVec_succ_zero]
          exact IsCoef_add (IsCoef_dthU (ih 0)) (IsCoef_mul IsCoef_four_sin_sq (ih 0))
        · rw [cVec_succ_of_ne j r h h0]
          exact IsCoef_add (IsCoef_add (IsCoef_dthU (ih r))
            (IsCoef_mul IsCoef_four_sin_sq (ih r))) (ih (r - 1))

/-- A uniform bound for the coefficients `cVec j r`. -/
noncomputable def cB (j r : ℕ) : ℝ :=
  Classical.choose (IsCoef_bounded (cVec_isCoef j r))

theorem cB_nonneg (j r : ℕ) : 0 ≤ cB j r :=
  (Classical.choose_spec (IsCoef_bounded (cVec_isCoef j r))).1

theorem cB_spec (j r : ℕ) (θ : ℝ) : |cVec j r θ| ≤ cB j r :=
  (Classical.choose_spec (IsCoef_bounded (cVec_isCoef j r))).2 θ

end Work.FTS.PhiStar.Psi0Est
