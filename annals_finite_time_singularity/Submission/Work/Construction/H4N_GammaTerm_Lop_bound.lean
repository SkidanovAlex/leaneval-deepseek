/-
# The `D_θ`-iterate bound for `ψ = c2m·Γ`

This file proves

`Work.Construction.H4N_GammaTerm_Lop_bound`: there is a universal `D > 0` with

`|D_θ^i ψ(θ)| ≤ D·Γ(θ)·(sin²(2θ) + α)`  for `0 < α ≤ 1`, `1 ≤ i ≤ 4`, `θ ∈ (0,π/2)`,

where `ψ = c2m·Γ` is the angular factor of the `Γ`-term (`D_θ = Lop = sin(2θ)∂_θ`).

The proof runs through the substitution `x = cos²θ`: on the open quadrant

* `D_θ(Γ) = (α/3)(6cos²θ - 4)·Γ`, and
* `D_θ(a(cos²θ)) = -4cos²θ(1-cos²θ)·a'(cos²θ)`,

so that with `Aᵢ` the explicit polynomials of `Submission/Work/Construction/GLop_Aux.lean`
(`A₀ = 3x - 2 = c2m`, `Aᵢ₊₁ = -4x(1-x)Aᵢ' + (α/3)(6x-4)Aᵢ`)

  `D_θ^i ψ(θ) = Γ(θ)·Aᵢ(cos²θ, α)`.

Since `4cos²θ(1-cos²θ) = sin²(2θ)` and each `Aᵢ` is bounded by
`10^7(α + 4x(1-x))` on `[0,1]` (for `0 < α ≤ 1`), the conclusion follows with `D = 10^7`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.GLop_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## Derivatives of the explicit polynomials `Aᵢ` -/

theorem glop_deriv_Aang_zero (x α : ℝ) : deriv (fun y : ℝ => Aang 0 y α) x = 3 := by
  have h : (fun y : ℝ => Aang 0 y α)
      = fun y : ℝ => (-2) + 3 * y + 0 * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_zero]
    ring
  rw [h, deriv_mono5]
  ring

theorem glop_deriv_Aang_one (x α : ℝ) :
    deriv (fun y : ℝ => Aang 1 y α) x = (-8 * α - 12) + 2 * (6 * α + 12) * x := by
  have h : (fun y : ℝ => Aang 1 y α)
      = fun y : ℝ => (8 * α / 3) + (-8 * α - 12) * y + (6 * α + 12) * y ^ 2
          + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_one]
    ring
  rw [h, deriv_mono5]
  ring

theorem glop_deriv_Aang_two (x α : ℝ) :
    deriv (fun y : ℝ => Aang 2 y α) x
      = (16 * α ^ 2 + 48 * α + 48) + 2 * (-24 * α ^ 2 - 120 * α - 144) * x
        + 3 * (12 * α ^ 2 + 72 * α + 96) * x ^ 2 := by
  have h : (fun y : ℝ => Aang 2 y α)
      = fun y : ℝ => (-32 * α ^ 2 / 9) + (16 * α ^ 2 + 48 * α + 48) * y
          + (-24 * α ^ 2 - 120 * α - 144) * y ^ 2 + (12 * α ^ 2 + 72 * α + 96) * y ^ 3
          + 0 * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_two]
    ring
  rw [h, deriv_mono5]
  ring

theorem glop_deriv_Aang_three (x α : ℝ) :
    deriv (fun y : ℝ => Aang 3 y α) x
      = (-256 * α ^ 3 / 9 - 128 * α ^ 2 - 256 * α - 192)
        + 2 * (64 * α ^ 3 + 512 * α ^ 2 + 1440 * α + 1344) * x
        + 3 * (-64 * α ^ 3 - 672 * α ^ 2 - 2240 * α - 2304) * x ^ 2
        + 4 * (24 * α ^ 3 + 288 * α ^ 2 + 1056 * α + 1152) * x ^ 3 := by
  have h : (fun y : ℝ => Aang 3 y α)
      = fun y : ℝ => (128 * α ^ 3 / 27) + (-256 * α ^ 3 / 9 - 128 * α ^ 2 - 256 * α - 192) * y
          + (64 * α ^ 3 + 512 * α ^ 2 + 1440 * α + 1344) * y ^ 2
          + (-64 * α ^ 3 - 672 * α ^ 2 - 2240 * α - 2304) * y ^ 3
          + (24 * α ^ 3 + 288 * α ^ 2 + 1056 * α + 1152) * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_three]
    ring
  rw [h, deriv_mono5]
  ring

/-- The polynomials `Aᵢ` (`i ≤ 4`) are differentiable. -/
theorem differentiable_Aang (j : ℕ) (hj : j ≤ 4) (α : ℝ) :
    Differentiable ℝ (fun y : ℝ => Aang j y α) := by
  interval_cases j
  · simp only [Aang_zero]; fun_prop
  · simp only [Aang_one]; fun_prop
  · simp only [Aang_two]; fun_prop
  · simp only [Aang_three]; fun_prop
  · simp only [Aang_four]; fun_prop

/-- The recurrence `Aᵢ₊₁ = -4x(1-x)Aᵢ' + (α/3)(6x-4)Aᵢ` for `i ≤ 3`. -/
theorem glop_Aang_succ (j : ℕ) (hj : j ≤ 3) (x α : ℝ) :
    -4 * x * (1 - x) * deriv (fun y : ℝ => Aang j y α) x
      + (α / 3) * (6 * x - 4) * Aang j x α
      = Aang (j + 1) x α := by
  interval_cases j
  · rw [glop_deriv_Aang_zero, Aang_zero, Aang_one]; ring
  · rw [glop_deriv_Aang_one, Aang_one, Aang_two]; ring
  · rw [glop_deriv_Aang_two, Aang_two, Aang_three]; ring
  · rw [glop_deriv_Aang_three, Aang_three, Aang_four]; ring

/-! ## The two building blocks of the `θ`-calculation -/

/-- `D_θ(Γ) = (α/3)(6cos²θ - 4)·Γ` on the open quadrant. -/
theorem glop_Gam_deriv (α θ : ℝ) (_hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Lop (Work.Spaces.Gam α) θ
      = (α / 3) * (6 * Real.cos θ ^ 2 - 4) * Work.Spaces.Gam α θ := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hg : 0 < Real.sin θ * Real.cos θ ^ 2 := mul_pos hsin (pow_pos hcos 2)
  have hcos2' : HasDerivAt (fun y : ℝ => Real.cos y ^ 2) (-2 * Real.cos θ * Real.sin θ) θ := by
    have h : HasDerivAt (fun y : ℝ => Real.cos y * Real.cos y)
        (-2 * Real.cos θ * Real.sin θ) θ := by
      have hh := (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_cos θ)
      have hv : -Real.sin θ * Real.cos θ + Real.cos θ * -Real.sin θ
          = -2 * Real.cos θ * Real.sin θ := by ring
      rw [hv] at hh
      exact hh
    simpa [pow_two] using h
  have hg' : HasDerivAt (fun y : ℝ => Real.sin y * Real.cos y ^ 2)
      (Real.cos θ * (3 * Real.cos θ ^ 2 - 2)) θ := by
    have h := (Real.hasDerivAt_sin θ).mul hcos2'
    convert h using 1
    · ring_nf
      rw [Real.sin_sq]
      ring
  have hderivG : deriv (Work.Spaces.Gam α) θ
      = (α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * (Real.cos θ * (3 * Real.cos θ ^ 2 - 2)) := by
    have hrpow : HasDerivAt (fun y : ℝ => y ^ (α / 3))
        ((α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
        (Real.sin θ * Real.cos θ ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hg))
    have hcomp := hrpow.comp θ hg'
    have hd := hcomp.deriv
    change deriv ((fun y : ℝ => y ^ (α / 3))
      ∘ (fun y : ℝ => Real.sin y * Real.cos y ^ 2)) θ = _
    rw [hd]
  rw [show Work.Spaces.Lop (Work.Spaces.Gam α) θ
        = Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ from rfl, hderivG,
      show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl,
      Real.sin_two_mul]
  have hgpow : (Real.sin θ * Real.cos θ ^ 2) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
    have h := Real.rpow_add hg (α / 3 - 1) 1
    rw [sub_add_cancel, Real.rpow_one] at h
    rw [h]
    ring
  calc 2 * Real.sin θ * Real.cos θ *
        ((α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * (Real.cos θ * (3 * Real.cos θ ^ 2 - 2)))
      = (α / 3) * (2 * Real.sin θ * Real.cos θ * Real.cos θ * (3 * Real.cos θ ^ 2 - 2))
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
    _ = (α / 3) * ((6 * Real.cos θ ^ 2 - 4) * (Real.sin θ * Real.cos θ ^ 2))
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
    _ = (α / 3) * (6 * Real.cos θ ^ 2 - 4)
          * ((Real.sin θ * Real.cos θ ^ 2) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)) := by
        ring
    _ = (α / 3) * (6 * Real.cos θ ^ 2 - 4) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
        rw [hgpow]

/-- The chain rule `D_θ(a(cos²θ)) = -4cos²θ(1-cos²θ)·a'(cos²θ)`. -/
theorem glop_comp_cos_sq (a : ℝ → ℝ) (ha : Differentiable ℝ a) (θ : ℝ) :
    Work.Spaces.Lop (fun θ => a (Real.cos θ ^ 2)) θ
      = -4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) * deriv a (Real.cos θ ^ 2) := by
  show Real.sin (2 * θ) * deriv (fun θ => a (Real.cos θ ^ 2)) θ = _
  have hu : DifferentiableAt ℝ (fun θ : ℝ => Real.cos θ ^ 2) θ := by fun_prop
  have ha' : DifferentiableAt ℝ a (Real.cos θ ^ 2) := ha.differentiableAt
  rw [show (fun θ : ℝ => a (Real.cos θ ^ 2)) = a ∘ (fun θ : ℝ => Real.cos θ ^ 2) from rfl,
    deriv_comp θ ha' hu]
  have hdu : deriv (fun θ : ℝ => Real.cos θ ^ 2) θ = -2 * Real.cos θ * Real.sin θ := by
    have h := ((hasDerivAt_pow 2 (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).deriv
    change deriv ((fun x : ℝ => x ^ 2) ∘ Real.cos) θ = -2 * Real.cos θ * Real.sin θ
    rw [h]
    ring
  rw [hdu, Real.sin_two_mul]
  ring_nf
  rw [Real.sin_sq]
  ring

/-! ## The one-step identity -/

/-- One step of the `θ`-calculation: the action of `D_θ` on `Γ(θ)·a(cos²θ)`. -/
theorem glop_step (α : ℝ) (hα : 0 < α) (a : ℝ → ℝ) (ha : Differentiable ℝ a) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * a (Real.cos y ^ 2)) θ
      = Work.Spaces.Gam α θ * (-4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)
          * deriv a (Real.cos θ ^ 2)
          + (α / 3) * (6 * Real.cos θ ^ 2 - 4) * a (Real.cos θ ^ 2)) := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hGam_diff : DifferentiableAt ℝ (Work.Spaces.Gam α) θ := by
    rw [show Work.Spaces.Gam α = fun y : ℝ => (Real.sin y * Real.cos y ^ 2) ^ (α / 3) from rfl]
    exact (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => Real.sin y * Real.cos y ^ 2) θ).rpow_const
      (Or.inl (ne_of_gt (mul_pos hsin (pow_pos hcos 2))))
  have ha_comp : DifferentiableAt ℝ (fun y : ℝ => a (Real.cos y ^ 2)) θ :=
    ha.differentiableAt.comp θ (by fun_prop)
  rw [show (fun y : ℝ => Work.Spaces.Gam α y * a (Real.cos y ^ 2))
      = Work.Spaces.Gam α * (fun y : ℝ => a (Real.cos y ^ 2)) from rfl,
    Work.Spaces.Lop_mul _ _ θ hGam_diff ha_comp]
  rw [glop_Gam_deriv α θ hα hθ, glop_comp_cos_sq a ha θ]
  ring

/-! ## The iterates of `ψ` -/

/-- `D_θ^i ψ(θ) = Γ(θ)·Aᵢ(cos²θ, α)` for `i ≤ 4` and `θ ∈ (0,π/2)`. -/
theorem glop_Lop_iter_psiA (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i] (psiA α)) θ = Work.Spaces.Gam α θ * Aang i (Real.cos θ ^ 2) α := by
  induction i with
  | zero =>
      intro θ hθ
      have hc : c2m θ = 3 * Real.cos θ ^ 2 - 2 := by
        rw [c2m_eq, Real.cos_two_mul, Real.sin_sq]
        ring
      simp only [Function.iterate_zero, id_eq, psiA, Aang_zero]
      rw [hc]
      ring
  | succ j ih =>
      intro θ hθ
      have hj : j ≤ 4 := le_trans (Nat.le_succ j) hi
      have hev : (Work.Spaces.Lop^[j] (psiA α))
          =ᶠ[𝓝 θ] (fun y => Work.Spaces.Gam α y * Aang j (Real.cos y ^ 2) α) := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
        exact ih hj y hy
      rw [Function.iterate_succ_apply']
      rw [show Work.Spaces.Lop (Work.Spaces.Lop^[j] (psiA α)) θ
          = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * Aang j (Real.cos y ^ 2) α) θ from by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (psiA α)) θ
            = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y * Aang j (Real.cos y ^ 2) α) θ
        rw [hev.deriv_eq]]
      rw [glop_step α hα (fun y : ℝ => Aang j y α) (differentiable_Aang j hj α) θ hθ]
      rw [glop_Aang_succ j (by omega) (Real.cos θ ^ 2) α]

/-! ## The pointwise bounds for the polynomials `Aᵢ` -/

/-- Five-term triangle inequality. -/
theorem abs_five_le {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  linarith

/-- `|A₁(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_one (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (_hα1 : α ≤ 1) :
    |Aang 1 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hW : |4 * x * (1 - x) * (-3)| ≤ 3 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4, abs_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)]
    linarith
  have hP1 : |18 * x ^ 2 - 24 * x + 8| ≤ 50 := by
    have h2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx.2
    have h2' : 0 ≤ x ^ 2 := pow_nonneg hx0 2
    rw [abs_le]
    constructor <;> nlinarith
  have hR1 : |(α / 3) * (18 * x ^ 2 - 24 * x + 8)| ≤ 50 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have h0 : |(0 : ℝ)| ≤ 0 := by norm_num
  have hsum := abs_five_le hW hR1 h0 h0 h0
  calc |Aang 1 x α|
      = |4 * x * (1 - x) * (-3) + (α / 3) * (18 * x ^ 2 - 24 * x + 8) + 0 + 0 + 0| := by
        rw [Aang_one]
        ring
    _ ≤ 3 * (4 * x * (1 - x)) + 50 * (α / 3) + 0 + 0 + 0 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1]

/-- `|A₂(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_two (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang 2 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hk2 : (α / 3) ^ 2 ≤ α := by nlinarith
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → 0 ≤ x ^ k ∧ x ^ k ≤ 1 := by
    intro k hk0 hk4
    exact ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx.2⟩
  have hV : |12 - 24 * x| ≤ 36 := by
    rw [abs_le]; constructor <;> nlinarith
  have hP1 : |216 * x ^ 3 - 360 * x ^ 2 + 144 * x| ≤ 720 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP2 : |108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32| ≤ 500 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hW : |4 * x * (1 - x) * (12 - 24 * x)| ≤ 36 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4]
    have := mul_le_mul_of_nonneg_left hV h4
    linarith
  have hR1 : |(α / 3) * (216 * x ^ 3 - 360 * x ^ 2 + 144 * x)| ≤ 720 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have hR2 : |(α / 3) ^ 2 * (108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32)| ≤ 500 * (α / 3) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 2)]
    have := mul_le_mul_of_nonneg_left hP2 (pow_nonneg hα3 2)
    linarith
  have h0 : |(0 : ℝ)| ≤ 0 := by norm_num
  have hsum := abs_five_le hW hR1 hR2 h0 h0
  calc |Aang 2 x α|
      = |4 * x * (1 - x) * (12 - 24 * x) + (α / 3) * (216 * x ^ 3 - 360 * x ^ 2 + 144 * x)
          + (α / 3) ^ 2 * (108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32) + 0 + 0| := by
        rw [Aang_two]
        ring
    _ ≤ 36 * (4 * x * (1 - x)) + 720 * (α / 3) + 500 * (α / 3) ^ 2 + 0 + 0 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1, hk2]

/-- `|A₃(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_three (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang 3 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hk2 : (α / 3) ^ 2 ≤ α := by nlinarith
  have hk3 : (α / 3) ^ 3 ≤ α := by nlinarith
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → 0 ≤ x ^ k ∧ x ^ k ≤ 1 := by
    intro k hk0 hk4
    exact ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx.2⟩
  have hV : |-48 + 288 * x - 288 * x ^ 2| ≤ 624 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP1 : |3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x| ≤ 14976 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP2 : |2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x| ≤ 14400 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP3 : |648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128| ≤ 5000 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hW : |4 * x * (1 - x) * (-48 + 288 * x - 288 * x ^ 2)| ≤ 624 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4]
    have := mul_le_mul_of_nonneg_left hV h4
    linarith
  have hR1 : |(α / 3) * (3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x)|
      ≤ 14976 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have hR2 : |(α / 3) ^ 2 * (2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x)|
      ≤ 14400 * (α / 3) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 2)]
    have := mul_le_mul_of_nonneg_left hP2 (pow_nonneg hα3 2)
    linarith
  have hR3 : |(α / 3) ^ 3 * (648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128)|
      ≤ 5000 * (α / 3) ^ 3 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 3)]
    have := mul_le_mul_of_nonneg_left hP3 (pow_nonneg hα3 3)
    linarith
  have h0 : |(0 : ℝ)| ≤ 0 := by norm_num
  have hsum := abs_five_le hW hR1 hR2 hR3 h0
  calc |Aang 3 x α|
      = |4 * x * (1 - x) * (-48 + 288 * x - 288 * x ^ 2)
          + (α / 3) * (3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x)
          + (α / 3) ^ 2 * (2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x)
          + (α / 3) ^ 3 * (648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128) + 0| := by
        rw [Aang_three]
        ring
    _ ≤ 624 * (4 * x * (1 - x)) + 14976 * (α / 3) + 14400 * (α / 3) ^ 2 + 5000 * (α / 3) ^ 3
          + 0 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1, hk2, hk3]

/-- `|A₄(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_four (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang 4 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hk2 : (α / 3) ^ 2 ≤ α := by nlinarith
  have hk3 : (α / 3) ^ 3 ≤ α := by nlinarith
  have hk4 : (α / 3) ^ 4 ≤ α := by nlinarith
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ 5 → 0 ≤ x ^ k ∧ x ^ k ≤ 1 := by
    intro k hk0 hk5
    exact ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx.2⟩
  have hV : |192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3| ≤ 14400 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP1 : |57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2 + 3840 * x|
      ≤ 387840 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP2 : |60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2 + 7680 * x|
      ≤ 460800 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP3 : |25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2 + 7680 * x|
      ≤ 240000 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP4 : |3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2 + 3840 * x - 512|
      ≤ 50000 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hW : |4 * x * (1 - x) * (192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3)|
      ≤ 14400 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4]
    have := mul_le_mul_of_nonneg_left hV h4
    linarith
  have hR1 : |(α / 3) * (57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2
        + 3840 * x)| ≤ 387840 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have hR2 : |(α / 3) ^ 2 * (60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2
        + 7680 * x)| ≤ 460800 * (α / 3) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 2)]
    have := mul_le_mul_of_nonneg_left hP2 (pow_nonneg hα3 2)
    linarith
  have hR3 : |(α / 3) ^ 3 * (25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2
        + 7680 * x)| ≤ 240000 * (α / 3) ^ 3 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 3)]
    have := mul_le_mul_of_nonneg_left hP3 (pow_nonneg hα3 3)
    linarith
  have hR4 : |(α / 3) ^ 4 * (3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2
        + 3840 * x - 512)| ≤ 50000 * (α / 3) ^ 4 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 4)]
    have := mul_le_mul_of_nonneg_left hP4 (pow_nonneg hα3 4)
    linarith
  have hsum := abs_five_le hW hR1 hR2 hR3 hR4
  calc |Aang 4 x α|
      = |4 * x * (1 - x) * (192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3)
          + (α / 3) * (57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2
              + 3840 * x)
          + (α / 3) ^ 2 * (60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2
              + 7680 * x)
          + (α / 3) ^ 3 * (25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2
              + 7680 * x)
          + (α / 3) ^ 4 * (3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2
              + 3840 * x - 512)| := by
        rw [Aang_four]
    _ ≤ 14400 * (4 * x * (1 - x)) + 387840 * (α / 3) + 460800 * (α / 3) ^ 2
          + 240000 * (α / 3) ^ 3 + 50000 * (α / 3) ^ 4 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1, hk2, hk3, hk4]

/-! ## The target theorem -/

theorem H4N_GammaTerm_Lop_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα (Set.Ioo_subset_Icc_self hθ)).1
  have hxc : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by linarith [Real.cos_sq_le_one θ]⟩
  have hsin2 : 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) = Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]
    ring_nf
    rw [Real.sin_sq]
    ring
  have hb : |Aang i (Real.cos θ ^ 2) α| ≤ 10 ^ 7 * (α + 4 * Real.cos θ ^ 2
      * (1 - Real.cos θ ^ 2)) := by
    interval_cases i
    · exact glop_Aang_bound_one _ _ hxc hα hα1
    · exact glop_Aang_bound_two _ _ hxc hα hα1
    · exact glop_Aang_bound_three _ _ hxc hα hα1
    · exact glop_Aang_bound_four _ _ hxc hα hα1
  rw [glop_Lop_iter_psiA α hα i hi4 θ hθ]
  calc |Work.Spaces.Gam α θ * Aang i (Real.cos θ ^ 2) α|
      = Work.Spaces.Gam α θ * |Aang i (Real.cos θ ^ 2) α| := by
        rw [abs_mul, abs_of_nonneg hGam0]
    _ ≤ Work.Spaces.Gam α θ
          * (10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
        mul_le_mul_of_nonneg_left hb hGam0
    _ = 10 ^ 7 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
        rw [hsin2]
        ring

end Work.Construction
