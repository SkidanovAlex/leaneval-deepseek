/-
# `E4R3/N4C/L12AbsLeHon` — the uniform `D_z`-iterate bound of `L₁₂(g)` in the honest class

The honest (open-quadrant) counterpart of `Work.FTS.NonlinRows.L12_dzdIter_abs_le`
(`Submission/Work/FTS/NonlinRows/NRow1_7Aux.lean`): for `g` of class `C^∞` on the open quadrant,
honestly in `ℋ⁴`, with vanishing zero mode `L₁₂(g)(0) = 0`,

  `|D_z^b L₁₂(g)(z)| ≤ KL · Xn α g`   for `b ≤ 4`, `z > 0`,

with an absolute constant `KL`.  The two inputs of the frozen proof are replaced by their open
twins:

* `Work.FTS.Nonlinear.Pieces.L12_sq_le_growth`  ↦ `Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest`;
* `Work.FTS.Nonlinear.Pieces.L12_dzdIter_moment` ↦ `Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest`;
* `Work.FTS.Nonlinear.Pieces.Qang_sq_le_const`  ↦ `Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open`
  (which needs no decay hypothesis at all);

the `SmoothQuad`/`DecayInZ`-type hypotheses of the frozen statement are simply dropped.

Everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest
import Submission.Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest
import Submission.Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The uniform bounds on the `D_z`-iterates of `L₁₂(g)` in the honest class.**
`|D_z^b L₁₂(g)(z)| ≤ KL·Xn α g` for `b ≤ 4` and every `z > 0`: the `b = 0` case is the growth
estimate `(L₁₂ g z)² ≤ Kc X² min(z³, 1/z)`, and `b ≥ 1` is the angular-moment recursion
`D_z^{k+1}L₁₂(g) = -Qang g k` together with `(Qang g k z)² ≤ (∫Kθ²)·HkSq α 4 g`. -/
theorem L12_dzdIter_abs_le_open :
    ∃ KL : ℝ, 0 < KL ∧ ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ KL * Work.FTS.Nonlin.Xn α g := by
  set Kc : ℝ := max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / (3 : ℝ))
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 with hKc
  have hKth0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hmax0 : 0 ≤ max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / (3 : ℝ))
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) :=
    le_trans (by positivity) (le_max_right _ _)
  have hKc1 : 1 ≤ Kc := by rw [hKc]; linarith
  have hKc0 : 0 < Kc := lt_of_lt_of_le zero_lt_one hKc1
  refine ⟨Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1,
    by positivity, ?_⟩
  intro α g hα hα1 hsm hmem h0 b hb z hz
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXs : (Work.Spaces.HkSq α 4 g) = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    obtain ⟨hgrowth1, hgrowth2⟩ :=
      Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest α hα hα1 hsm hmem h0
    have hKcX0 : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
    have hbound : (Work.Construction.L12 g z) ^ 2 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rcases le_or_gt z 1 with hz1 | hz1
      · refine (hgrowth1 z hz).trans ?_
        have : z ^ 3 ≤ 1 := pow_le_one₀ hz.le hz1
        calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3
            ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left this hKcX0
          _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
      · refine (hgrowth2 z hz).trans ?_
        have : 1 / z ≤ 1 := by rw [div_le_one hz]; linarith
        calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
            = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := by ring
          _ ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left this hKcX0
          _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    have h1 : |Work.Construction.L12 g z| ≤ Real.sqrt Kc * Work.FTS.Nonlin.Xn α g := by
      have h := Real.sqrt_le_sqrt hbound
      rw [Real.sqrt_mul (le_of_lt hKc0), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hX0] at h
      exact h
    have h2 : Real.sqrt Kc * Work.FTS.Nonlin.Xn α g
        ≤ (Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * Work.FTS.Nonlin.Xn α g := by
      have h1' : Real.sqrt Kc ≤ Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ ^ 2) + 1 := by
        have := Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        linarith
      exact mul_le_mul_of_nonneg_right h1' hX0
    calc |Work.Elliptic.DzdIter 0 (fun z => Work.Construction.L12 g z) z|
        = |Work.Construction.L12 g z| := rfl
      _ ≤ Real.sqrt Kc * Work.FTS.Nonlin.Xn α g := h1
      _ ≤ _ := h2
  · have hrec := (Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest α hα hα1 hsm hmem h0).1
      (b - 1) (by omega) z hz
    have hbsucc : b = (b - 1) + 1 := by omega
    rw [hbsucc, hrec, abs_neg]
    have hq := Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open (α := α) (g := g) hα hα1
      hsm hmem (i := b - 1) (by omega) (z := z) hz
    have hq' : (Work.Elliptic.Qang g (b - 1) z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rw [hXs] at hq; exact hq
    have h1 : |Work.Elliptic.Qang g (b - 1) z|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.FTS.Nonlin.Xn α g := by
      have h := Real.sqrt_le_sqrt hq'
      rw [Real.sqrt_mul hKth0, Real.sqrt_sq_eq_abs, Real.sqrt_sq hX0] at h
      exact h
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.FTS.Nonlin.Xn α g
        ≤ (Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * Work.FTS.Nonlin.Xn α g := by
      have h1' : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          ≤ Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 := by
        have := Real.sqrt_nonneg Kc
        linarith
      exact mul_le_mul_of_nonneg_right h1' hX0
    calc |Work.Elliptic.Qang g (b - 1) z| ≤ _ := h1
      _ ≤ _ := h2

end Work.FTS.StrongEps.E4R3.N4C
