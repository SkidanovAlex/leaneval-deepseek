/-
Copyright: work module for the Elgindi finite-time singularity project.

# The quotient sequence attached to `D_θ^k (2 cos 2θ)`

`Work.Elliptic.Dth1Iter k` is the `k`-th iterate of the angular operator `D_θ = sin(2θ) ∂_θ`.
For the specific angular profile `f(θ) = 2 cos 2θ` the iterates are all divisible by
`sin(2θ)²`: this module defines the quotient sequence `gSeq` by the recursion

  `gSeq 0 = -4`,   `gSeq (n+1) = 4 cos(2θ) · gSeq n + sin(2θ) · (gSeq n)'`,

which is precisely the identity

  `D_θ (sin(2θ)² g) = sin(2θ)² (4 cos(2θ) g + sin(2θ) g')`,

so that `D_θ^{n+1} (2 cos 2θ) = sin(2θ)² · gSeq n` (proved in `Dth1IterTwoCosFactor`).

The structural facts recorded here are
* `gSeq_contDiff` : every `gSeq n` is `C^∞` on `ℝ` (so that `deriv` behaves and the recursion
  can be iterated);
* `gSeq_periodic` : every `gSeq n` is `π`-periodic (so that it is determined on `[0, π]`),
and the boundedness `gSeq_bdd` that follows from them by compactness of `[0, π]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.EllipticEst

noncomputable section

/-- The quotient sequence `gSeq n` of `D_θ^{n+1}(2 cos 2θ)` by `sin(2θ)²`. -/
def gSeq : ℕ → ℝ → ℝ
  | 0 => fun _ => -4
  | n + 1 => fun θ => 4 * Real.cos (2 * θ) * gSeq n θ + Real.sin (2 * θ) * deriv (gSeq n) θ

theorem gSeq_zero : gSeq 0 = fun _ => (-4 : ℝ) := rfl

theorem gSeq_succ (n : ℕ) :
    gSeq (n + 1) = fun θ => 4 * Real.cos (2 * θ) * gSeq n θ
      + Real.sin (2 * θ) * deriv (gSeq n) θ := rfl

/-- Every `gSeq n` is `C^∞`. -/
theorem gSeq_contDiff : ∀ n : ℕ, ContDiff ℝ ∞ (gSeq n) := by
  intro n
  induction n with
  | zero => rw [gSeq_zero]; exact contDiff_const
  | succ n ih =>
    have hd : ContDiff ℝ ∞ (deriv (gSeq n)) := (contDiff_infty_iff_deriv.mp ih).2
    have hcos : ContDiff ℝ ∞ (fun θ : ℝ => 4 * Real.cos (2 * θ)) :=
      contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
    have hsin : ContDiff ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
    have h : ContDiff ℝ ∞ (fun θ : ℝ => 4 * Real.cos (2 * θ) * gSeq n θ
        + Real.sin (2 * θ) * deriv (gSeq n) θ) := (hcos.mul ih).add (hsin.mul hd)
    rw [gSeq_succ]
    exact h

/-- Every `gSeq n` is differentiable. -/
theorem gSeq_differentiable (n : ℕ) : Differentiable ℝ (gSeq n) :=
  (contDiff_infty_iff_deriv.mp (gSeq_contDiff n)).1

/-- The derivative of a `c`-periodic function is `c`-periodic. -/
theorem periodic_deriv {f : ℝ → ℝ} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  rw [← deriv_comp_add_const f c x, show (fun y => f (y + c)) = f from funext fun y => h y]

theorem periodic_cos_two : Function.Periodic (fun θ : ℝ => Real.cos (2 * θ)) Real.pi := by
  intro θ
  show Real.cos (2 * (θ + Real.pi)) = Real.cos (2 * θ)
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring, Real.cos_add_two_pi]

theorem periodic_sin_two : Function.Periodic (fun θ : ℝ => Real.sin (2 * θ)) Real.pi := by
  intro θ
  show Real.sin (2 * (θ + Real.pi)) = Real.sin (2 * θ)
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring, Real.sin_add_two_pi]

theorem periodic_four_cos_two : Function.Periodic (fun θ : ℝ => 4 * Real.cos (2 * θ)) Real.pi := by
  intro θ
  show 4 * Real.cos (2 * (θ + Real.pi)) = 4 * Real.cos (2 * θ)
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring, Real.cos_add_two_pi]

/-- Every `gSeq n` is `π`-periodic. -/
theorem gSeq_periodic : ∀ n : ℕ, Function.Periodic (gSeq n) Real.pi := by
  intro n
  induction n with
  | zero =>
    rw [gSeq_zero]
    intro x
    simp
  | succ n ih =>
    have h1 : Function.Periodic (fun θ : ℝ => 4 * Real.cos (2 * θ) * gSeq n θ) Real.pi :=
      periodic_four_cos_two.mul ih
    have h2 : Function.Periodic (fun θ : ℝ => Real.sin (2 * θ) * deriv (gSeq n) θ) Real.pi :=
      periodic_sin_two.mul (periodic_deriv ih)
    have h := h1.add h2
    rw [gSeq_succ]
    exact h

/-- Each `gSeq n` is bounded on `ℝ`: it is continuous and `π`-periodic, hence bounded on the
compact `[0, π]`, and every point is `π`-periodically transported into `[0, π)`. -/
theorem gSeq_bdd (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, |gSeq n θ| ≤ C := by
  have hcont : Continuous (gSeq n) := (gSeq_contDiff n).continuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc 0 Real.pi) hcont.continuousOn
  have hC0 : 0 ≤ C := by
    have h0 : |gSeq n 0| ≤ C := by
      simpa [Real.norm_eq_abs] using hC 0 (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
    exact le_trans (abs_nonneg _) h0
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), fun θ => ?_⟩
  obtain ⟨y, hy, hyθ⟩ := (gSeq_periodic n).exists_mem_Ico₀ Real.pi_pos θ
  rw [hyθ]
  have hyI : y ∈ Set.Icc (0 : ℝ) Real.pi := Set.mem_Icc.mpr ⟨hy.1, le_of_lt hy.2⟩
  have h1 : |gSeq n y| ≤ C := by
    simpa [Real.norm_eq_abs] using hC y hyI
  exact le_trans h1 (le_max_left C 1)

end

end Work.FTS.EllipticEst
