import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular sequence controlling the `dthU`-iterates of `deriv Γ`

With `Γ(θ) = (sin θ cos²θ)^{α/3}` and `D_θ = sin(2θ) ∂_θ` one has (on `(0,π/2)`)

  `D_θ Γ = α · q(θ) · Γ`,   `q(θ) = cos 2θ - 1/3`,      (`Work.Spaces.dthU_Gam`)

so `deriv Γ = α·q/(sin 2θ)·Γ = α·Gseq α 0·Γ/(sin θ cos θ)` with `Gseq α 0 = q/2`.  The
denominator `sin θ cos θ` is *not* preserved by `D_θ` alone, but a short computation shows
that the whole quotient is, provided one puts

  `Gseq α (d+1) := D_θ (Gseq α d) + g · Gseq α d`,   `g(θ) = (α-2) q(θ) - 2/3`,

i.e. `D_θ^d (deriv Γ) = α · Gseq α d · Γ/(sin θ cos θ)` for every `d` (proved in
`Gam_deriv_bounds.lean`).

This file only sets up the definitions and the elementary pointwise bounds on the factor
`g`; the induction that bounds all `D_θ`-iterates of `Gseq α d` by constants is stated (and
proved) separately as `Gseq_iter_bounded`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)

/-! ## The angular factor `g` -/

/-- The factor of the recursion for `Gseq`:
`gfun α θ = (α-2)·q(θ) - 2/3 = α·q(θ) - 2 cos 2θ`. -/
noncomputable def gfun (α θ : ℝ) : ℝ := (α - 2) * Work.Spaces.qfun θ - 2 / 3

/-- The two forms of `gfun` that are used: `α q - 2 cos 2θ`. -/
theorem gfun_eq (α θ : ℝ) : gfun α θ = α * Work.Spaces.qfun θ - 2 * Real.cos (2 * θ) := by
  rw [gfun, Work.Spaces.qfun_apply]; ring

/-- `|q(θ)| ≤ 4/3` everywhere. -/
theorem abs_qfun_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply]
  have h1 : |Real.cos (2 * θ) - 1 / 3| ≤ |Real.cos (2 * θ)| + 1 / 3 := by
    have h := abs_sub_le (Real.cos (2 * θ)) 0 (1 / 3 : ℝ)
    rw [sub_zero, zero_sub, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at h
    exact h
  have h2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  linarith

/-! ## `dthU` and subtraction -/

theorem dthU_sub (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Work.Spaces.dthU (f - g) = Work.Spaces.dthU f - Work.Spaces.dthU g := by
  funext θ
  simp only [Work.Spaces.dthU_apply, Pi.sub_apply]
  rw [deriv_sub (hf θ) (hg θ)]
  ring

theorem dthU_const (c : ℝ) : Work.Spaces.dthU (fun _ : ℝ => c) = 0 := by
  funext θ
  simp [Work.Spaces.dthU_apply]

/-- Iterating `dthU` from the inside: `D_θ^i (D_θ f) = D_θ^{i+1} f`. -/
theorem dthU_iter_dthU (i : ℕ) (f : ℝ → ℝ) :
    Work.Spaces.dthU^[i] (Work.Spaces.dthU f) = Work.Spaces.dthU^[i+1] f :=
  (Function.iterate_succ_apply Work.Spaces.dthU i f).symm

/-- For `i ≥ 1` the constant `-2/3` of `gfun` has been annihilated: all the
`dthU`-iterates of `gfun` are those of `(α-2)·q`. -/
theorem dthU_iter_gfun (α : ℝ) (i : ℕ) (hi : 1 ≤ i) :
    Work.Spaces.dthU^[i] (fun θ => gfun α θ)
      = fun θ => (α - 2) * Work.Spaces.dthU^[i] Work.Spaces.qfun θ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hsplit : (fun θ => gfun α θ)
      = (fun θ => (α - 2) * Work.Spaces.qfun θ) - (fun _ : ℝ => 2 / 3) := by
    funext θ
    simp only [Pi.sub_apply, gfun]
  have hd1 : Differentiable ℝ (fun θ => (α - 2) * Work.Spaces.qfun θ) :=
    (contDiff_const.mul Work.Spaces.qfun_smooth).differentiable (by simp)
  have hd2 : Differentiable ℝ (fun _ : ℝ => (2 / 3 : ℝ)) := differentiable_const (2 / 3)
  have hstep : Work.Spaces.dthU (fun θ => gfun α θ)
      = fun θ => (α - 2) * Work.Spaces.dthU Work.Spaces.qfun θ := by
    rw [hsplit, dthU_sub _ _ hd1 hd2, Work.Spaces.dthU_const_mul, dthU_const, sub_zero]
  rw [Function.iterate_succ_apply, hstep, Work.Spaces.dthU_iter_const_mul,
    dthU_iter_dthU]

/-! ## The sequence `Gseq` -/

/-- The angular sequence with `D_θ^d (deriv (Gam α)) = α · Gseq α d · Gam α / (sin θ cos θ)`
on `(0,π/2)`.  Defined by `Gseq α 0 = q/2` and
`Gseq α (d+1) = D_θ (Gseq α d) + gfun α · Gseq α d`. -/
noncomputable def Gseq (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun θ => Work.Spaces.qfun θ / 2
  | (d + 1) => fun θ => Work.Spaces.dthU (Gseq α d) θ + gfun α θ * Gseq α d θ

@[simp] theorem Gseq_zero (α θ : ℝ) : Gseq α 0 θ = Work.Spaces.qfun θ / 2 := rfl

@[simp] theorem Gseq_succ_apply (α : ℝ) (d : ℕ) (θ : ℝ) :
    Gseq α (d + 1) θ = Work.Spaces.dthU (Gseq α d) θ + gfun α θ * Gseq α d θ := rfl

theorem Gseq_succ (α : ℝ) (d : ℕ) :
    Gseq α (d + 1) = Work.Spaces.dthU (Gseq α d) + (fun θ => gfun α θ) * Gseq α d := rfl

/-- `Gseq α d` is `C^∞`. -/
theorem Gseq_smooth (α : ℝ) (d : ℕ) : ContDiff ℝ C∞ (Gseq α d) := by
  induction d with
  | zero =>
      have h : Gseq α 0 = fun θ => (1 / 2 : ℝ) * Work.Spaces.qfun θ := by
        funext θ; simp only [Gseq_zero]; ring
      rw [h]
      exact contDiff_const.mul Work.Spaces.qfun_smooth
  | succ d ih =>
      rw [Gseq_succ]
      refine (Work.Spaces.dthU_smooth ih).add ?_
      exact (((contDiff_const.mul Work.Spaces.qfun_smooth).sub contDiff_const)).mul ih

/-! ## The pointwise bounds for the iterates of `g` -/

/-- The constant bounding the `dthU`-iterates of `gfun α`. -/
noncomputable def gBnd (i : ℕ) : ℝ := 2 * Work.Spaces.qBound i + 10 / 3

theorem gBnd_nonneg (i : ℕ) : 0 ≤ gBnd i := by
  unfold gBnd
  have := Work.Spaces.qBound_nonneg i
  linarith

/-- `|D_θ^i (gfun α) θ| ≤ gBnd i` on `Iθ`. -/
theorem dthU_gfun_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) : |Work.Spaces.dthU^[i] (fun θ => gfun α θ) θ| ≤ gBnd i := by
  have h2 : |α - 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Function.iterate_zero_apply]
    have hq := abs_qfun_le θ
    have h3 : gfun α θ = (α - 2) * Work.Spaces.qfun θ - 2 / 3 := rfl
    rw [h3]
    have h5 : |(α - 2) * Work.Spaces.qfun θ| ≤ 2 * (4 / 3) := by
      rw [abs_mul]
      exact mul_le_mul h2 hq (abs_nonneg _) (by norm_num)
    have h4 : |(α - 2) * Work.Spaces.qfun θ - 2 / 3| ≤ 10 / 3 := by
      have h := abs_sub_le ((α - 2) * Work.Spaces.qfun θ) 0 (2 / 3 : ℝ)
      rw [sub_zero, zero_sub, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at h
      linarith
    unfold gBnd
    have := Work.Spaces.qBound_nonneg 0
    linarith
  · rw [dthU_iter_gfun α i hi, abs_mul]
    refine le_trans (mul_le_mul h2 (Work.Spaces.dthU_qfun_le_qBound i hθ) (abs_nonneg _)
      (by norm_num)) ?_
    unfold gBnd
    have := Work.Spaces.qBound_nonneg i
    linarith

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
