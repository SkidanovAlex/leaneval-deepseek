/-
# `Work.FTS.GalBasis.cc.PsiCutDeriv` — the Leibniz rules and affine reductions behind `psiCut_spec`

This module proves the uniform-in-`N` bounds on the iterated derivatives of the two
one-dimensional steps

  `cutA N z = s((N+1) z - 1) · s(2 - z/(N+1))`,   `cutB N θ = s((N+1) θ - 1) · s((N+1)(π/2-θ) - 1)`

(`s = Real.smoothTransition`) that the fifth conjunct of `psiCut_spec` needs.

Two mechanisms are used:

* the *rescaled variables* of `PsiCutAux`: in `u = λ z + a` the operator `D_z = z∂_z` becomes
  `Eiter · (u ↦ u - a)` and in `u = λ θ + c` the operator `D_θ = sin(2θ)∂_θ` becomes
  `Eiter · (u ↦ ρ_λ(u))` with `ρ_λ(u) = λ sin(2 (u+1)/λ)`; the coefficient functions have
  derivatives bounded by constants *independent of `λ`*, which is the point of the
  scale-invariant mesh `1/(N+1)`;
* the one-variable Leibniz rules `DzIter1_mul`, `DthIter1_mul` for the products
  `cutA N = cutA1 · cutA2` and `cutB N = cutB1 · cutB2`.

(Note that `Work.Spaces.DzIter_mul` / `DthIter_mul` cannot be used here: their hypothesis
`ContDiffOn ℝ ⊤` is the *analytic* order `ω` of this Mathlib, whereas the steps are merely
smooth.)
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.GalBasis.cc.PsiCutAux
import Submission.Work.FTS.GalBasis.cc.psiCut_mixed_factor
import Submission.Work.FTS.GalBasis.cc.iteratedDeriv_smoothTransition_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Small trigonometric bounds -/

theorem abs_sin_le_one (x : ℝ) : |Real.sin x| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

theorem abs_cos_le_one (x : ℝ) : |Real.cos x| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-! ## The one-variable Leibniz rules

The product rules for the one-variable operators `Dz1 f = z f'` and `Dth1 b = sin(2θ) b'` of
`psiCut_mixed_factor`.  They hold pointwise, with no restriction on the point, unlike the
two-variable `Work.Spaces.DzIter_mul`/`DthIter_mul` (whose `ContDiffOn ℝ ⊤` hypothesis is the
analytic order and hence unusable for the smooth steps). -/

theorem contDiff_DzIter1 {f : ℝ → ℝ} (hf : ∀ n : ℕ, ContDiff ℝ n f) :
    ∀ k n : ℕ, ContDiff ℝ n (DzIter1 k f) := by
  intro k
  induction k with
  | zero => intro n; simpa using hf n
  | succ k ih =>
      intro n
      have h : DzIter1 (k + 1) f = (fun z : ℝ => z) * deriv (DzIter1 k f) := rfl
      rw [h]
      exact contDiff_id.mul ((ih (n + 1)).deriv')

theorem contDiff_DthIter1 {b : ℝ → ℝ} (hb : ∀ n : ℕ, ContDiff ℝ n b) :
    ∀ k n : ℕ, ContDiff ℝ n (DthIter1 k b) := by
  intro k
  induction k with
  | zero => intro n; simpa using hb n
  | succ k ih =>
      intro n
      have h : DthIter1 (k + 1) b = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (DthIter1 k b) := rfl
      rw [h]
      exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).mul ((ih (n + 1)).deriv')

theorem DzIter1_succ_apply (k : ℕ) (f : ℝ → ℝ) (z : ℝ) :
    DzIter1 (k + 1) f z = z * deriv (DzIter1 k f) z := rfl

theorem DthIter1_succ_apply (k : ℕ) (b : ℝ → ℝ) (θ : ℝ) :
    DthIter1 (k + 1) b θ = Real.sin (2 * θ) * deriv (DthIter1 k b) θ := rfl

theorem DzIter1_mul (j : ℕ) {f g : ℝ → ℝ} (hf : ∀ n : ℕ, ContDiff ℝ n f)
    (hg : ∀ n : ℕ, ContDiff ℝ n g) :
    ∀ z : ℝ, DzIter1 j (fun z' => f z' * g z') z
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * (DzIter1 a f z * DzIter1 (j - a) g z) := by
  induction j with
  | zero => intro z; simp
  | succ j ih =>
      intro z
      have hfune : DzIter1 j (fun z' => f z' * g z')
          = fun z' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ) * (DzIter1 a f z' * DzIter1 (j - a) g z') := by
        funext z'; exact ih z'
      rw [DzIter1_succ, hfune]
      show z * deriv (fun w : ℝ => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (DzIter1 a f w * DzIter1 (j - a) g w)) z = _
      have hfun : (fun w : ℝ => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (DzIter1 a f w * DzIter1 (j - a) g w))
          = ∑ a ∈ Finset.range (j + 1), (fun w : ℝ => (j.choose a : ℝ) *
              (DzIter1 a f w * DzIter1 (j - a) g w)) := by
        funext w; rw [Finset.sum_apply]
      rw [hfun]
      have hsum := deriv_sum (u := Finset.range (j + 1)) (x := z)
        (A := fun a => fun w : ℝ => (j.choose a : ℝ) *
          (DzIter1 a f w * DzIter1 (j - a) g w))
        (by intro a _
            exact (((contDiff_DzIter1 hf a 1).differentiable (by norm_num)).differentiableAt.mul
              (((contDiff_DzIter1 hg (j - a) 1).differentiable (by norm_num)).differentiableAt)).const_mul _)
      rw [hsum, Finset.mul_sum]
      rw [show (∑ a ∈ Finset.range (j + 1), z * deriv (fun w : ℝ => (j.choose a : ℝ) *
              (DzIter1 a f w * DzIter1 (j - a) g w)) z)
            = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
                (DzIter1 (a + 1) f z * DzIter1 (j - a) g z
                  + DzIter1 a f z * DzIter1 (j - a + 1) g z) from by
        apply Finset.sum_congr rfl
        intro a _
        have hda : DifferentiableAt ℝ (DzIter1 a f) z :=
          ((contDiff_DzIter1 hf a 1).differentiable (by norm_num)).differentiableAt
        have hdb : DifferentiableAt ℝ (DzIter1 (j - a) g) z :=
          ((contDiff_DzIter1 hg (j - a) 1).differentiable (by norm_num)).differentiableAt
        change z * deriv ((fun _ : ℝ => (j.choose a : ℝ)) *
            (DzIter1 a f * DzIter1 (j - a) g)) z = _
        rw [deriv_mul (differentiableAt_const _) (hda.mul hdb), deriv_const, deriv_mul hda hdb,
          DzIter1_succ_apply, DzIter1_succ_apply]
        ring]
      exact Work.Spaces.leibniz_step j (fun b => DzIter1 b f z) (fun b => DzIter1 b g z)

theorem DthIter1_mul (i : ℕ) {b c : ℝ → ℝ} (hb : ∀ n : ℕ, ContDiff ℝ n b)
    (hc : ∀ n : ℕ, ContDiff ℝ n c) :
    ∀ θ : ℝ, DthIter1 i (fun θ' => b θ' * c θ') θ
      = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * (DthIter1 a b θ * DthIter1 (i - a) c θ) := by
  induction i with
  | zero => intro θ; simp
  | succ i ih =>
      intro θ
      have hfune : DthIter1 i (fun θ' => b θ' * c θ')
          = fun θ' => ∑ a ∈ Finset.range (i + 1),
              (i.choose a : ℝ) * (DthIter1 a b θ' * DthIter1 (i - a) c θ') := by
        funext θ'; exact ih θ'
      rw [DthIter1_succ, hfune]
      show Real.sin (2 * θ) * deriv (fun w : ℝ => ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (DthIter1 a b w * DthIter1 (i - a) c w)) θ = _
      have hfun : (fun w : ℝ => ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (DthIter1 a b w * DthIter1 (i - a) c w))
          = ∑ a ∈ Finset.range (i + 1), (fun w : ℝ => (i.choose a : ℝ) *
              (DthIter1 a b w * DthIter1 (i - a) c w)) := by
        funext w; rw [Finset.sum_apply]
      rw [hfun]
      have hsum := deriv_sum (u := Finset.range (i + 1)) (x := θ)
        (A := fun a => fun w : ℝ => (i.choose a : ℝ) *
          (DthIter1 a b w * DthIter1 (i - a) c w))
        (by intro a _
            exact (((contDiff_DthIter1 hb a 1).differentiable (by norm_num)).differentiableAt.mul
              (((contDiff_DthIter1 hc (i - a) 1).differentiable (by norm_num)).differentiableAt)).const_mul _)
      rw [hsum, Finset.mul_sum]
      rw [show (∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ) * deriv (fun w : ℝ => (i.choose a : ℝ) *
              (DthIter1 a b w * DthIter1 (i - a) c w)) θ)
            = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
                (DthIter1 (a + 1) b θ * DthIter1 (i - a) c θ
                  + DthIter1 a b θ * DthIter1 (i - a + 1) c θ) from by
        apply Finset.sum_congr rfl
        intro a _
        have hda : DifferentiableAt ℝ (DthIter1 a b) θ :=
          ((contDiff_DthIter1 hb a 1).differentiable (by norm_num)).differentiableAt
        have hdb : DifferentiableAt ℝ (DthIter1 (i - a) c) θ :=
          ((contDiff_DthIter1 hc (i - a) 1).differentiable (by norm_num)).differentiableAt
        change Real.sin (2 * θ) * deriv ((fun _ : ℝ => (i.choose a : ℝ)) *
            (DthIter1 a b * DthIter1 (i - a) c)) θ = _
        rw [deriv_mul (differentiableAt_const _) (hda.mul hdb), deriv_const, deriv_mul hda hdb,
          DthIter1_succ_apply, DthIter1_succ_apply]
        ring]
      exact Work.Spaces.leibniz_step i (fun m => DthIter1 m b θ) (fun m => DthIter1 m c θ)

end Work.FTS.GalBasis.cc
