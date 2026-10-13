/-
Copyright: work module for the Elgindi finite-time singularity project.

# Leibniz rule for the iterated angular operator `D_θ`

For fixed `z`, the operator `D_θ f = sin(2θ) ∂_θ f` acts on the `θ`-slice
`θ ↦ f z θ` as the derivation `L u θ = sin(2θ) u'(θ)`.  Consequently every
iterate satisfies the binomial (Leibniz) rule

`D_θ^j (f · g) = ∑_{a ≤ j} (j.choose a) · (D_θ^a f · D_θ^{j-a} g)`.

This file isolates this purely one-dimensional statement.  The reindexing
(Pascal) identity used in the induction step is `Work.Spaces.leibniz_step`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DerivLikeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter

namespace Work.Spaces

/-- The operator `L u θ = sin(2θ) · u'(θ)`: the action of `D_θ` on functions of `θ` alone. -/
noncomputable def Lop (u : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv u θ

/-- For fixed `z`, `DthIter n f z` is the `n`-fold iterate of `Lop` applied to
`θ ↦ f z θ`. -/
lemma DthIter_eq_iterate_Lop (n : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (DthIter n f) z = Lop^[n] (fun θ => f z θ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [DthIter_succ]
      funext θ
      simp only [Dth, pth]
      rw [Function.iterate_succ_apply']
      show Real.sin (2 * θ) * deriv (fun θ' => DthIter n f z θ') θ =
        Real.sin (2 * θ) * deriv (Lop^[n] (fun θ => f z θ)) θ
      congr 1
      rw [show (fun θ' => DthIter n f z θ') = (DthIter n f) z from rfl, ih]

/-- `Lop` satisfies the product rule (it is a derivation for the pointwise product). -/
lemma Lop_mul (u v : ℝ → ℝ) (θ : ℝ) (hu : DifferentiableAt ℝ u θ)
    (hv : DifferentiableAt ℝ v θ) :
    Lop (u * v) θ = Lop u θ * v θ + u θ * Lop v θ := by
  unfold Lop
  rw [deriv_mul hu hv]
  ring

/-- Iterating `Lop` preserves `C^∞`-regularity at a point. -/
lemma Lop_iter_contDiffAt (u : ℝ → ℝ) (θ : ℝ) (hu : ContDiffAt ℝ ⊤ u θ) (j : ℕ) :
    ContDiffAt ℝ ⊤ (Lop^[j] u) θ := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hsin : ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
      have hd : ContDiffAt ℝ ⊤ (deriv (Lop^[j] u)) θ :=
        ContDiffAt.derivWithin (m := ⊤) ih (by simp)
      have heq : Lop (Lop^[j] u) = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (Lop^[j] u) := rfl
      rw [heq]
      exact hsin.mul hd

/-- Differentiating the `a`-th term of the Leibniz sum. -/
lemma sin_deriv_term (u v : ℝ → ℝ) (θ : ℝ) (j a : ℕ)
    (ha : DifferentiableAt ℝ (Lop^[a] u) θ) (hb : DifferentiableAt ℝ (Lop^[j - a] v) θ) :
    Real.sin (2 * θ)
        * deriv (fun θ' => (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ')) θ =
      (j.choose a : ℝ)
        * (Lop^[a + 1] u θ * Lop^[j - a] v θ + Lop^[a] u θ * Lop^[j - a + 1] v θ) := by
  have hfun2 : (fun θ' => (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ'))
      = (fun y => (j.choose a : ℝ) * ((Lop^[a] u * Lop^[j - a] v) y)) := rfl
  rw [hfun2, deriv_const_mul (j.choose a : ℝ) (ha.mul hb), deriv_mul ha hb,
      Function.iterate_succ_apply' Lop a u, Function.iterate_succ_apply' Lop (j - a) v,
      show Lop (Lop^[a] u) θ = Real.sin (2 * θ) * deriv (Lop^[a] u) θ from rfl,
      show Lop (Lop^[j - a] v) θ = Real.sin (2 * θ) * deriv (Lop^[j - a] v) θ from rfl]
  ring

/-- The iterated Leibniz rule for `Lop`. -/
lemma Lop_iter_mul_eqOn (u v : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ⊤ u U) (hv : ContDiffOn ℝ ⊤ v U) (j : ℕ) :
    Set.EqOn (Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Lop^[a] u θ * Lop^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hFa : ∀ a, ContDiffAt ℝ ⊤ (Lop^[a] u) θ :=
        fun a => Lop_iter_contDiffAt u θ (hu.contDiffAt (hU.mem_nhds hθ)) a
      have hGb : ∀ b, ContDiffAt ℝ ⊤ (Lop^[b] v) θ :=
        fun b => Lop_iter_contDiffAt v θ (hv.contDiffAt (hU.mem_nhds hθ)) b
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ')) θ := by
        intro a ha
        exact ((hFa a).differentiableAt (by simp)).mul
          ((hGb (j - a)).differentiableAt (by simp)) |>.const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ')) θ :=
        (ih.deriv hU) hθ
      have hkey : Lop (Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ) * (Lop^[a] u θ' * Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      rw [Finset.sum_congr rfl
        (fun a _ => sin_deriv_term u v θ j a ((hFa a).differentiableAt (by simp))
          ((hGb (j - a)).differentiableAt (by simp)))]
      exact leibniz_step j (fun b => Lop^[b] u θ) (fun b => Lop^[b] v θ)

/-- **Leibniz rule for `D_θ^j`.**  On an open set `U` where the `θ`-slices of `f` and `g`
are `C^∞`, the `j`-th iterate of `D_θ` applied to the pointwise product satisfies the
binomial expansion. -/
theorem DthIter_mul (j : ℕ) (f g : ℝ → ℝ → ℝ) (z : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ⊤ (fun θ => f z θ) U) (hg : ContDiffOn ℝ ⊤ (fun θ => g z θ) U) :
    ∀ θ ∈ U, Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (j - a) g z θ) := by
  intro θ hθ
  have hmain := Lop_iter_mul_eqOn (fun θ' => f z θ') (fun θ' => g z θ') U hU hf hg j hθ
  have hstep : DthIter j (fun z θ => f z θ * g z θ) z θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (Lop^[a] (fun θ' => f z θ') θ * Lop^[j - a] (fun θ' => g z θ') θ) := by
    rw [show (fun θ' => f z θ') * (fun θ' => g z θ') = (fun θ' => f z θ' * g z θ')
        from rfl] at hmain
    simp only [] at hmain
    rw [← hmain]
    exact congrFun (DthIter_eq_iterate_Lop j (fun z θ => f z θ * g z θ) z) θ
  rw [hstep]
  apply Finset.sum_congr rfl
  intro a ha
  rw [DthIter_eq_iterate_Lop a f z, DthIter_eq_iterate_Lop (j - a) g z]

end Work.Spaces
