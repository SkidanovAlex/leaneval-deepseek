/-
# Leibniz rule for `D_θ^j` with the genuine `C^∞` order

`Work.Spaces.DthIter_mul` proves the binomial (Leibniz) expansion

`D_θ^j (f · g) = ∑_{a ≤ j} (j.choose a) · (D_θ^a f · D_θ^{j-a} g)`

for slices that are **analytic** on an open set: its hypothesis is `ContDiffOn ℝ ⊤`, and in
this Mathlib `⊤ : ℕ∞ω` is the *analytic* order.  The localised data of this chapter live in
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)` (genuine `C^∞`, the class `SmoothQuad`), which
is *not* analytic (a cut-off is smooth but never analytic), so the analytic statement does not
apply.  This module redoes the one-dimensional argument of `Work.Spaces.Lop_iter_mul_eqOn` for
the genuine smooth order.

The only new ingredient is that `smoothOrder` is a fixed point of `n ↦ n + 1`
(`smoothOrder + 1 = smoothOrder`, since `⊤ + 1 = ⊤` in `ℕ∞`), so the `θ`-slice of a `C^∞`
function has `C^∞` derivative (`ContDiffAt.derivWithin` at `m = n = smoothOrder`).  Everything
else — the derivation `Lop u θ = sin(2θ)·u'(θ)`, the identification of `DthIter` with the
iterate of `Lop`, the product rule, the termwise derivative and the Pascal reindexing
`Work.Spaces.leibniz_step` — is the existing, order-agnostic machinery of
`Submission/Work/Spaces/DthIter_mul.lean`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- `smoothOrder` is a fixed point of `n ↦ n + 1`: the derivative of a `C^∞` function is
again `C^∞`. -/
theorem smoothOrder_add_one : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl

/-- Iterating the one-dimensional operator `Lop u θ = sin(2θ)·u'(θ)` preserves the genuine
`C^∞` order at a point.  (The analytic counterpart is the anonymous step inside
`Work.Spaces.Lop_iter_contDiffAt`, which uses `ContDiffAt.derivWithin` at `⊤ = ω`.) -/
theorem Lop_iter_contDiffAt_smooth (u : ℝ → ℝ) (θ : ℝ)
    (hu : ContDiffAt ℝ Work.Stability.smoothOrder u θ) (j : ℕ) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[j] u) θ := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hsin : ContDiffAt ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Real.sin (2 * θ)) θ := by
        fun_prop
      have hd : ContDiffAt ℝ Work.Stability.smoothOrder
          (deriv (Work.Spaces.Lop^[j] u)) θ :=
        ih.derivWithin smoothOrder_add_one.le
      have heq : Work.Spaces.Lop (Work.Spaces.Lop^[j] u)
          = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (Work.Spaces.Lop^[j] u) := rfl
      rw [heq]
      exact hsin.mul hd

/-- **Iterated Leibniz rule for `Lop`, genuine smooth order.**  On an open set `U` where
`u` and `v` are `C^∞` (in the genuine sense `smoothOrder`), the `j`-fold iterate of `Lop`
applied to the pointwise product agrees on `U` with the binomial convolution. -/
theorem Lop_iter_mul_eqOn_smooth (u v : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder u U)
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder v U) (j : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hFa : ∀ a, ContDiffAt ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[a] u) θ :=
        fun a => Lop_iter_contDiffAt_smooth u θ (hu.contDiffAt (hU.mem_nhds hθ)) a
      have hGb : ∀ b, ContDiffAt ℝ Work.Stability.smoothOrder (Work.Spaces.Lop^[b] v) θ :=
        fun b => Lop_iter_contDiffAt_smooth v θ (hv.contDiffAt (hU.mem_nhds hθ)) b
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        exact (((hFa a).differentiableAt (by simp)).mul
          ((hGb (j - a)).differentiableAt (by simp))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        (ih.deriv hU) hθ
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      rw [Finset.sum_congr rfl
        (fun a _ => Work.Spaces.sin_deriv_term u v θ j a ((hFa a).differentiableAt (by simp))
          ((hGb (j - a)).differentiableAt (by simp)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

/-- **Leibniz rule for `D_θ^j`, genuine smooth order.**  On an open set `U` where the
`θ`-slices of `f` and `g` (at the fixed `z`) are `C^∞`, the `j`-th iterate of `D_θ` applied
to the pointwise product satisfies the binomial expansion. -/
theorem DthIter_mul_smooth (j : ℕ) (f g : ℝ → ℝ → ℝ) (z : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) U)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => g z θ) U) :
    ∀ θ ∈ U, Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (j - a) g z θ) := by
  intro θ hθ
  have hmain := Lop_iter_mul_eqOn_smooth (fun θ' => f z θ') (fun θ' => g z θ') U hU hf hg j hθ
  have hstep : Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (Work.Spaces.Lop^[a] (fun θ' => f z θ') θ
            * Work.Spaces.Lop^[j - a] (fun θ' => g z θ') θ) := by
    rw [show (fun θ' => f z θ') * (fun θ' => g z θ') = (fun θ' => f z θ' * g z θ')
        from rfl] at hmain
    simp only [] at hmain
    rw [← hmain]
    exact congrFun (Work.Spaces.DthIter_eq_iterate_Lop j (fun z θ => f z θ * g z θ) z) θ
  rw [hstep]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Work.Spaces.DthIter_eq_iterate_Lop a f z,
    Work.Spaces.DthIter_eq_iterate_Lop (j - a) g z]

/-- **The Leibniz rule of the localisation chapter.**  For `C^∞` (genuine, order
`smoothOrder`) `θ`-slices at the fixed `z` on the angular interval `(0,π/2)`, the `j`-th
iterate of `D_θ` applied to a pointwise product expands into the binomial convolution. -/
theorem DthIter_mul_smoothQuad (j : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => f z θ') (Set.Ioo 0 (Real.pi / 2)))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ') (Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (j - a) g z θ) :=
  DthIter_mul_smooth j f g z (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo hf hg θ hθ

end Work.FTS.LocData
