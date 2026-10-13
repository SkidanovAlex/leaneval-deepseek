import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The iterated Leibniz rule for `Lop` at finite smoothness order

`Work.Spaces.Lop` is the derivation `L u θ = sin(2θ) · u'(θ)` (the action of `D_θ` on a
`θ`-slice).  `Work.Spaces.Lop_iter_mul_eqOn` proves the binomial expansion of `L^[i] (u * v)`
on an open set on which `u` and `v` are **analytic** (`⊤ : WithTop ℕ∞` is the analytic order
in this Mathlib).  The statement proved here is the same binomial expansion under the much
weaker finite-order hypothesis `ContDiffOn ℝ (i + 1)`.

The only new ingredients are:

* `Lop_iter_contDiffOn_aux`: if `u` is `C^N` on an open set `V`, then `L^[k] u` is `C^m` there
  whenever `k + m ≤ N` (induction on `k`, using `ContDiffOn.deriv_of_isOpen` and the product
  rule for `ContDiffOn`).  This replaces the analyticity used in `Work.Spaces.Lop_iter_mul_eqOn`
  and supplies the differentiability of the summands in the induction step.
* `Lop_iter_mul_aux`: the induction on `i`, a verbatim adaptation of the proof of
  `Work.Spaces.Lop_iter_mul_eqOn` with the new smoothness source.
-/

open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

/-- Iterating the derivation `Lop` raises the smoothness order: if `u` is `C^N` on the open
set `V` then `Lop^[k] u` is `C^m` on `V` whenever `k + m ≤ N`. -/
lemma Lop_iter_contDiffOn_aux (u : ℝ → ℝ) (V : Set ℝ) (hV : IsOpen V) (N : ℕ) :
    ∀ k m : ℕ, k + m ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u V →
      ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Spaces.Lop^[k] u) V := by
  intro k
  induction k with
  | zero =>
      intro m hm hu
      simpa using hu.of_le (Nat.cast_le.mpr (by omega : m ≤ N))
  | succ k ih =>
      intro m hm hu
      have hk : k + (m + 1) ≤ N := by omega
      have hih := ih (m + 1) hk hu
      have hderiv : ContDiffOn ℝ (m : WithTop ℕ∞) (deriv (Work.Spaces.Lop^[k] u)) V :=
        hih.deriv_of_isOpen hV (le_of_eq rfl)
      have hsin : ContDiffOn ℝ (m : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) V := by
        fun_prop
      rw [Function.iterate_succ_apply']
      exact hsin.mul hderiv

/-- The iterated Leibniz rule for `Lop`, on an open set where `u` and `v` are only `C^(i+1)`. -/
theorem Lop_iter_mul_aux (i : ℕ) :
    ∀ (u v : ℝ → ℝ) (V : Set ℝ), IsOpen V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V →
      Set.EqOn (Work.Spaces.Lop^[i] (u * v))
        (fun θ => ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[i - a] v θ)) V := by
  induction i with
  | zero =>
      intro u v V hV hu hv θ hθ
      simp [Function.iterate_zero_apply]
  | succ i ih =>
      intro u v V hV hu hv θ hθ
      dsimp only
      rw [Function.iterate_succ_apply']
      have hu' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V :=
        hu.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hv' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V :=
        hv.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hih := ih u v V hV hu' hv'
      have hFa : ∀ a ≤ i, DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := fun a ha =>
        ((Lop_iter_contDiffOn_aux u V hV (i + 1) a 1 (by omega) hu').contDiffAt
          (hV.mem_nhds hθ)).differentiableAt (by norm_num)
      have hGb : ∀ b ≤ i, DifferentiableAt ℝ (Work.Spaces.Lop^[b] v) θ := fun b hb =>
        ((Lop_iter_contDiffOn_aux v V hV (i + 1) b 1 (by omega) hv').contDiffAt
          (hV.mem_nhds hθ)).differentiableAt (by norm_num)
      have hmem : ∀ a ∈ Finset.range (i + 1), DifferentiableAt ℝ
          (fun θ' => (i.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ := by
        intro a ha
        exact (((hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))).mul
          (hGb (i - a) (Nat.sub_le i a))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ'))
          = ∑ a ∈ Finset.range (i + 1),
            (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Lop^[i] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (i + 1),
              (i.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ :=
        (hih.deriv hV) hθ
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[i] (u * v)) θ
          = ∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (i.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[i] (u * v)) θ
          = ∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (i.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      trans ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
          (Work.Spaces.Lop^[a + 1] u θ * Work.Spaces.Lop^[i - a] v θ
            + Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[i - a + 1] v θ)
      · exact Finset.sum_congr rfl (fun a ha => Work.Spaces.sin_deriv_term u v θ i a
          (hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))) (hGb (i - a) (Nat.sub_le i a)))
      · exact Work.Spaces.leibniz_step i (fun b => Work.Spaces.Lop^[b] u θ)
          (fun b => Work.Spaces.Lop^[b] v θ)

theorem Lop_iter_mul_of_contDiffOn {i : ℕ} {u v : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (hu : ContDiffOn ℝ (i + 1) u V) (hv : ContDiffOn ℝ (i + 1) v V) :
    ∀ θ ∈ V, Work.Spaces.Lop^[i] (u * v) θ
      = ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[i - a] v θ) :=
  Lop_iter_mul_aux i u v V hV hu hv

end Work.FTS.Nonlinear.Pieces.RNP.row19
