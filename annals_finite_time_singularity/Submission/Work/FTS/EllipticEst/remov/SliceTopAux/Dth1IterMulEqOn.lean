/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Leibniz (binomial) rule for the iterated angular operator `D_θ = sin(2θ)∂_θ`

For `u`, `v` of class `C^N` on the open angular interval `(0, π/2)`,

  `D_θ^N (u · v) = ∑_{a ≤ N} C(N,a) · (D_θ^a u) · (D_θ^{N-a} v)`   on `(0, π/2)`.

This is the *finite order* version of the Leibniz rule: unlike the sibling statements
`Work.Spaces.Lop_iter_mul_eqOn` / `Work.FTS.EllipticEst.Lop_iter_mul`, which ask for the
analytic order `⊤` (equivalently genuine `C^∞`, cf. `Work.FTS.LocData.Lop_iter_mul_eqOn_smooth`),
here only `N` derivatives are needed — the order drops by one per iteration of `D_θ`, so `C^N`
is exactly the right hypothesis at level `N`.

`D_θ` acts on a `θ`-slice by the derivation `Lop u θ = sin(2θ)·u'(θ)`, and
`Dth1Iter n f = Lop^[n] f` (`Dth1Iter_eq_lop_iterate` below), so the substance is the
binomial expansion for the iterate of a derivation, proved by induction on `N`:
at level `N+1` one differentiates the level-`N` identity (valid on the *whole* open set `U`,
hence on a neighbourhood of the point) and uses the product rule, the identity
`sin(2θ)·(Lop^a u)' = Lop^{a+1} u`, and the Pascal reindexing `Work.Spaces.leibniz_step`.

The only genuinely finite-order input is that `a ≤ j` implies `Lop^[a] u` is differentiable
at the point when `u ∈ C^{j+1}` — that is `contDiffOn_Lop_iterate` below: iterating `Lop`
costs one order of regularity, `D_θ^a u ∈ C^{n-a}` for `u ∈ C^n`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov.SliceTopAux

/-! ## Auxiliary facts about the one-dimensional operator `Lop` -/

/-- `Dth1Iter` is the iterate of the derivation `Lop u θ = sin(2θ)·u'(θ)`. -/
private lemma Dth1Iter_eq_lop_iterate (n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter n f = Work.Spaces.Lop^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Elliptic.Dth1Iter_succ, ih, Function.iterate_succ_apply']
      rfl

/-- Iterating `Lop` costs one order of regularity: if `u` is `C^n` on the open set `U` then
`Lop^[a] u = D_θ^a u` is `C^{n-a}` there (for `a ≤ n`). -/
private lemma contDiffOn_Lop_iterate {U : Set ℝ} (hU : IsOpen U) {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) u U) :
    ∀ a ≤ n, ContDiffOn ℝ (((n - a : ℕ) : WithTop ℕ∞)) (Work.Spaces.Lop^[a] u) U := by
  intro a ha
  induction a with
  | zero => simpa using hu
  | succ j ih =>
      have hj : j ≤ n := Nat.le_of_succ_le ha
      have ihj : ContDiffOn ℝ (((n - j : ℕ) : WithTop ℕ∞)) (Work.Spaces.Lop^[j] u) U := ih hj
      have hle1 : 1 ≤ n - j := by omega
      have hder : ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (deriv (Work.Spaces.Lop^[j] u)) U := by
        refine ContDiffOn.deriv_of_isOpen ihj hU ?_
        have hcast : (((n - j - 1 : ℕ) : WithTop ℕ∞)) + 1 = ((n - j : ℕ) : WithTop ℕ∞) := by
          rw [← Nat.sub_add_cancel hle1]; push_cast; ring
        exact le_of_eq hcast
      have key : ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (Work.Spaces.Lop (Work.Spaces.Lop^[j] u)) U := by
        show ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] u) θ) U
        exact (by fun_prop : ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (fun θ : ℝ => Real.sin (2 * θ)) U).mul hder
      have hns : n - (j + 1) = n - j - 1 := by omega
      rw [Function.iterate_succ_apply', hns]
      exact key

/-! ## The finite-order Leibniz rule for `Lop` -/

/-- **Leibniz rule for iterates of `Lop`, finite order.**  On an open set `U` where `u` and `v`
are `C^j`, the `j`-th iterate of `Lop` applied to the pointwise product agrees on `U` with the
binomial convolution.  The hypothesis is of order `j`, not `⊤`: one order of regularity is
spent at each induction step, exactly the amount needed to differentiate the level-`(j-1)`
identity and to differentiate the `Lop^[a] u` for `a ≤ j - 1`. -/
private theorem Lop_iter_mul_eqOn_fin (U : Set ℝ) (hU : IsOpen U) (j : ℕ) :
    ∀ (u v : ℝ → ℝ),
      ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) u U →
      ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) v U →
      Set.EqOn (Work.Spaces.Lop^[j] (u * v))
        (fun θ => ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro u v hu hv θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro u v hu hv θ hθ
      rw [Function.iterate_succ_apply']
      have hle : ((j : ℕ) : WithTop ℕ∞) ≤ ((j + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast Nat.le_succ j
      have hprev := ih u v (hu.of_le hle) (hv.of_le hle)
      -- `Lop^[a] u`, `Lop^[b] v` are differentiable at `θ` for `a, b ≤ j`
      have hFa : ∀ a, a ≤ j → DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := by
        intro a ha
        have hcont := contDiffOn_Lop_iterate hU hu a (le_trans ha (Nat.le_succ j))
        have hne : (((j + 1 - a : ℕ) : WithTop ℕ∞)) ≠ 0 := by
          rw [Nat.cast_ne_zero]; omega
        exact (hcont.differentiableOn hne).differentiableAt (hU.mem_nhds hθ)
      have hGb : ∀ b, b ≤ j → DifferentiableAt ℝ (Work.Spaces.Lop^[b] v) θ := by
        intro b hb
        have hcont := contDiffOn_Lop_iterate hU hv b (le_trans hb (Nat.le_succ j))
        have hne : (((j + 1 - b : ℕ) : WithTop ℕ∞)) ≠ 0 := by
          rw [Nat.cast_ne_zero]; omega
        exact (hcont.differentiableOn hne).differentiableAt (hU.mem_nhds hθ)
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        rw [Finset.mem_range] at ha
        exact (((hFa a (Nat.lt_succ_iff.mp ha)).mul (hGb (j - a) (Nat.sub_le j a))).const_mul _)
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
        (hprev.deriv hU) hθ
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
        (fun a ha => Work.Spaces.sin_deriv_term u v θ j a
          (hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          (hGb (j - a) (Nat.sub_le j a)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

/-! ## The requested statement -/

theorem Dth1IterMulEqOn (N : ℕ) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ (N : WithTop ℕ∞) u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ContDiffOn ℝ (N : WithTop ℕ∞) v (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Elliptic.Dth1Iter N (fun θ => u θ * v θ))
      (fun θ => ∑ a ∈ Finset.range (N + 1),
        (N.choose a : ℝ) * (Work.Elliptic.Dth1Iter a u θ * Work.Elliptic.Dth1Iter (N - a) v θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have h := (Lop_iter_mul_eqOn_fin (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo N u v hu hv)
    (x := θ) hθ
  simp only [Dth1Iter_eq_lop_iterate]
  rw [show (fun θ : ℝ => u θ * v θ) = u * v from rfl]
  exact h

end Work.FTS.EllipticEst.remov.SliceTopAux
