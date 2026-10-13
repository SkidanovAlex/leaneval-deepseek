/-
Copyright: work module for the Elgindi finite-time singularity project.

# Subtraction commutes with the iterated angular operator `D_θ = sin(2θ) ∂_θ`

For two functions `u`, `v` of class `C^N` on the open angular interval `(0, π/2)`, the `N`-th
iterate of `D_θ` applied to the difference `u - v` is the difference of the `N`-th iterates:

  `Dth1Iter N (fun θ => u θ - v θ) =ᵉ[Ioo 0 (π/2)] fun θ => Dth1Iter N u θ - Dth1Iter N v θ`.

This is the `C^N` (finite regularity) analogue of
`Work.FTS.EllipticEst.TT.Dth1Iter_add_of_smooth`, which assumes `C^∞` on a neighbourhood of the
closed interval.  The point of the finite regularity version is that `Dth1Iter n f` is only
asserted to be differentiable where the underlying regularity allows it: `D_θ` is *not*
additive as a global operation on `ℝ → ℝ` (`deriv` is only additive at points where both
summands are differentiable), so the identity can only be asserted on the open set carrying the
hypothesis.

The proof runs by induction on the number of iterations.  At each step the induction
hypothesis supplies equality on all of `Ioo 0 (π/2)`, which is a neighbourhood of the point
`θ`, so `Filter.EventuallyEq.deriv_eq` replaces the derivative of the iterate of the
difference by the derivative of the iterate of the difference of the pieces; the auxiliary
smoothness lemma `Dth1Iter_contDiffOn` (proved here) says that `Dth1Iter n u` and
`Dth1Iter n v` are differentiable at `θ` as long as `n < N`, which is exactly what
`deriv_sub` requires.
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

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SliceTopAux

noncomputable section

/-- **Smoothness of the iterates at finite order.**  If `f` is `C^k` on the open interval
`(0, π/2)` then its `n`-th `D_θ`-iterate is `C^{k-n}` there, for every `n ≤ k`.

The subtraction of orders is genuine: each application of `D_θ` uses one derivative of the
current iterate (`ContDiffOn.deriv_of_isOpen`) and multiplication by the smooth factor
`sin(2θ)`. -/
private lemma Dth1Iter_contDiffOn (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ n : ℕ, n ≤ k →
      ContDiffOn ℝ ((k - n : ℕ) : WithTop ℕ∞) (Work.Elliptic.Dth1Iter n f)
        (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  induction n with
  | zero => intro _; simpa using hf
  | succ n ih =>
    intro hn
    have hn' : n ≤ k := le_trans (Nat.le_succ n) hn
    have ih' := ih hn'
    have hle : 1 ≤ k - n := by omega
    -- one derivative is spent: `(k - n - 1) + 1 ≤ k - n`
    have hm : ((k - n - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((k - n : ℕ) : WithTop ℕ∞) := by
      have h1 : ((k - n - 1 : ℕ) : WithTop ℕ∞) + 1
          = (((k - n - 1) + 1 : ℕ) : WithTop ℕ∞) := by
        norm_cast
      rw [h1, Nat.sub_add_cancel hle]
    have hd : ContDiffOn ℝ ((k - n - 1 : ℕ) : WithTop ℕ∞)
        (deriv (Work.Elliptic.Dth1Iter n f)) (Set.Ioo 0 (Real.pi / 2)) :=
      ih'.deriv_of_isOpen isOpen_Ioo hm
    have hsin : ContDiffOn ℝ ((k - n - 1 : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have hmul := hsin.mul hd
    rw [show k - (n + 1) = k - n - 1 from (Nat.sub_sub k n 1).symm]
    change ContDiffOn ℝ ((k - n - 1 : ℕ) : WithTop ℕ∞)
      (fun x : ℝ => Real.sin (2 * x) * deriv (Work.Elliptic.Dth1Iter n f) x)
      (Set.Ioo 0 (Real.pi / 2))
    exact hmul

theorem Dth1IterSubEqOn (N : ℕ) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ (N : WithTop ℕ∞) u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ContDiffOn ℝ (N : WithTop ℕ∞) v (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Elliptic.Dth1Iter N (fun θ => u θ - v θ))
      (fun θ => Work.Elliptic.Dth1Iter N u θ - Work.Elliptic.Dth1Iter N v θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have key : ∀ n : ℕ, n ≤ N → Set.EqOn (Work.Elliptic.Dth1Iter n (fun θ => u θ - v θ))
      (fun θ => Work.Elliptic.Dth1Iter n u θ - Work.Elliptic.Dth1Iter n v θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    induction n with
    | zero => intro _ θ hθ; simp [Work.Elliptic.Dth1Iter]
    | succ n ih =>
      intro hn θ hθ
      have hnN : n ≤ N := le_trans (Nat.le_succ n) hn
      have hIH := ih hnN
      -- `n < N`, so the `n`-th iterates are differentiable at `θ`
      have hne : ((N - n : ℕ) : WithTop ℕ∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hd_u : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n u) θ :=
        ((Dth1Iter_contDiffOn N hu n hnN).differentiableOn hne).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd_v : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n v) θ :=
        ((Dth1Iter_contDiffOn N hv n hnN).differentiableOn hne).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      -- the induction hypothesis holds on the whole open interval, hence near `θ`
      have heq : Work.Elliptic.Dth1Iter n (fun θ => u θ - v θ) =ᶠ[𝓝 θ]
          (fun θ => Work.Elliptic.Dth1Iter n u θ - Work.Elliptic.Dth1Iter n v θ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
        exact hIH hy
      calc Work.Elliptic.Dth1Iter (n + 1) (fun θ => u θ - v θ) θ
          = Real.sin (2 * θ)
              * deriv (Work.Elliptic.Dth1Iter n (fun θ => u θ - v θ)) θ := rfl
        _ = Real.sin (2 * θ)
              * deriv (fun θ => Work.Elliptic.Dth1Iter n u θ
                  - Work.Elliptic.Dth1Iter n v θ) θ := by
              rw [heq.deriv_eq]
        _ = Real.sin (2 * θ)
              * (deriv (Work.Elliptic.Dth1Iter n u) θ
                  - deriv (Work.Elliptic.Dth1Iter n v) θ) := by
              rw [show deriv (fun θ : ℝ => Work.Elliptic.Dth1Iter n u θ
                    - Work.Elliptic.Dth1Iter n v θ) θ
                    = deriv (Work.Elliptic.Dth1Iter n u) θ
                      - deriv (Work.Elliptic.Dth1Iter n v) θ
                  from deriv_sub hd_u hd_v]
        _ = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n u) θ
              - Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n v) θ := by rw [mul_sub]
        _ = Work.Elliptic.Dth1Iter (n + 1) u θ
              - Work.Elliptic.Dth1Iter (n + 1) v θ := rfl
  exact key N le_rfl

end

end Work.FTS.EllipticEst.remov.SliceTopAux
