import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped BigOperators

namespace Work.EllipticEst.ModalSolution.PairIdent

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer

/-! ## `Lzero` on a `z`-independent function, and its linearity over finite mode sums

`Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` involves only `θ`-derivatives, so on a function of
`θ` alone it is the one-variable operator `Lzero1 f = -f'' + (tan · f)' - 6f` (`lzero_indep`).
It is linear, hence commutes with a finite sum of modes whose summands are differentiable
(`deriv_sum_const_mul`, `deriv_sum_tan_const_mul`), and each mode is an eigenfunction with
eigenvalue `lam m = 2m(2m+5)` (`eFam_Lzero`), which gives `lzero_sum_indep` and then the
requested identity for the truncated mode series. -/

/-- `Lzero` applied to a function of `θ` alone: the `z`-variable is irrelevant. -/
private lemma lzero_indep (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -(deriv (deriv f) θ) + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `∂_θ` of a finite sum of modes `θ ↦ ∑ m, a m · e m θ`. -/
private lemma deriv_sum_const_mul (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => ∑ m ∈ s, a m * e m θ') θ = ∑ m ∈ s, a m * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, a m * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => a m * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (a m))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (a m) (he m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of modes `θ ↦ ∑ m, a m · e m θ`. -/
private lemma deriv_sum_tan_const_mul (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * e m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * e m θ') θ := by
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hfun : (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, a m * e m θ'))
      = ∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) := by
    funext θ'; rw [Finset.sum_apply, Finset.mul_sum]
  have hstep : deriv (∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))) θ
      = ∑ m ∈ s, deriv (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) θ :=
    deriv_sum (fun m hm => htan.mul ((he m hm).const_mul (a m)))
  rw [hfun, hstep]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))
      = fun θ' : ℝ => a m * (Real.tan θ' * e m θ') from by funext θ'; ring]
  exact deriv_const_mul (a m) (htan.mul (he m hm))

/-- **`Lzero` on a finite sum of eigenmodes.**  For any finite set `s` of modes and any `θ`
with `cos θ ≠ 0`, the action of `Lzero` on `θ ↦ ∑ m ∈ s, a m · eFam m θ` is the mode-wise
action, with eigenvalue `lam m = 2m(2m+5)`. -/
private lemma lzero_sum_indep (a : ℕ → ℝ) (s : Finset ℕ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eFam m θ') z θ
      = ∑ m ∈ s, lam m * a m * eFam m θ := by
  have he : ∀ m ∈ s, ∀ θ' : ℝ, DifferentiableAt ℝ (eFam m) θ' :=
    fun m _ θ' => (Work.FTS.PhiStar.Series.contDiff_eFam m).differentiable (by norm_num)
      |>.differentiableAt
  have he1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (eFam m)) θ :=
    fun m _ => (ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.contDiff_eFam m)).differentiable
      (by norm_num) |>.differentiableAt
  have h2 : deriv (deriv (fun θ' => ∑ m ∈ s, a m * eFam m θ')) θ
      = ∑ m ∈ s, a m * deriv (deriv (eFam m)) θ := by
    have hf : deriv (fun θ' => ∑ m ∈ s, a m * eFam m θ')
        = fun θ' => ∑ m ∈ s, a m * deriv (eFam m) θ' := by
      funext θ'
      exact deriv_sum_const_mul s a (fun m => eFam m) θ' (fun m hm => he m hm θ')
    rw [hf]
    exact deriv_sum_const_mul s a (fun m => deriv (eFam m)) θ (fun m hm => he1 m hm)
  have h1 : deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * eFam m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eFam m θ') θ :=
    deriv_sum_tan_const_mul s a (fun m => eFam m) θ hθ (fun m hm => he m hm θ)
  have hL : Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eFam m θ') z θ
      = -(∑ m ∈ s, a m * deriv (deriv (eFam m)) θ)
        + (∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eFam m θ') θ)
        - 6 * (∑ m ∈ s, a m * eFam m θ) := by
    rw [lzero_indep]
    rw [h2, h1]
  have hLam : ∀ m ∈ s, deriv (fun θ' => Real.tan θ' * eFam m θ') θ
      - deriv (deriv (eFam m)) θ - 6 * eFam m θ = lam m * eFam m θ := by
    intro m _
    have h6 := lzero_indep (eFam m) z θ
    rw [eFam_Lzero m hθ z] at h6
    linarith [h6]
  rw [hL]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  calc -(a m * deriv (deriv (eFam m)) θ) + a m * deriv (fun θ' => Real.tan θ' * eFam m θ') θ
        - 6 * (a m * eFam m θ)
      = a m * (deriv (fun θ' => Real.tan θ' * eFam m θ') θ - deriv (deriv (eFam m)) θ
          - 6 * eFam m θ) := by ring
    _ = a m * (lam m * eFam m θ) := by rw [hLam m hm]
    _ = lam m * a m * eFam m θ := by ring

theorem lzero_finSum_eFam (a : ℕ → ℝ) (N : ℕ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero
        (fun _ θ' => ∑ m ∈ Finset.range (N + 1),
          a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  exact lzero_sum_indep a (Finset.range (N + 1)) z θ hθ

end Work.EllipticEst.ModalSolution.PairIdent
