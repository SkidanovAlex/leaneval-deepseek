/-
# `Work.EllipticEst.ModalSolution.PTBSupp` — finite-sum mode lemmas for `psiTrunc_tail_bound`

Supporting lemmas about finite sums of the angular modes `eFam m`, needed by
`Work.EllipticEst.ModalSolution.psiTrunc_tail_bound`:

* `finSum_bilin_gen` — bilinear Parseval for an arbitrary finite index set (the `Finset`-generic
  version of `PairIdent.eFam_finSum_bilin`, whose statement is specialised to
  `Finset.range (N+1)`);
* `lzero_finSum_gen` — `Lzero` acts diagonally on a finite sum of modes (the `Finset`-generic
  version of `PairIdent.lzero_finSum_eFam`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.PTBSupp

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "lamF" => Work.FTS.PhiStar.Gegenbauer.lam

/-! ## Elementary facts about the modes -/

private lemma continuous_eFam' (m : ℕ) : Continuous (eF m) := by
  have h : eF m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

private lemma integrableOn_eFam_mul' (m n : ℕ) :
    IntegrableOn (fun θ => eF m θ * eF n θ * Real.cos θ) Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((continuous_eFam' m).mul (continuous_eFam' n)).mul Real.continuous_cos).continuousOn

private lemma setIntegral_Iθ_eq_interval' (f : ℝ → ℝ) :
    (∫ θ in Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  show (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), f θ) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm

private lemma eFam_orth_Iθ' {m n : ℕ} (hmn : m ≠ n) :
    (∫ θ in Iθ, eF m θ * eF n θ * Real.cos θ) = 0 := by
  rw [setIntegral_Iθ_eq_interval']
  exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn

private lemma eFam_diag' (m : ℕ) :
    (∫ θ in Iθ, eF m θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

/-! ## Bilinear Parseval for a finite set of modes -/

/-- **Bilinear Parseval for a finite set of modes**: the `L²(Iθ, cos θ dθ)` pairing of two finite
mode sums collapses to the diagonal sum. -/
theorem finSum_bilin_gen (a b : ℕ → ℝ) (s : Finset ℕ) :
    (∫ θ in Iθ,
        (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ)
      = ∑ m ∈ s,
          (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * a m * b m := by
  have hpt : ∀ θ : ℝ, (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ
      = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (eF m θ * eF n θ * Real.cos θ) := by
    intro θ
    calc (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ
        = (∑ m ∈ s, (a m * eF m θ) * (∑ n ∈ s, b n * eF n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ((a m * eF m θ) * (∑ n ∈ s, b n * eF n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (eF m θ * eF n θ * Real.cos θ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  have hint : ∀ m ∈ s, ∀ n ∈ s,
      IntegrableOn (fun θ => (a m * b n) * (eF m θ * eF n θ * Real.cos θ)) Iθ :=
    fun m _ n _ => (integrableOn_eFam_mul' m n).const_mul (a m * b n)
  have h1 : (∫ θ in Iθ, (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ)
      = ∫ θ in Iθ, ∑ m ∈ s, ∑ n ∈ s,
          (a m * b n) * (eF m θ * eF n θ * Real.cos θ) :=
    integral_congr_ae (Eventually.of_forall hpt)
  rw [h1]
  rw [MeasureTheory.integral_finset_sum s
    (fun m hm => MeasureTheory.integrable_finset_sum s (fun n hn => hint m hm n hn))]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finset_sum s (fun n hn => hint m hm n hn)]
  have hkey : (∑ n ∈ s, (a m * b n) * (∫ θ in Iθ, eF m θ * eF n θ * Real.cos θ))
      = (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * a m * b m := by
    have hsingle := Finset.sum_eq_single (s := s)
      (f := fun n => (a m * b n) * (∫ θ in Iθ, eF m θ * eF n θ * Real.cos θ)) m
      (fun n _ hnm => by rw [eFam_orth_Iθ' (Ne.symm hnm), mul_zero])
      (fun hms => absurd hm hms)
    rw [hsingle, eFam_diag' m]
    ring
  rw [Finset.sum_congr rfl (fun n _ => by rw [MeasureTheory.integral_const_mul])]
  exact hkey

/-! ## The action of `Lzero` on a finite sum of modes -/

private lemma lzero_indep' (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -(deriv (deriv f) θ) + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

private lemma deriv_sum_const_mul' (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => ∑ m ∈ s, a m * e m θ') θ = ∑ m ∈ s, a m * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, a m * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => a m * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (a m))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (a m) (he m hm)

private lemma deriv_sum_tan_const_mul' (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
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

/-- **`Lzero` acts diagonally on a finite sum of modes**: for `cos θ ≠ 0` the modes are
eigenfunctions with eigenvalue `lam m = 2m(2m+5)`. -/
theorem lzero_finSum_gen (a : ℕ → ℝ) (s : Finset ℕ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eF m θ') z θ
      = ∑ m ∈ s, lamF m * a m * eF m θ := by
  have he : ∀ m ∈ s, ∀ θ' : ℝ, DifferentiableAt ℝ (eF m) θ' :=
    fun m _ θ' => (Work.FTS.PhiStar.Series.contDiff_eFam m).differentiable (by norm_num)
      |>.differentiableAt
  have he1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (eF m)) θ :=
    fun m _ => (ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.contDiff_eFam m)).differentiable
      (by norm_num) |>.differentiableAt
  have h2 : deriv (deriv (fun θ' => ∑ m ∈ s, a m * eF m θ')) θ
      = ∑ m ∈ s, a m * deriv (deriv (eF m)) θ := by
    have hf : deriv (fun θ' => ∑ m ∈ s, a m * eF m θ')
        = fun θ' => ∑ m ∈ s, a m * deriv (eF m) θ' := by
      funext θ'
      exact deriv_sum_const_mul' s a (fun m => eF m) θ' (fun m hm => he m hm θ')
    rw [hf]
    exact deriv_sum_const_mul' s a (fun m => deriv (eF m)) θ (fun m hm => he1 m hm)
  have h1 : deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * eF m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eF m θ') θ :=
    deriv_sum_tan_const_mul' s a (fun m => eF m) θ hθ (fun m hm => he m hm θ)
  have hL : Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eF m θ') z θ
      = -(∑ m ∈ s, a m * deriv (deriv (eF m)) θ)
        + (∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eF m θ') θ)
        - 6 * (∑ m ∈ s, a m * eF m θ) := by
    rw [lzero_indep']
    rw [h2, h1]
  have hLam : ∀ m ∈ s, deriv (fun θ' => Real.tan θ' * eF m θ') θ
      - deriv (deriv (eF m)) θ - 6 * eF m θ = lamF m * eF m θ := by
    intro m _
    have h6 := lzero_indep' (eF m) z θ
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z] at h6
    linarith [h6]
  rw [hL]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  calc -(a m * deriv (deriv (eF m)) θ) + a m * deriv (fun θ' => Real.tan θ' * eF m θ') θ
        - 6 * (a m * eF m θ)
      = a m * (deriv (fun θ' => Real.tan θ' * eF m θ') θ - deriv (deriv (eF m)) θ
          - 6 * eF m θ) := by ring
    _ = a m * (lamF m * eF m θ) := by rw [hLam m hm]
    _ = lamF m * a m * eF m θ := by ring

end Work.EllipticEst.ModalSolution.PTBSupp
