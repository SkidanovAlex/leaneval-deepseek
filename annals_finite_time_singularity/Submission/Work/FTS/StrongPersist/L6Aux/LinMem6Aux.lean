/-
# `Work.FTS.StrongPersist.L6Aux.LinMem6Aux` — helpers for the `ℋ⁶`-membership of `-𝓛_Γ^T f`

Smoothness helpers for the open quadrant, the angular majorant `Mth6` of the nonlocal term
(together with its integrability), the radial slot sum `SlotSum` of a `z`-only profile, and the
finite-smoothness multiplier estimate `zmul_finite6` at level six.  Consumers:
`L6Aux.LinMem6LocOp`, `L6Aux.LinMem6Acf` and `H6LinMem6`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3_lin_mem
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.Coercivity.dthIterAng_sq_integrable
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §0 Local smoothness helpers for the open quadrant -/

theorem linMem_neg {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg ⊢
  have hfun : Function.uncurry (fun z θ => -g z θ)
      = fun p : ℝ × ℝ => -(Function.uncurry g p) := rfl
  rw [hfun]
  exact hg.neg

theorem linMem_const_mul (c : ℝ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg ⊢
  have hfun : Function.uncurry (fun z θ => c * g z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry g p := rfl
  rw [hfun]
  exact contDiffOn_const.mul hg

theorem linMem_mul {g h : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z θ * h z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg hh ⊢
  have hfun : Function.uncurry (fun z θ => g z θ * h z θ)
      = fun p : ℝ × ℝ => Function.uncurry g p * Function.uncurry h p := rfl
  rw [hfun]
  exact hg.mul hh

theorem linMem_radial {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => φ z) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have hfst : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiff_fst.contDiffOn
  exact hφ.comp hfst (fun p hp => by
    have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    exact show (-1 : ℝ) < p.1 from by linarith)

theorem linMem_two_div (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => 2 / (1 + z)) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ m (fun z : ℝ => 1 + z) (Set.Ioi (-1)) :=
    contDiffOn_const.add contDiffOn_id
  exact (contDiffOn_const (c := (2 : ℝ))).div hden (fun z hz => by
    simp only [Set.mem_Ioi] at hz
    exact ne_of_gt (by linarith))

theorem linMem_two_div_smooth :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 / (1 + z)) (Set.Ioi (-1)) :=
  contDiffOn_iff_forall_nat_le.mpr (fun m _ => linMem_two_div m)

/-- `2x/d = (2/3)·((3/d)·x)`: the two ways of writing the `2/(1+z)`-coefficient, used to reach
the delegated jet bound for `z ↦ 3/(1+z)`. -/
theorem linMem_two_mul_div_eq (x d : ℝ) : 2 * x / d = (2 / 3) * ((3 / d) * x) := by
  rcases eq_or_ne d 0 with h | h
  · rw [h]; simp
  · field_simp

/-! ## §1 The angular majorant of the nonlocal term -/

/-- The angular majorant `Mth6 α` of the level-six nonlocal summand: the `η`-weighted square of
the separated coefficient `gamCoef α = Γ(θ)/c(α)` plus the `γ`-weighted squares of its angular
jets up to order six. -/
def Mth6 (α : ℝ) : ℝ → ℝ := fun θ =>
  (gamCoef α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 7,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] (gamCoef α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The radial slot sum of a `z`-only profile: the sum of the weighted squares of its `D_z`-
iterates up to order six. -/
def SlotSum (B : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 7,
    (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2

/-- `dthU^[i]` commutes with multiplication by a constant. -/
theorem dthU_iter_const_mul (c : ℝ) (v : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.dthU^[i] (fun θ => c * v θ) = fun θ => c * Work.Spaces.dthU^[i] v θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        Work.Spaces.dthU_const_mul]

/-- `gamCoef α = c(α)⁻¹·Γ`. -/
theorem gamCoef_eq_inv_mul (α : ℝ) :
    gamCoef α = fun θ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α θ := by
  funext θ
  rw [gamCoef]
  ring

/-- **The angular majorant is integrable.**  The `η`-term is the `η`-mass of `Γ/c` of
`L3Aux.GamJetBounds`; the `γ`-terms are the `c⁻²`-multiples of the all-order masses
`Coercivity.dthIterAng_sq_integrable`. -/
theorem Mth6_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (Mth6 α) Work.Spaces.Iθ := by
  obtain ⟨_, _, _, hη, _⟩ := Work.FTS.StrongPersist.L3Aux.GamJetBounds
  obtain ⟨hγint, -⟩ := Work.Coercivity.dthIterAng_sq_integrable α hα hα1
  refine (hη α hα hα1).1.add ?_
  refine MeasureTheory.integrable_finset_sum (Finset.range 7) (fun i hi => ?_)
  by_cases hi1 : 1 ≤ i
  · simp only [if_pos hi1]
    have hfun : (fun θ : ℝ => (Work.Spaces.dthU^[i] (gamCoef α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = fun θ : ℝ => ((Work.Spaces.c α)⁻¹) ^ 2
            * ((Work.Coercivity.CT.DthIterAng i (Work.Spaces.Gam α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      funext θ
      rw [gamCoef_eq_inv_mul, dthU_iter_const_mul, ← Work.Coercivity.CT.DthIterAng_eq_iterate]
      ring
    rw [hfun]
    exact (hγint i).const_mul _
  · simp only [if_neg hi1]
    exact integrableOn_zero

/-- The angular majorant is nonnegative on `Iθ`. -/
theorem Mth6_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Mth6 α θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Elliptic.sin_two_nonneg_of_mem hθ
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : 1 ≤ i
  · simp only [if_pos hi]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  · simp only [if_neg hi]
    exact le_refl 0

/-- The radial slot sum is nonnegative. -/
theorem SlotSum_nonneg (B : ℝ → ℝ) (z : ℝ) : 0 ≤ SlotSum B z :=
  Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## §2 The finite-smoothness multiplier estimate at level six -/

/-- **The multiplier estimate at level six, for data which are only `C⁶` on the open
half-line.**  This is `L3Aux.zmul_quad` with the `SmoothOpen` hypothesis on `g` replaced by the
finite smoothness which the Leibniz expansions of `zmul_pt` actually need (the situation of
`g = gamCoef α · L₁₂(f)`, whose `z`-slices are only `C⁶`). -/
theorem zmul_finite6 (α : ℝ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hφ : ∀ (b : ℕ), b ≤ 6 → ContDiffOn ℝ b φ (Set.Ioi (0 : ℝ)))
    (hg : ∀ (i : ℕ), i ≤ 6 → ∀ θ : ℝ, ContDiffOn ℝ i (fun z => g z θ) (Set.Ioi (0 : ℝ)))
    (hgθ : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i g z θ) (Set.Ioi (0 : ℝ))) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => φ z * g z θ) z θ
        ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2
            * Work.Spaces.HkIntegrand α 6 g z θ := by
  intro z hz θ hθ
  have hCnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 6 * (1 + K) ^ 2 :=
    mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 6).le (sq_nonneg _)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
  · subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst]
    exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ)
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 (fun z θ => φ z * g z θ) z θ hs]
    exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
  · have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases lt_or_eq_of_le hθ.1 with h | h
        · exact h
        · exact absurd (by rw [← h]; simp) hs
      · rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · refine absurd ?_ hs
          rw [h]
          have hpi : 2 * (Real.pi / 2) = Real.pi := by ring
          rw [hpi, Real.sin_pi]
    exact Work.FTS.StrongPersist.L3Aux.zmul_pt α 6 φ g hK (fun b hb => hB b hb z hzpos)
      (fun i hi => Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ g isOpen_Ioi
        (hφ i hi) (hg i hi θ) z hzpos)
      (fun j i hi hij => Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ g isOpen_Ioi
        (hφ j (by omega)) (hgθ j i hi hij θ) z hzpos)

theorem linMem_zmul_joint {n : ℕ} {φ : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hφ : ContDiffOn ℝ n φ (Set.Ioi (0 : ℝ)))
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => φ z * g z θ)) Work.FTS.EllipticEst.Q0 := by
  have hfst : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 :=
    contDiff_fst.contDiffOn
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => φ p.1) Work.FTS.EllipticEst.Q0 :=
    hφ.comp hfst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfun : Function.uncurry (fun z θ => φ z * g z θ)
      = fun p : ℝ × ℝ => φ p.1 * Function.uncurry g p := rfl
  rw [hfun]
  exact h1.mul hg


end Work.FTS.StrongPersist
