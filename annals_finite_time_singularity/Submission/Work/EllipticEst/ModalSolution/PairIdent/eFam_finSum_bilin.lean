import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.PairIdent

local notation "e" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about the modes `eFam m` needed for the bilinear expansion -/

/-- `eFam m` is continuous (it is `cos θ · gC (2m+1) (sin θ)`). -/
private lemma continuous_eFam (m : ℕ) : Continuous (e m) := by
  have h : e m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

/-- `e m θ · e n θ · cos θ` is integrable on `Iθ` (continuous on a compact interval). -/
private lemma integrableOn_eFam_mul (m n : ℕ) :
    IntegrableOn (fun θ => e m θ * e n θ * Real.cos θ) Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((continuous_eFam m).mul (continuous_eFam n)).mul Real.continuous_cos).continuousOn

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `(0, π/2)`; the two
differ only at the (`volume`-null) endpoint `θ = 0`. -/
private lemma setIntegral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  show (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), f θ) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm

/-- Orthogonality of the modes, in the set-integral form over `Iθ` used below. -/
private lemma eFam_orth_Iθ {m n : ℕ} (hmn : m ≠ n) :
    (∫ θ in Iθ, e m θ * e n θ * Real.cos θ) = 0 := by
  rw [setIntegral_Iθ_eq_interval]
  exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn

/-- The diagonal entry of the Gram matrix, with the square written as `e m θ ^ 2`. -/
private lemma eFam_diag (m : ℕ) :
    (∫ θ in Iθ, e m θ * e m θ * Real.cos θ)
      = ∫ θ in Iθ, e m θ ^ 2 * Real.cos θ := by
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

/-! ## The bilinear identity -/

/-- **Bilinearity of the `L²(Iθ, cos θ dθ)` pairing of two finite mode sums.**  Since the modes
`eFam m` are mutually orthogonal with respect to the weight `cos θ`, the pairing of the two
partial sums `∑_{m ≤ N} a m · e_m` and `∑_{m ≤ N} b m · e_m` collapses to the diagonal sum
`∑_{m ≤ N} (∫ e_m² cos) · a m · b m`. -/
theorem eFam_finSum_bilin (a b : ℕ → ℝ) (N : ℕ) :
    (∫ θ in Work.Spaces.Iθ,
        (∑ m ∈ Finset.range (N + 1), a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1),
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
            * a m * b m := by
  set s : Finset ℕ := Finset.range (N + 1) with hs
  -- Step 1: expand the product of the two finite sums into a double sum.
  have hpt : ∀ θ : ℝ, (∑ m ∈ s, a m * e m θ) * (∑ m ∈ s, b m * e m θ) * Real.cos θ
      = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (e m θ * e n θ * Real.cos θ) := by
    intro θ
    calc (∑ m ∈ s, a m * e m θ) * (∑ m ∈ s, b m * e m θ) * Real.cos θ
        = (∑ m ∈ s, (a m * e m θ) * (∑ n ∈ s, b n * e n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ((a m * e m θ) * (∑ n ∈ s, b n * e n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (e m θ * e n θ * Real.cos θ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  -- Step 2: integrate the double sum term by term.
  have hint : ∀ m ∈ s, ∀ n ∈ s,
      IntegrableOn (fun θ => (a m * b n) * (e m θ * e n θ * Real.cos θ)) Iθ :=
    fun m _ n _ => (integrableOn_eFam_mul m n).const_mul (a m * b n)
  have h1 : (∫ θ in Iθ, (∑ m ∈ s, a m * e m θ) * (∑ m ∈ s, b m * e m θ) * Real.cos θ)
      = ∫ θ in Iθ, ∑ m ∈ s, ∑ n ∈ s,
          (a m * b n) * (e m θ * e n θ * Real.cos θ) :=
    integral_congr_ae (Eventually.of_forall hpt)
  rw [h1]
  rw [MeasureTheory.integral_finset_sum s
    (fun m hm => MeasureTheory.integrable_finset_sum s (fun n hn => hint m hm n hn))]
  -- Step 3: pull out the constants and collapse each inner sum to its diagonal term.
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finset_sum s (fun n hn => hint m hm n hn)]
  have hkey : (∑ n ∈ s, (a m * b n) * (∫ θ in Iθ, e m θ * e n θ * Real.cos θ))
      = (∫ θ in Iθ, e m θ ^ 2 * Real.cos θ) * a m * b m := by
    have hsingle := Finset.sum_eq_single (s := s)
      (f := fun n => (a m * b n) * (∫ θ in Iθ, e m θ * e n θ * Real.cos θ)) m
      (fun n _ hnm => by rw [eFam_orth_Iθ (Ne.symm hnm), mul_zero])
      (fun hms => absurd hm hms)
    rw [hsingle, eFam_diag m]
    ring
  rw [Finset.sum_congr rfl (fun n _ => by rw [MeasureTheory.integral_const_mul])]
  exact hkey

end Work.EllipticEst.ModalSolution.PairIdent
