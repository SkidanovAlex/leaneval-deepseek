import Mathlib
import Submission.Work.KMTAreas.A7.lacBumpDecimation
import Submission.Work.KMTAreas.A7.lacBumpKernel
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.A7.lacunaryDiffSymbol_mikhlin

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

open Work.KMTContract

/-- Per-term identity at the bottom scale. -/
lemma varphiNt_zero_sub_varphiN (N : ℕ) (t ξ : ℝ) :
    varphiNt N 0 t ξ - varphiN N 0 ξ
      = kmtEta (lacσ N 0 * ξ) * (ee ((N : ℝ) * t * ξ) - 1) := by
  rw [lacσ_eq]
  simp only [varphiNt, varphiN, if_true]
  push_cast
  ring_nf

/-- `lacσ m 0` is the power of two `2 ^ (Log m)`, and `m ≤ 2 * 2 ^ (Log m)`. -/
lemma le_two_mul_lacσ (m : ℕ) : (m : ℝ) ≤ 2 * lacσ m 0 := by
  have hlog : lacσ m 0 = (2 : ℝ) ^ (Nat.log 2 (max m 2)) := by
    have hexp : (Work.Analysis.EndVar.logN m : ℤ) - ((0 : ℕ) : ℤ)
        = (Nat.log 2 (max m 2) : ℤ) := by
      rw [Work.Analysis.EndVar.logN]
      norm_num
    rw [lacσ, hexp, zpow_natCast]
  rw [hlog]
  have h2 : max m 2 < 2 ^ (Nat.log 2 (max m 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hcast : (max m 2 : ℝ) < (2 : ℝ) ^ (Nat.log 2 (max m 2) + 1) := by
    exact_mod_cast h2
  have hpow : (2 : ℝ) ^ (Nat.log 2 (max m 2) + 1)
      = 2 * (2 : ℝ) ^ (Nat.log 2 (max m 2)) := by
    rw [pow_succ]; ring
  have hm : (m : ℝ) ≤ (max m 2 : ℝ) := by
    exact_mod_cast le_max_left m 2
  rw [hpow] at hcast
  linarith

/-- `ee (u * ξ)` in the `Complex.exp` normal form. -/
lemma ee_mul (u ξ : ℝ) :
    ee (u * ξ) = Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (ξ : ℂ))) := by
  have h1 : ((u * ξ : ℝ) : ℂ) = (u : ℂ) * (ξ : ℂ) := by push_cast; ring
  simp only [ee, h1]

/-- The Mikhlin multiplier operator as an explicit integral. -/
lemma contMulOp_eq_integral (m : ℝ → ℂ) (G : SchwartzMap ℝ ℂ) (x : ℝ) :
    Work.Analysis.IWMultiplier.contMulOp m (G : ℝ → ℂ) x
      = ∫ ξ : ℝ, (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • (FourierTransform.fourier (G : ℝ → ℂ) ξ) := by
  rw [Work.Analysis.IWMultiplier.contMulOp, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [smul_eq_mul]
  have hexp : (↑(2 * Real.pi * inner ℝ v x) * Complex.I : ℂ)
      = 2 * Real.pi * Complex.I * (x * v) := by
    rw [Real.inner_apply]
    push_cast
    ring
  rw [hexp]
  ring

theorem lacunaryBump_mult_bound_k0_diff (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1),
        Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal p)
          (fun ξ : ℝ => ∑ n ∈ U, ε n *
            (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)) C := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp p hp
  obtain ⟨M, hMpos, hMlac⟩ := lacBumpDecimation Λ hΛ
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hηcd, hη0, hη1, hη2, hηs0, hηs1, hηs2, hηd, hηd2⟩ :=
    kmtEta_deriv_bounds
  obtain ⟨A, hApos, hA⟩ := lacunaryDiffSymbol_mikhlin kmtEta M0 M1 M2 hM0 hM1 hM2 hηcd hη0
    hη1 hη2 hηs0 hηs1 hηs2 hηd hηd2 2 (by norm_num)
  have hCnpos : (0 : ℝ) < (M : ℝ) * (Cm * A) := by positivity
  refine ⟨⟨(M : ℝ) * (Cm * A), le_of_lt hCnpos⟩, hCnpos, ?_⟩
  intro t ht a ha ha1 U ε hε f
  let ρ : ℕ → ℝ := fun n => lacσ (Nat.floor (a n)) 0
  let c : ℕ → ℝ := fun n => (Nat.floor (a n) : ℝ) * t
  have hsym : (fun ξ : ℝ => ∑ n ∈ U, ε n * (varphiNt (Nat.floor (a n)) 0 t ξ
        - varphiN (Nat.floor (a n)) 0 ξ))
      = fun ξ : ℝ => ∑ n ∈ U, ε n * (kmtEta (ρ n * ξ)
          * (Complex.exp (2 * Real.pi * Complex.I * (c n * ξ)) - 1)) := by
    funext ξ
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [varphiNt_zero_sub_varphiN, ee_mul]
  rw [hsym]
  let fib : ℕ → ℝ → ℂ := fun r ξ => ∑ n ∈ U.filter (fun n => n % M = r), ε n *
      (kmtEta (ρ n * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c n * ξ)) - 1))
  have hΦeq : (fun ξ : ℝ => ∑ n ∈ U, ε n * (kmtEta (ρ n * ξ)
        * (Complex.exp (2 * Real.pi * Complex.I * (c n * ξ)) - 1)))
      = fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ := by
    funext ξ
    simp only [fib]
    exact (Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range M) (g := fun n => n % M)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hMpos))
      (fun n => ε n * (kmtEta (ρ n * ξ)
        * (Complex.exp (2 * Real.pi * Complex.I * (c n * ξ)) - 1)))).symm
  rw [hΦeq]
  have hfib : ∀ r ∈ Finset.range M, ContDiff ℝ 2 (fib r) ∧ (∀ ξ : ℝ, ‖fib r ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| * ‖deriv (fib r) ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fib r) ξ‖ ≤ A) := by
    intro r hr
    have hlac : Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r)) ρ :=
      hMlac 0 a ha ha1 U r
    have hcb : ∀ i ∈ U.filter (fun n => n % M = r), |c i| ≤ 2 * ρ i := by
      intro i hi
      have hle : (Nat.floor (a i) : ℝ) ≤ 2 * lacσ (Nat.floor (a i)) 0 :=
        le_two_mul_lacσ (Nat.floor (a i))
      have htle : t ≤ 1 := ht.2
      have hci : c i = (Nat.floor (a i) : ℝ) * t := rfl
      have ht0 : 0 ≤ t := by linarith [ht.1]
      rw [hci, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ht0)]
      calc (Nat.floor (a i) : ℝ) * t ≤ (Nat.floor (a i) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left htle (Nat.cast_nonneg _)
        _ = (Nat.floor (a i) : ℝ) := mul_one _
        _ ≤ 2 * ρ i := by simpa only [ρ] using hle
    have heps : ∀ i ∈ U.filter (fun n => n % M = r), ‖ε i‖ ≤ 1 := fun i _ => hε i
    have hh := hA (U.filter (fun n => n % M = r)) ρ c ε hlac hcb heps
    simpa only [fib] using hh
  have hMA : (0 : ℝ) ≤ (M : ℝ) * A := by positivity
  have hcd : ContDiff ℝ 2 (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) :=
    ContDiff.sum (fun r hr => (hfib r hr).1)
  have hsup : ∀ ξ : ℝ, ‖∑ r ∈ Finset.range M, fib r ξ‖ ≤ (M : ℝ) * A := by
    intro ξ
    calc ‖∑ r ∈ Finset.range M, fib r ξ‖ ≤ ∑ r ∈ Finset.range M, ‖fib r ξ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.range M, A := Finset.sum_le_sum (fun r hr => (hfib r hr).2.1 ξ)
      _ = (M : ℝ) * A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hd1 : ∀ ξ : ℝ, |ξ| * ‖deriv (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) ξ‖
      ≤ (M : ℝ) * A := by
    intro ξ
    have hdiff : ∀ r ∈ Finset.range M, DifferentiableAt ℝ (fib r) ξ :=
      fun r hr => (((hfib r hr).1).differentiable (by norm_num)).differentiableAt
    have hsumfun : (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ)
        = ∑ r ∈ Finset.range M, fib r := by
      funext ξ; simp only [Finset.sum_apply]
    rw [hsumfun, deriv_sum hdiff]
    calc |ξ| * ‖∑ r ∈ Finset.range M, deriv (fib r) ξ‖
        ≤ |ξ| * ∑ r ∈ Finset.range M, ‖deriv (fib r) ξ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg ξ)
      _ = ∑ r ∈ Finset.range M, |ξ| * ‖deriv (fib r) ξ‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ r ∈ Finset.range M, A := Finset.sum_le_sum (fun r hr => (hfib r hr).2.2.1 ξ)
      _ = (M : ℝ) * A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hd2 : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) ξ‖
      ≤ (M : ℝ) * A := by
    intro ξ
    have hcdat : ∀ r ∈ Finset.range M, ContDiffAt ℝ 2 (fib r) ξ :=
      fun r hr => ((hfib r hr).1).contDiffAt
    have hsumfun : (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ)
        = ∑ r ∈ Finset.range M, fib r := by
      funext ξ; simp only [Finset.sum_apply]
    rw [hsumfun, iteratedDeriv_sum hcdat]
    calc |ξ| ^ 2 * ‖∑ r ∈ Finset.range M, iteratedDeriv 2 (fib r) ξ‖
        ≤ |ξ| ^ 2 * ∑ r ∈ Finset.range M, ‖iteratedDeriv 2 (fib r) ξ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ r ∈ Finset.range M, |ξ| ^ 2 * ‖iteratedDeriv 2 (fib r) ξ‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ r ∈ Finset.range M, A := Finset.sum_le_sum (fun r hr => (hfib r hr).2.2.2 ξ)
      _ = (M : ℝ) * A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain := hCm (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) ((M : ℝ) * A) hMA hcd hsup hd1 hd2 f
  have hbridge : Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ)
      (f : ℝ → ℂ)
      = fun x : ℝ => ∫ ξ : ℝ, ((∑ r ∈ Finset.range M, fib r ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • (FourierTransform.fourier (f : ℝ → ℂ) ξ) := by
    funext x
    exact contMulOp_eq_integral _ f x
  rw [hbridge]
  calc MeasureTheory.eLpNorm (fun x : ℝ => ∫ ξ : ℝ, ((∑ r ∈ Finset.range M, fib r ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • (FourierTransform.fourier (f : ℝ → ℂ) ξ))
        (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal (Cm * ((M : ℝ) * A))
          * MeasureTheory.eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume := hmain
    _ = ENNReal.ofReal ((M : ℝ) * (Cm * A))
          * MeasureTheory.eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume := by
        rw [show Cm * ((M : ℝ) * A) = (M : ℝ) * (Cm * A) by ring]

end Work.KMTAreas.A7
