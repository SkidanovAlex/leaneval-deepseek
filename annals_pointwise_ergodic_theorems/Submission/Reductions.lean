import ChallengeDeps
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Basic
import Submission.Variational
import Submission.Commons.Analysis.Real.strictMono_floor_mul_geom
import Submission.Commons.Analysis.Real.floor_mul_geom_ratio
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
import Submission.Commons.MeasureTheory.Lp.exists_bounded_tendsto_eLpNorm
import Submission.Commons.Analysis.ErgodicPrinciple.ae_cauchy_of_approx
import Submission.Commons.MeasureTheory.Lp.tendsto_eLpNorm_of_ae_tendsto_of_bound
import Submission.Port.Aesm

/-!
# Reductions towards Theorem 1.17

Following Krause--Mirek--Tao, Proposition 3.1, the long variational estimate (Theorem 1.17(iv))
implies the maximal estimate (iii), the pointwise convergence (ii) and the mean convergence (i).
This file builds that reduction for the specific definitions of the challenge.
-/

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- `Ab` is nonnegative for nonnegative `f`, `g`. -/
lemma Ab_nonneg (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) {f g : 𝓧 → ℝ}
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (x : 𝓧) : 0 ≤ Ab T N P₁ P₂ f g x :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun n _ => mul_nonneg (hf _) (hg _)))

/-- The `enorm` of the averaged absolute values is the `ofReal` of `Ab`. -/
lemma enorm_A_ofReal_eq (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) {f g : 𝓧 → ℝ}
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (x : 𝓧) :
    ‖A T N P₁ P₂ (fun y => (f y : ℂ)) (fun y => (g y : ℂ)) x‖ₑ
      = ENNReal.ofReal (Ab T N P₁ P₂ f g x) := by
  rw [A_ofReal, ← ofReal_norm, Complex.norm_of_nonneg (Ab_nonneg T N P₁ P₂ hf hg x)]

/-- At any scale, the average of nonnegative `f`, `g` is dominated by twice the supremum of the
dyadic averages. -/
lemma ofReal_Ab_le_two_dyadic (T : 𝓧 ≃ᵐ 𝓧) (P₁ P₂ : ℤ[X]) {f g : 𝓧 → ℝ}
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (N : ℕ+) (x : 𝓧) :
    ENNReal.ofReal (Ab T (N : ℝ≥0) P₁ P₂ f g x)
      ≤ 2 * ⨆ k : ℕ, ENNReal.ofReal (Ab T ((2 : ℝ≥0) ^ k) P₁ P₂ f g x) := by
  set K : ℕ := Nat.log2 (N : ℕ) with hK
  set D : ℕ := 2 ^ (K + 1) with hD
  have hK1 : 2 ^ K ≤ (N : ℕ) := by
    rw [hK, Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 (by exact_mod_cast N.pos.ne')
  have hK2 : (N : ℕ) < D := by
    rw [hD, hK, Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hNf : Nat.floor ((N : ℕ) : ℝ≥0) = (N : ℕ) := Nat.floor_natCast _
  have hDf : Nat.floor ((D : ℕ) : ℝ≥0) = D := Nat.floor_natCast _
  have hsum : (∑ n ∈ Icc 1 (N : ℕ), f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
        * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))
      ≤ ∑ n ∈ Icc 1 D, f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
        * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hK2.le)
      (fun n _ _ => mul_nonneg (hf _) (hg _))
  have hmain : Ab T (N : ℝ≥0) P₁ P₂ f g x ≤ 2 * Ab T (D : ℝ≥0) P₁ P₂ f g x := by
    simp only [Ab, hNf, hDf]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    have hratio : (D : ℝ) / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      have hle : (D : ℝ) ≤ 2 * (N : ℝ) := by
        have : D ≤ 2 * (N : ℕ) := by
          rw [hD]
          calc 2 ^ (K + 1) = 2 * 2 ^ K := by ring
            _ ≤ 2 * N := Nat.mul_le_mul_left 2 hK1
        exact_mod_cast this
      linarith
    calc (N : ℝ)⁻¹ * (∑ n ∈ Icc 1 (N : ℕ), f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
          * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))
        ≤ (N : ℝ)⁻¹ * (∑ n ∈ Icc 1 D, f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
          * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)) := by
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
      _ = ((D : ℝ) / (N : ℝ)) * ((D : ℝ)⁻¹ * (∑ n ∈ Icc 1 D,
            f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
              * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))) := by
          field_simp
      _ ≤ 2 * ((D : ℝ)⁻¹ * (∑ n ∈ Icc 1 D, f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)
              * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))) :=
          mul_le_mul_of_nonneg_right hratio (by
            exact mul_nonneg (inv_nonneg.mpr hDpos.le)
              (Finset.sum_nonneg (fun n _ => mul_nonneg (hf _) (hg _))))
  calc ENNReal.ofReal (Ab T (N : ℝ≥0) P₁ P₂ f g x)
      ≤ ENNReal.ofReal (2 * Ab T (D : ℝ≥0) P₁ P₂ f g x) := ENNReal.ofReal_le_ofReal hmain
    _ = 2 * ENNReal.ofReal (Ab T (D : ℝ≥0) P₁ P₂ f g x) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ ≤ 2 * ⨆ k : ℕ, ENNReal.ofReal (Ab T ((2 : ℝ≥0) ^ k) P₁ P₂ f g x) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ≥0∞) ≤ 2)
        have hcast : ((D : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ (K + 1) := by
          rw [hD]; push_cast; ring
        rw [hcast]
        exact le_iSup (fun k : ℕ => ENNReal.ofReal (Ab T ((2 : ℝ≥0) ^ k) P₁ P₂ f g x)) (K + 1)

/-! ### The lacunary scale sequences `s (1 + 1/s)^n` -/

/-- The lacunary scale sequence `n ↦ s (1 + 1/s)^n` (used to instantiate the variational estimate
at arbitrarily fine lacunarity). -/
noncomputable def geomScale (s : ℕ) : ℕ → ℝ≥0 := fun n => (s : ℝ≥0) * (1 + (s : ℝ≥0)⁻¹) ^ n

/-- The integer index associated to the scale `s (1 + 1/s)^n`. -/
noncomputable def geomIdx (s : ℕ) (n : ℕ) : ℕ := ⌊geomScale s n⌋₊

lemma geomScale_cast (s n : ℕ) :
    ((geomScale s n : ℝ≥0) : ℝ) = (s : ℝ) * (1 + (s : ℝ)⁻¹) ^ n := by
  simp [geomScale]

lemma geomIdx_eq (s n : ℕ) : geomIdx s n = Nat.floor ((s : ℝ) * (1 + (s : ℝ)⁻¹) ^ n) := by
  have h : ((geomScale s n : ℝ≥0) : ℝ) = (s : ℝ) * (1 + (s : ℝ)⁻¹) ^ n := by simp [geomScale]
  rw [geomIdx, ← h]
  rfl

lemma geomIdx_zero (s : ℕ) : geomIdx s 0 = s := by
  rw [geomIdx_eq]; simp

lemma geomIdx_strictMono (s : ℕ) (hs : 1 ≤ s) : StrictMono (geomIdx s) := by
  intro a b hab
  rw [geomIdx_eq, geomIdx_eq]
  exact Commons.Analysis.Real.strictMono_floor_mul_geom s hs hab

lemma geomIdx_ratio (s n : ℕ) (hs : 1 ≤ s) :
    (geomIdx s (n + 1) : ℝ) ≤ (1 + 3 / (s : ℝ)) * (geomIdx s n : ℝ) := by
  rw [geomIdx_eq, geomIdx_eq]
  exact Commons.Analysis.Real.floor_mul_geom_ratio s n hs

/-- For every `k ≥ s` there is a scale index `n` whose integer index lies between `k` and
`(1 + 3/s) k`. -/
lemma exists_geomIdx_between (s k : ℕ) (hs : 1 ≤ s) (hk : s ≤ k) :
    ∃ n : ℕ, k ≤ geomIdx s n ∧ (geomIdx s n : ℝ) ≤ (1 + 3 / (s : ℝ)) * (k : ℝ) := by
  have hmono := geomIdx_strictMono s hs
  have hex : ∃ n, k ≤ geomIdx s n := ⟨k, hmono.id_le k⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, geomIdx_zero]
    have h0' : (0 : ℝ) ≤ 3 / (s : ℝ) := by positivity
    nlinarith [show (s : ℝ) ≤ (k : ℝ) by exact_mod_cast hk]
  · have hmin : geomIdx s (Nat.find hex - 1) < k := by
      have hlt : Nat.find hex - 1 < Nat.find hex := by omega
      by_contra hc
      push Not at hc
      exact Nat.find_min hex hlt hc
    have hstep := geomIdx_ratio s (Nat.find hex - 1) hs
    rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] at hstep
    have hk' : (geomIdx s (Nat.find hex - 1) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmin.le
    have h3 : (0 : ℝ) ≤ 1 + 3 / (s : ℝ) := by positivity
    nlinarith

lemma geomScale_one_le (s : ℕ) (hs : 1 ≤ s) (n : ℕ) : 1 ≤ geomScale s n := by
  have h1 : (1 : ℝ≥0) ≤ 1 + (s : ℝ≥0)⁻¹ := le_add_of_nonneg_right (by positivity)
  calc (1 : ℝ≥0) = 1 ^ n := (one_pow n).symm
    _ ≤ (1 + (s : ℝ≥0)⁻¹) ^ n := pow_le_pow_left' h1 n
    _ = (1 : ℝ≥0) * (1 + (s : ℝ≥0)⁻¹) ^ n := (one_mul _).symm
    _ ≤ (s : ℝ≥0) * (1 + (s : ℝ≥0)⁻¹) ^ n := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by positivity)

lemma lacunary_geomScale (s : ℕ) (hs : 1 ≤ s) :
    Lacunary (1 + (2 * (s : ℝ≥0))⁻¹) (geomScale s) := by
  intro n
  have hs0 : (s : ℝ≥0) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hscale : geomScale s (n + 1) = (1 + (s : ℝ≥0)⁻¹) * geomScale s n := by
    simp only [geomScale, pow_succ]; ring
  have hne : geomScale s n ≠ 0 := by
    simp only [geomScale]
    exact mul_ne_zero hs0 (pow_ne_zero _ (by positivity))
  rw [hscale, mul_div_assoc, div_self hne, mul_one]
  have h : (2 * (s : ℝ≥0))⁻¹ < (s : ℝ≥0)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    have h1 : (1 : ℝ≥0) ≤ s := by exact_mod_cast hs
    linarith
  linarith

/-! ### Pointwise convergence for bounded functions -/

variable {μ : Measure 𝓧} {p : ℝ≥0∞}
/-- Norm of a nonnegative real number, as a complex number. -/
lemma norm_ofReal_of_nonneg (r : ℝ) (h : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  have h2 : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (r : ℂ), h]

/-- The difference of two Cesaro averages at nearby scales, for a sequence with bounded terms. -/
lemma norm_average_sub_average_le' {c : ℕ → ℂ} {Mabs lam : ℝ} (hM : 0 ≤ Mabs) (hlam : 1 ≤ lam)
    {N N' : ℕ} (hN : 1 ≤ N) (hle : N ≤ N') (hlamN : (N' : ℝ) ≤ lam * (N : ℝ))
    (hc : ∀ n, ‖c n‖ ≤ Mabs) :
    ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, c n
        - (N' : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N', c n‖ ≤ 2 * (lam - 1) * Mabs := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN'pos : (0 : ℝ) < (N' : ℝ) := by exact_mod_cast (le_trans hN hle)
  set S := ∑ n ∈ Finset.Icc 1 N, c n with hS
  set T := ∑ n ∈ Finset.Ioc N N', c n with hT
  have hsplit : ∑ n ∈ Finset.Icc 1 N', c n = S + T := by
    rw [hS, hT]
    have h1 : Finset.Icc 1 N' = Finset.Icc 1 N ∪ Finset.Ioc N N' := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    rw [h1]
    refine Finset.sum_union ?_
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1
    simp only [Finset.mem_Ioc] at hx2
    omega
  have hSnorm : ‖S‖ ≤ (N : ℝ) * Mabs := by
    calc ‖S‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 N, Mabs := Finset.sum_le_sum (fun n _ => hc n)
      _ = (N : ℝ) * Mabs := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
  have hTnorm : ‖T‖ ≤ ((N' : ℝ) - (N : ℝ)) * Mabs := by
    calc ‖T‖ ≤ ∑ n ∈ Finset.Ioc N N', ‖c n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc N N', Mabs := Finset.sum_le_sum (fun n _ => hc n)
      _ = ((N' : ℝ) - (N : ℝ)) * Mabs := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
          congr 1
          push_cast [Nat.cast_sub hle]
          ring
  have hratio : ((N' : ℝ) - (N : ℝ)) / (N' : ℝ) ≤ lam - 1 := by
    rw [div_le_iff₀ hN'pos]
    have : (N' : ℝ) - (N : ℝ) ≤ (lam - 1) * (N' : ℝ) := by
      have h1 : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hle
      have h2 : (N' : ℝ) ≤ lam * (N : ℝ) := hlamN
      have h3 : (N' : ℝ) - (N : ℝ) ≤ lam * (N : ℝ) - (N : ℝ) := by linarith
      have h4 : lam * (N : ℝ) - (N : ℝ) = (lam - 1) * (N : ℝ) := by ring
      have h5 : (lam - 1) * (N : ℝ) ≤ (lam - 1) * (N' : ℝ) := by
        exact mul_le_mul_of_nonneg_left h1 (by linarith)
      linarith
    exact this
  have hkey : (N : ℝ)⁻¹ * S - (N' : ℝ)⁻¹ * (S + T)
      = ((N : ℝ)⁻¹ - (N' : ℝ)⁻¹) * S - (N' : ℝ)⁻¹ * T := by ring
  rw [hsplit, hkey]
  have hcoef : (0 : ℝ) ≤ (N : ℝ)⁻¹ - (N' : ℝ)⁻¹ := by
    have h1 : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hle
    exact sub_nonneg.mpr (inv_anti₀ hNpos h1)
  calc ‖((N : ℝ)⁻¹ - (N' : ℝ)⁻¹) * S - (N' : ℝ)⁻¹ * T‖
      ≤ ‖((N : ℝ)⁻¹ - (N' : ℝ)⁻¹) * S‖ + ‖(N' : ℝ)⁻¹ * T‖ := norm_sub_le _ _
    _ = ((N : ℝ)⁻¹ - (N' : ℝ)⁻¹) * ‖S‖ + (N' : ℝ)⁻¹ * ‖T‖ := by
        rw [norm_mul, norm_mul]
        rw [show ‖(((N : ℝ)⁻¹ : ℝ) : ℂ) - (((N' : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ - (N' : ℝ)⁻¹ from by
          have : (((N : ℝ)⁻¹ : ℝ) : ℂ) - (((N' : ℝ)⁻¹ : ℝ) : ℂ)
              = (((N : ℝ)⁻¹ - (N' : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
          rw [this, norm_ofReal_of_nonneg _ hcoef]]
        rw [norm_ofReal_of_nonneg _ (inv_nonneg.mpr hN'pos.le)]
    _ ≤ ((N : ℝ)⁻¹ - (N' : ℝ)⁻¹) * ((N : ℝ) * Mabs) + (N' : ℝ)⁻¹ * (((N' : ℝ) - (N : ℝ)) * Mabs) := by
        gcongr
    _ = (((N' : ℝ) - (N : ℝ)) / (N' : ℝ)) * Mabs + (((N' : ℝ) - (N : ℝ)) / (N' : ℝ)) * Mabs := by
        field_simp
    _ ≤ (lam - 1) * Mabs + (lam - 1) * Mabs := by
        gcongr
    _ = 2 * (lam - 1) * Mabs := by ring

/-- Comparison of the bilinear averages at two nearby integer scales, for bounded `f`, `g`. -/
lemma norm_A_sub_A_le_of_bounded (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X]) {f g : 𝓧 → ℂ} {Cf Cg : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hf : ∀ y, ‖f y‖ ≤ Cf) (hg : ∀ y, ‖g y‖ ≤ Cg)
    {k k' : ℕ} (hk : 1 ≤ k) (hkk' : k ≤ k') {lam : ℝ} (hlam1 : 1 ≤ lam)
    (hlam : (k' : ℝ) ≤ lam * (k : ℝ)) (x : 𝓧) :
    ‖A T (k : ℝ≥0) X P f g x - A T (k' : ℝ≥0) X P f g x‖ ≤ 2 * (lam - 1) * (Cf * Cg) := by
  have hM : 0 ≤ Cf * Cg := mul_nonneg hCf hCg
  have hterms : ∀ n : ℕ, ‖f ((T ^ (n : ℤ) : 𝓧 ≃ 𝓧) x)
      * g ((T ^ (P.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)‖ ≤ Cf * Cg := by
    intro n
    rw [norm_mul]
    exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hCf
  have h := norm_average_sub_average_le' (c := fun n =>
      f ((T ^ (n : ℤ) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x))
    hM hlam1 hk hkk' hlam hterms
  rw [A_unfold, A_unfold, Nat.floor_natCast, Nat.floor_natCast]
  exact h

/-- Pointwise convergence of the averages of bounded `f`, `g`, assuming the variational estimate
for all the (arbitrarily fine) lacunary scale sequences `s (1 + 1/s)^n`. -/
theorem ae_tendsto_of_bounded (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X]) {f g : 𝓧 → ℂ} {Cf Cg : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hfbd : ∀ y, ‖f y‖ ≤ Cf) (hgbd : ∀ y, ‖g y‖ ≤ Cg)
    (hf : Measurable f) (hg : Measurable g) {p : ℝ≥0∞} {μ : Measure 𝓧}
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    (hV : ∀ s : ℕ, 1 ≤ s →
      eLpNorm (fun x => variationalNorm 3 (fun n => A T (geomScale s n) X P f g x)) p μ
        < ⊤) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun k : ℕ => A T (k : ℝ≥0) X P f g x) atTop (𝓝 L) := by
  have hsub : ∀ᵐ x ∂μ, ∀ s : ℕ, 1 ≤ s → ∃ L : ℂ,
      Tendsto (fun n => A T (geomScale s n) X P f g x) atTop (𝓝 L) := by
    rw [ae_all_iff]
    intro s
    by_cases hs : 1 ≤ s
    · filter_upwards [ae_tendsto_of_eLpNorm_variationalNorm_lt_top (r := 3) (by norm_num)
        (fun n => measurable_A T _ X P hf hg) hp0 hpT (hV s hs)] with x hx
      exact fun _ => hx
    · filter_upwards with x
      exact fun h1 => absurd h1 hs
  have hMnn : 0 ≤ Cf * Cg := mul_nonneg hCf hCg
  filter_upwards [hsub] with x hx
  have hcauchy : CauchySeq (fun k : ℕ => A T (k : ℝ≥0) X P f g x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨s, hs1, hsmall⟩ : ∃ s : ℕ, 1 ≤ s ∧ 2 * (3 / (s : ℝ)) * (Cf * Cg) < ε / 4 := by
      have hε0 : 0 < ε := hε
      obtain ⟨s₀, hs₀⟩ := exists_nat_gt (24 * (Cf * Cg) / ε)
      refine ⟨max 1 (s₀ + 1), le_max_left _ _, ?_⟩
      have hs : (0 : ℝ) < ((max 1 (s₀ + 1) : ℕ) : ℝ) := by positivity
      have hbig : 24 * (Cf * Cg) / ε < ((max 1 (s₀ + 1) : ℕ) : ℝ) := by
        refine lt_of_lt_of_le hs₀ ?_
        have h : s₀ < max 1 (s₀ + 1) := by omega
        exact_mod_cast h.le
      rw [div_lt_iff₀ hε0] at hbig
      rw [show 2 * (3 / (((max 1 (s₀ + 1) : ℕ)) : ℝ)) * (Cf * Cg) = 6 * (Cf * Cg)
        / (((max 1 (s₀ + 1) : ℕ)) : ℝ) from by ring]
      rw [div_lt_iff₀ hs]
      linarith
    obtain ⟨Ls, hLs⟩ := hx s hs1
    obtain ⟨N0, hN0⟩ := Metric.cauchySeq_iff.mp hLs.cauchySeq (ε / 2) (by linarith)
    refine ⟨max (max s N0) (geomIdx s N0), fun m hm n hn => ?_⟩
    have hms : s ≤ m := le_trans (le_trans (le_max_left s N0) (le_max_left _ _)) hm
    have hns : s ≤ n := le_trans (le_trans (le_max_left s N0) (le_max_left _ _)) hn
    have hmN0 : geomIdx s N0 ≤ m := le_trans (le_max_right _ _) hm
    have hnN0 : geomIdx s N0 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨am, ham1, ham2⟩ := exists_geomIdx_between s m hs1 hms
    obtain ⟨an, han1, han2⟩ := exists_geomIdx_between s n hs1 hns
    have hamN : N0 ≤ am := by
      by_contra hc
      push Not at hc
      have := geomIdx_strictMono s hs1 hc
      omega
    have hanN : N0 ≤ an := by
      by_contra hc
      push Not at hc
      have := geomIdx_strictMono s hs1 hc
      omega
    have e1 : A T (geomIdx s am : ℝ≥0) X P f g x = A T (geomScale s am) X P f g x :=
      (A_floor T (geomScale s am) X P f g x).symm
    have e2 : A T (geomIdx s an : ℝ≥0) X P f g x = A T (geomScale s an) X P f g x :=
      (A_floor T (geomScale s an) X P f g x).symm
    have hlam1 : (1 : ℝ) ≤ 1 + 3 / (s : ℝ) := by
      have : (0 : ℝ) ≤ 3 / (s : ℝ) := by positivity
      linarith
    have h1 : dist (A T (m : ℝ≥0) X P f g x) (A T (geomScale s am) X P f g x)
        ≤ 2 * (3 / (s : ℝ)) * (Cf * Cg) := by
      rw [dist_eq_norm, ← e1]
      have h := norm_A_sub_A_le_of_bounded T P hCf hCg hfbd hgbd (k := m) (k' := geomIdx s am)
        (lam := 1 + 3 / (s : ℝ)) (le_trans hs1 hms) ham1 hlam1 ham2 x
      have hsub : (1 + 3 / (s : ℝ)) - 1 = 3 / (s : ℝ) := by ring
      rwa [hsub] at h
    have h2 : dist (A T (geomScale s an) X P f g x) (A T (n : ℝ≥0) X P f g x)
        ≤ 2 * (3 / (s : ℝ)) * (Cf * Cg) := by
      rw [dist_eq_norm, ← e2, norm_sub_rev]
      have h := norm_A_sub_A_le_of_bounded T P hCf hCg hfbd hgbd (k := n) (k' := geomIdx s an)
        (lam := 1 + 3 / (s : ℝ)) (le_trans hs1 hns) han1 hlam1 han2 x
      have hsub : (1 + 3 / (s : ℝ)) - 1 = 3 / (s : ℝ) := by ring
      rwa [hsub] at h
    have h3 : dist (A T (geomScale s am) X P f g x) (A T (geomScale s an) X P f g x) < ε / 2 :=
      hN0 am hamN an hanN
    have htri := dist_triangle (A T (geomScale s am) X P f g x)
      (A T (geomScale s an) X P f g x) (A T (n : ℝ≥0) X P f g x)
    calc dist (A T (m : ℝ≥0) X P f g x) (A T (n : ℝ≥0) X P f g x)
        ≤ dist (A T (m : ℝ≥0) X P f g x) (A T (geomScale s am) X P f g x)
          + dist (A T (geomScale s am) X P f g x) (A T (n : ℝ≥0) X P f g x) :=
          dist_triangle _ _ _
      _ ≤ dist (A T (m : ℝ≥0) X P f g x) (A T (geomScale s am) X P f g x)
          + (dist (A T (geomScale s am) X P f g x) (A T (geomScale s an) X P f g x)
          + dist (A T (geomScale s an) X P f g x) (A T (n : ℝ≥0) X P f g x)) := by
          linarith
      _ < ε := by linarith
  exact cauchySeq_tendsto_of_complete hcauchy

/-! ### The maximal estimate from the variational estimate -/

/-- `MemLp` is preserved by replacing a function by the complexification of its norm. -/
lemma memLp_norm_coe {f : 𝓧 → ℂ} {p : ℝ≥0∞} {μ : Measure 𝓧} (hf : MemLp f p μ) :
    MemLp (fun y => (‖f y‖ : ℂ)) p μ := by
  rw [MeasureTheory.memLp_iff, eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm)
    (g := fun y => ‖f y‖) (by
    filter_upwards with y
    rw [norm_ofReal_of_nonneg _ (norm_nonneg _)]
    simp)]
  exact hf.norm.eLpNorm_lt_top

/-- The `Lᵖ` seminorm of the complexified norm of `f` agrees with that of `f`. -/
lemma enorm_toLp_norm_coe {f : 𝓧 → ℂ} {p : ℝ≥0∞} {μ : Measure 𝓧} (hf : MemLp f p μ) :
    ‖(memLp_norm_coe hf).toLp‖ₑ = ‖hf.toLp‖ₑ := by
  rw [show ‖(memLp_norm_coe hf).toLp‖ₑ = eLpNorm (fun y => (‖f y‖ : ℂ)) p μ from by simp,
    show ‖hf.toLp‖ₑ = eLpNorm f p μ from by simp]
  exact eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm) (by
    filter_upwards with y
    exact norm_ofReal_of_nonneg _ (norm_nonneg _))

/-- The long variational estimate of Theorem 1.17(iv), in the form used for the reductions. -/
def VarEst (T : 𝓧 ≃ᵐ 𝓧) (μ : Measure 𝓧) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (f g : 𝓧 → ℂ) (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x => variationalNorm 3 (fun n => A T (a n) X P f g x)) p μ
      ≤ (Cv Λ : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

/-- The maximal function is dominated by twice the variational norm of the dyadic averages
(of the absolute values). -/
lemma maximal_le_two_varDyadic (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X]) {f g : 𝓧 → ℂ} (x : 𝓧) :
    (⨆ (N : ℕ+), ‖A T N X P f g x‖ₑ)
      ≤ 2 * variationalNorm 3 (fun n => A T (geomScale 1 n) X P
          (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x) := by
  refine iSup_le (fun N => ?_)
  have h1 : ‖A T (N : ℝ≥0) X P f g x‖
      ≤ Ab T (N : ℝ≥0) X P (fun y => ‖f y‖) (fun y => ‖g y‖) x :=
    norm_A_le_Ab T (by exact_mod_cast N.2) X P f g x
  have h1e : ‖A T (N : ℝ≥0) X P f g x‖ₑ
      ≤ ENNReal.ofReal (Ab T (N : ℝ≥0) X P (fun y => ‖f y‖) (fun y => ‖g y‖) x) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h1
  have h2 := ofReal_Ab_le_two_dyadic T X P (fun y => norm_nonneg (f y))
    (fun y => norm_nonneg (g y)) N x
  have h3 : (⨆ k : ℕ, ENNReal.ofReal (Ab T ((2 : ℝ≥0) ^ k) X P
        (fun y => ‖f y‖) (fun y => ‖g y‖) x))
      ≤ variationalNorm 3 (fun n => A T (geomScale 1 n) X P
          (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x) := by
    refine iSup_le (fun k => ?_)
    have h4 : ENNReal.ofReal (Ab T ((2 : ℝ≥0) ^ k) X P (fun y => ‖f y‖) (fun y => ‖g y‖) x)
        = ‖A T ((2 : ℝ≥0) ^ k) X P (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x‖ₑ :=
      (enorm_A_ofReal_eq T _ X P (fun y => norm_nonneg (f y)) (fun y => norm_nonneg (g y)) x).symm
    rw [h4]
    have h5 : (2 : ℝ≥0) ^ k = geomScale 1 k := by
      rw [geomScale]
      norm_num
    rw [h5]
    exact le_variationalNorm 3 (fun n => A T (geomScale 1 n) X P
      (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x) k
  calc ‖A T (N : ℝ≥0) X P f g x‖ₑ
      ≤ ENNReal.ofReal (Ab T (N : ℝ≥0) X P (fun y => ‖f y‖) (fun y => ‖g y‖) x) := h1e
    _ ≤ 2 * ⨆ k : ℕ, ENNReal.ofReal (Ab T ((2 : ℝ≥0) ^ k) X P
          (fun y => ‖f y‖) (fun y => ‖g y‖) x) := h2
    _ ≤ 2 * variationalNorm 3 (fun n => A T (geomScale 1 n) X P
          (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x) := by
        exact mul_le_mul_of_nonneg_left h3 (by norm_num)

/-- The maximal estimate (Theorem 1.17(iii)) from the long variational estimate. -/
theorem eLpNorm_maximal_le_of_varEst {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ)
    (hmeas : AEStronglyMeasurable (fun x => ⨆ (N : ℕ+), ‖A T N X P f g x‖ₑ) μ) :
    eLpNorm (fun x => ⨆ (N : ℕ+), ‖A T N X P f g x‖ₑ) p μ
      ≤ (2 * Cv (3 / 2) : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ := by
  have hf' := memLp_norm_coe hf
  have hg' := memLp_norm_coe hg
  have hlac : Lacunary (3 / 2) (geomScale 1) := by
    have h := lacunary_geomScale 1 (by norm_num)
    convert h using 2
    norm_num
  have h1n : ∀ n, 1 ≤ geomScale 1 n := geomScale_one_le 1 (by norm_num)
  have hV := hVar (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) hf' hg' (geomScale 1) (3 / 2)
    (by norm_num) hlac h1n
  calc eLpNorm (fun x => ⨆ (N : ℕ+), ‖A T N X P f g x‖ₑ) p μ
      ≤ eLpNorm (fun x => 2 * variationalNorm 3 (fun n => A T (geomScale 1 n) X P
          (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x)) p μ :=
        eLpNorm_mono_enorm hmeas (fun x => maximal_le_two_varDyadic T P x)
    _ = 2 * eLpNorm (fun x => variationalNorm 3 (fun n => A T (geomScale 1 n) X P
          (fun y => (‖f y‖ : ℂ)) (fun y => (‖g y‖ : ℂ)) x)) p μ :=
        Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (by norm_num) hp0 hpT
    _ ≤ 2 * ((Cv (3 / 2) : ℝ≥0∞) * ‖hf'.toLp‖ₑ * ‖hg'.toLp‖ₑ) := by
        gcongr
    _ = (2 * Cv (3 / 2) : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ := by
        rw [enorm_toLp_norm_coe hf, enorm_toLp_norm_coe hg]; ring

/-! ### The maximal function at all positive scales -/

variable {μ : Measure 𝓧}

/-- The maximal function of the bilinear averages over all positive scales. -/
noncomputable def bilinMax (T : 𝓧 ≃ᵐ 𝓧) (P₁ P₂ : ℤ[X]) (a b : 𝓧 → ℂ) (x : 𝓧) : ℝ≥0∞ :=
  ⨆ (N : ℕ+), ‖A T N P₁ P₂ a b x‖ₑ

lemma measurable_bilinMax (T : 𝓧 ≃ᵐ 𝓧) (P₁ P₂ : ℤ[X]) {a b : 𝓧 → ℂ}
    (ha : Measurable a) (hb : Measurable b) : Measurable (bilinMax T P₁ P₂ a b) := by
  refine Measurable.iSup (fun N => ?_)
  exact (measurable_A T N P₁ P₂ ha hb).enorm

lemma le_bilinMax (T : 𝓧 ≃ᵐ 𝓧) (P₁ P₂ : ℤ[X]) {a b : 𝓧 → ℂ} (x : 𝓧) (N : ℕ+) :
    ‖A T N P₁ P₂ a b x‖ₑ ≤ bilinMax T P₁ P₂ a b x :=
  le_iSup (fun N : ℕ+ => ‖A T N P₁ P₂ a b x‖ₑ) N

/-- The maximal estimate for `bilinMax`, obtained from the variational estimate. -/
theorem eLpNorm_bilinMax_le {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) {a b : 𝓧 → ℂ} (ha : MemLp a p₁ μ) (hb : MemLp b p₂ μ)
    (hmeas : AEStronglyMeasurable (bilinMax T X P a b) μ) :
    eLpNorm (bilinMax T X P a b) p μ ≤ (2 * Cv (3 / 2) : ℝ≥0∞) * ‖ha.toLp‖ₑ * ‖hb.toLp‖ₑ :=
  eLpNorm_maximal_le_of_varEst hVar hp0 hpT ha hb hmeas

/-- Markov/Chebyshev bound for the maximal function. -/
lemma mul_measure_lt_bilinMax_le {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) {a b : 𝓧 → ℂ} (ha : MemLp a p₁ μ) (hb : MemLp b p₂ μ)
    (ha' : Measurable a) (hb' : Measurable b) {c : ℝ≥0∞} :
    c ^ p.toReal * μ {x | c < bilinMax T X P a b x}
      ≤ ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖ha.toLp‖ₑ * ‖hb.toLp‖ₑ) ^ p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpT
  have hM := measurable_bilinMax T X P ha' hb'
  have hbound := eLpNorm_bilinMax_le hVar hp0 hpT ha hb hM.aestronglyMeasurable
  have hmarkov := mul_meas_ge_le_lintegral (μ := μ)
    (f := fun x => (bilinMax T X P a b x) ^ p.toReal) (hM.pow_const _) (c ^ p.toReal)
  have hsep : {x | c < bilinMax T X P a b x} ⊆ {x | c ^ p.toReal ≤ (bilinMax T X P a b x) ^ p.toReal} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact le_of_lt (ENNReal.rpow_lt_rpow hx hq)
  have hlin : ∫⁻ x, (bilinMax T X P a b x) ^ p.toReal ∂μ
      = (eLpNorm (bilinMax T X P a b) p μ) ^ p.toReal := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpT]
    simp only [enorm_eq_self]
    rw [one_div, ENNReal.rpow_inv_rpow hq.ne']
  calc c ^ p.toReal * μ {x | c < bilinMax T X P a b x}
      ≤ c ^ p.toReal * μ {x | c ^ p.toReal ≤ (bilinMax T X P a b x) ^ p.toReal} :=
        mul_le_mul_of_nonneg_left (measure_mono hsep) bot_le
    _ ≤ ∫⁻ x, (bilinMax T X P a b x) ^ p.toReal ∂μ := hmarkov
    _ = (eLpNorm (bilinMax T X P a b) p μ) ^ p.toReal := hlin
    _ ≤ ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖ha.toLp‖ₑ * ‖hb.toLp‖ₑ) ^ p.toReal :=
        ENNReal.rpow_le_rpow hbound hq.le

/-- Multiplication by a finite constant preserves convergence to `0` in `ℝ≥0∞`. -/
lemma tendsto_const_mul_zero_ennreal {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : a ≠ ⊤) (hf : Tendsto f atTop (𝓝 0)) : Tendsto (fun j => a * f j) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero] at hf ⊢
  intro ε hε
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, fun n _ => by simp [hε.le]⟩
  · have hδ : 0 < ε / a := ENNReal.div_pos_iff.mpr ⟨hε.ne', ha⟩
    obtain ⟨N, hN⟩ := hf (ε / a) hδ
    refine ⟨N, fun n hn => ?_⟩
    calc a * f n = f n * a := mul_comm _ _
      _ ≤ (ε / a) * a := mul_le_mul_of_nonneg_right (hN n hn) bot_le
      _ = (ε / a) * a := rfl
      _ = ε := ENNReal.div_mul_cancel ha0 ha

/-- Pointwise convergence of the averages of measurable inputs, assuming the long variational
estimate. -/
theorem ae_tendsto_of_varEst {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hp1 : 1 ≤ p) (hp₁ne : p₁ ≠ ⊤) (hp₂ne : p₂ ≠ ⊤)
    {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ)
    (hfm : Measurable f) (hgm : Measurable g) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun k : ℕ => A T (k : ℝ≥0) X P f g x) atTop (𝓝 L) := by
  classical
  have hbounded : ∀ (a b : 𝓧 → ℂ), MemLp a p₁ μ → MemLp b p₂ μ → Measurable a → Measurable b →
      (∃ Ca : ℝ, ∀ x, ‖a x‖ ≤ Ca) → (∃ Cb : ℝ, ∀ x, ‖b x‖ ≤ Cb) →
      ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun k : ℕ => A T (k : ℝ≥0) X P a b x) atTop (𝓝 L) := by
    intro a b ha hb ham hbm hba hbb
    obtain ⟨Ca, hCa⟩ := hba
    obtain ⟨Cb, hCb⟩ := hbb
    have hV : ∀ s : ℕ, 1 ≤ s → eLpNorm (fun x => variationalNorm 3
        (fun n => A T (geomScale s n) X P a b x)) p μ < ⊤ := by
      intro s hs
      have hΛ : (1 : ℝ≥0) < 1 + (2 * (s : ℝ≥0))⁻¹ := by
        have hpos : (0 : ℝ≥0) < (2 * (s : ℝ≥0))⁻¹ := inv_pos.mpr (by positivity)
        linarith
      refine lt_of_le_of_lt (hVar a b ha hb (geomScale s) (1 + (2 * (s : ℝ≥0))⁻¹) hΛ
        (lacunary_geomScale s hs) (geomScale_one_le s hs)) ?_
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ?_) ?_
      · rw [show ‖ha.toLp‖ₑ = eLpNorm a p₁ μ from by simp]
        exact ha.eLpNorm_lt_top
      · rw [show ‖hb.toLp‖ₑ = eLpNorm b p₂ μ from by simp]
        exact hb.eLpNorm_lt_top
    exact ae_tendsto_of_bounded T P (le_max_right _ _) (le_max_right _ _)
      (fun y => le_trans (hCa y) (le_max_left _ _)) (fun y => le_trans (hCb y) (le_max_left _ _))
      ham hbm hp0 hpT hV
  obtain ⟨f', hf'meas, hf'bd, hf'mem, hf'le, hf'cv⟩ :=
    Commons.MeasureTheory.Lp.exists_bounded_tendsto_eLpNorm hp₁ne hf
  obtain ⟨g', hg'meas, hg'bd, hg'mem, hg'le, hg'cv⟩ :=
    Commons.MeasureTheory.Lp.exists_bounded_tendsto_eLpNorm hp₂ne hg
  have hM_meas : ∀ j : ℕ, Measurable (fun x => bilinMax T X P (f - f' j) g x
      + bilinMax T X P (f' j) (g - g' j) x) := by
    intro j
    exact (measurable_bilinMax T X P (hfm.sub (hf'meas j)) hgm).add
      (measurable_bilinMax T X P (hf'meas j) (hgm.sub (hg'meas j)))
  have hx : Tendsto (fun j : ℕ => ‖(hf.sub (hf'mem j)).toLp‖ₑ) atTop (𝓝 0) := by
    have heq : (fun j : ℕ => ‖(hf.sub (hf'mem j)).toLp‖ₑ)
        = fun j : ℕ => eLpNorm (f - f' j) p₁ μ := by
      funext j; simp
    rw [heq]; exact hf'cv
  have hy : Tendsto (fun j : ℕ => ‖(hg.sub (hg'mem j)).toLp‖ₑ) atTop (𝓝 0) := by
    have heq : (fun j : ℕ => ‖(hg.sub (hg'mem j)).toLp‖ₑ)
        = fun j : ℕ => eLpNorm (g - g' j) p₂ μ := by
      funext j; simp
    rw [heq]; exact hg'cv
  have hc1 : ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖hg.toLp‖ₑ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) ?_
    rw [show ‖hg.toLp‖ₑ = eLpNorm g p₂ μ from by simp]
    exact hg.eLpNorm_lt_top.ne
  have hc2 : ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖hf.toLp‖ₑ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) ?_
    rw [show ‖hf.toLp‖ₑ = eLpNorm f p₁ μ from by simp]
    exact hf.eLpNorm_lt_top.ne
  have hsum : Tendsto (fun j : ℕ =>
      ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖hg.toLp‖ₑ) * ‖(hf.sub (hf'mem j)).toLp‖ₑ
        + ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖hf.toLp‖ₑ) * ‖(hg.sub (hg'mem j)).toLp‖ₑ)
      atTop (𝓝 0) := by
    have h1 := tendsto_const_mul_zero_ennreal hc1 hx
    have h2 := tendsto_const_mul_zero_ennreal hc2 hy
    simpa using h1.add h2
  have hM_le : ∀ j : ℕ, eLpNorm (fun x => bilinMax T X P (f - f' j) g x
      + bilinMax T X P (f' j) (g - g' j) x) p μ
      ≤ ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖hg.toLp‖ₑ) * ‖(hf.sub (hf'mem j)).toLp‖ₑ
        + ((2 * Cv (3 / 2) : ℝ≥0∞) * ‖hf.toLp‖ₑ) * ‖(hg.sub (hg'mem j)).toLp‖ₑ := by
    intro j
    refine (eLpNorm_add_le hp1).trans
      (add_le_add ?_ ?_)
    · refine (eLpNorm_bilinMax_le hVar hp0 hpT (hf.sub (hf'mem j)) hg
        (measurable_bilinMax T X P (hfm.sub (hf'meas j)) hgm).aestronglyMeasurable).trans
        (le_of_eq ?_)
      ac_rfl
    · refine (eLpNorm_bilinMax_le hVar hp0 hpT (hf'mem j) (hg.sub (hg'mem j))
        (measurable_bilinMax T X P (hf'meas j) (hgm.sub (hg'meas j))).aestronglyMeasurable).trans ?_
      have hb : ‖(hf'mem j).toLp‖ₑ ≤ ‖hf.toLp‖ₑ := by
        rw [show ‖(hf'mem j).toLp‖ₑ = eLpNorm (f' j) p₁ μ from by simp,
          show ‖hf.toLp‖ₑ = eLpNorm f p₁ μ from by simp]
        exact hf'le j
      calc (2 * Cv (3 / 2) : ℝ≥0∞) * ‖(hf'mem j).toLp‖ₑ * ‖(hg.sub (hg'mem j)).toLp‖ₑ
          = (2 * Cv (3 / 2) : ℝ≥0∞)
              * (‖(hf'mem j).toLp‖ₑ * ‖(hg.sub (hg'mem j)).toLp‖ₑ) := by
            rw [mul_assoc]
        _ ≤ (2 * Cv (3 / 2) : ℝ≥0∞)
              * (‖hf.toLp‖ₑ * ‖(hg.sub (hg'mem j)).toLp‖ₑ) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb bot_le) bot_le
        _ = (2 * Cv (3 / 2) : ℝ≥0∞) * ‖hf.toLp‖ₑ * ‖(hg.sub (hg'mem j)).toLp‖ₑ := by
            ac_rfl

  have hM_tend : Tendsto (fun j : ℕ => eLpNorm (fun x => bilinMax T X P (f - f' j) g x
      + bilinMax T X P (f' j) (g - g' j) x) p μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
    · filter_upwards with j
      exact bot_le
    · filter_upwards with j
      exact hM_le j
  have hbd : ∀ (j n : ℕ) (x : 𝓧),
      ‖A T (n : ℝ≥0) X P f g x - A T (n : ℝ≥0) X P (f' j) (g' j) x‖ₑ
        ≤ bilinMax T X P (f - f' j) g x + bilinMax T X P (f' j) (g - g' j) x := by
    intro j n x
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [A]
    rw [A_sub_bilin]
    refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
    · exact le_bilinMax T X P x ⟨n, hn⟩
    · exact le_bilinMax T X P x ⟨n, hn⟩
  have hv : ∀ j : ℕ, ∀ᵐ x ∂μ, ∃ L : ℂ,
      Tendsto (fun n : ℕ => A T (n : ℝ≥0) X P (f' j) (g' j) x) atTop (𝓝 L) :=
    fun j => hbounded (f' j) (g' j) (hf'mem j) (hg'mem j) (hf'meas j) (hg'meas j)
      (hf'bd j) (hg'bd j)
  have hcauchy := Commons.Analysis.ErgodicPrinciple.ae_cauchy_of_approx hp0 hpT hM_meas hM_tend hbd hv
  filter_upwards [hcauchy] with x hx'
  exact cauchySeq_tendsto_of_complete hx'

/-! ### Passing from the integer-indexed averages to the real-indexed ones -/

lemma tendsto_nat_floor_atTop_NNReal : Tendsto (fun N : ℝ≥0 => Nat.floor N) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  exact ⟨(k : ℝ≥0), fun N hN => Nat.le_floor hN⟩

lemma tendsto_floor_iff {F : ℕ → ℂ} {L : ℂ} :
    Tendsto (fun N : ℝ≥0 => F (Nat.floor N)) atTop (𝓝 L) ↔ Tendsto F atTop (𝓝 L) := by
  constructor
  · intro h
    have h1 : Tendsto (fun k : ℕ => (k : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun k : ℕ => F (Nat.floor ((k : ℝ≥0)))) atTop (𝓝 L) := h.comp h1
    simpa using h2
  · intro h
    exact h.comp tendsto_nat_floor_atTop_NNReal

lemma tendsto_floor_iff_exists {F : ℕ → ℂ} :
    (∃ L : ℂ, Tendsto (fun N : ℝ≥0 => F (Nat.floor N)) atTop (𝓝 L))
      ↔ ∃ L : ℂ, Tendsto F atTop (𝓝 L) :=
  exists_congr (fun _ => tendsto_floor_iff)

/-- Pointwise convergence of the real-indexed averages, assuming the variational estimate. -/
theorem ae_tendsto_real_of_varEst {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hp1 : 1 ≤ p) (hp₁ne : p₁ ≠ ⊤) (hp₂ne : p₂ ≠ ⊤)
    {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ)
    (hfm : Measurable f) (hgm : Measurable g) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun N : ℝ≥0 => A T N X P f g x) atTop (𝓝 L) := by
  filter_upwards [ae_tendsto_of_varEst hVar hp0 hpT hp1 hp₁ne hp₂ne hf hg hfm hgm] with x hx
  rw [show (fun N : ℝ≥0 => A T N X P f g x)
      = fun N : ℝ≥0 => A T ((Nat.floor N : ℕ) : ℝ≥0) X P f g x from by
    funext N; exact A_floor T N X P f g x]
  exact tendsto_floor_iff_exists.mpr hx

/-- The iterates of a measure-preserving equivalence are quasi-measure-preserving. -/
lemma quasiMeasurePreserving_zpow (T : 𝓧 ≃ᵐ 𝓧) {μ : Measure 𝓧}
    (hT : MeasurePreserving T μ μ) (k : ℤ) :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun x => (T ^ k : 𝓧 ≃ 𝓧) x) μ μ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · subst hm
    have h1 : (fun x => (T ^ (m : ℤ) : 𝓧 ≃ 𝓧) x) = T^[m] := by
      funext x
      rw [show (T ^ (m : ℤ) : 𝓧 ≃ 𝓧) = (T : 𝓧 ≃ 𝓧) ^ m from by simp [zpow_natCast]]
      simp [Equiv.Perm.coe_pow]
    rw [h1]
    exact (hT.iterate m).quasiMeasurePreserving
  · subst hm
    have h1 : (fun x => (T ^ (-(m : ℤ)) : 𝓧 ≃ 𝓧) x) = (T.symm)^[m] := by
      funext x
      rw [show (T ^ (-(m : ℤ)) : 𝓧 ≃ 𝓧) = (T.symm : 𝓧 ≃ 𝓧) ^ m from by
        rw [zpow_neg, zpow_natCast, ← inv_pow]
        rfl]
      simp [Equiv.Perm.coe_pow]
    rw [h1]
    exact (hT.symm.iterate m).quasiMeasurePreserving

/-- Pointwise convergence of the real-indexed averages for `Lᵖ` inputs, assuming the variational
estimate. -/
theorem ae_tendsto_real_of_varEst_memLp {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ)
    (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hp1 : 1 ≤ p) (hp₁ne : p₁ ≠ ⊤) (hp₂ne : p₂ ≠ ⊤)
    {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun N : ℝ≥0 => A T N X P f g x) atTop (𝓝 L) := by
  set f₀ : 𝓧 → ℂ := hf.aemeasurable.mk f with hf₀def
  set g₀ : 𝓧 → ℂ := hg.aemeasurable.mk g with hg₀def
  have hf₀m : Measurable f₀ := hf.aemeasurable.measurable_mk
  have hg₀m : Measurable g₀ := hg.aemeasurable.measurable_mk
  have hf₀eq : f =ᵐ[μ] f₀ := hf.aemeasurable.ae_eq_mk
  have hg₀eq : g =ᵐ[μ] g₀ := hg.aemeasurable.ae_eq_mk
  have hf₀mem : MemLp f₀ p₁ μ := hf.ae_eq hf₀eq
  have hg₀mem : MemLp g₀ p₂ μ := hg.ae_eq hg₀eq
  have hmain := ae_tendsto_real_of_varEst hVar hp0 hpT hp1 hp₁ne hp₂ne hf₀mem hg₀mem hf₀m hg₀m
  -- the (conull) set where all the evaluations of `f` and `f₀` (resp. `g` and `g₀`) agree
  have hZf : ∀ k : ℤ, μ {x | f ((T ^ k : 𝓧 ≃ 𝓧) x) ≠ f₀ ((T ^ k : 𝓧 ≃ 𝓧) x)} = 0 := fun k =>
    (quasiMeasurePreserving_zpow T hT k).preimage_null (ae_iff.mp hf₀eq)
  have hZg : ∀ k : ℤ, μ {x | g ((T ^ k : 𝓧 ≃ 𝓧) x) ≠ g₀ ((T ^ k : 𝓧 ≃ 𝓧) x)} = 0 := fun k =>
    (quasiMeasurePreserving_zpow T hT k).preimage_null (ae_iff.mp hg₀eq)
  have hgood : ∀ᵐ x ∂μ, (∀ k : ℤ, f ((T ^ k : 𝓧 ≃ 𝓧) x) = f₀ ((T ^ k : 𝓧 ≃ 𝓧) x))
      ∧ (∀ k : ℤ, g ((T ^ k : 𝓧 ≃ 𝓧) x) = g₀ ((T ^ k : 𝓧 ≃ 𝓧) x)) := by
    have hA : ∀ᵐ x ∂μ, ∀ k : ℤ, f ((T ^ k : 𝓧 ≃ 𝓧) x) = f₀ ((T ^ k : 𝓧 ≃ 𝓧) x) := by
      rw [ae_all_iff]
      intro k
      rw [ae_iff]
      simpa using hZf k
    have hB : ∀ᵐ x ∂μ, ∀ k : ℤ, g ((T ^ k : 𝓧 ≃ 𝓧) x) = g₀ ((T ^ k : 𝓧 ≃ 𝓧) x) := by
      rw [ae_all_iff]
      intro k
      rw [ae_iff]
      simpa using hZg k
    filter_upwards [hA, hB] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  filter_upwards [hmain, hgood] with x hx hxg
  obtain ⟨L, hL⟩ := hx
  refine ⟨L, ?_⟩
  rw [show (fun N : ℝ≥0 => A T N X P f g x) = fun N : ℝ≥0 => A T N X P f₀ g₀ x from ?_]
  · exact hL
  · funext N
    simp only [A_unfold]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hxg.1 (n : ℤ), hxg.2 (P.eval (n : ℤ))]

/-- Almost-everywhere measurability of the bilinear average, given that the transformation is
measure preserving. -/
lemma aemeasurable_A_of_measurePreserving (T : 𝓧 ≃ᵐ 𝓧) {μ : Measure 𝓧}
    (hT : MeasurePreserving T μ μ) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) {f g : 𝓧 → ℂ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (A T N P₁ P₂ f g) μ := by
  unfold A
  refine AEMeasurable.const_mul ?_ _
  have hterm : ∀ n : ℕ, AEMeasurable (fun x : 𝓧 =>
      f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)) μ := by
    intro n
    exact (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_zpow T hT _)).mul
      (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_zpow T hT _))
  have heq : (∑ i ∈ Finset.Icc 1 (Nat.floor N), (fun x : 𝓧 =>
      f ((T ^ (P₁.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x)))
      = (fun x : 𝓧 => ∑ i ∈ Finset.Icc 1 (Nat.floor N),
          f ((T ^ (P₁.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (i : ℤ)) : 𝓧 ≃ 𝓧) x)) := by
    ext x
    simp only [Finset.sum_apply]
  rw [← heq]
  exact Finset.aemeasurable_sum (Finset.Icc 1 (Nat.floor N)) (fun n _ => hterm n)

/-- Norm convergence in `Lᵖ` for the averages, assuming the variational estimate. -/
theorem exists_tendsto_eLpNorm_of_varEst {T : 𝓧 ≃ᵐ 𝓧} {μ : Measure 𝓧} {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hT : MeasurePreserving T μ μ)
    (hVar : VarEst T μ P p₁ p₂ p Cv)
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hp1 : 1 ≤ p) (hp₁ne : p₁ ≠ ⊤) (hp₂ne : p₂ ≠ ⊤)
    {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ
      ∧ (∀ᵐ x ∂μ, Tendsto (fun N : ℝ≥0 => A T N X P f g x) atTop (𝓝 (h x)))
      ∧ Tendsto (fun N : ℝ≥0 => eLpNorm (A T N X P f g - h) p μ) atTop (𝓝 0) := by
  classical
  have hBlt : eLpNorm (bilinMax T X P f g) p μ < ⊤ := by
    refine lt_of_le_of_lt (eLpNorm_bilinMax_le hVar hp0 hpT hf hg
      (AEMeasurable.iSup fun N : ℕ+ => (aemeasurable_A_of_measurePreserving T hT N X P
        hf.aemeasurable hg.aemeasurable).enorm).aestronglyMeasurable) ?_
    have h1 : ‖hf.toLp‖ₑ < ⊤ := by
      rw [show ‖hf.toLp‖ₑ = eLpNorm f p₁ μ from by simp]; exact hf.eLpNorm_lt_top
    have h2 : ‖hg.toLp‖ₑ < ⊤ := by
      rw [show ‖hg.toLp‖ₑ = eLpNorm g p₂ μ from by simp]; exact hg.eLpNorm_lt_top
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top h1) h2
  have hpt : ∀ (n : ℕ) (x : 𝓧), ‖A T (n : ℝ≥0) X P f g x‖ₑ ≤ bilinMax T X P f g x := by
    intro n x
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [A]
    · exact le_bilinMax T X P x ⟨n, hn⟩
  have hmeasA : ∀ n : ℕ, AEMeasurable (fun x => A T (n : ℝ≥0) X P f g x) μ := fun n =>
    aemeasurable_A_of_measurePreserving T hT _ X P hf.aemeasurable hg.aemeasurable
  have hae : ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun n : ℕ =>
      A T (n : ℝ≥0) X P f g x) atTop (𝓝 L) := by
    filter_upwards [ae_tendsto_real_of_varEst_memLp hT hVar hp0 hpT hp1 hp₁ne hp₂ne hf hg]
      with x hx
    rw [show (fun N : ℝ≥0 => A T N X P f g x)
        = fun N : ℝ≥0 => A T ((Nat.floor N : ℕ) : ℝ≥0) X P f g x from by
      funext N; exact A_floor T N X P f g x] at hx
    exact (tendsto_floor_iff_exists (F := fun k : ℕ => A T (k : ℝ≥0) X P f g x)).mp hx
  let h : 𝓧 → ℂ := fun x => if hx : ∃ L : ℂ, Tendsto (fun n : ℕ =>
      A T (n : ℝ≥0) X P f g x) atTop (𝓝 L) then Classical.choose hx else 0
  have hh : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => A T (n : ℝ≥0) X P f g x) atTop (𝓝 (h x)) := by
    filter_upwards [hae] with x hx
    simp only [h, dif_pos hx]
    exact Classical.choose_spec hx
  have hmeas : AEMeasurable h μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => hmeasA n) hh
  let h' : 𝓧 → ℂ := hmeas.mk h
  have hh'meas : Measurable h' := hmeas.measurable_mk
  have hh'eq : h =ᵐ[μ] h' := hmeas.ae_eq_mk
  have hh' : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => A T (n : ℝ≥0) X P f g x) atTop (𝓝 (h' x)) := by
    filter_upwards [hh, hh'eq] with x hx hxe
    rwa [hxe] at hx
  have hmem' : MemLp h' p μ := by
    rw [MeasureTheory.memLp_iff]
    have hbound : ∀ᶠ n : ℕ in atTop, eLpNorm (fun x => A T (n : ℝ≥0) X P f g x) p μ
        ≤ eLpNorm (bilinMax T X P f g) p μ := by
      filter_upwards with n
      exact eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by rw [enorm_eq_self]; exact hpt n x)
    refine lt_of_le_of_lt (MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (hg := by pw_aesm)
      (C := eLpNorm (bilinMax T X P f g) p μ) hbound
      (fun n => (hmeasA n).aestronglyMeasurable) hh') hBlt
  have hconv := Commons.MeasureTheory.Lp.tendsto_eLpNorm_of_ae_tendsto_of_bound hp0 hpT
    (f := fun n : ℕ => fun x => A T (n : ℝ≥0) X P f g x) (g := h') (B := bilinMax T X P f g)
    (fun n => (hmeasA n).aestronglyMeasurable) hBlt
    (by filter_upwards with x n; rw [ofReal_norm]; exact hpt n x) hh'
  have hae' : ∀ᵐ x ∂μ, Tendsto (fun N : ℝ≥0 => A T N X P f g x) atTop (𝓝 (h' x)) := by
    filter_upwards [hh'] with x hx
    rw [show (fun N : ℝ≥0 => A T N X P f g x)
        = fun N : ℝ≥0 => A T ((Nat.floor N : ℕ) : ℝ≥0) X P f g x from by
      funext N; exact A_floor T N X P f g x]
    exact tendsto_floor_iff.mpr hx
  refine ⟨h', hmem', ?_⟩
  refine ⟨hae', ?_⟩
  refine (hconv.comp tendsto_nat_floor_atTop_NNReal).congr' ?_
  filter_upwards with N
  show eLpNorm ((fun x => A T ((Nat.floor N : ℕ) : ℝ≥0) X P f g x) - h') p μ
      = eLpNorm ((fun x => A T N X P f g x) - h') p μ
  rw [show ((fun x => A T ((Nat.floor N : ℕ) : ℝ≥0) X P f g x) - h')
      = ((fun x => A T N X P f g x) - h') from by
    congr 1
    funext x
    exact (A_floor T N X P f g x).symm]

/-! ### Elementary facts about the exponents -/

lemma one_le_of_inv_le_one {p : ℝ≥0∞} (hp : p⁻¹ ≤ 1) : 1 ≤ p := ENNReal.inv_le_one.mp hp

lemma ne_zero_of_inv_add_eq {p₁ p₂ p : ℝ≥0∞} (h₁ : 1 < p₁) (h₂ : 1 < p₂)
    (h : p₁⁻¹ + p₂⁻¹ = p⁻¹) : p ≠ 0 := by
  intro hp0
  have hfin : p₁⁻¹ + p₂⁻¹ < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨ENNReal.inv_lt_top.mpr (lt_trans zero_lt_one h₁),
      ENNReal.inv_lt_top.mpr (lt_trans zero_lt_one h₂)⟩
  rw [hp0, ENNReal.inv_zero] at h
  exact hfin.ne h

lemma ne_top_of_inv_add_eq {p₁ p₂ p : ℝ≥0∞} (h₁ : p₁ < ⊤) (h₂ : p₂ < ⊤)
    (h : p₁⁻¹ + p₂⁻¹ = p⁻¹) : p ≠ ⊤ := by
  intro hpT
  rw [hpT, ENNReal.inv_top] at h
  have h1 : p₁⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.inv_eq_zero]
    exact h₁.ne
  exact h1 (le_antisymm (h ▸ le_self_add) bot_le)
