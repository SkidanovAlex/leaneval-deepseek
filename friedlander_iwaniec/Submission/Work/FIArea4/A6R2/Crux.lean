/-
# Area 4 (round 6): the crux `ExpBound6` from its two analytic inputs

`ExpBound6` (the variance half of *FI* §15 for the ratio symbol `(z₂/z₁|d)`, with the `τ³` energy
and the `(log N+1)^4` budget of Proposition 14.1) is assembled here from

* `pD6Stratum` — the per-modulus `e`-stratified class Cauchy–Schwarz (*FI* (15.1)–(15.2));
* `strUvarSum6` — the dyadic summation of the stratum class variances against Proposition 14.1,
  whose `τ³` energy absorbs the whole `Σ_{e|d}` stratification.

The assembly is the round-6 analogue of `Work.FIArea4.assemble_viaMobius` (the frozen assembly of
`S15expSum_bound`): the reindexing `expSum6 = Σ_d pD6 d`, the pointwise bound, the pointwise AM–GM
`√a√b ≤ (a+b)/2` over the divisor pairs, the `d = e·d'` reindexing
(`Work.FIArea4.S15EG_sum_divisors_Icc_filter`), the companion `S15strV = S15strU(-t)`
(`Work.FIArea4.S15EG_strV_eq_strU_neg`), and the diagonal correction

  `Σ_{d ≤ Y} 2 Σ_{z ∈ boxN} ‖β z‖² = 2 Y Σ_{z ∈ boxN} ‖β z‖² ≤ C (log N+1)^4 · S15Br6 · A6Ener3`

(no logarithm is needed: `Y = ⌈N/(X2^j)⌉+1 ≤ N/X + 2 ≤ 3 (log N+1)^4 S15Br6` because
`S15Br6 ≥ X^{-1/2}N ≥ N/X` and `S15Br6 ≥ 1`).
-/
import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
-- (the module `Submission.Work.FIArea4.S15EvarG_filtered_sum_le`, which used to supply the two
-- helper lemmas below, was removed by the frozen-chain agents; its content is re-proved in the
-- two dedicated modules imported here.)
import Submission.Work.FIArea4.S15EG_strV_eq_strU_neg
import Submission.Work.FIArea4.S15EG_sum_divisors_Icc_filter
import Submission.Work.FIArea4.S15EG_sum_sum_sqrt_mul_sqrt_le

namespace Work.FIArea4
namespace A6R2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary bracketing facts -/

lemma S15Br6_nonneg (Pa : Work.FITop.Params) (X : ℕ) : 0 ≤ S15Br6 Pa X := by
  unfold S15Br6
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h1 : 0 ≤ (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N :=
    mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h2 : 0 ≤ Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)
  have h3 : 0 ≤ Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) := Real.rpow_nonneg hN0 _
  linarith

/-- The first term `X^{-1/2}N` of the round-6 bracket is dominated by the bracket. -/
lemma first_term_le_Br (Pa : Work.FITop.Params) (X : ℕ) :
    (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N ≤ S15Br6 Pa X := by
  unfold S15Br6
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have h2 : 0 ≤ Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)
  have h3 : 0 ≤ Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) := Real.rpow_nonneg hN0 _
  linarith

/-- `X^{-1/2} = 1/√X`. -/
lemma rpow_neg_half_eq (X : ℕ) (hX : 1 ≤ X) :
    (X : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (X : ℝ) := by
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hne : (-(1 : ℝ) / 2) = -(1 / 2) := by norm_num
  rw [hne, Real.rpow_neg hX0, Real.rpow_div_two_eq_sqrt (1 : ℝ) hX0, Real.rpow_one, one_div]

/-- `N/X ≤ X^{-1/2}N` for `1 ≤ X`, hence `N/X ≤ S15Br6`. -/
lemma N_div_X_le_Br (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X) :
    Pa.N / (X : ℝ) ≤ S15Br6 Pa X := by
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hsqrtX : Real.sqrt (X : ℝ) ≤ (X : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨le_of_lt hX0, by nlinarith⟩
  have h1 : (1 : ℝ) / (X : ℝ) ≤ (X : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [rpow_neg_half_eq X hX]
    exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hX0) hsqrtX
  have h2 : Pa.N / (X : ℝ) ≤ (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N := by
    rw [div_eq_mul_inv]
    have h3 : Pa.N * (1 / (X : ℝ)) ≤ Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left h1 hN0
    have h4 : (X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N = Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2) := by ring
    rw [h4]
    simpa [one_div] using h3
  exact le_trans h2 (first_term_le_Br Pa X)

/-- `1 ≤ S15Br6 Pa X` for `1 ≤ X ≤ N^{1/9}`. -/
lemma one_le_Br (Pa : Work.FITop.Params) (X : ℕ) (hX : 1 ≤ X)
    (hX9 : (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9)) : 1 ≤ S15Br6 Pa X := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXN : (X : ℝ) ≤ Pa.N :=
    le_trans hX9 (Real.rpow_le_self_of_one_le hN1 (by norm_num))
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ Pa.N / (X : ℝ) := by
    rw [le_div_iff₀ hX0, one_mul]; exact hXN
  exact le_trans h1 (N_div_X_le_Br Pa X hX)

/-! ## 2. The reindexing `expSum6ng = Σ_d pD6ng d` -/

/-- The unfiltered round-6 per-modulus sum vanishes for `d ≤ X`. -/
lemma pD6ng_eq_zero_of_le (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (h : d ≤ X) : pD6ng Pa X j d β ℓ u t = 0 := by
  unfold pD6ng
  refine Finset.sum_eq_zero (fun z1 _ => Finset.sum_eq_zero (fun z2 _ => ?_))
  rw [if_neg]
  intro hh
  exact absurd hh.1 (not_lt.mpr h)

/-- `expSum6ng` is the sum of its per-modulus pieces. -/
theorem expSum6ng_eq_sum_pD (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) :
    expSum6ng Pa X j β ℓ u t = ∑ d ∈ Finset.Icc 1 (S15Y Pa X j), pD6ng Pa X j d β ℓ u t := by
  classical
  let G : S15Id → ℂ := fun p =>
    (if X < p.2 ∧ 4 * p.2 ∣ Work.FIPlan.absDelta p.1.1 p.1.2 ∧
        0 < Work.FIPlan.absDelta p.1.1 p.1.2
      then coef6 β p * S15theta ℓ p.1.1 p.1.2 * S15phase X j u t p else 0)
  have h1 : expSum6ng Pa X j β ℓ u t
      = ∑ p ∈ (Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ Finset.Icc 1 (S15Y Pa X j), G p := by
    unfold expSum6ng ngset6
    rw [Finset.sum_filter]
  have h2 : (∑ p ∈ (Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ Finset.Icc 1 (S15Y Pa X j), G p)
      = ∑ d ∈ Finset.Icc 1 (S15Y Pa X j), pD6ng Pa X j d β ℓ u t := by
    rw [Finset.sum_product, Finset.sum_product, Work.FIArea4.sum_comm3]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold pD6ng
    rfl
  exact h1.trans h2

/-! ## 3. The diagonal correction -/

/-- `S15Y Pa X j ≤ N/X + 2`. -/
lemma S15Y_le (Pa : Work.FITop.Params) (X j : ℕ) (hX : 1 ≤ X) :
    (S15Y Pa X j : ℝ) ≤ Pa.N / (X : ℝ) + 2 := by
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hden : (0 : ℝ) < (X : ℝ) * (2 : ℝ) ^ j := mul_pos hX0 (pow_pos (by norm_num) j)
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ Pa.N / ((X : ℝ) * (2 : ℝ) ^ j) from
      le_of_lt (div_pos (by linarith [Pa.hN1]) hden))
  have hY : (S15Y Pa X j : ℝ) = ((⌈Pa.N / ((X : ℝ) * (2 : ℝ) ^ j)⌉₊ : ℕ) : ℝ) + 1 := by
    unfold S15Y; push_cast; ring
  rw [hY]
  have h1 : ((⌈Pa.N / ((X : ℝ) * (2 : ℝ) ^ j)⌉₊ : ℕ) : ℝ)
      < Pa.N / ((X : ℝ) * (2 : ℝ) ^ j) + 1 := hceil
  have hle : Pa.N / ((X : ℝ) * (2 : ℝ) ^ j) ≤ Pa.N / (X : ℝ) := by
    apply div_le_div_of_nonneg_left (by linarith [Pa.hN1]) hX0
    nlinarith [h2j]
  linarith

/-- **The diagonal correction** of the assembly. -/
lemma diag_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (X j : ℕ) (φ : ℝ) (β : GaussianInt → ℂ),
      IsPrimBoxCoeff Pa φ β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
      (S15Y Pa X j : ℝ) * (∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z))
        ≤ C * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by
  refine ⟨16, by norm_num, ?_⟩
  intro Pa X j φ β hβ hX hX9
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hL1 : (1 : ℝ) ≤ Real.log Pa.N + 1 := by
    have := Real.log_nonneg hN1; linarith
  have hL4 : (1 : ℝ) ≤ (Real.log Pa.N + 1) ^ 4 := one_le_pow₀ hL1
  have hE : (∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z)) ≤ A6Ener3 Pa β := by
    unfold A6Ener3
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases hz0 : β z = 0
    · rw [hz0]; simp
    · have hbox := hβ.inPolarBox hz0
      have hodd : Odd z.re := hbox.1.1
      have hre : z.re ≠ 0 := fun h => absurd (h ▸ hodd) (by decide)
      have hcard : 1 ≤ z.re.natAbs.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (fun h =>
          hre (Int.natAbs_eq_zero.mp h))⟩
      have h3 : (1 : ℝ) ≤ ((z.re.natAbs.divisors.card : ℕ) : ℝ) := by exact_mod_cast hcard
      have h1 : (1 : ℝ) ≤ ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) := one_le_pow₀ h3
      calc Complex.normSq (β z) = 1 * Complex.normSq (β z) := by ring
        _ ≤ ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z) :=
            mul_le_mul_of_nonneg_right h1 (Complex.normSq_nonneg _)
  have hEnn : 0 ≤ A6Ener3 Pa β := A6Ener3_nonneg Pa β
  have hSn : 0 ≤ ∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z) :=
    Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _)
  have hBr : Pa.N / (X : ℝ) ≤ S15Br6 Pa X := N_div_X_le_Br Pa X hX
  have hBr1 : (1 : ℝ) ≤ S15Br6 Pa X := one_le_Br Pa X hX hX9
  have hYb : (S15Y Pa X j : ℝ) ≤ 3 * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X := by
    have hYs := S15Y_le Pa X j hX
    have h2 : (2 : ℝ) ≤ 2 * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X := by
      have h3 : (2 : ℝ) * 1 * 1 ≤ 2 * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL4 (by norm_num)) hBr1
          (by norm_num) (by positivity)
      linarith
    nlinarith [hYs, hBr, hL4, hBr1]
  have hBnn : 0 ≤ (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X :=
    mul_nonneg (by positivity) (S15Br6_nonneg Pa X)
  calc (S15Y Pa X j : ℝ) * (∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z))
      ≤ (3 * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X) * A6Ener3 Pa β :=
        mul_le_mul hYb hE hSn (by positivity)
    _ = 3 * ((Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β) := by ring
    _ ≤ 16 * ((Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β) := by
        have hnn : (0 : ℝ) ≤ (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β :=
          mul_nonneg hBnn hEnn
        nlinarith
    _ = 16 * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by ring

/-! ## 4. The assembly -/

/-- **The unfiltered crux from its two inputs.** -/
theorem ExpBound6ng_of_inputs (hD : pD6ngStratum) (hE : strUvarSum6) : ExpBound6ng := by
  obtain ⟨Ce, x0e, hCe, hE⟩ := hE
  obtain ⟨Cd, hCd, hDia⟩ := diag_bound
  refine ⟨2 * Ce + 2 * Cd, x0e, by positivity, ?_⟩
  intro Pa hx0 X j φ β ℓ u t hβ hX hX9
  set S : Finset ℕ := (Finset.Icc 1 (S15Y Pa X j)).filter (fun d => X < d) with hSdef
  have hSsub : S ⊆ Finset.Icc 1 (S15Y Pa X j) := by
    rw [hSdef]; exact Finset.filter_subset _ _
  have hSn : 0 ≤ ∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z) :=
    Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _)
  -- ### 1. the two stratum-variance sums
  have hU : (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
        ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
          EvarG (Work.FITop.radN Pa) (4 * d') (S15strU β u t ℓ e))
      ≤ Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β :=
    hE Pa hx0 X j φ β ℓ u t hβ hX hX9
  have hV : (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
        ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
          EvarG (Work.FITop.radN Pa) (4 * d') (S15strV β u t ℓ e))
      ≤ Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by
    have h := hE Pa hx0 X j φ β ℓ u (-t) hβ hX hX9
    have heq : (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
          ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
            EvarG (Work.FITop.radN Pa) (4 * d') (S15strV β u t ℓ e))
        = (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
          ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
            EvarG (Work.FITop.radN Pa) (4 * d') (S15strU β u (-t) ℓ e)) := by
      refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun d' _ => ?_))
      rw [Work.FIArea4.S15EG_strV_eq_strU_neg]
    rw [heq]; exact h
  -- ### 2. the main (stratum) term
  have hmain : (∑ d ∈ S, ∑ e ∈ d.divisors,
        Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strU β u t ℓ e))
        * Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strV β u t ℓ e)))
      ≤ Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by
    rw [hSdef]
    rw [Work.FIArea4.S15EG_sum_divisors_Icc_filter X (S15Y Pa X j) (fun d' e =>
      Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * d') (S15strU β u t ℓ e))
      * Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * d') (S15strV β u t ℓ e)))]
    refine le_trans (Work.FIArea4.S15EG_sum_sum_sqrt_mul_sqrt_le (Finset.Icc 1 (S15Y Pa X j))
      (fun e => (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'))
      (fun e d' => EvarG (Work.FITop.radN Pa) (4 * d') (S15strU β u t ℓ e))
      (fun e d' => EvarG (Work.FITop.radN Pa) (4 * d') (S15strV β u t ℓ e))
      (fun e _ d' _ => EvarG_nonneg _ _ _) (fun e _ d' _ => EvarG_nonneg _ _ _)) ?_
    calc (1 / 2) * ((∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
            ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
              EvarG (Work.FITop.radN Pa) (4 * d') (S15strU β u t ℓ e))
          + (∑ e ∈ Finset.Icc 1 (S15Y Pa X j),
            ∑ d' ∈ (Finset.Icc 1 (S15Y Pa X j / e)).filter (fun d' => X < e * d'),
              EvarG (Work.FITop.radN Pa) (4 * d') (S15strV β u t ℓ e)))
        ≤ (1 / 2) * (Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β
            + Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β) :=
          mul_le_mul_of_nonneg_left (add_le_add hU hV) (by norm_num)
      _ = Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by ring
  -- ### 3. the diagonal
  have hcard : (S.card : ℝ) ≤ (S15Y Pa X j : ℝ) := by
    have h1 : S.card ≤ (Finset.Icc 1 (S15Y Pa X j)).card := Finset.card_le_card hSsub
    have h2 : (Finset.Icc 1 (S15Y Pa X j)).card = S15Y Pa X j := by
      rw [Nat.card_Icc]; omega
    rw [h2] at h1
    exact_mod_cast h1
  have hdiag : (S.card : ℝ) * (∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z))
      ≤ Cd * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β :=
    le_trans (mul_le_mul_of_nonneg_right hcard hSn) (hDia Pa X j φ β hβ hX hX9)
  -- ### 4. the pointwise per-modulus bound
  have hpt : ∀ d ∈ S, ‖pD6ng Pa X j d β ℓ u t‖
      ≤ 2 * (∑ e ∈ d.divisors,
          Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strU β u t ℓ e))
          * Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strV β u t ℓ e)))
        + 2 * ∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (hSsub hd)).1
    have h := hD Pa X j d φ β ℓ u t hβ hd1
    simpa only [Complex.normSq_eq_norm_sq] using h
  -- ### 5. `expSum6` as a sum over `S`
  have hexp : expSum6ng Pa X j β ℓ u t = ∑ d ∈ S, pD6ng Pa X j d β ℓ u t := by
    rw [expSum6ng_eq_sum_pD, hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    by_cases h : X < d
    · rw [if_pos h]
    · rw [if_neg h]
      exact pD6ng_eq_zero_of_le Pa X j d β ℓ u t (by omega)
  -- ### 6. the chain
  rw [hexp]
  calc ‖∑ d ∈ S, pD6ng Pa X j d β ℓ u t‖
      ≤ ∑ d ∈ S, ‖pD6ng Pa X j d β ℓ u t‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ S, (2 * (∑ e ∈ d.divisors,
          Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strU β u t ℓ e))
          * Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strV β u t ℓ e)))
        + 2 * ∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z)) := Finset.sum_le_sum hpt
    _ = 2 * (∑ d ∈ S, ∑ e ∈ d.divisors,
          Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strU β u t ℓ e))
          * Real.sqrt (EvarG (Work.FITop.radN Pa) (4 * (d / e)) (S15strV β u t ℓ e)))
        + 2 * ((S.card : ℝ) * ∑ z ∈ Work.FITop.boxN Pa, Complex.normSq (β z)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ 2 * (Ce * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β)
        + 2 * (Cd * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β) :=
        add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num))
          (mul_le_mul_of_nonneg_left hdiag (by norm_num))
    _ = (2 * Ce + 2 * Cd) * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by ring



/-! ## 5. The filtered crux from the unfiltered crux and the coprimality removal -/

/-- **The crux from the unfiltered crux and the removal of the pair coprimality.** -/
theorem ExpBound6_of_ng_and_removal (hng : ExpBound6ng) (hrm : Removal6) : ExpBound6 := by
  obtain ⟨C₁, x₁, hC₁, hng⟩ := hng
  obtain ⟨C₂, x₂, hC₂, hrm⟩ := hrm
  refine ⟨C₁ + C₂, max x₁ x₂, by positivity, ?_⟩
  intro Pa hx X j φ β ℓ u t hβ hX hX9
  have h1 := hng Pa (le_trans (le_max_left x₁ x₂) hx) X j φ β ℓ u t hβ hX hX9
  have h2 := hrm Pa (le_trans (le_max_right x₁ x₂) hx) X j φ β ℓ u t hβ hX hX9
  have hsplit : expSum6 Pa X j β ℓ u t
      = expSum6ng Pa X j β ℓ u t + (expSum6 Pa X j β ℓ u t - expSum6ng Pa X j β ℓ u t) := by
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  calc ‖expSum6ng Pa X j β ℓ u t‖ + ‖expSum6 Pa X j β ℓ u t - expSum6ng Pa X j β ℓ u t‖
      ≤ C₁ * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β
        + C₂ * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := add_le_add h1 h2
    _ = (C₁ + C₂) * (Real.log Pa.N + 1) ^ 4 * S15Br6 Pa X * A6Ener3 Pa β := by ring

end

end A6R2

end Work.FIArea4
