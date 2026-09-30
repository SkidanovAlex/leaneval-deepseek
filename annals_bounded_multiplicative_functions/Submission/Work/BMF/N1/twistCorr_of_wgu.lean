import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `k = 0` conversion: weak Gowers uniformity norm of order `1` is the
Matomäki–Radziwiłł twisted correlation (`ψ = 1`, `T₀ = 0`)

For `k = 0` the weak Gowers uniformity norm of `g : ℤ → ℂ` is a supremum over
constant polynomials only, hence

`weakGowersUniformityNorm 0 y H g = H⁻¹ ‖∑_{n ∈ [⌈y⌉, ⌊y+H⌋] ∩ ℤ} g n‖`   (`H > 0`).

Consequently, for `f : ℕ → ℂ` and `H > 0`,

`‖∑_{n ∈ ℕ ∩ [y, y+H]} f n‖ = H * weakGowersUniformityNorm 0 y H (fun z ↦ f ⌊z⌋₊)`,

so the hypothesis `∫_X^{2X} ‖f‖_{u¹[x,x+H]} ≥ ηX` is exactly the hypothesis
`TwistCorr f 1 0 X H η` of the Matomäki–Radziwiłł node.
-/

namespace Work.BMF.N1

open Polynomial Finset Real Complex BoundedMultiplicativeFunctions
open Work.BMF

/-- `Finset.Icc m M` on `ℕ` as a shifted range. -/
lemma twistCorr_Icc_nat_eq_map_range (m M : ℕ) :
    Finset.Icc m M = (Finset.range (M + 1 - m)).map (addLeftEmbedding m) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
  constructor
  · rintro ⟨hmx, hxM⟩
    exact ⟨x - m, by omega, by omega⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨by omega, ?_⟩
    have h1 : m + a < m + (M + 1 - m) := by omega
    rw [Nat.add_sub_of_le (by omega)] at h1
    omega

/-- The weak Gowers uniformity norm of order `0` (i.e. the `u¹` norm) is the
normalised modulus of the plain sum over the interval. -/
lemma twistCorr_wgu_zero_eq (g : ℤ → ℂ) (y H : ℝ) (hH : 0 < H) :
    weakGowersUniformityNorm 0 y H g = (1 / H) * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, g n‖ := by
  classical
  have hconst : ∀ (P : ℝ[X]), P ∈ degreeLE ℝ (0:ℕ) →
      (1 / H * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, g n * cexp (2 * π * I * -(P.eval (n:ℝ)))‖)
        = (1 / H) * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, g n‖ := by
    intro P hP
    have hdeg : P.degree ≤ 0 := (Polynomial.mem_degreeLE).1 hP
    obtain ⟨c, rfl⟩ : ∃ c, P = Polynomial.C c := ⟨_, Polynomial.eq_C_of_degree_le_zero hdeg⟩
    have hz : ‖cexp (2 * π * I * -(c:ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * (π:ℂ) * Complex.I * -(c:ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero]
    simp only [Polynomial.eval_C]
    rw [← Finset.sum_mul, norm_mul, hz, mul_one]
  have hc_nonneg : 0 ≤ (1 / H) * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, g n‖ := by
    have h1 : (0:ℝ) ≤ 1/H := div_nonneg zero_le_one (le_of_lt hH)
    exact mul_nonneg h1 (norm_nonneg _)
  have hbdd : BddAbove (Set.range fun P : ℝ[X] =>
      ⨆ (_ : P ∈ degreeLE ℝ (0:ℕ)),
        1 / H * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, g n * cexp (2 * π * I * -(P.eval (n:ℝ)))‖) := by
    refine ⟨(1 / H) * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, g n‖, ?_⟩
    rintro x ⟨P, rfl⟩
    simp only []
    rw [ciSup_eq_ite]
    split_ifs with hP
    · rw [hconst P hP]
    · rw [Real.sSup_empty]; exact hc_nonneg
  rw [weakGowersUniformityNorm]
  have : Nonempty ℝ[X] := ⟨0⟩
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun P => ?_
    rw [ciSup_eq_ite]
    split_ifs with hP
    · rw [hconst P hP]
    · rw [Real.sSup_empty]; exact hc_nonneg
  · have h0mem : (0:ℝ[X]) ∈ degreeLE ℝ (0:ℕ) := by
      rw [Polynomial.mem_degreeLE, Polynomial.degree_zero]; exact bot_le
    have hval : (⨆ (_ : (0:ℝ[X]) ∈ degreeLE ℝ (0:ℕ)),
        1 / H * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋,
          g n * cexp (2 * π * I * -(((0:ℝ[X])).eval (n:ℝ)))‖)
        = (1/H) * ‖∑ n ∈ Finset.Icc ⌈y⌉ ⌊y+H⌋, g n‖ := by
      rw [ciSup_eq_ite, dite_eq_left h0mem]
      exact hconst 0 h0mem
    rw [← hval]
    exact le_ciSup hbdd 0

/-- Sums of an arithmetic function over the integer interval `[⌈y⌉, ⌊y+H⌋]` agree with
sums over `ℕ ∩ [y, y+H]`, for `y ≥ 0`, `H ≥ 0`. -/
lemma twistCorr_sum_Icc_int_eq_sum_natIcc (f : ℕ → ℂ) {y H : ℝ} (hy : 0 ≤ y) (hH : 0 ≤ H) :
    ∑ n ∈ Finset.Icc ⌈y⌉ ⌊y + H⌋, f ⌊n⌋₊ = ∑ n ∈ natIcc y (y + H), f n := by
  have hA : 0 ≤ ⌈y⌉ := Int.ceil_nonneg hy
  have hyH : 0 ≤ y + H := add_nonneg hy hH
  have hB : 0 ≤ ⌊y + H⌋ := (Int.floor_nonneg).2 hyH
  have hAB : ⌈y⌉ ≤ ⌊y + H⌋ + 1 := by
    rw [Int.ceil_le]
    have := Int.lt_floor_add_one (y + H)
    push_cast
    linarith
  have hnat : (⌊y + H⌋ + 1 - ⌈y⌉).toNat = ⌊y + H⌋₊ + 1 - ⌈y⌉₊ := by
    apply Nat.cast_injective (R := ℤ)
    have hBcast : ((⌊y + H⌋₊ : ℕ) : ℤ) = ⌊y + H⌋ := by
      rw [← Int.floor_toNat (y + H), Int.toNat_of_nonneg hB]
    have hAcast : ((⌈y⌉₊ : ℕ) : ℤ) = ⌈y⌉ := by
      rw [← Int.ceil_toNat y, Int.toNat_of_nonneg hA]
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ⌊y + H⌋ + 1 - ⌈y⌉)]
    rw [Nat.cast_sub (by omega : ⌈y⌉₊ ≤ ⌊y + H⌋₊ + 1), Nat.cast_add, Nat.cast_one, hBcast, hAcast]
  rw [Int.Icc_eq_finset_map, Finset.sum_map, natIcc, twistCorr_Icc_nat_eq_map_range,
    Finset.sum_map, hnat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  congr 1
  change (⌈y⌉ + (k:ℤ)).toNat = ⌈y⌉₊ + k
  rw [Int.toNat_add hA (Int.natCast_nonneg k), Int.toNat_natCast, Int.ceil_toNat]

theorem twistCorr_of_wgu (f : ℕ → ℂ) (X H η : ℝ) (hX : 1 ≤ X) (hH : 0 < H)
    (h : ∫ x in X..(2 * X), weakGowersUniformityNorm 0 x H (fun z : ℤ ↦ f ⌊z⌋₊) ≥ η * X) :
    TwistCorr f (fun _ ↦ 1) 0 X H η := by
  rw [TwistCorr]
  have hpt : ∀ y : ℝ, 0 ≤ y →
      ‖∑ n ∈ natIcc y (y + H), f n * (fun _ ↦ 1) n * (n : ℂ) ^ (-(Complex.I * (0:ℝ)))‖
        = H * weakGowersUniformityNorm 0 y H (fun z : ℤ => f ⌊z⌋₊) := by
    intro y hy
    have h1 : (∑ n ∈ natIcc y (y + H), f n * (fun _ ↦ 1) n * (n : ℂ) ^ (-(Complex.I * (0:ℝ))))
        = ∑ n ∈ natIcc y (y + H), f n := by
      apply Finset.sum_congr rfl
      intro n _
      simp
    rw [h1, ← twistCorr_sum_Icc_int_eq_sum_natIcc f hy (le_of_lt hH),
      twistCorr_wgu_zero_eq (fun z : ℤ => f ⌊z⌋₊) y H hH]
    rw [← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hH), one_mul]
  have hX0 : (0:ℝ) ≤ X := by linarith
  have hle2 : X ≤ 2 * X := by linarith
  have hint : ∫ y in X..(2 * X),
        ‖∑ n ∈ natIcc y (y + H), f n * (fun _ ↦ 1) n * (n : ℂ) ^ (-(Complex.I * (0:ℝ)))‖
      = ∫ y in X..(2 * X), H * weakGowersUniformityNorm 0 y H (fun z : ℤ => f ⌊z⌋₊) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hle2] at hy
    exact hpt y (le_trans hX0 hy.1)
  rw [hint, intervalIntegral.integral_const_mul]
  calc η * H * X = H * (η * X) := by ring
    _ ≤ H * ∫ y in X..(2 * X), weakGowersUniformityNorm 0 y H (fun z : ℤ => f ⌊z⌋₊) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hH)

end Work.BMF.N1
