import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.profHatCube_moments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 1. The central-binomial pigeonhole -/

/-- `4^M ≤ (2M+1)·C(2M,M)`: the largest of the `2M+1` binomial coefficients of `(1+1)^{2M}`
is the middle one, and their sum is `2^{2M} = 4^M`. -/
lemma four_pow_le_choose_mul (M : ℕ) : 4 ^ M ≤ (2 * M + 1) * (2 * M).choose M := by
  have hsum : 2 ^ (2 * M) = ∑ k ∈ Finset.range (2 * M + 1), (2 * M).choose k :=
    (Nat.sum_range_choose (2 * M)).symm
  rw [show (4 : ℕ) ^ M = 2 ^ (2 * M) by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]]
  rw [hsum]
  calc ∑ k ∈ Finset.range (2 * M + 1), (2 * M).choose k
      ≤ ∑ _k ∈ Finset.range (2 * M + 1), (2 * M).choose M := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hM2 : (2 * M) / 2 = M := by omega
        have h := Nat.choose_le_middle k (2 * M)
        rwa [hM2] at h
    _ = (2 * M + 1) * (2 * M).choose M := by
        rw [Finset.sum_const, Finset.card_range]
        simp

/-! ## 2. The lower Wallis bound for `∫ ζ^{2M}` -/

/-- **The lower bound `1/(2M+1) ≤ ∫_ℝ ζ^{2M}`** for the 1D cosine profile `ζ = zeta1d`
(`cos(π·)` on `|·| ≤ 1/2`, zero outside).  The exact value is `C(2M,M)/4^M`
(`Work.SmallBoxTBWord.zeta1d_pow_two_mul_integral_eq_choose`), and `four_pow_le_choose_mul`
gives `C(2M,M)/4^M ≥ 1/(2M+1)`. -/
lemma zeta1d_pow_two_mul_integral_ge (M : ℕ) (hM : 1 ≤ M) :
    1 / (2 * (M : ℝ) + 1) ≤ ∫ u : ℝ, zeta1d u ^ (2 * M) := by
  rw [Work.SmallBoxTBWord.zeta1d_pow_two_mul_integral_eq_choose M hM]
  have hnat : 4 ^ M ≤ (2 * M + 1) * (2 * M).choose M := four_pow_le_choose_mul M
  have hpos4 : (0 : ℝ) < 4 ^ M := by positivity
  have hR : (4 : ℝ) ^ M ≤ (2 * (M : ℝ) + 1) * ((2 * M).choose M : ℝ) := by
    exact_mod_cast hnat
  rw [le_div_iff₀ hpos4]
  have h1 : (1 : ℝ) / (2 * (M : ℝ) + 1) * (4 : ℝ) ^ M ≤ ((2 * M).choose M : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 1))
    rwa [show (1 : ℝ) / (2 * (M : ℝ) + 1) * ((2 * (M : ℝ) + 1) * ((2 * M).choose M : ℝ))
        = ((2 * M).choose M : ℝ) from by field_simp] at h
  linarith [h1]

/-! ## 3. The normalisation constant of the cube bump -/

/-- `chiSmall M = chiSmallBase M / √(∫ chiSmallBase²)`, `phiC M = ζ^M`, so
`∫_ℝ phiC M ² = ∫_ℝ ζ^{2M}`. -/
private lemma integral_phiC_sq_eq (M : ℕ) :
    (∫ x : ℝ, phiC M x ^ 2) = ∫ x : ℝ, zeta1d x ^ (2 * M) := by
  apply integral_congr_ae
  filter_upwards with x
  show phiC M x ^ 2 = zeta1d x ^ (2 * M)
  rw [phiC]
  calc (zeta1d x ^ M) ^ 2 = zeta1d x ^ (M * 2) := by rw [pow_mul]
    _ = zeta1d x ^ (2 * M) := by rw [Nat.mul_comm]

/-- **The normalisation integral is at least `1/(2M+1)³`.** -/
lemma chiSmallNormSq_ge (M : ℕ) (hM : 1 ≤ M) :
    ((2 * (M : ℝ) + 1) ^ 3)⁻¹ ≤ chiSmallNormSq M := by
  have hA : 1 / (2 * (M : ℝ) + 1) ≤ ∫ x : ℝ, phiC M x ^ 2 := by
    rw [integral_phiC_sq_eq M]
    exact zeta1d_pow_two_mul_integral_ge M hM
  rw [chiSmallNormSq_eq]
  have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (2 * (M : ℝ) + 1)) hA 3
  rwa [show (1 / (2 * (M : ℝ) + 1)) ^ 3 = ((2 * (M : ℝ) + 1) ^ 3)⁻¹ from by
    rw [one_div, inv_pow]] at h3

/-- **The normalisation factor of the cube bump is at most `(2M+1)^{3/2}`.** -/
lemma chiSmallNormFactor_sq_le (M : ℕ) (hM : 1 ≤ M) :
    (chiSmallNormFactor M) ^ 2 ≤ (2 * (M : ℝ) + 1) ^ 3 := by
  have hNpos : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
  have hNge : ((2 * (M : ℝ) + 1) ^ 3)⁻¹ ≤ chiSmallNormSq M := chiSmallNormSq_ge M hM
  have h3pos : 0 < (2 * (M : ℝ) + 1) ^ 3 := by positivity
  have hNinv : (chiSmallNormFactor M) ^ 2 = (chiSmallNormSq M)⁻¹ := by
    rw [chiSmallNormFactor, inv_pow, Real.sq_sqrt hNpos.le]
  rw [hNinv, inv_le_comm₀ hNpos h3pos]
  exact hNge

/-- `cSmall` is the same constant as `chiSmallNormFactor`. -/
lemma cSmall_eq_chiSmallNormFactor (M : ℕ) : cSmall M = chiSmallNormFactor M := rfl

/-- **`(cSmall M)² ≤ (2M+1)³`.** -/
lemma cSmall_sq_le (M : ℕ) (hM : 1 ≤ M) : (cSmall M) ^ 2 ≤ (2 * (M : ℝ) + 1) ^ 3 := by
  rw [cSmall_eq_chiSmallNormFactor]
  exact chiSmallNormFactor_sq_le M hM

/-! ## 4. The explicit partial derivatives of the cube bump -/

/-- The explicit `k`-th partial derivative `pcD M k` of the cube bump vanishes as soon as one
coordinate of `z` has `|z_j| > 1/2` (the support is the unit cube, not merely the unit ball). -/
lemma pcD_eq_zero_of_half_lt_abs {M : ℕ} (hM : 1 ≤ M) (k : Fin 3) {z : E3} {j : Fin 3}
    (hj : 1 / 2 < |z.ofLp j|) : pcD M k z = 0 := by
  rw [pcD]
  by_cases hjk : j = k
  · subst hjk
    rw [phiCDeriv_eq_zero_of_half_le (le_of_lt hj), mul_zero, zero_mul]
  · have hz : phiC M (z.ofLp j) = 0 := phiC_eq_zero_of_half_le hM (le_of_lt hj)
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩) hz]
    ring

/-- **Sup bound for the explicit partial derivatives**: `|pcD M k z| ≤ cSmall M · Mπ`. -/
lemma pcD_abs_le {M : ℕ} (k : Fin 3) (z : E3) :
    |pcD M k z| ≤ cSmall M * ((M : ℝ) * Real.pi) := by
  have hc : 0 ≤ chiSmallNormFactor M := chiSmallNormFactor_nonneg M
  have hder : |phiCDeriv M (z.ofLp k)| ≤ (M : ℝ) * Real.pi := abs_phiCDeriv_le M _
  have hprod : |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_phiC_le_one M _)
  have hb : 0 ≤ (M : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg M) Real.pi_pos.le
  have h1 : chiSmallNormFactor M * |phiCDeriv M (z.ofLp k)|
      ≤ chiSmallNormFactor M * ((M : ℝ) * Real.pi) := mul_le_mul_of_nonneg_left hder hc
  have h2 : chiSmallNormFactor M * |phiCDeriv M (z.ofLp k)|
        * |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)|
      ≤ chiSmallNormFactor M * ((M : ℝ) * Real.pi) * 1 :=
    mul_le_mul h1 hprod (abs_nonneg _) (mul_nonneg hc hb)
  rw [pcD, cSmall_eq_chiSmallNormFactor, abs_mul, abs_mul, abs_of_nonneg hc]
  simpa using h2

/-- **Squared sup bound for the explicit partial derivatives.** -/
lemma pcD_sq_le {M : ℕ} (k : Fin 3) (z : E3) :
    (pcD M k z) ^ 2 ≤ (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 := by
  rw [← sq_abs (pcD M k z)]
  exact pow_le_pow_left₀ (abs_nonneg _) (pcD_abs_le k z) 2

/-! ## 5. The explicit moment bound and the diluteness threshold -/

/-- The explicit bound for the second moment of the cube profile at regularity `M`:
`(2π)⁻³ ∫ ‖p‖² (profHatCube M p)² ≤ cubeMomBound M`. -/
def cubeMomBound (M : ℕ) : ℝ := 3 * ((M : ℝ) * Real.pi) ^ 2 * (2 * (M : ℝ) + 1) ^ 3

lemma cubeMomBound_nonneg (M : ℕ) : 0 ≤ cubeMomBound M := by
  rw [cubeMomBound]
  have : (0 : ℝ) ≤ (M : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg M) Real.pi_pos.le
  positivity

/-- The explicit small scale `δ` attached to the moment bound `cubeMomBound M`: `s ≤ δ` forces
both moment criteria of the cube two-cut comparison at `C = 1/s`. -/
noncomputable def cubeSymScale (M : ℕ) : ℝ :=
  min (1 / 2) (min ((cubeMomBound M + 2)⁻¹) ((33 * (cubeMomBound M + 1))⁻¹))

/-- The explicit diluteness threshold `ε₀ = δ^{323}` for the cube two-cut comparison. -/
noncomputable def cubeSymEps0 (M : ℕ) : ℝ := (cubeSymScale M) ^ (323 : ℝ)

lemma cubeSymScale_pos (M : ℕ) : 0 < cubeSymScale M := by
  rw [cubeSymScale]
  refine lt_min (by norm_num) (lt_min ?_ ?_)
  · exact inv_pos.mpr (by linarith [cubeMomBound_nonneg M])
  · exact inv_pos.mpr (by linarith [cubeMomBound_nonneg M])

lemma cubeSymEps0_pos (M : ℕ) : 0 < cubeSymEps0 M :=
  Real.rpow_pos_of_pos (cubeSymScale_pos M) _

lemma cubeSymScale_le_half (M : ℕ) : cubeSymScale M ≤ 1 / 2 := min_le_left _ _

lemma cubeSymScale_le_mom2 (M : ℕ) : cubeSymScale M ≤ (cubeMomBound M + 2)⁻¹ :=
  le_trans (min_le_right _ _) (min_le_left _ _)

lemma cubeSymScale_le_mom1 (M : ℕ) : cubeSymScale M ≤ (33 * (cubeMomBound M + 1))⁻¹ :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- **The pure-real arithmetic of the two moment criteria.**  If `K₂` is at most the bound
`cubeMomBound M`, `K₁ ≤ 1 + K₂`, `0 < s ≤ cubeSymScale M` and `d ≤ 1/2`, then both criteria of
`symACube_fsKinCoeff_mix_scaled` hold at `C = 1/s`. -/
lemma cubeSymArith {K₁ K₂ s d : ℝ} (M : ℕ) (hK₂ : K₂ ≤ cubeMomBound M)
    (hK₁ : K₁ ≤ 1 + K₂) (hs0 : 0 < s) (hs : s ≤ cubeSymScale M) (hd : d ≤ 1 / 2) :
    K₁ ≤ 1 / s ∧ 8 * K₂ ≤ (1 - d) ^ 2 * (1 / s) ^ 2 := by
  have hKb : 0 ≤ cubeMomBound M := cubeMomBound_nonneg M
  have hpos1 : 0 < cubeMomBound M + 2 := by linarith
  have hpos33 : 0 < 33 * (cubeMomBound M + 1) := by linarith
  have hge1 : cubeMomBound M + 2 ≤ 1 / s := by
    have h := one_div_le_one_div_of_le hs0 (le_trans hs (cubeSymScale_le_mom2 M))
    simpa [one_div] using h
  have hge2 : 33 * (cubeMomBound M + 1) ≤ 1 / s := by
    have h := one_div_le_one_div_of_le hs0 (le_trans hs (cubeSymScale_le_mom1 M))
    simpa [one_div] using h
  constructor
  · linarith
  · have hsq : (33 * (cubeMomBound M + 1)) ^ 2 ≤ (1 / s) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hpos33) hge2 2
    have hquarter : (1 : ℝ) / 4 ≤ (1 - d) ^ 2 := by nlinarith
    have h2 : (1 / 4) * (33 * (cubeMomBound M + 1)) ^ 2 ≤ (1 - d) ^ 2 * (1 / s) ^ 2 :=
      mul_le_mul hquarter hsq (by positivity) (by positivity)
    have hkey : 8 * cubeMomBound M ≤ (1 / 4) * (33 * (cubeMomBound M + 1)) ^ 2 := by
      nlinarith [hKb, sq_nonneg (cubeMomBound M + 1), sq_nonneg (cubeMomBound M)]
    have hK₈ : 8 * K₂ ≤ 8 * cubeMomBound M := by linarith
    linarith

end Work.BoseFixB1S
