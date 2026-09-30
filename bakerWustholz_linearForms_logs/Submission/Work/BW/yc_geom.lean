import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Pure real-arithmetic core of `yc_geom`.  For `0 < ξ ≤ 1`, `0 ≤ T`, `0 ≤ S` and any
`r, J`, writing `ζ = ξ^{rJ} ∈ (0,1]`:
* `(⌊ξT^{(J)}⌋+1) ≥ ξT^{(J)} = ξζT` because `⌊x⌋ + 1 ≥ x`;
* `2⌊2S^{(J)}⌋+1 ≥ 4S^{(J)} − 1 = 4ζ^{-1}S − 1` because `⌊y⌋ > y − 1`;
* the product is `≥ ξζT·(4ζ^{-1}S − 1) = ξT(4S − ζ) ≥ ξT(4S − 1)` since `ζ ≤ 1`. -/
private lemma yc_geom_aux {ξ T S : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1) (hT : 0 ≤ T)
    (_hS : 0 ≤ S) (r J : ℕ) :
    ξ * T * (4 * S - 1) ≤
      ((⌊ξ * (ξ ^ (r * J) * T)⌋₊ : ℝ) + 1) *
        (2 * (⌊2 * (ξ ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℝ) + 1) := by
  have hζpos : 0 < ξ ^ (r * J) := pow_pos hξ0 _
  have hζle : ξ ^ (r * J) ≤ 1 := pow_le_one₀ (le_of_lt hξ0) hξ1
  have hzpow : ξ ^ (-((r * J : ℕ) : ℤ)) = (ξ ^ (r * J))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hzpow]
  have hA : ξ * (ξ ^ (r * J) * T) ≤ ((⌊ξ * (ξ ^ (r * J) * T)⌋₊ : ℝ) + 1) :=
    le_of_lt (Nat.lt_floor_add_one _)
  have hB : 4 * (ξ ^ (r * J))⁻¹ * S - 1 ≤ 2 * (⌊2 * ((ξ ^ (r * J))⁻¹ * S)⌋₊ : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (2 * ((ξ ^ (r * J))⁻¹ * S))
    linarith
  have hxnn : 0 ≤ ξ * (ξ ^ (r * J) * T) := by positivity
  have hBnn : 0 ≤ 2 * (⌊2 * ((ξ ^ (r * J))⁻¹ * S)⌋₊ : ℝ) + 1 := by positivity
  have hξT : 0 ≤ ξ * T := by positivity
  calc ξ * T * (4 * S - 1)
      ≤ ξ * T * (4 * S - ξ ^ (r * J)) := by
        apply mul_le_mul_of_nonneg_left _ hξT
        linarith
    _ = ξ * (ξ ^ (r * J) * T) * (4 * (ξ ^ (r * J))⁻¹ * S - 1) := by
        field_simp
    _ ≤ (⌊ξ * (ξ ^ (r * J) * T)⌋₊ + 1) * (2 * ⌊2 * ((ξ ^ (r * J))⁻¹ * S)⌋₊ + 1) := by
        have h1 := mul_le_mul_of_nonneg_right hA hBnn
        have h2 := mul_le_mul_of_nonneg_left hB hxnn
        calc ξ * (ξ ^ (r * J) * T) * (4 * (ξ ^ (r * J))⁻¹ * S - 1)
            = (ξ * (ξ ^ (r * J) * T)) * (4 * (ξ ^ (r * J))⁻¹ * S - 1) := by ring
          _ ≤ (ξ * (ξ ^ (r * J) * T)) * (2 * ⌊2 * ((ξ ^ (r * J))⁻¹ * S)⌋₊ + 1) := h2
          _ ≤ ((⌊ξ * (ξ ^ (r * J) * T)⌋₊ : ℝ) + 1) *
                (2 * ⌊2 * ((ξ ^ (r * J))⁻¹ * S)⌋₊ + 1) := h1

/-- The uniform (all-`J`) geometric lower bound for the Y-free counting inequality: for `r ≥ 2` and every descent level `J`, the product `(⌊ξT^{(J)}⌋+1)(2⌊2S^{(J)}⌋+1)` dominates the reduced bound `ξ·T·(4S−1)`. Uses `S^{(J)}T^{(J)} = ST`: with `ζ = ξ^{rJ} ∈ (0,1]`, `S^{(J)} = ζ^{-1}S` and `T^{(J)} = ζT`, the two factors are `≥ ξζT` and `≥ 4ζ^{-1}S − 1`. -/
theorem yc_geom {K : Type*} [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v J : ℕ)
    (σ : Fin r → ℝ) (hr : 2 ≤ r) :
    pxi r * (pT r (dK K) σ : ℝ) * (4 * (pS r (dK K) (acH K b v) : ℝ) - 1)
      ≤ ((⌊pxi r * TJ K σ J⌋₊ : ℝ) + 1) * (2 * (⌊2 * SJ K r b v J⌋₊ : ℝ) + 1) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hξ0 : 0 < pxi r := by
    rw [pxi]
    have h : (0.536 : ℝ) / r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hξ1 : pxi r ≤ 1 := by
    rw [pxi]
    have h : (0 : ℝ) ≤ (0.536 : ℝ) / r := by positivity
    linarith
  have key := yc_geom_aux hξ0 hξ1
    (show (0 : ℝ) ≤ (pT r (dK K) σ : ℝ) by positivity)
    (show (0 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) by positivity) r J
  show pxi r * (pT r (dK K) σ : ℝ) * (4 * (pS r (dK K) (acH K b v) : ℝ) - 1)
      ≤ ((⌊pxi r * (pxi r ^ (r * J) * (pT r (dK K) σ : ℝ))⌋₊ : ℝ) + 1) *
        (2 * (⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) *
          (pS r (dK K) (acH K b v) : ℝ))⌋₊ : ℝ) + 1)
  exact key

end Work.BW
