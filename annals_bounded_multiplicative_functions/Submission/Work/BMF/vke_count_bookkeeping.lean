import Mathlib
import Submission.Work.BMF.vke_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **Counting bookkeeping for the reduced block sum.** With `A = 4^k`, `f = (k-1)!`, `k = vkK N t`,
`μ` the size of the `k`-th derivative, `N ≥ 2`, `N ≤ t`, `M ≤ 2N`, `μ(N+1) ≤ 1`, `μ > 0` and
`1 ≤ H ≤ 7 N^{1−λ/k}`, the counting bound `𝒩 ≤ K A² f M (1+μM)(1+H)` implies
`𝒩 ≤ 84 K A² f N^{2−λ/k}`. -/
theorem vke_count_bookkeeping {N t Kcnt μ H 𝒩 : ℝ} {M : ℕ}
    (hN : 2 ≤ N) (hNt : N ≤ t) (hKcnt : 0 < Kcnt) (hμpos : 0 < μ)
    (hmuM_le : μ * (N + 1) ≤ 1) (hM2N : (M : ℝ) ≤ 2 * N)
    (hH1 : 1 ≤ H) (hHle : H ≤ 7 * N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)))
    (hcount : 𝒩 ≤ Kcnt * ((4 : ℝ) ^ (vkK N t)) ^ 2
        * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) * (M : ℝ)
        * (1 + μ * (M : ℝ)) * (1 + H)) :
    𝒩 ≤ 84 * Kcnt * ((4 : ℝ) ^ (vkK N t)) ^ 2
        * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ)
        * N ^ (2 - vkLam N t / ((vkK N t : ℕ) : ℝ)) := by
  have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
  have hkpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by
    have : (0 : ℕ) < vkK N t := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNp1pos : (0 : ℝ) < N + 1 := by linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  -- the exponent `1 - λ/k` is nonnegative
  have hlam_le_k : vkLam N t ≤ ((vkK N t : ℕ) : ℝ) := by
    have := (vkK_bounds hN hNt).1; linarith
  have hexpnn : 0 ≤ 1 - vkLam N t / ((vkK N t : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one hkpos]; exact hlam_le_k
  -- abbreviate the saving factor
  set x : ℝ := N ^ (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef]; exact Real.one_le_rpow hN1 hexpnn
  -- `1 + μM ≤ 3`
  have hmu_le : μ ≤ 1 / (N + 1) := by
    rw [le_div_iff₀ hNp1pos]; linarith [hmuM_le]
  have hmuM : μ * (M : ℝ) ≤ 2 := by
    calc μ * (M : ℝ) ≤ (1 / (N + 1)) * (M : ℝ) := mul_le_mul_of_nonneg_right hmu_le hMnn
      _ = (M : ℝ) / (N + 1) := by ring
      _ ≤ (2 * N) / (N + 1) := div_le_div_of_nonneg_right hM2N (le_of_lt hNp1pos)
      _ ≤ 2 := by rw [div_le_iff₀ hNp1pos]; linarith
  have hmuM3 : 1 + μ * (M : ℝ) ≤ 3 := by linarith
  have hMu_nn : 0 ≤ 1 + μ * (M : ℝ) := by
    have := mul_nonneg (le_of_lt hμpos) hMnn; linarith
  -- `1 + H ≤ 8 x`
  have hHle' : H ≤ 7 * x := hHle
  have hHbound : 1 + H ≤ 8 * x := by linarith
  have hH_nn : 0 ≤ 1 + H := by linarith
  -- combine the three factors
  have hprod1 : (M : ℝ) * (1 + μ * (M : ℝ)) ≤ 6 * N := by
    have h := mul_le_mul hM2N hmuM3 hMu_nn (by linarith : (0 : ℝ) ≤ 2 * N)
    linarith [h]
  have hprod2 : (M : ℝ) * (1 + μ * (M : ℝ)) * (1 + H) ≤ (6 * N) * (8 * x) :=
    mul_le_mul hprod1 hHbound hH_nn (by positivity)
  have hNx : N ^ (2 - vkLam N t / ((vkK N t : ℕ) : ℝ)) = N * x := by
    rw [show (2 - vkLam N t / ((vkK N t : ℕ) : ℝ))
          = 1 + (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) by ring,
        Real.rpow_add hNpos, Real.rpow_one, hxdef]
  have hprodfinal : (M : ℝ) * (1 + μ * (M : ℝ)) * (1 + H)
      ≤ 84 * N ^ (2 - vkLam N t / ((vkK N t : ℕ) : ℝ)) := by
    rw [show (6 * N) * (8 * x) = 48 * (N * x) by ring, ← hNx] at hprod2
    nlinarith [hprod2,
      Real.rpow_nonneg (le_of_lt hNpos) (2 - vkLam N t / ((vkK N t : ℕ) : ℝ))]
  -- multiply by the nonnegative prefactor
  set A2 : ℝ := ((4 : ℝ) ^ (vkK N t)) ^ 2 with hA2def
  set F : ℝ := ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) with hFdef
  have hA2nn : 0 ≤ A2 := by rw [hA2def]; positivity
  have hFnn : 0 ≤ F := by rw [hFdef]; positivity
  have hKAF : 0 ≤ Kcnt * A2 * F := by positivity
  calc 𝒩 ≤ Kcnt * A2 * F * (M : ℝ) * (1 + μ * (M : ℝ)) * (1 + H) := hcount
    _ = (Kcnt * A2 * F) * ((M : ℝ) * (1 + μ * (M : ℝ)) * (1 + H)) := by ring
    _ ≤ (Kcnt * A2 * F) * (84 * N ^ (2 - vkLam N t / ((vkK N t : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hprodfinal hKAF
    _ = 84 * Kcnt * A2 * F * N ^ (2 - vkLam N t / ((vkK N t : ℕ) : ℝ)) := by ring

end Work.BMF
