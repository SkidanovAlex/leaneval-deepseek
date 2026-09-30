import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs
import Submission.Work.BMF.liouville.vk_easy_numeric_key

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

noncomputable section

/-- Logarithmic comparison underlying the absorption of the second "easy" term of Ford's
Lemma 5.1 in the large-`λ` regime, with the exponent `4/5` interpreted as the *real*
number `(4:ℝ)/5`: if `M ≤ 2 N^{2/5}`, `t = N^lam`, `lam ≤ K/5 - 1/5` and
`2^{2K+1} ≤ N^{1/5}`, then `t·(M²)^{K+1} ≤ 2K·N^{4/5+K}`. -/
lemma vk_easy_log_compare_aux2 (N t M : ℝ) (K : ℕ) (lam : ℝ)
    (hN1 : 1 ≤ N) (hM1 : 1 ≤ M) (hMle : M ≤ 2 * N ^ ((2:ℝ)/5))
    (htpos : 0 < t) (ht : Real.log t = lam * Real.log N)
    (hlam : lam ≤ (K:ℝ)/5 - 1/5) (hK1 : 1 ≤ K)
    (hkey : (2 * (K:ℝ) + 1) * Real.log 2 ≤ (1/5) * Real.log N) :
    t * (M * M) ^ (K + 1) ≤ 2 * (K:ℝ) * N ^ ((4:ℝ)/5 + (K:ℝ)) := by
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := by linarith
  have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK1
  -- the logarithm of `M`
  have hlogM : Real.log M ≤ Real.log 2 + (2/5) * Real.log N := by
    have h1 : Real.log M ≤ Real.log (2 * N ^ ((2:ℝ)/5)) := Real.log_le_log hMpos hMle
    have h2 : Real.log (2 * N ^ ((2:ℝ)/5)) = Real.log 2 + (2/5) * Real.log N := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hNpos _)),
        Real.log_rpow hNpos]
    rwa [h2] at h1
  -- positivity of both sides
  have hpowpos : 0 < (M * M) ^ (K + 1) := pow_pos (mul_pos hMpos hMpos) _
  have hApos : 0 < t * (M * M) ^ (K + 1) := mul_pos htpos hpowpos
  have hCpos : 0 < 2 * (K:ℝ) * N ^ ((4:ℝ)/5 + (K:ℝ)) := by
    have h : 0 < N ^ ((4:ℝ)/5 + (K:ℝ)) := Real.rpow_pos_of_pos hNpos _
    positivity
  refine (Real.log_le_log_iff hApos hCpos).mp ?_
  -- logarithms of the two sides
  have hlogA : Real.log (t * (M * M) ^ (K + 1))
      = lam * Real.log N + (2 * (K:ℝ) + 2) * Real.log M := by
    rw [Real.log_mul (ne_of_gt htpos) (ne_of_gt hpowpos), Real.log_pow,
      Real.log_mul (ne_of_gt hMpos) (ne_of_gt hMpos), ht]
    push_cast
    ring
  have hlogC : Real.log (2 * (K:ℝ) * N ^ ((4:ℝ)/5 + (K:ℝ)))
      = Real.log 2 + Real.log (K:ℝ) + (4/5 + (K:ℝ)) * Real.log N := by
    rw [Real.log_mul (ne_of_gt (by linarith : (0:ℝ) < 2 * (K:ℝ)))
        (ne_of_gt (Real.rpow_pos_of_pos hNpos _)),
      Real.log_mul (by norm_num) (ne_of_gt hKpos), Real.log_rpow hNpos]
  rw [hlogA, hlogC]
  have hstep1 : (lam + (4 * (K:ℝ) + 4)/5) * Real.log N ≤ ((K:ℝ) + 3/5) * Real.log N := by
    have hle : lam + (4 * (K:ℝ) + 4)/5 ≤ (K:ℝ) + 3/5 := by linarith [hlam]
    exact mul_le_mul_of_nonneg_right hle hlogNnn
  have hstep2 : (2 * (K:ℝ) + 2) * Real.log 2
      ≤ Real.log 2 + Real.log (K:ℝ) + (1/5) * Real.log N := by
    have hlogK : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
    have heq : (2 * (K:ℝ) + 2) * Real.log 2 = (2 * (K:ℝ) + 1) * Real.log 2 + Real.log 2 := by
      ring
    rw [heq]
    linarith [hkey, hlogK]
  have hstep3 : lam * Real.log N + (2 * (K:ℝ) + 2) * Real.log M
      ≤ (lam + (4 * (K:ℝ) + 4)/5) * Real.log N + (2 * (K:ℝ) + 2) * Real.log 2 := by
    have hcoef : (0:ℝ) ≤ 2 * (K:ℝ) + 2 := by linarith
    calc lam * Real.log N + (2 * (K:ℝ) + 2) * Real.log M
        ≤ lam * Real.log N + (2 * (K:ℝ) + 2) * (Real.log 2 + (2/5) * Real.log N) :=
          add_le_add (le_refl (lam * Real.log N)) (mul_le_mul_of_nonneg_left hlogM hcoef)
      _ = (lam + (4 * (K:ℝ) + 4)/5) * Real.log N + (2 * (K:ℝ) + 2) * Real.log 2 := by
          ring
  calc lam * Real.log N + (2 * (K:ℝ) + 2) * Real.log M
      ≤ (lam + (4 * (K:ℝ) + 4)/5) * Real.log N + (2 * (K:ℝ) + 2) * Real.log 2 := hstep3
    _ ≤ ((K:ℝ) + 3/5) * Real.log N
          + (Real.log 2 + Real.log (K:ℝ) + (1/5) * Real.log N) := add_le_add hstep1 hstep2
    _ = Real.log 2 + Real.log (K:ℝ) + (4/5 + (K:ℝ)) * Real.log N := by ring

/-- The two "easy" terms of Ford's Lemma 5.1 are absorbed by `N^{4/5}`.  (The exponent is the
real number `4/5`, written `((4:ℝ)/5)` to avoid it being read as the natural-number division
`4/5 = 0`.) -/
theorem vk_large_easy_terms2 (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t) (lam : ℝ)
    (hlam : lam = dLam N t) (hlamge : 13/5 ≤ lam) (hlogN : 1000 * lam ^ 2 ≤ Real.log N) :
    2 * (dM N : ℝ) * (dM N : ℝ) ≤ 8 * N ^ ((4 : ℝ)/5) ∧
    t * ((dM N : ℝ) * (dM N : ℝ)) ^ (dK lam + 1) / ((dK lam : ℝ) * N ^ (dK lam))
      ≤ 2 * N ^ ((4 : ℝ)/5) := by
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have htpos : 0 < t := lt_of_lt_of_le hNpos hNt
  have hlampos : 0 < lam := by linarith
  have hlogNpos : 0 < Real.log N := by
    have h : 0 < 1000 * lam ^ 2 := by positivity
    linarith
  have hXpos : 0 < N ^ ((2:ℝ)/5) := Real.rpow_pos_of_pos hNpos _
  have hX1 : (1:ℝ) ≤ N ^ ((2:ℝ)/5) := Real.one_le_rpow hN1 (by norm_num)
  -- bounds for `M = ⌈N^{2/5}⌉`
  have hMge1 : (1:ℝ) ≤ (dM N : ℝ) := by
    have h : N ^ ((2:ℝ)/5) ≤ (dM N : ℝ) := by
      simpa only [dM] using Nat.le_ceil (N ^ ((2:ℝ)/5))
    linarith
  have hMpos : (0:ℝ) < (dM N : ℝ) := by linarith
  have hMle : (dM N : ℝ) ≤ 2 * N ^ ((2:ℝ)/5) := by
    have h : (dM N : ℝ) < N ^ ((2:ℝ)/5) + 1 := by
      simpa only [dM] using Nat.ceil_lt_add_one (le_of_lt hXpos)
    linarith
  -- bounds for `k = dK lam`
  have hG5 : (5:ℝ) * lam ≤ (dG lam : ℝ) := by
    simpa only [dG] using Nat.le_ceil (5 * lam)
  have hKeq : (dK lam : ℝ) = (dG lam : ℝ) + 1 := by simp [dK]
  have hKge : 5 * lam + 1 ≤ (dK lam : ℝ) := by rw [hKeq]; linarith
  have hK1 : 1 ≤ dK lam := by simp [dK]
  constructor
  · -- first term: `2 M² ≤ 8 N^{4/5}`
    have hsq : ((dM N : ℝ))^2 ≤ 4 * N ^ ((4:ℝ)/5) := by
      have h4 : (2 * N ^ ((2:ℝ)/5))^2 = 4 * N ^ ((4:ℝ)/5) := by
        rw [mul_pow]
        have h3 : (N ^ ((2:ℝ)/5))^2 = N ^ ((4:ℝ)/5) := by
          rw [← Real.rpow_natCast (N ^ ((2:ℝ)/5)) 2, ← Real.rpow_mul hNpos.le]
          norm_num
        rw [h3]
        norm_num
      calc ((dM N : ℝ))^2 ≤ (2 * N ^ ((2:ℝ)/5))^2 :=
            pow_le_pow_left₀ (le_of_lt hMpos) hMle 2
        _ = 4 * N ^ ((4:ℝ)/5) := h4
    have he : 2 * (dM N : ℝ) * (dM N : ℝ) = 2 * ((dM N : ℝ))^2 := by ring
    rw [he]
    linarith
  · -- second term: `t (M²)^{k+1} / (k N^k) ≤ 2 N^{4/5}`
    have hlogt : Real.log t = lam * Real.log N := by
      rw [hlam, dLam, div_mul_cancel₀ _ (ne_of_gt hlogNpos)]
    have hkey := vk_easy_numeric_key N lam hlamge hlogN
    have hlamK : lam ≤ ((dK lam : ℝ))/5 - 1/5 := by linarith [hKge]
    have hstep := vk_easy_log_compare_aux2 N t (dM N : ℝ) (dK lam) lam hN1 hMge1 hMle
      htpos hlogt hlamK hK1 hkey
    have hBpos : 0 < (dK lam : ℝ) * N ^ (dK lam) := by
      have h1 : (0:ℝ) < (dK lam : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hK1
      exact mul_pos h1 (pow_pos hNpos _)
    rw [div_le_iff₀ hBpos]
    calc t * ((dM N : ℝ) * (dM N : ℝ)) ^ (dK lam + 1)
        ≤ 2 * (dK lam : ℝ) * N ^ ((4:ℝ)/5 + (dK lam : ℝ)) := hstep
      _ = (2 * N ^ ((4:ℝ)/5)) * ((dK lam : ℝ) * N ^ (dK lam)) := by
          have hsplit : N ^ ((4:ℝ)/5 + (dK lam : ℝ))
              = N ^ ((4:ℝ)/5) * N ^ (dK lam) := by
            rw [Real.rpow_add hNpos, Real.rpow_natCast]
          rw [hsplit]
          ring

end

end Work.BMF.liouville
