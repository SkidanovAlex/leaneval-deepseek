/-
# The support of the modulated `d`-fold bump `φ̃_{N,t}`, with no regime restriction

The bump `φ̃_N` of §6 is `η(2^{d(Log N - k₂)}·) - η(2^{d(Log N - k₂)+d}·)` for `k₂ ≠ 0` (and
`η(2^{d·Log N}·)` at the bottom scale `k₂ = 0`), a difference of rescalings of the fixed cutoff
`η = Work.KMTContract.kmtEta`, whose support is the open unit ball of `ℝ`.  Hence a nonzero value
of `φ̃_N` forces `|ξ| ≤ 2^{d(k₂ - Log N)}`.

Note that `varphitildeNt_support_le` proves the band statement `|ξ| ≤ 2^{-2u}` *on the main
regime* `k₂ + 2u ≤ Log N`, where the exponent `k₂ - Log N` is comparable to `-2u`.  The statement
proved here is the *unrestricted* one: the exponent `d(k₂ - Log N)` is exactly the one arising
from the first rescaled cutoff, so the support bound needs neither `1 ≤ d` nor `k₂ ≤ Log N`.
The modulation `φ̃_{N,t} = φ̃_N · e(P(Nt)·)` never changes the support, since `e(x) = e^{2πix}`
is nowhere zero.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphiNt_support_le

namespace Work.KMTAreas.A7

/-- **The support of a rescaled cutoff.**  If `η(2^a ξ) ≠ 0` for the KMT cutoff `η`, then
`|ξ| ≤ 2^{-a}`: `η` vanishes for `|x| ≥ 1`, and `2^a > 0`. -/
private lemma eta_rpow_ne_zero_abs_le {a : ℝ} {ξ : ℝ}
    (h : Work.KMTContract.kmtEta ((2 : ℝ) ^ a * ξ) ≠ 0) : |ξ| ≤ (2 : ℝ) ^ (-a) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlt : ¬ (1 ≤ |(2 : ℝ) ^ a * ξ|) := fun hc => h (Work.KMTContract.kmtEta_zero hc)
  have h3 : |(2 : ℝ) ^ a * ξ| < 1 := lt_of_not_ge hlt
  have hp : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos h2 _
  rw [abs_mul, abs_of_pos hp] at h3
  have h4 : (2 : ℝ) ^ a * |ξ| < (2 : ℝ) ^ a * ((2 : ℝ) ^ a)⁻¹ := by
    rwa [mul_inv_cancel₀ (ne_of_gt hp)]
  have h5 : |ξ| < ((2 : ℝ) ^ a)⁻¹ := lt_of_mul_lt_mul_left h4 (le_of_lt hp)
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h5
  exact le_of_lt h5

/-- Monotonicity of `x ↦ 2^x`. -/
private lemma rpow_two_mono {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h

/-- **The support bound for the `d`-fold bump `φ̃_N`, with no regime restriction.**  A nonzero
value of `φ̃_N` forces `|ξ| ≤ 2^{d(k₂ - Log N)}`. -/
private lemma varphitildeN_ne_zero_abs_le_all (d N k₂ : ℕ) {ξ : ℝ}
    (h : varphitildeN d N k₂ ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  by_cases hk0 : k₂ = 0
  · subst hk0
    rw [varphitildeN, if_pos rfl] at h
    have hb := eta_rpow_ne_zero_abs_le
      (a := (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) h
    convert hb using 1
    push_cast
    ring
  · rw [varphitildeN, if_neg hk0] at h
    -- at least one term of the difference is nonzero
    have hbor :
        Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ))) * ξ) ≠ 0 ∨
          Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1)) * ξ)
              ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    rcases hbor with hc | hc
    · -- the coarse term of the difference already gives the claimed exponent
      have hb := eta_rpow_ne_zero_abs_le
        (a := (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ))) hc
      convert hb using 1
      ring
    · -- the fine term lives at the scale `2^d` above, hence a fortiori in the same window
      have hb := eta_rpow_ne_zero_abs_le
        (a := (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1)) hc
      refine le_trans hb (rpow_two_mono ?_)
      have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith

theorem varphitildeNt_support_all (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P d N k₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  intro ξ hξ
  -- the modulation `e(P(Nt)·)` is nowhere zero, so a nonzero value of `φ̃_{N,t}` is one of `φ̃_N`
  have hN : varphitildeN d N k₂ ξ ≠ 0 := (mul_ne_zero_iff.mp hξ).1
  exact varphitildeN_ne_zero_abs_le_all d N k₂ hN

end Work.KMTAreas.A7
