/-
# The model weight absorbs the constant of the `symD` estimate

Area `A6` uses the single-scale model approximation (`mod-approx`) in the weight

  `modelWeight A ρ l₁ l₂ k₁ k₂ = ⟨L⟩^A · 2^{A·2^{ρL}}`,   `L = lcL l₁ l₂ k₁ k₂`,

(`Work.KMTAreas.A7.ModelApproxAux`, `Work.KMTPlan.A6.LowDefs`).  The bound on the symbol
difference `symD` (`Work.KMTPlan.A6.LowSmallSymDefs`) produced by the §6 analysis carries,
besides the exponential factor `2^{K(2^{ρL}+L)}`, a *fixed* constant `D > 0` and the
elementary factor `2^{2(k₁ + d k₂) + 3}` coming from the two §5 bumps `φ_N`, `φ̃_N`
(`d = P.natDegree`).  This module proves that all of it is absorbed by the weight, uniformly
in the scale quadruple `(l₁,l₂,k₁,k₂)`:

  `∃ A ≥ 0, ∀ l₁ l₂ k₁ k₂,  D·2^{K(2^{ρL}+L)}·2^{2(k₁+dk₂)+3} ≤ modelWeight A ρ l₁ l₂ k₁ k₂`.

The constant `A` may depend on `P`, `ρ`, `K`, `D` (all fixed before it is chosen), but not on
the scale.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTPlan.A6.le_two_rpow_self_of_ceil

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

/-- `lmaxR` is the `ℝ`-valued version of `lcL`. -/
lemma absorbs_lmaxR_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
  simp only [Work.KMTAreas.A7.lmaxR, Work.KMTPlan.A6.lcL, Work.Analysis.EndVar.lmax]
  push_cast
  ring

/-- `modelWeight` depends on the quadruple only through `lcL`. -/
lemma modelWeight_diag_eq (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.modelWeight A ρ (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂)
        (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂)
      = Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ := by
  have h : Work.KMTAreas.A7.lmaxR (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂)
      (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂) = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    rw [absorbs_lmaxR_eq_lcL]
    simp only [lcL, Nat.cast_max, max_self]
  rw [Work.KMTAreas.A7.modelWeight, Work.KMTAreas.A7.modelWeight, h,
    absorbs_lmaxR_eq_lcL l₁ l₂ k₁ k₂]

/-- **The model weight absorbs a fixed multiple of any exponential weight
`2^{C(2^{ρL}+L)}`.**  For every `C ≥ 0`, every `D8 > 0` and every `ρ > 0` there is `A ≥ 0`
such that for *all* scales `L`

  `D8 · 2^{C·(2^{ρL} + L)} ≤ modelWeight A ρ L L L L = ⟨L⟩^A · 2^{A·2^{ρL}}`.

This is `Work.KMTPlan.A6.exists_modelWeight_absorb` with the extra constant factor `D8 > 0`:
replace `A` there by `A + s` with `2^s ≥ D8`.  The proof below makes this explicit by taking
`A = max (2C + s) (C(2^{ρN}+N) + s)`, `N = ⌈16/ρ²⌉`, `s = max 0 (logb 2 D8)`: on the finitely
many scales `L < N` the constant `D8 ≤ 2^s` and the bounded exponent are handled by
`A ≤ A·2^{ρL}`, while for `L ≥ N` one has `2^{ρL} ≥ L` and `s + C(2^{ρL}+L) ≤ (2C+s)·2^{ρL}`. -/
lemma modelWeight_absorb_const (C D8 ρ : ℝ) (hC : 0 ≤ C) (hD8 : 0 < D8) (hρ : 0 < ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ℕ,
      D8 * (2 : ℝ) ^ (C * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        ≤ Work.KMTAreas.A7.modelWeight A ρ L L L L := by
  -- a real `s ≥ 0` with `2^s ≥ D8`
  obtain ⟨s, hs0, hDs⟩ : ∃ s : ℝ, 0 ≤ s ∧ D8 ≤ (2 : ℝ) ^ s := by
    refine ⟨max 0 (Real.logb 2 D8), le_max_left _ _, ?_⟩
    rcases lt_or_ge D8 1 with h | h
    · calc D8 ≤ (1 : ℝ) := le_of_lt h
        _ = (2 : ℝ) ^ (0 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ max 0 (Real.logb 2 D8) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_left _ _)
    · have hlog : (2 : ℝ) ^ Real.logb 2 D8 = D8 :=
        Real.rpow_logb (by norm_num) (by norm_num) hD8
      calc D8 = (2 : ℝ) ^ Real.logb 2 D8 := hlog.symm
        _ ≤ (2 : ℝ) ^ max 0 (Real.logb 2 D8) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_right _ _)
  set N : ℕ := Nat.ceil (16 / ρ ^ 2) with hNdef
  have hNreal : 16 / ρ ^ 2 ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  set A : ℝ := max (2 * C + s) (C * ((2 : ℝ) ^ (ρ * (N : ℝ)) + (N : ℝ)) + s) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact le_trans (by linarith : (0 : ℝ) ≤ 2 * C + s) (le_max_left _ _)
  refine ⟨A, hA0, ?_⟩
  intro L
  have hLmax : Work.KMTAreas.A7.lmaxR L L L L = (L : ℝ) := by
    simp [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
  rw [Work.KMTAreas.A7.modelWeight, hLmax]
  set t : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; exact Real.rpow_nonneg (by norm_num) _
  have ht1 : 1 ≤ t := by rw [htdef]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hge1 : (1 : ℝ) ≤ 1 + (L : ℝ) := by
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  have hw : (2 : ℝ) ^ (A * t) ≤ (1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * t) := by
    have h1 : (1 : ℝ) ≤ (1 + (L : ℝ)) ^ A := Real.one_le_rpow hge1 hA0
    have h2 : 0 ≤ (2 : ℝ) ^ (A * t) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hexp : s + C * (t + (L : ℝ)) ≤ A * t := by
    rcases lt_or_ge L N with hLN | hLN
    · have hLR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_of_lt hLN)
      have hpow : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (2 : ℝ) ^ (ρ * (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      have hpoweq : t ≤ (2 : ℝ) ^ (ρ * (N : ℝ)) := by rw [htdef]; exact hpow
      have h1 : C * (t + (L : ℝ)) ≤ C * ((2 : ℝ) ^ (ρ * (N : ℝ)) + (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      have h2 : C * ((2 : ℝ) ^ (ρ * (N : ℝ)) + (N : ℝ)) + s ≤ A := by
        rw [hAdef]; exact le_max_right _ _
      have h3 : A ≤ A * t := by nlinarith [ht1, hA0]
      linarith
    · have hLle : (L : ℝ) ≤ t := by
        rw [htdef]; exact le_two_rpow_self_of_ceil ρ hρ L hLN
      have hA2 : 2 * C + s ≤ A := by rw [hAdef]; exact le_max_left _ _
      have hCs : C * (t + (L : ℝ)) + s ≤ (2 * C + s) * t := by nlinarith
      nlinarith [hCs, hA2, ht0, hs0]
  calc D8 * (2 : ℝ) ^ (C * (t + (L : ℝ)))
      ≤ (2 : ℝ) ^ s * (2 : ℝ) ^ (C * (t + (L : ℝ))) :=
        mul_le_mul_of_nonneg_right hDs (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (s + C * (t + (L : ℝ))) := by rw [Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (A * t) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * t) := hw

/-- **The model weight absorbs the elementary factor `2^{2(k₁+dk₂)+3}` together with a fixed
constant and a fixed exponential weight.**  For every `D > 0`, `K ≥ 0`, `ρ > 0` and every
`d : ℕ` there is `A ≥ 0` such that for all scales `L` and all `k₁,k₂ ≤ L`

  `D · 2^{K(2^{ρL}+L)} · 2^{2(k₁+dk₂)+3} ≤ modelWeight A ρ L L L L`.

Indeed `2^{2(k₁+dk₂)+3} ≤ 2^{(2+2d)L+3} = 8·2^{(2+2d)L}`, and
`K(2^{ρL}+L) + (2+2d)L ≤ (K+2+2d)(2^{ρL}+L)`, so the left side is at most
`(D·8)·2^{(K+2+2d)(2^{ρL}+L)}`, which `modelWeight_absorb_const` absorbs. -/
lemma modelWeight_absorb_generic (D K ρ : ℝ) (d : ℕ) (hD : 0 < D) (hK : 0 ≤ K) (hρ : 0 < ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (L : ℕ) (k₁ k₂ : ℕ), k₁ ≤ L → k₂ ≤ L →
      D * (2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        * (2 : ℝ) ^ (2 * (k₁ + d * k₂) + 3)
        ≤ Work.KMTAreas.A7.modelWeight A ρ L L L L := by
  have hD8 : 0 < D * 8 := by linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  set C : ℝ := K + 2 + 2 * (d : ℝ) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; linarith
  obtain ⟨A, hA0, hAw⟩ := modelWeight_absorb_const C (D * 8) ρ hC0 hD8 hρ
  refine ⟨A, hA0, ?_⟩
  intro L k₁ k₂ hk1 hk2
  have hnatle : 2 * (k₁ + d * k₂) + 3 ≤ (2 + 2 * d) * L + 3 := by
    have hR : ((2 * (k₁ + d * k₂) + 3 : ℕ) : ℝ) ≤ (((2 + 2 * d) * L + 3 : ℕ) : ℝ) := by
      push_cast
      have hk1R : (k₁ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hk1
      have hk2R : (k₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hk2
      nlinarith [hd0]
    exact_mod_cast hR
  have hpow2 : (2 : ℝ) ^ (2 * (k₁ + d * k₂) + 3) ≤ (2 : ℝ) ^ ((2 + 2 * d) * L + 3) :=
    pow_le_pow_right₀ (by norm_num) hnatle
  have hZ01 : (2 : ℝ) ^ ((2 + 2 * d) * L + 3)
      = 8 * (2 : ℝ) ^ ((2 + 2 * (d : ℝ)) * (L : ℝ)) := by
    have h1 : (2 : ℝ) ^ ((2 + 2 * d) * L) = (2 : ℝ) ^ ((2 + 2 * (d : ℝ)) * (L : ℝ)) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [pow_add, h1, show (2 : ℝ) ^ 3 = (8 : ℝ) by norm_num]
    ring
  have ht0 : 0 ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hchain1 : D * (2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        * (2 : ℝ) ^ (2 * (k₁ + d * k₂) + 3)
      ≤ D * (2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        * (2 : ℝ) ^ ((2 + 2 * d) * L + 3) :=
    mul_le_mul_of_nonneg_left hpow2 (mul_nonneg hD.le (Real.rpow_nonneg (by norm_num) _))
  have hchain2 : D * (2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
        * (2 : ℝ) ^ ((2 + 2 * d) * L + 3)
      = (D * 8) * ((2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
          * (2 : ℝ) ^ ((2 + 2 * (d : ℝ)) * (L : ℝ))) := by
    rw [hZ01, mul_mul_mul_comm]
  have hchain3 : (D * 8) * ((2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))
          * (2 : ℝ) ^ ((2 + 2 * (d : ℝ)) * (L : ℝ)))
      = (D * 8) * (2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))
          + (2 + 2 * (d : ℝ)) * (L : ℝ)) := by
    rw [← Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
  have hexp : K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)) + (2 + 2 * (d : ℝ)) * (L : ℝ)
      ≤ C * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)) := by
    rw [hCdef]
    nlinarith [ht0, hL0, hd0]
  have hchain4 : (D * 8) * (2 : ℝ) ^ (K * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))
          + (2 + 2 * (d : ℝ)) * (L : ℝ))
      ≤ (D * 8) * (2 : ℝ) ^ (C * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (le_of_lt hD8)
  exact le_trans hchain1 (le_trans (le_of_eq hchain2)
    (le_trans (le_of_eq hchain3) (le_trans hchain4 (hAw L))))

/-- **The model weight of the single-scale estimate absorbs the constant of the `symD` bound.**
The symbol estimate of §6 for `symD` carries a fixed constant `D`, the exponential weight
`2^{K(2^{ρL}+L)}` (`L = lcL l₁ l₂ k₁ k₂`) and the factor `2^{2(k₁+P.natDegree·k₂)+3}` of the two
§5 bumps; all of it is dominated by `modelWeight A ρ l₁ l₂ k₁ k₂` for a constant `A ≥ 0`
depending only on `P, ρ, K, D`. -/
theorem modelWeight_absorbs_symD (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (K D : ℝ)
    (hK : 0 ≤ K) (hD : 0 < D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (l₁ l₂ k₁ k₂ : ℕ),
      D * (2 : ℝ) ^ (K * (2 ^ (ρ * (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℝ)) + (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℝ)))
        * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3)
        ≤ Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ := by
  obtain ⟨A, hA0, hA⟩ := modelWeight_absorb_generic D K ρ P.natDegree hD hK hρ
  refine ⟨A, hA0, ?_⟩
  intro l₁ l₂ k₁ k₂
  have hk1 : k₁ ≤ lcL l₁ l₂ k₁ k₂ := by
    rw [lcL]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hk2 : k₂ ≤ lcL l₁ l₂ k₁ k₂ := by
    rw [lcL]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  exact le_trans (hA (lcL l₁ l₂ k₁ k₂) k₁ k₂ hk1 hk2)
    (le_of_eq (modelWeight_diag_eq A ρ l₁ l₂ k₁ k₂))

end Work.KMTPlan.A6
