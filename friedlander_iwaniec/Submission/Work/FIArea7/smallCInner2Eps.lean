import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.prop172defs
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sum_sqfree_peel
import Submission.Work.FIArea7.sqfreeSum_eq_sepPair_add_peel
import Submission.Work.FIArea7.sepPair_bounds
import Submission.Work.FIArea7.sepDiv_pow_le_of_smooth
import Submission.Work.FIArea7.normQuadEigenLe
import Submission.Work.FIArea7.sepDiv_pow_le
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.smallCInner2EpsAux.bound_combine
import Submission.Work.FIArea7.smallCInner2EpsAux.hyperbolaBilinEps
import Submission.Work.FIArea7.smallCInner2EpsAux.smoothBilinEps
import Submission.Work.FIArea7.smallCInner2EpsAux.sepLHSBoundEps
import Submission.Work.FIArea7.smallCInner2EpsAux.peelBigBoundEps
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallBound

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- *FI* §25 at a fixed small `c`, with the power loss forced by *FI* (23.8). -/
theorem smallCInner2Eps (h31 : Work.FIArea7.Prop231) (h2psi : Work.FIArea7.Theorem2psi) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (d c r T : ℕ)
        (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ d → 1 ≤ c → 1 ≤ T → 2 ≤ r →
        (2 : ℝ) ^ (r * r) ≤ (T : ℝ) →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        (∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖∑ ℓ ∈ Finset.Icc 1 T,
            (if Nat.Coprime c ℓ then Work.FIArea7.nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
              * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ℓ) else 0)‖
          ≤ C * ((d : ℝ)) * (((c * d).divisors.card : ℝ)) * (|(k : ℝ)| + 1)
              * ((c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)
                + (T : ℝ) ^ ((23 : ℝ) / 24) + (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)))
              * (Real.log ((T : ℝ) + 2)) ^ A * (((T : ℝ) + (c : ℝ) + 2) ^ ε)
              * (K * |b - a| + 1) := by
  intro ε hε
  have hεhalf : (0:ℝ) < ε/2 := by linarith
  obtain ⟨C1, A1, hC1, hA1, hsep⟩ := smallCInner2EpsAux.sepLHSBoundEps h31 (ε/2) hεhalf
  obtain ⟨C2, A2, hC2, hA2, hbig⟩ := smallCInner2EpsAux.peelBigBoundEps h31 (ε/2) hεhalf
  obtain ⟨C3, A3, hC3, hA3, hsmall⟩ := smallCInner2EpsAux.peelSmallBound h2psi
  refine ⟨C1 + C2 * (2:ℝ)^((1:ℝ)/12) + 20*C3, max A1 (max A2 A3) + 1, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro Pa chi k d c r T P a b K hd hc hT hr h2r hchi hmul hper1 hper2 hP hPa hP0 hP1 hPsupp hPder
    have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hT0 : (0:ℝ) < (T:ℝ) := by exact_mod_cast (by omega : 0 < T)
    have hT1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
    have hK0 : 0 ≤ K := le_trans (abs_nonneg (deriv P 0)) (hPder 0)
    set z : ℕ := ⌊(T:ℝ) ^ ((1:ℝ)/(r:ℝ)^2)⌋₊ with hzdef
    set D : ℕ := ⌊(T:ℝ) ^ ((2:ℝ)/(r:ℝ))⌋₊ with hDdef
    have hzle : (z:ℝ) ≤ (T:ℝ)^((1:ℝ)/(r:ℝ)^2) := by
      rw [hzdef]; exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hT0) _)
    have hzr : z^(r*r) ≤ T := by
      have hpow : ((T:ℝ)^((1:ℝ)/(r:ℝ)^2)) ^ (r*r:ℕ) = (T:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hT0)]
        rw [show ((1:ℝ)/(r:ℝ)^2) * (((r*r:ℕ)):ℝ) = 1 by push_cast; field_simp]
        rw [Real.rpow_one]
      have h1 : (z:ℝ)^(r*r:ℕ) ≤ ((T:ℝ)^((1:ℝ)/(r:ℝ)^2)) ^ (r*r:ℕ) :=
        pow_le_pow_left₀ (by positivity) hzle (r*r)
      rw [hpow] at h1
      exact_mod_cast h1
    have h2x : (2:ℝ) ≤ (T:ℝ)^((1:ℝ)/(r:ℝ)^2) := by
      have h2rr : (2:ℝ)^(((r*r:ℕ)):ℝ) ≤ (T:ℝ) := by
        rw [Real.rpow_natCast]; exact h2r
      have hiff := Real.rpow_le_rpow_iff (x := (2:ℝ)) (y := (T:ℝ)^((1:ℝ)/(r:ℝ)^2))
        (z := ((r*r:ℕ):ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hT0) _) (by positivity)
      have hTy : ((T:ℝ)^((1:ℝ)/(r:ℝ)^2)) ^ (((r*r:ℕ)):ℝ) = (T:ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hT0)]
        rw [show ((1:ℝ)/(r:ℝ)^2) * (((r*r:ℕ)):ℝ) = 1 by push_cast; field_simp]
        rw [Real.rpow_one]
      exact hiff.mp (by rw [hTy]; exact h2rr)
    have hz2 : 2 ≤ z := by
      rw [hzdef]; apply Nat.le_floor; exact h2x
    have hzT : z ≤ T := by
      have h2 : (T:ℝ)^((1:ℝ)/(r:ℝ)^2) ≤ (T:ℝ) := by
        have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
        have hle : ((1:ℝ)/(r:ℝ)^2) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith [hr1]
        simpa using Real.rpow_le_rpow_of_exponent_le hT1 hle
      exact_mod_cast (le_trans hzle h2)
    have hzge : (T:ℝ)^((1:ℝ)/(r:ℝ)^2) / 2 ≤ (z:ℝ) := by
      have hfl : (T:ℝ)^((1:ℝ)/(r:ℝ)^2) - 1 < (z:ℝ) := by
        rw [hzdef]; exact Nat.sub_one_lt_floor _
      linarith
    have hzsq : (z:ℝ)^2 ≤ (T:ℝ)^((2:ℝ)/(r:ℝ)^2) := by
      have h1 : (z:ℝ)^2 ≤ ((T:ℝ)^((1:ℝ)/(r:ℝ)^2))^2 := pow_le_pow_left₀ (by positivity) hzle 2
      have h2 : ((T:ℝ)^((1:ℝ)/(r:ℝ)^2))^2 = (T:ℝ)^((2:ℝ)/(r:ℝ)^2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hT0)]
        congr 1; ring
      rwa [h2] at h1
    have hD1 : 1 ≤ D := by
      rw [hDdef]; apply Nat.le_floor
      simpa using Real.one_le_rpow hT1 (by positivity : (0:ℝ) ≤ (2:ℝ)/(r:ℝ))
    have hDle : (D:ℝ) ≤ (T:ℝ)^((2:ℝ)/(r:ℝ)) := by
      rw [hDdef]; exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hT0) _)
    have hDpow : (D:ℝ)^((1:ℝ)/12) ≤ (T:ℝ)^((1:ℝ)/(6*(r:ℝ))) := by
      have h1 : (D:ℝ)^((1:ℝ)/12) ≤ ((T:ℝ)^((2:ℝ)/(r:ℝ)))^((1:ℝ)/12) :=
        Real.rpow_le_rpow (by positivity) hDle (by norm_num)
      have h2 : ((T:ℝ)^((2:ℝ)/(r:ℝ)))^((1:ℝ)/12) = (T:ℝ)^((1:ℝ)/(6*(r:ℝ))) := by
        rw [← Real.rpow_mul (le_of_lt hT0)]
        congr 1; field_simp; ring
      rwa [h2] at h1
    have hDh : ∀ l dd m n, Squarefree l → l ≤ T → (∀ p, p.Prime → p ∣ l → p ≤ z) →
        IsSepPair r dd m n → dd * m * n = l → dd ≤ D := by
      intro l dd m n hsl hlT hzsm hsep' heq
      obtain ⟨kk, p, hp, hdd, hm, hn⟩ := hsep'
      rcases Nat.eq_zero_or_pos kk with hk | hk
      · subst hk
        have h1 : dd = 1 := by rw [hdd]; simp [Work.FIArea7.dIdx]
        rw [h1]; exact hD1
      · have hprod : (∏ i, p i) = l := by rw [← hp.2.2, heq]
        have hp0z : p ⟨0, hk⟩ ≤ z := by
          refine hzsm _ (hp.2.1 _) ?_
          rw [← hprod]
          exact Finset.dvd_prod_of_mem p (Finset.mem_univ _)
        have hzp : (p ⟨0, hk⟩) ^ (r*r) ≤ T :=
          le_trans (Nat.pow_le_pow_left hp0z (r*r)) hzr
        have hmain := Work.FIArea7.sepDiv_pow_le_of_smooth r kk T p hk hr hp.1 hp.2.1
          (by rw [hprod]; exact hlT) hzp
        have hddr : dd^r ≤ T^2 := by rw [hdd]; exact hmain
        rw [hDdef]
        apply Nat.le_floor
        have hcast : (dd:ℝ)^(r:ℕ) ≤ (T:ℝ)^(2:ℕ) := by exact_mod_cast hddr
        have hdd_eq : (dd:ℝ) = ((dd:ℝ)^(r:ℕ)) ^ ((1:ℝ)/(r:ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (dd:ℝ))]
          rw [show (((r:ℕ):ℝ) * ((1:ℝ)/(r:ℝ))) = 1 by push_cast; field_simp]
          rw [Real.rpow_one]
        have h3 : ((dd:ℝ)^(r:ℕ)) ^ ((1:ℝ)/(r:ℝ)) ≤ ((T:ℝ)^(2:ℕ)) ^ ((1:ℝ)/(r:ℝ)) :=
          Real.rpow_le_rpow (by positivity) hcast (by positivity)
        have h4 : ((T:ℝ)^(2:ℕ)) ^ ((1:ℝ)/(r:ℝ)) = (T:ℝ)^((2:ℝ)/(r:ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hT0)]
          congr 1; ring
        calc (dd:ℝ) = ((dd:ℝ)^(r:ℕ)) ^ ((1:ℝ)/(r:ℝ)) := hdd_eq
          _ ≤ ((T:ℝ)^(2:ℕ)) ^ ((1:ℝ)/(r:ℝ)) := h3
          _ = (T:ℝ)^((2:ℝ)/(r:ℝ)) := h4
    set F : ℕ → ℂ := fun ℓ => if ℓ ≤ T then smallCInner2EpsAux.cTerm Pa chi k c P ℓ else 0 with hF
    have hFc : ∀ ℓ, ℓ ≤ T → F ℓ = smallCInner2EpsAux.cTerm Pa chi k c P ℓ := by
      intro ℓ hℓ; rw [hF]; simp [hℓ]
    have hsum1 : (∑ ℓ ∈ Finset.Icc 1 T,
        (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
          * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
          * quadEigen (grossenChar chi k) (c * ℓ) else 0))
        = ∑ ℓ ∈ Finset.Icc 1 T, F ℓ := by
      apply Finset.sum_congr rfl; intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ
      rw [hFc ℓ hℓ.2, smallCInner2EpsAux.cTerm]
    have hsum2 : (∑ ℓ ∈ Finset.Icc 1 T, F ℓ) = sqfreeSum T F := by
      rw [sqfreeSum]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro l hl hne
      by_contra hnsf
      rw [hFc l (Finset.mem_Icc.mp hl).2, smallCInner2EpsAux.cTerm] at hne
      by_cases hcop : Nat.Coprime c l
      · apply hne
        rw [if_pos hcop, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
        simp
      · exact hne (if_neg hcop)
    have h24 : sqfreeSum T F = sepSumLHS T z F + peelSum T z F := sum_sqfree_peel T z F
    have hpeel : peelSum T z F
        = smallCInner2EpsAux.peelSmall2 T z F + smallCInner2EpsAux.peelBig2 T z F :=
      smallCInner2EpsAux.peelSum_eq_small2_add_big2 T z F
    have hsepL : sepSumLHS T z F = sepSumLHS T z (smallCInner2EpsAux.cTerm Pa chi k c P) := by
      rw [sepSumLHS, sepSumLHS]
      apply Finset.sum_congr rfl; intro l hl
      rw [Finset.mem_filter, Finset.mem_Icc] at hl
      exact hFc l hl.1.2
    have hpeelS : smallCInner2EpsAux.peelSmall2 T z F
        = smallCInner2EpsAux.peelSmall2 T z (smallCInner2EpsAux.cTerm Pa chi k c P) := by
      rw [smallCInner2EpsAux.peelSmall2, smallCInner2EpsAux.peelSmall2]
      apply Finset.sum_congr rfl; intro p hp
      apply Finset.sum_congr rfl; intro q hq
      by_cases hcond : Squarefree (p*q) ∧ p*q ≤ T
      · rw [if_pos hcond, if_pos hcond, hFc (p*q) hcond.2]
      · rw [if_neg hcond, if_neg hcond]
    have hpeelB : smallCInner2EpsAux.peelBig2 T z F
        = smallCInner2EpsAux.peelBig2 T z (smallCInner2EpsAux.cTerm Pa chi k c P) := by
      rw [smallCInner2EpsAux.peelBig2, smallCInner2EpsAux.peelBig2]
      apply Finset.sum_congr rfl; intro p hp
      apply Finset.sum_congr rfl; intro q hq
      by_cases hcond : Squarefree (p*q) ∧ p*q ≤ T
      · rw [if_pos hcond, if_pos hcond, hFc (p*q) hcond.2]
      · rw [if_neg hcond, if_neg hcond]
    have hs := hsep Pa chi k c D r T z P a b K hc hD1 hr hz2 hzr hchi hmul hP hPa hP0 hP1 hPsupp hPder hDh
    have hb := hbig Pa chi k c T z P a b K hc (by omega : 1 ≤ z) hzT hchi hmul hP hPa hP0 hP1 hPsupp hPder
    have hm := hsmall Pa chi k c d T z P a b K hc hd hz2 hzT hchi hmul hper1 hper2 hP hPa hP0 hP1 hPsupp hPder
    have harith := smallCInner2EpsAux.bound_combine c d r T z D k b a K C1 A1 C2 A2 C3 A3 hC1 hC2 hC3 hA1 hA2 hA3 hT hr hc hd hK0 hzle hzge hzsq hDpow
    set Q : ℝ := ((T:ℝ) + (c:ℝ) + 2)^ε with hQdef
    have hQ1 : 1 ≤ Q := by
      rw [hQdef]
      exact Real.one_le_rpow (by linarith : (1:ℝ) ≤ (T:ℝ)+(c:ℝ)+2) (le_of_lt hε)
    have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ1
    have hc1 : (1:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have hc0 : (0:ℝ) ≤ (c:ℝ) := by linarith
    have h2r1 : (2:ℝ)/(r:ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hr
    have hDleT : (D:ℝ) ≤ (T:ℝ) := by
      refine le_trans hDle ?_
      simpa using Real.rpow_le_rpow_of_exponent_le hT1 h2r1
    have hlog0 : (0:ℝ) ≤ Real.log ((T:ℝ)+2) := Real.log_nonneg (by linarith)
    have hbase1 : ((T:ℝ) + (c:ℝ)*(D:ℝ) + 2)^(ε/2) ≤ Q := by
      rw [hQdef]
      have hA0 : (0:ℝ) < (T:ℝ)+(c:ℝ)+2 := by positivity
      have hcD : (c:ℝ)*(D:ℝ) ≤ (c:ℝ)*(T:ℝ) := mul_le_mul_of_nonneg_left hDleT hc0
      have hsq : (T:ℝ) + (c:ℝ)*(D:ℝ) + 2 ≤ ((T:ℝ)+(c:ℝ)+2)^2 := by
        nlinarith [hT1, hc1, hcD]
      calc ((T:ℝ) + (c:ℝ)*(D:ℝ) + 2)^(ε/2)
          ≤ (((T:ℝ)+(c:ℝ)+2)^2)^(ε/2) := Real.rpow_le_rpow (by positivity) hsq (by linarith)
        _ = ((T:ℝ)+(c:ℝ)+2)^ε := by
            rw [← Real.rpow_natCast_mul (le_of_lt hA0) 2 (ε/2)]
            congr 1; ring
    have hbase2 : ((T:ℝ) + (c:ℝ) + 2)^(ε/2) ≤ Q := by
      rw [hQdef]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (T:ℝ)+(c:ℝ)+2) (by linarith)
    have hsQ : ‖sepSumLHS T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
        ≤ C1 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
            * (Real.log ((T:ℝ)+2))^A1 * Q * (K * |b-a| + 1) := by
      refine le_trans hs ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase1 ?_) ?_ <;> positivity
    have hbQ : ‖smallCInner2EpsAux.peelBig2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
        ≤ C2 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
            * (Real.log ((T:ℝ)+2))^A2 * Q * (K * |b-a| + 1) := by
      refine le_trans hb ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase2 ?_) ?_ <;> positivity
    have hmQ : ‖smallCInner2EpsAux.peelSmall2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
        ≤ C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
            * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
            * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1) * Q := by
      have hSm0nn : (0:ℝ) ≤ C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
          * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
              + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
          * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1) := le_trans (norm_nonneg _) hm
      calc ‖smallCInner2EpsAux.peelSmall2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
          ≤ C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
              * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                  + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
              * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1) := hm
        _ = (C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
              * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                  + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
              * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1)) * 1 := (mul_one _).symm
        _ ≤ (C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
              * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                  + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
              * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1)) * Q :=
            mul_le_mul_of_nonneg_left hQ1 hSm0nn
    have hnorm : ‖∑ ℓ ∈ Finset.Icc 1 T,
        (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
          * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
          * quadEigen (grossenChar chi k) (c * ℓ) else 0)‖
        ≤ (C1 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
              * (Real.log ((T:ℝ)+2))^A1 * (K * |b-a| + 1)
          + C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
              * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                  + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
              * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1)
          + C2 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
              * (Real.log ((T:ℝ)+2))^A2 * (K * |b-a| + 1)) * Q := by
      rw [hsum1, hsum2, h24, hpeel, hsepL, hpeelS, hpeelB]
      refine le_trans (norm_add_le _ _) ?_
      have h2 : ‖smallCInner2EpsAux.peelSmall2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)
            + smallCInner2EpsAux.peelBig2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
          ≤ ‖smallCInner2EpsAux.peelSmall2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
            + ‖smallCInner2EpsAux.peelBig2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖ :=
        norm_add_le _ _
      have h3 : ‖sepSumLHS T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
            + ‖smallCInner2EpsAux.peelSmall2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
            + ‖smallCInner2EpsAux.peelBig2 T z (smallCInner2EpsAux.cTerm Pa chi k c P)‖
          ≤ (C1 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
                * (Real.log ((T:ℝ)+2))^A1 * Q * (K * |b-a| + 1)
            + C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
                * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                    + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
                * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1) * Q
            + C2 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
                * (Real.log ((T:ℝ)+2))^A2 * Q * (K * |b-a| + 1)) := by
        linarith [hsQ, hmQ, hbQ]
      have h4 : (C1 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
                * (Real.log ((T:ℝ)+2))^A1 * Q * (K * |b-a| + 1)
            + C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
                * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                    + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
                * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1) * Q
            + C2 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
                * (Real.log ((T:ℝ)+2))^A2 * Q * (K * |b-a| + 1))
          = (C1 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
                * (Real.log ((T:ℝ)+2))^A1 * (K * |b-a| + 1)
            + C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
                * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                    + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
                * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1)
            + C2 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
                * (Real.log ((T:ℝ)+2))^A2 * (K * |b-a| + 1)) * Q := by ring
      linarith [h2, h3, h4.le, h4.ge]
    have hfin : (C1 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
              * (Real.log ((T:ℝ)+2))^A1 * (K * |b-a| + 1)
          + C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
              * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
                  + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
              * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1)
          + C2 * (((c.divisors.card : ℕ)) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
              * (Real.log ((T:ℝ)+2))^A2 * (K * |b-a| + 1)) * Q
        ≤ ((C1 + C2 * (2:ℝ)^((1:ℝ)/12) + 20*C3) * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ)
            * (|(k:ℝ)|+1)
            * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77 + 2/(r:ℝ)^2) + (T:ℝ)^((23:ℝ)/24)
                + (T:ℝ)^(1 - 1/(12*(r:ℝ)^2)))
            * (Real.log ((T:ℝ)+2))^(max A1 (max A2 A3) + 1) * (K * |b-a| + 1)) * Q :=
      mul_le_mul_of_nonneg_right harith hQ0
    refine le_trans (le_trans hnorm hfin) (le_of_eq ?_)
    rw [hQdef]; ring

end

end Work.FIArea7
