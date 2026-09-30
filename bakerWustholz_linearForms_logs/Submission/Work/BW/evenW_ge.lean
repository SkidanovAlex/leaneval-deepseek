import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BW

/-- Auxiliary arithmetic lemma (isolated so that `nlinarith` never has to see the floors and
casts): under the six numeric hypotheses collected in `evenW_ge`, the product
`(m+1)·(2k)·L` dominates `13.4·S·D`. -/
private lemma evenW_arith {A u S D P ξr k m L : ℝ}
    (hTp : A ≤ m + 1) (hXu : 4*u*S - 2 ≤ 2*k) (h4u : 0 ≤ 4*u*S - 2)
    (hA_low : 6.297 * P * D ≤ A) (hA_up : A ≤ 6.3 * D) (hPuv : P * u = ξr) (hPu1 : P ≤ 1)
    (hDnn : 0 ≤ D) (hSnn : 0 ≤ S) (hξr : 0.535 ≤ ξr) (hSD : 12.6 * D ≤ 0.0208 * S * D)
    (hm0 : 0 ≤ m) (hL : 1 ≤ L) :
    13.4 * S * D ≤ (m + 1) * (2 * k) * L := by
  have hmp1 : 0 ≤ m + 1 := by linarith
  have h2k : 0 ≤ 2*k := by linarith [h4u, hXu]
  have e1 : A * (4*u*S - 2) ≤ (m+1)*(2*k) := mul_le_mul hTp hXu h4u hmp1
  have e2 : (m+1)*(2*k) ≤ (m+1)*(2*k)*L := by
    have h := mul_le_mul_of_nonneg_left hL (mul_nonneg hmp1 h2k)
    simpa using h
  have hAlg : 6.297 * P * D * (4*u*S - 2) = 25.188 * ξr * S * D - 12.594 * P * D := by
    rw [← hPuv]; ring
  have hb1 : 6.297 * P * D * (4*u*S - 2) ≤ A * (4*u*S - 2) :=
    mul_le_mul_of_nonneg_right hA_low h4u
  have hPle : 12.594 * P * D ≤ 12.6 * D := by nlinarith [hPu1, hDnn]
  have hb2 : 25.188 * ξr * S * D - 12.6 * D ≤ 6.297 * P * D * (4*u*S - 2) := by
    rw [hAlg]; linarith [hPle]
  have hb3 : 13.4 * S * D ≤ 25.188 * ξr * S * D - 12.6 * D := by
    nlinarith [hξr, hSD, hSnn, hDnn, mul_nonneg hSnn hDnn]
  linarith [e1, e2, hb1, hb2, hb3]

/-- Numeric lower bound for the lacunary-product term `evW` of the even step (BW §19, (23'), pp. 57–58), in units of `S·D`.

`evW r d h σ J = (T'+1)·X·log(R/(X+2))` with `T' = evTp r J T = ⌊(1−ξ)ξ^r·ξ^{rJ}T⌋`, `X = evX = 2·evSP`, `evSP = ⌊2ξ^{-rJ}S⌋`, `R = 7.2·evSP`, `S = pS r d h`, `D = pD r d σ`, `T = pT r d σ`, `ξ = pxi r`.

Route. Let `u = ξ^{-rJ} ≥ 1`, `A = (1−ξ)ξ^rξ^{rJ}T`, so `T' = ⌊A⌋ > A − 1`, i.e. `T'+1 > A`.
* `num_T`: `(1−ξ)T ≥ 6.297 D`, hence `A ≥ 6.297·ξ^{r(J+1)}·D`; also `(1−ξ)T ≤ 6.3D` hence `A ≤ 6.3ξ^{r(J+1)}D ≤ 6.3D`.
* `evSP > 2uS − 1`, so `X = 2·evSP > 4uS − 2`.
* `num_T`: `S ≥ 608`; with `u ≥ 1` this gives `evSP ≥ 1216`, hence `R/(X+2) = 7.2·evSP/(2·evSP+2) ≥ 7.2·1216/2434 = 3.597 ≥ e`, so `log(R/(X+2)) ≥ 1` (use `Real.exp_one_lt_three` and `Real.le_log_iff_exp_le`).
* Therefore `evW > A·(4uS−2) ≥ 6.297ξ^{r(J+1)}D·(4uS−2) = 25.188·ξ^r·S·D − 2A ≥ 25.188·ξ^r·S·D − 12.6·D`.
* `num_xi`: `ξ^r ≥ 0.535`, so `25.188·0.535 = 13.4756`, and `12.6·D ≤ 0.0756·S·D` because `6.3·2/608 = 0.0207 ≤ 0.0756` and `S ≥ 608`. -/
theorem evenW_ge {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h) {σ : Fin r → ℝ}
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : J + 1 ≤ pI r d) :
    13.4 * (pS r d h : ℝ) * pD r d σ ≤ evW r d h σ J := by
  -- ## basic numeric facts about the parameters
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hξpos : 0 < pxi r := by
    have h : (0.536:ℝ)/r < 1 := by rw [div_lt_one hr0]; linarith
    rw [pxi]; linarith
  have hξle1 : pxi r ≤ 1 := by
    have h : (0:ℝ) < 0.536/r := div_pos (by norm_num) hr0
    rw [pxi]; linarith
  have hξnn : 0 ≤ pxi r := le_of_lt hξpos
  have h1mξ : 0 ≤ 1 - pxi r := by linarith
  -- ## `num_T`, `num_xi` (their conclusions get rewritten by the `set`s below)
  obtain ⟨hTl0, hTu0, _hdhT0, hS608⟩ := num_T hr hd hh σ hσ
  obtain ⟨_hu187, hξr0535, _hξrm1, _hξj, _hb107⟩ := num_xi hr
  -- ## unfold `evW` and introduce abbreviations for its ingredients
  unfold evW evTp evX evSP evR
  set S : ℝ := (pS r d h : ℝ) with hSdef
  set D : ℝ := pD r d σ with hDdef
  set T : ℝ := (pT r d σ : ℝ) with hTdef
  set u : ℝ := pxi r ^ (-((r*J:ℕ):ℤ)) with hudef
  set k : ℕ := ⌊2 * (u * S)⌋₊ with hkdef
  set A : ℝ := (1 - pxi r) * pxi r ^ r * (pxi r ^ (r*J) * T) with hAdef
  set m : ℕ := ⌊A⌋₊ with hmdef
  -- ## `num_T` in the abbreviated language
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  have hS608' : (608:ℝ) ≤ S := hS608
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  have hDnn : 0 ≤ D := by rw [hDdef]; linarith [pD_ge_one hr hd σ hσ]
  have hTl : 6.297 * D ≤ (1 - pxi r) * T := hTl0
  have hTu : (1 - pxi r) * T ≤ 6.3 * D := hTu0
  -- ## powers of `ξ`
  have hPeq : pxi r ^ (r * (J+1)) = pxi r ^ (r*J) * pxi r ^ r := by
    rw [Nat.mul_succ, pow_add]
  have hAT : (1 - pxi r) * T * (pxi r ^ (r*(J+1))) = A := by rw [hAdef, hPeq]; ring
  have hPle1 : pxi r ^ (r*(J+1)) ≤ 1 := pow_le_one₀ hξnn hξle1
  have hPnn : 0 ≤ pxi r ^ (r*(J+1)) := pow_nonneg hξnn _
  -- ## bounds on `A`
  have hA_low : 6.297 * (pxi r ^ (r*(J+1))) * D ≤ A := by
    have h1 : 6.297 * D * (pxi r ^ (r*(J+1))) ≤ (1 - pxi r) * T * (pxi r ^ (r*(J+1))) :=
      mul_le_mul_of_nonneg_right hTl hPnn
    rw [hAT] at h1
    nlinarith [h1]
  have hA_up : A ≤ 6.3 * D := by
    have h1 : (1 - pxi r) * T * (pxi r ^ (r*(J+1))) ≤ 6.3 * D * 1 :=
      mul_le_mul hTu hPle1 hPnn (by linarith [hDnn])
    rw [hAT, mul_one] at h1
    exact h1
  -- ## bounds on `u`
  have huz : pxi r ^ (-((r*J:ℕ):ℤ)) = (pxi r ^ (r*J))⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hu1 : 1 ≤ u := by
    rw [hudef, huz]
    exact (one_le_inv₀ (pow_pos hξpos (r*J))).mpr (pow_le_one₀ hξnn hξle1)
  have hPuv : pxi r ^ (r*(J+1)) * u = pxi r ^ r := by
    rw [hudef, huz, hPeq]
    have hAne : pxi r ^ (r*J) ≠ 0 := pow_ne_zero _ (ne_of_gt hξpos)
    calc (pxi r ^ (r*J) * pxi r ^ r) * (pxi r ^ (r*J))⁻¹
        = pxi r ^ r * ((pxi r ^ (r*J)) * (pxi r ^ (r*J))⁻¹) := by ring
      _ = pxi r ^ r * 1 := by rw [mul_inv_cancel₀ hAne]
      _ = pxi r ^ r := by ring
  -- ## floor facts: `T' = evTp r J T` and `X = evX r J S`
  have hTp : A ≤ (m:ℝ) + 1 := by
    have h := Nat.lt_floor_add_one A
    rw [← hmdef] at h
    exact le_of_lt h
  have hZ1216 : (1216:ℝ) ≤ 2 * (u * S) := by nlinarith [hu1, hS608']
  have hk1216 : 1216 ≤ k := by rw [hkdef]; exact Nat.le_floor hZ1216
  have hkR5 : (5:ℝ) ≤ (k:ℝ) := by
    have h : (5:ℕ) ≤ k := le_trans (by norm_num) hk1216
    exact_mod_cast h
  have hXu : 4*u*S - 2 ≤ 2*(k:ℝ) := by
    have h := Nat.lt_floor_add_one (2 * (u*S))
    rw [← hkdef] at h
    linarith
  have h4u : 0 ≤ 4*u*S - 2 := by nlinarith [hu1, hS608']
  -- ## the logarithmic factor is at least `1`
  have hden : (0:ℝ) < 2*(k:ℝ) + 2 := by positivity
  have hratio3 : (3:ℝ) ≤ 7.2 * (k:ℝ) / (2*(k:ℝ) + 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [hkR5]
  have hexp3 : Real.exp 1 ≤ 7.2 * (k:ℝ) / (2*(k:ℝ) + 2) :=
    le_trans (le_of_lt Real.exp_one_lt_three) hratio3
  have hlog : 1 ≤ Real.log (7.2 * (k:ℝ) / (2*(k:ℝ) + 2)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp3
    rwa [Real.log_exp] at h
  -- ## `12.6·D ≤ 0.0208·S·D` from `S ≥ 608`
  have hSD : 12.6 * D ≤ 0.0208 * S * D := by
    have h1 : (12.6:ℝ) ≤ 0.0208 * S := by nlinarith [hS608']
    nlinarith [h1, hDnn]
  -- ## reconcile the casts in the goal and apply the arithmetic lemma
  have hcast1 : (((m + 1 : ℕ) : ℝ)) = (m:ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hcast2 : (((2 * k : ℕ) : ℝ)) = 2 * (k:ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
  rw [hcast1, hcast2]
  exact evenW_arith (A := A) (u := u) (S := S) (D := D) (P := pxi r ^ (r*(J+1)))
    (ξr := pxi r ^ r) (k := (k:ℝ)) (m := (m:ℝ))
    (L := Real.log (7.2 * (k:ℝ) / (2*(k:ℝ) + 2)))
    hTp hXu h4u hA_low hA_up hPuv hPle1 hDnn hSnn hξr0535 hSD
    (Nat.cast_nonneg m) hlog

end Work.BW
