import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fhat_inversion
import Submission.Work.GM.Affine.comb_sum_le
import Submission.Work.GM.Affine.aliasing_le
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.crude_b.pointwise_le
import Submission.Work.GM.Affine.crude_b.integral_sq_le
import Submission.Work.GM.Affine.crude_b.final_arith
import Submission.Work.GM.Affine.aliasing_sharp

/-!
# GM §9: the crude case of Proposition 9.1 (`Work.GM.Affine.crude_case`)

The target is the explicit-constant form of the case `Mbig ≳ T` of GM's Proposition 9.1:

`∫ u, (affineSum K M₁ M₂ M₃ f u)^2 ≤ 2^22 (1+c(j,ε))^2 (1+c(2,ε))^2 (C₀+K+1) *
    max (Mbig^6 (∫f)^2) (T^{4+4ε+2j} (∫f)^2 Mbig^{6-2j})`.

## Route

* `pointwise_le` (area `crude_b`, already proved): for fixed `u`, summing Poisson summation
  (`comb_sum_le`) over the `m₂`-range and using the *sharp* aliasing bound
  `aliasing f m ≤ ∫f + 4 (∫f)^{1-1/j} (c(j,ε) T^ε (T/m)^j sup f)^{1/j}`
  (`aliasing_sharp`, this area) together with `sup f ≤ 16 c(2,ε) T^ε T² ∫f`
  gives `J(u) ≤ #R₁ · (∫f) · (4 M₂² + 8 K M₂)` with `K = (16 c(j,ε) c(2,ε) T^{j+2+2ε})^{1/j}`.
* `integral_sq_le` (area `crude_b`): `J` is supported in `[-L,L]`,
  `L = (2C₀M₂+KM₃)/M₁`, hence `∫ J² ≤ 2L (sup J)²`.
* `crude_card_R1_sq_le`: `#R₁ ≤ 4M₁`, i.e. `(#R₁)² Mbig ≤ 32 Mbig² M₁`.
* `crude_arith_step`: the elementary arithmetic collapsing the two main terms to
  `2048 (2C₀+K) Mbig^6 (∫f)² + 8192 (2C₀+K) K² Mbig^4 (∫f)²`.
* `final_arith` (area `crude_b`): the case analysis on which term of the `max` dominates, via
  weighted AM–GM (`T^{2+(4+4ε)/j} Mbig^4 ≤ max (Mbig^6) (T^{4+4ε+2j} Mbig^{6-2j})`).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ### Counting the `m₁`-range `R₁` -/

/-- `#(R1 M₁) ≤ 4 M₁`: the elements of `R1 M₁` are the integers `m ≠ 0` in `[-⌊2M₁⌋, ⌊2M₁⌋]`
with `|m| > M₁`, and there are at most `2⌊2M₁⌋ ≤ 4 M₁` of those. -/
lemma crude_card_R1_le {M₁ : ℝ} (hM₁ : 0 < M₁) : ((R1 M₁).card : ℝ) ≤ 4 * M₁ := by
  set N : ℤ := ⌊2 * M₁⌋ with hN
  have hN0 : 0 ≤ N := by rw [hN]; exact Int.floor_nonneg.mpr (by linarith)
  have hsub : R1 M₁ ⊆ (Finset.Icc (-N) N).erase 0 := by
    intro m hm
    rw [R1, Finset.mem_filter] at hm
    obtain ⟨hmI, hmM⟩ := hm
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro h0
      rw [h0] at hmM
      simp at hmM
      linarith
    · simpa [hN] using hmI
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_Icc.mpr ⟨by omega, hN0⟩), Int.card_Icc] at hcard
  have h1 : ((⌊2 * M₁⌋ + 1 - -⌊2 * M₁⌋ : ℤ).toNat - 1 : ℕ) ≤ (2 * ⌊2 * M₁⌋).toNat := by
    have h2n : (0 : ℤ) ≤ ⌊2 * M₁⌋ + 1 - -⌊2 * M₁⌋ := by omega
    have h3 : ((⌊2 * M₁⌋ + 1 - -⌊2 * M₁⌋ : ℤ).toNat : ℤ) = ⌊2 * M₁⌋ + 1 - -⌊2 * M₁⌋ :=
      Int.toNat_of_nonneg h2n
    have h4 : (0 : ℤ) ≤ 2 * ⌊2 * M₁⌋ := by omega
    have h5 : ((2 * ⌊2 * M₁⌋).toNat : ℤ) = 2 * ⌊2 * M₁⌋ := Int.toNat_of_nonneg h4
    omega
  have h2 : ((((2 * ⌊2 * M₁⌋).toNat : ℕ)) : ℝ) ≤ 4 * M₁ := by
    have h3 : (0 : ℤ) ≤ 2 * ⌊2 * M₁⌋ := by omega
    have h5 : ((((2 * ⌊2 * M₁⌋).toNat : ℕ)) : ℝ) = (2 * (⌊2 * M₁⌋ : ℝ)) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h3]; push_cast; ring
    rw [h5]
    have h6 := Int.floor_le (2 * M₁)
    linarith
  calc ((R1 M₁).card : ℝ)
      ≤ (((⌊2 * M₁⌋ + 1 - -⌊2 * M₁⌋ : ℤ).toNat - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ((((2 * ⌊2 * M₁⌋).toNat : ℕ)) : ℝ) := by exact_mod_cast h1
    _ ≤ 4 * M₁ := h2

/-- `(#R1 M₁)² Mbig ≤ 32 Mbig² M₁` for `0 < M₁ ≤ Mbig`, `1 ≤ Mbig` (the cardinality input of
`crude_arith_step`). -/
lemma crude_card_R1_sq_le {M₁ Mbig : ℝ} (hM₁ : 0 < M₁) (hM1 : M₁ ≤ Mbig) (hMb : 1 ≤ Mbig) :
    (((R1 M₁).card : ℝ)) ^ 2 * Mbig ≤ 32 * Mbig ^ 2 * M₁ := by
  have hc := crude_card_R1_le hM₁
  have hcnn : (0 : ℝ) ≤ ((R1 M₁).card : ℝ) := by positivity
  have hMnn : 0 ≤ M₁ := le_of_lt hM₁
  have hMbnn : 0 ≤ Mbig := le_trans zero_le_one hMb
  have h4 : ((R1 M₁).card : ℝ) ^ 2 ≤ 16 * M₁ ^ 2 := by
    have := mul_self_le_mul_self hcnn (by linarith : ((R1 M₁).card : ℝ) ≤ 4 * M₁)
    nlinarith [this]
  calc (((R1 M₁).card : ℝ)) ^ 2 * Mbig ≤ 16 * M₁ ^ 2 * Mbig :=
        mul_le_mul_of_nonneg_right h4 hMbnn
    _ ≤ 16 * M₁ * Mbig ^ 2 := by
        have h5 : M₁ ^ 2 * Mbig ≤ M₁ * Mbig ^ 2 := by
          calc M₁ ^ 2 * Mbig = (M₁ * Mbig) * M₁ := by ring
            _ ≤ (M₁ * Mbig) * Mbig := mul_le_mul_of_nonneg_left hM1 (by positivity)
            _ = M₁ * Mbig ^ 2 := by ring
        linarith [h5]
    _ ≤ 32 * Mbig ^ 2 * M₁ := by
        have h6 : 0 ≤ M₁ * Mbig ^ 2 := mul_nonneg hMnn (sq_nonneg Mbig)
        linarith

/-! ### The elementary arithmetic step -/

/-- Combining the pointwise bound `J(u) ≤ #R₁ · A · (4M₂²+8αM₂)`, the support-length `2L` and the
cardinality bound `(#R₁)²Mbig ≤ 32 Mbig²M₁`:
`2L sup(J)² ≤ 2048(2C₀+K)Mbig^6 A² + 8192(2C₀+K) α² Mbig^4 A²`. -/
lemma crude_arith_step {C₀ K M₁ M₂ M₃ Mbig A α : ℝ}
    (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hMb : 1 ≤ Mbig) (hM1 : M₁ ≤ Mbig) (hM2 : M₂ ≤ Mbig) (hM3 : M₃ ≤ Mbig)
    (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hcard : (((R1 M₁).card : ℝ)) ^ 2 * Mbig ≤ 32 * Mbig ^ 2 * M₁) :
    2 * ((2 * C₀ * M₂ + K * M₃) / M₁) * ((((R1 M₁).card : ℝ)) * A * (4 * M₂ ^ 2 + 8 * α * M₂)) ^ 2 ≤
      2048 * (2 * C₀ + K) * Mbig ^ 6 * A ^ 2 + 8192 * (2 * C₀ + K) * α ^ 2 * Mbig ^ 4 * A ^ 2 := by
  set N : ℝ := ((R1 M₁).card : ℝ) with hN
  have hNnn : 0 ≤ N := by rw [hN]; positivity
  have hMbpos : 0 < Mbig := lt_of_lt_of_le zero_lt_one hMb
  have hcard' : N ^ 2 * Mbig ≤ 32 * Mbig ^ 2 * M₁ := by rw [hN]; exact hcard
  have hN2 : N ^ 2 ≤ 32 * Mbig * M₁ := by
    have h : N ^ 2 * Mbig ≤ (32 * Mbig * M₁) * Mbig := by nlinarith [hcard']
    exact (mul_le_mul_iff_of_pos_right hMbpos).mp h
  have hbase : 0 ≤ 4 * M₂ ^ 2 + 8 * α * M₂ := by nlinarith
  have hsq : (4 * M₂ ^ 2 + 8 * α * M₂) ^ 2 ≤ 32 * M₂ ^ 4 + 128 * α ^ 2 * M₂ ^ 2 := by
    nlinarith [sq_nonneg (M₂ - 2 * α), sq_nonneg M₂]
  have h2C0K : 0 ≤ 2 * C₀ + K := by linarith
  have hMM : 2 * C₀ * M₂ + K * M₃ ≤ (2 * C₀ + K) * Mbig := by nlinarith
  have hMMnn : 0 ≤ 2 * C₀ * M₂ + K * M₃ := by nlinarith
  have hM2sq : M₂ ^ 2 ≤ Mbig ^ 2 := by nlinarith
  have hM2pow : M₂ ^ 4 ≤ Mbig ^ 4 := by nlinarith
  have hkey1 : N ^ 2 * M₂ ^ 4 ≤ 32 * Mbig ^ 5 * M₁ := by
    calc N ^ 2 * M₂ ^ 4 ≤ (32 * Mbig * M₁) * Mbig ^ 4 :=
          mul_le_mul hN2 hM2pow (by positivity) (by positivity)
      _ = 32 * Mbig ^ 5 * M₁ := by ring
  have hkey2 : N ^ 2 * M₂ ^ 2 ≤ 32 * Mbig ^ 3 * M₁ := by
    calc N ^ 2 * M₂ ^ 2 ≤ (32 * Mbig * M₁) * Mbig ^ 2 :=
          mul_le_mul hN2 hM2sq (by positivity) (by positivity)
      _ = 32 * Mbig ^ 3 * M₁ := by ring
  have hkey1' : (2 * C₀ * M₂ + K * M₃) * (N ^ 2 * M₂ ^ 4) ≤ (32 * (2 * C₀ + K) * Mbig ^ 6) * M₁ := by
    calc (2 * C₀ * M₂ + K * M₃) * (N ^ 2 * M₂ ^ 4)
        ≤ ((2 * C₀ + K) * Mbig) * (32 * Mbig ^ 5 * M₁) :=
          mul_le_mul hMM hkey1 (by positivity) (by nlinarith)
      _ = (32 * (2 * C₀ + K) * Mbig ^ 6) * M₁ := by ring
  have hkey2' : (2 * C₀ * M₂ + K * M₃) * (N ^ 2 * M₂ ^ 2) ≤ (32 * (2 * C₀ + K) * Mbig ^ 4) * M₁ := by
    calc (2 * C₀ * M₂ + K * M₃) * (N ^ 2 * M₂ ^ 2)
        ≤ ((2 * C₀ + K) * Mbig) * (32 * Mbig ^ 3 * M₁) :=
          mul_le_mul hMM hkey2 (by positivity) (by nlinarith)
      _ = (32 * (2 * C₀ + K) * Mbig ^ 4) * M₁ := by ring
  have hdiv1 : ((2 * C₀ * M₂ + K * M₃) / M₁) * N ^ 2 * M₂ ^ 4 ≤ 32 * (2 * C₀ + K) * Mbig ^ 6 := by
    calc ((2 * C₀ * M₂ + K * M₃) / M₁) * N ^ 2 * M₂ ^ 4
        = ((2 * C₀ * M₂ + K * M₃) * (N ^ 2 * M₂ ^ 4)) / M₁ := by ring
      _ ≤ 32 * (2 * C₀ + K) * Mbig ^ 6 := by
          rw [div_le_iff₀ hM₁]
          linarith [hkey1']
  have hdiv2 : ((2 * C₀ * M₂ + K * M₃) / M₁) * N ^ 2 * M₂ ^ 2 ≤ 32 * (2 * C₀ + K) * Mbig ^ 4 := by
    calc ((2 * C₀ * M₂ + K * M₃) / M₁) * N ^ 2 * M₂ ^ 2
        = ((2 * C₀ * M₂ + K * M₃) * (N ^ 2 * M₂ ^ 2)) / M₁ := by ring
      _ ≤ 32 * (2 * C₀ + K) * Mbig ^ 4 := by
          rw [div_le_iff₀ hM₁]
          linarith [hkey2']
  have hsq2 : (N * A * (4 * M₂ ^ 2 + 8 * α * M₂)) ^ 2 = N ^ 2 * A ^ 2 * (4 * M₂ ^ 2 + 8 * α * M₂) ^ 2 := by
    ring
  calc 2 * ((2 * C₀ * M₂ + K * M₃) / M₁) * (N * A * (4 * M₂ ^ 2 + 8 * α * M₂)) ^ 2
      ≤ 2 * ((2 * C₀ * M₂ + K * M₃) / M₁) * (N ^ 2 * A ^ 2 * (32 * M₂ ^ 4 + 128 * α ^ 2 * M₂ ^ 2)) := by
        rw [hsq2]
        have h1 : N ^ 2 * A ^ 2 * (4 * M₂ ^ 2 + 8 * α * M₂) ^ 2 ≤
            N ^ 2 * A ^ 2 * (32 * M₂ ^ 4 + 128 * α ^ 2 * M₂ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        have h2 : 0 ≤ 2 * ((2 * C₀ * M₂ + K * M₃) / M₁) := by
          have := div_nonneg hMMnn hM₁.le; linarith
        exact mul_le_mul_of_nonneg_left h1 h2
    _ = 64 * (((2 * C₀ * M₂ + K * M₃) / M₁) * N ^ 2 * M₂ ^ 4) * A ^ 2
        + 256 * (((2 * C₀ * M₂ + K * M₃) / M₁) * N ^ 2 * M₂ ^ 2) * α ^ 2 * A ^ 2 := by ring
    _ ≤ 64 * (32 * (2 * C₀ + K) * Mbig ^ 6) * A ^ 2
        + 256 * (32 * (2 * C₀ + K) * Mbig ^ 4) * α ^ 2 * A ^ 2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiv1 (by norm_num)) (by positivity)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv2 (by norm_num)) (by positivity)) (by positivity)
    _ = 2048 * (2 * C₀ + K) * Mbig ^ 6 * A ^ 2 + 8192 * (2 * C₀ + K) * α ^ 2 * Mbig ^ 4 * A ^ 2 := by ring

/-! ### Assembly -/

/-- The crude case, given the sharp aliasing bound `hsharp` as a hypothesis (so that this file
can be built independently of `aliasing_sharp`). -/
theorem crude_case_of_sharp {c : ℕ → ℝ → ℝ} {K C₀ T Mbig M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ}
    {j : ℕ} {ε : ℝ}
    (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hj : 3 ≤ j) (hε : 0 < ε) (hT : 0 ≤ T)
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f)
    (hsupp : SuppHyp C₀ f) (hdec : DecayHyp c T f)
    (hcj : 0 ≤ c j ε) (hc2 : 0 ≤ c 2 ε)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hM1 : M₁ ≤ Mbig) (hM2 : M₂ ≤ Mbig) (hM3 : M₃ ≤ Mbig) (hMb : 1 ≤ Mbig)
    (hsharp : ∀ m : ℝ, 0 < m → aliasing f m ≤ (∫ u, f u) +
        4 * (∫ u, f u) ^ (1 - 1/(j:ℝ)) * (c j ε * T ^ ε * (T/m) ^ j * supf f) ^ (1/(j:ℝ))) :
    ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 ≤
      (2 ^ 22 * (1 + c j ε) ^ 2 * (1 + c 2 ε) ^ 2 * (C₀ + K + 1)) *
        max (Mbig ^ 6 * (∫ u, f u) ^ 2)
            (T ^ (4 + 4 * ε + 2 * j) * (∫ u, f u) ^ 2 * Mbig ^ (6 - 2 * (j : ℝ))) := by
  have hU : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hpt := crude_b.pointwise_le (c := c) (K := K) (C₀ := C₀) (T := T) (M₁ := M₁)
    (M₂ := M₂) (M₃ := M₃) (f := f) (j := j) (ε := ε) hε hj hT hf hnn hcs hdec hcj hc2 hM₁ hM₂ hsharp
  have hKnn : 0 ≤ (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) := by positivity
  have hPnn : 0 ≤ ((R1 M₁).card : ℝ) * (∫ u, f u) *
      (4 * M₂ ^ 2 + 8 * (16 * c j ε * c 2 ε * T ^ ((j:ℝ) + 2 + 2*ε)) ^ (1/(j:ℝ)) * M₂) := by
    have h2 : 0 ≤ ∫ u, f u := integral_nonneg hnn
    positivity
  have hint := crude_b.integral_sq_le hC₀ hK hM₁ hM₂ hM₃ hnn hsupp hPnn hpt
  have hcard := crude_card_R1_sq_le hM₁ hM1 hMb
  have harith := crude_arith_step hC₀ hK hM₁ hM₂ hM₃ hMb hM1 hM2 hM3 hU hKnn hcard
  have hfin := crude_b.final_arith (C₀ := C₀) (K := K) (T := T) (Mbig := Mbig)
    (U := ∫ u, f u) (cj := c j ε) (c2 := c 2 ε) (j := j) (ε := ε) hC₀ hK hj hε hT hU hMb hcj hc2
  exact le_trans hint (le_trans harith hfin)

theorem crude_case {c : ℕ → ℝ → ℝ} {K C₀ T Mbig M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} {j : ℕ} {ε : ℝ}
    (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hj : 3 ≤ j) (hε : 0 < ε) (hT : 0 ≤ T)
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f)
    (hsupp : SuppHyp C₀ f) (hdec : DecayHyp c T f)
    (hcj : 0 ≤ c j ε) (hc2 : 0 ≤ c 2 ε)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hM1 : M₁ ≤ Mbig) (hM2 : M₂ ≤ Mbig) (hM3 : M₃ ≤ Mbig) (hMb : 1 ≤ Mbig) :
    ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 ≤
      (2 ^ 22 * (1 + c j ε) ^ 2 * (1 + c 2 ε) ^ 2 * (C₀ + K + 1)) *
        max (Mbig ^ 6 * (∫ u, f u) ^ 2)
            (T ^ (4 + 4 * ε + 2 * j) * (∫ u, f u) ^ 2 * Mbig ^ (6 - 2 * (j : ℝ))) :=
  crude_case_of_sharp hC₀ hK hj hε hT hf hnn hcs hsupp hdec hcj hc2 hM₁ hM₂ hM₃ hM1 hM2 hM3 hMb
    (fun m hm => aliasing_sharp hf hnn hcs hdec hj hε m hm)

end

end Work.GM.Affine
