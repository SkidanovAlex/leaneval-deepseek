import Mathlib
import Submission.Work.Peluse.Reduction
import Submission.Work.Peluse.Statement
import Submission.Work.Peluse.RpowTools

/-!
# `AreaA2` from the crux

This module proves that `PeluseCrux` (the two deep chapters of Peluse's inverse theorem, packaged
in `Nodes.lean`) implies Peluse's inverse theorem in the form `AreaA2` of `Statement.lean`.

Everything here is constant bookkeeping; the mathematical content is inside `PeluseCrux`.

The reduction (with `d = P.natDegree`, `δ` the correlation threshold, `N` the number of polynomial
values, `N₀` the `x`-range, `ε = δ N^d / N₀`):

* the trivial bound `δ N^d ≤ |⟨Ã_N(f,g),h⟩| ≤ 2N₀+1` (`AhalfZ_pairing_bound`) shows that in the
  non-degenerate case (`N` larger than the first alternative) one has `N₀ ≥ 1` and the scale
  imbalance `N^d/N₀` is at most `δ^{-1}` (up to `A`), which is exactly what `PeluseCrux` needs;
* the upper-half average is a full average minus half of the average over `⌊N/2⌋`
  (`half_le_of_pairing`), so `ε ≤ ‖Λ^{N₀,N}‖` gives a lower bound for `Λ` either at `N` (with `ε/2`)
  or at `⌊N/2⌋` (with `ε`); this is the only place where the workspace's `AhalfZ` (the paper's
  upper-half average) enters;
* for each of the two scales `Nc ∈ {N, ⌊N/2⌋}` one applies `PeluseCrux` with threshold
  `δc = min 1 (ε_c N₀ / Nc^d) ≥ δ²/(6A)`: the hypothesis `δc Nc^d ≤ ‖Λ‖ N₀` holds by construction,
  and the three conclusions of `PeluseCrux` are turned into the three requirements of
  `PeluseInverseKMT` by `δc^K ≥ δ^{2K}/(6A)^K` and `K₁ = 4K+1 ≥ 4K`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

open Work.Analysis.InverseTheory (AhalfZ bilinPair)

/-- In the non-degenerate case, `δ x ≥ 2` together with the trivial bound `δ x ≤ 2N₀+1` forces
`N₀ ≥ 1`. -/
private lemma one_le_of_two_le_mul {δ x : ℝ} {N₀ : ℕ} (h : 2 ≤ δ * x)
    (htriv : δ * x ≤ 2 * (N₀ : ℝ) + 1) : 1 ≤ N₀ := by
  by_contra hcon
  have h0 : N₀ = 0 := by omega
  subst h0
  simp at htriv
  linarith

/-- `N ≤ 2⌊N/2⌋ + 1`. -/
private lemma nat_self_le_two_div_add_one (N : ℕ) : N ≤ 2 * (N / 2) + 1 := by
  have h := Nat.div_add_mod N 2
  have hmod : N % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt N (by norm_num : 0 < 2))
  omega

/-- `(N-1)/2 ≤ ⌊N/2⌋`. -/
private lemma half_div_cast_le (N : ℕ) : ((N : ℝ) - 1) / 2 ≤ ((N / 2 : ℕ) : ℝ) := by
  have h1 := nat_self_le_two_div_add_one N
  have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
    have hcast : (N : ℝ) ≤ ((2 * (N / 2) + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h1
    push_cast at hcast
    linarith
  linarith

/-- `x * x⁻¹^(m+1) = x⁻¹^m` for `x ≠ 0`. -/
private lemma mul_inv_pow_succ' {x : ℝ} (hx : x ≠ 0) (m : ℕ) :
    x * x⁻¹ ^ (m + 1) = x⁻¹ ^ m := by
  rw [pow_succ, ← mul_assoc, mul_comm x (x⁻¹ ^ m), mul_assoc, mul_inv_cancel₀ hx, mul_one]

/-- `(a/b) * (b*c) = a*c` for `b ≠ 0`. -/
private lemma div_mul_const {a b c : ℝ} (hb : b ≠ 0) : (a / b) * (b * c) = a * c := by
  field_simp

/-- `(a/b) * (x/c * z) = (a/(b*c)) * (x*z)` for `b, c ≠ 0`. -/
private lemma div_mul_div_mul' {a b c x z : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    (a / b) * (x / c * z) = (a / (b * c)) * (x * z) := by
  field_simp

/-- **Area A2 from the crux.** -/
theorem AreaA2_of_crux (h : ∀ P : Polynomial ℤ, 2 ≤ P.natDegree → Work.Peluse.PeluseCrux P) :
    Work.Peluse.AreaA2 := by
  intro P hd A hA1
  have hA1' : (1 : ℝ) ≤ A := hA1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have h4d1 : (1 : ℝ) ≤ (4 : ℝ) ^ P.natDegree := one_le_pow₀ (by norm_num)
  set A' : ℝ := A * 4 ^ P.natDegree with hA'def
  have hA'1 : 1 ≤ A' := by rw [hA'def]; nlinarith only [hA1', h4d1]
  have hA'pos : 0 < A' := lt_of_lt_of_le zero_lt_one hA'1
  obtain ⟨C, K, hCn, hKn, hcrux⟩ := h P hd A' hA'1
  have hCp : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCn
  have hCpos : (0 : ℝ) < (C : ℝ) := by linarith only [hCp]
  set C1 : ℝ := 8 * (C : ℝ) * (6 * A) ^ (2 * K) * A' + 8 with hC1def
  set K1 : ℕ := 4 * K + 1 with hK1def
  have hC1pos : 0 < C1 := by rw [hC1def]; positivity
  have hK1pos : 0 < K1 := by rw [hK1def]; omega
  have h6A1 : (1 : ℝ) ≤ 6 * A := by linarith only [hA1']
  have h6Apos : (0 : ℝ) < 6 * A := by linarith only [h6A1]
  have hpow1 : (1 : ℝ) ≤ (6 * A) ^ K := one_le_pow₀ h6A1
  have hpow12 : (6 * A) ^ K ≤ (6 * A) ^ (2 * K) := pow_le_pow_right₀ h6A1 (by omega)
  have h6ApowKpos : (0 : ℝ) < (6 * A) ^ K := pow_pos h6Apos K
  have hC1_8 : (8 : ℝ) ≤ C1 := by
    rw [hC1def]
    have h : (0 : ℝ) ≤ 8 * (C : ℝ) * (6 * A) ^ (2 * K) * A' := by positivity
    linarith only [h]
  have hc7 : (C : ℝ) * (6 * A) ^ K ≤ C1 := by
    rw [hC1def]
    have h1 : (6 * A) ^ K ≤ 8 * (6 * A) ^ (2 * K) * A' := by
      nlinarith only [hpow12, hpow1, hA'1]
    have h2 := mul_le_mul_of_nonneg_left h1 hCpos.le
    linarith only [h2]
  have hc4 : 4 * (C : ℝ) * (6 * A) ^ K ≤ C1 := by
    rw [hC1def]
    have h1 : 4 * (6 * A) ^ K ≤ 8 * (6 * A) ^ (2 * K) * A' := by
      nlinarith only [hpow12, hpow1, hA'1]
    have h2 := mul_le_mul_of_nonneg_left h1 hCpos.le
    linarith only [h2]
  have hc4d : (4 : ℝ) ^ P.natDegree * (C : ℝ) * (6 * A) ^ K ≤ C1 := by
    rw [hC1def]
    have h3 : (6 * A) ^ K ≤ 8 * (A * (6 * A) ^ (2 * K)) := by
      nlinarith only [hpow12, hpow1, hA1']
    have h4 : (4 : ℝ) ^ P.natDegree * (6 * A) ^ K
        ≤ (4 : ℝ) ^ P.natDegree * (8 * (A * (6 * A) ^ (2 * K))) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h4 hCpos.le
    rw [hA'def]
    linarith only [h5]
  have hclarge : 4 * A' * (6 * A) ^ K + 1 ≤ C1 := by
    rw [hC1def]
    have h3 : 4 * (6 * A) ^ K ≤ 8 * (C : ℝ) * (6 * A) ^ (2 * K) := by
      nlinarith only [hpow12, hpow1, hCp]
    have h4 : 4 * (6 * A) ^ K * A' ≤ 8 * (C : ℝ) * (6 * A) ^ (2 * K) * A' := by
      have := mul_le_mul_of_nonneg_right h3 hA'pos.le
      linarith only [this]
    linarith only [h4]
  refine ⟨C1, (K1 : ℝ), hC1pos, by exact_mod_cast hK1pos, ?_⟩
  intro N N₀ δ f g hh hN hδ0 hδ1 hN₀A hsf hsg hsh hbf hbg hbh hmain
  rw [rpow_nat_eq_pow, rpow_nat_eq_pow]
  by_cases hsmall : (N : ℝ) ≤ C1 * (δ⁻¹) ^ K1
  · exact Or.inl hsmall
  · push_neg at hsmall
    have hδpos : 0 < δ := hδ0
    have hδinv1 : 1 ≤ δ⁻¹ := by rw [one_le_inv₀ hδ0]; exact hδ1
    have hδinvnn : (0 : ℝ) ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ0)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hδinvK1 : (1 : ℝ) ≤ (δ⁻¹) ^ K1 := one_le_pow₀ hδinv1
    have hC1ltN : C1 < (N : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hδinvK1 hC1pos.le
      linarith only [h1, hsmall]
    have hN8 : 8 ≤ N := by
      have h : (8 : ℝ) ≤ (N : ℝ) := by linarith only [hC1ltN, hC1_8]
      exact_mod_cast h
    have hNc4 : 4 ≤ N / 2 := by omega
    have htriv : δ * (N : ℝ) ^ P.natDegree ≤ 2 * (N₀ : ℝ) + 1 :=
      AhalfZ_pairing_bound (by omega) P f g hh hsh hsf hsg hbh hbf hbg hmain
    have hδdelta : δ * (δ⁻¹) ^ K1 = (δ⁻¹) ^ (4 * K) := by
      rw [hK1def]
      exact mul_inv_pow_succ' (ne_of_gt hδpos) (4 * K)
    have hδN : C1 ≤ δ * (N : ℝ) := by
      have h2 : δ * (C1 * (δ⁻¹) ^ K1) < δ * (N : ℝ) :=
        mul_lt_mul_of_pos_left hsmall hδpos
      have h5 : (1 : ℝ) ≤ (δ⁻¹) ^ (4 * K) := one_le_pow₀ hδinv1
      have h4 : C1 ≤ δ * (C1 * (δ⁻¹) ^ K1) := by
        calc C1 = C1 * 1 := (mul_one C1).symm
          _ ≤ C1 * (δ⁻¹) ^ (4 * K) := mul_le_mul_of_nonneg_left h5 hC1pos.le
          _ = δ * (C1 * (δ⁻¹) ^ K1) := by
              rw [show δ * (C1 * (δ⁻¹) ^ K1) = C1 * (δ * (δ⁻¹) ^ K1) by ring, hδdelta]
      linarith only [h4, h2]
    have hδN2 : 2 ≤ δ * (N : ℝ) := by linarith only [hC1_8, hδN]
    have hNd1 : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ hN1 (by omega)
    have hδNd2 : 2 ≤ δ * (N : ℝ) ^ P.natDegree := by
      have h1 : δ * (N : ℝ) ≤ δ * (N : ℝ) ^ P.natDegree :=
        mul_le_mul_of_nonneg_left hNd1 hδpos.le
      linarith only [h1, hδN2]
    have hN₀1 : 1 ≤ N₀ := one_le_of_two_le_mul hδNd2 htriv
    have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN₀1
    have h3N₀ : δ * (N : ℝ) ^ P.natDegree ≤ 3 * (N₀ : ℝ) := by
      have h : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀1
      linarith only [h, htriv]
    have hε : δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ) ≤ ‖LambdaHalfZ N₀ N P hh f g‖ := by
      apply le_LambdaHalfZ_of_pairing (by omega : 0 < N₀) (by omega : 0 < N) P f g hh hsh hsf hsg
      rw [div_mul_cancel₀ _ (ne_of_gt hN₀pos)]
      exact hmain
    have hY1 : (1 : ℝ) ≤ A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K) := by
      have h1 : (1 : ℝ) ≤ A' * (6 * A) ^ K := by
        have := mul_le_mul hA'1 hpow1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hA'pos)
        simpa using this
      have h2 : (1 : ℝ) ≤ (δ⁻¹) ^ (2 * K) := one_le_pow₀ hδinv1
      have h3 : (1 : ℝ) ≤ (A' * (6 * A) ^ K) * (δ⁻¹) ^ (2 * K) := by
        simpa using mul_le_mul h1 h2 (by norm_num) (by positivity)
      simpa [mul_assoc] using h3
    have hY2Knn : (0 : ℝ) ≤ (δ⁻¹) ^ (2 * K) := pow_nonneg hδinvnn _
    have hY4 : 4 * (A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K)) + 1 < (N : ℝ) := by
      have hpow : (δ⁻¹) ^ (2 * K) ≤ (δ⁻¹) ^ K1 := pow_le_pow_right₀ hδinv1 (by omega)
      have h1 : (4 * A' * (6 * A) ^ K + 1) * (δ⁻¹) ^ K1 ≤ C1 * (δ⁻¹) ^ K1 :=
        mul_le_mul_of_nonneg_right hclarge (by positivity)
      have h2 : 4 * (A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K)) + 1
          ≤ (4 * A' * (6 * A) ^ K + 1) * (δ⁻¹) ^ K1 := by
        have hexp : (4 * A' * (6 * A) ^ K + 1) * (δ⁻¹) ^ K1
            = 4 * A' * (6 * A) ^ K * (δ⁻¹) ^ K1 + (δ⁻¹) ^ K1 := by ring
        rw [hexp]
        have hlow : 4 * A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K)
            ≤ 4 * A' * (6 * A) ^ K * (δ⁻¹) ^ K1 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        have h4 : (1 : ℝ) ≤ (δ⁻¹) ^ K1 := one_le_pow₀ hδinv1
        linarith only [hlow, h4]
      linarith only [h2, h1, hsmall]
    -- the main step, once for each of the two scales
    have step : ∀ (Nc : ℕ) (εc : ℝ), 1 ≤ Nc → Nc ≤ N → (N : ℝ) ≤ 4 * (Nc : ℝ) →
        A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K) ≤ (Nc : ℝ) →
        δ / (2 * A) ≤ εc → 0 < εc → εc ≤ ‖LambdaZ N₀ Nc P hh f g‖ →
        ∃ (q : ℕ) (N' : ℕ), 1 ≤ q ∧ (q : ℝ) ≤ C1 * (δ⁻¹) ^ K1 ∧ 1 ≤ N' ∧ N' ≤ N ∧
          δ ^ K1 * (N : ℝ) ≤ C1 * (N' : ℝ) ∧
          δ ^ K1 * (N : ℝ) ^ P.natDegree ≤ C1 * progAvgSum N' (q : ℤ) f := by
      intro Nc εc hNc1 hNcN hN4 hYNc hεclow hεcpos hΛ
      have hNcposR : (0 : ℝ) < (Nc : ℝ) := by exact_mod_cast (by omega : 0 < Nc)
      have hNcRle : (Nc : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNcN
      have hNcdpos : (0 : ℝ) < (Nc : ℝ) ^ P.natDegree := pow_pos hNcposR _
      have hNcdnonneg : (0 : ℝ) ≤ (Nc : ℝ) ^ P.natDegree := hNcdpos.le
      have h6ApowKne : (6 * A) ^ K ≠ 0 := ne_of_gt h6ApowKpos
      have h6ApowKnn : (0 : ℝ) ≤ (6 * A) ^ K := h6ApowKpos.le
      have hC1nn : (0 : ℝ) ≤ C1 := hC1pos.le
      have hCn : (0 : ℝ) ≤ (C : ℝ) := hCpos.le
      set δc : ℝ := min 1 (εc * (N₀ : ℝ) / (Nc : ℝ) ^ P.natDegree) with hδcdef
      have hδcpos : 0 < δc := by
        rw [hδcdef]
        exact lt_min one_pos (div_pos (mul_pos hεcpos hN₀pos) hNcdpos)
      have hδc1 : δc ≤ 1 := by rw [hδcdef]; exact min_le_left _ _
      have hδcle : δc ≤ εc * (N₀ : ℝ) / (Nc : ℝ) ^ P.natDegree := by
        rw [hδcdef]; exact min_le_right _ _
      have hδcNcd : δc * (Nc : ℝ) ^ P.natDegree ≤ εc * (N₀ : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hδcle hNcdnonneg
        rwa [div_mul_cancel₀ _ (ne_of_gt hNcdpos)] at h
      have hδc_low : δ ^ 2 / (6 * A) ≤ δc := by
        rw [hδcdef]
        refine le_min ?_ ?_
        · rw [div_le_one (by positivity)]
          nlinarith only [hδ0, hδ1, hA1']
        · rw [le_div_iff₀ hNcdpos]
          have hNcdle : (Nc : ℝ) ^ P.natDegree ≤ (N : ℝ) ^ P.natDegree :=
            pow_le_pow_left₀ hNcposR.le hNcRle _
          have hN₀le3 : δ * (N : ℝ) ^ P.natDegree / 3 ≤ (N₀ : ℝ) := by linarith only [h3N₀]
          have h1 : δ / (2 * A) * (δ * (N : ℝ) ^ P.natDegree / 3) ≤ εc * (N₀ : ℝ) := by
            have h2 : 0 ≤ δ * (N : ℝ) ^ P.natDegree / 3 := by positivity
            calc δ / (2 * A) * (δ * (N : ℝ) ^ P.natDegree / 3)
                ≤ εc * (δ * (N : ℝ) ^ P.natDegree / 3) :=
                  mul_le_mul_of_nonneg_right hεclow h2
              _ ≤ εc * (N₀ : ℝ) := mul_le_mul_of_nonneg_left hN₀le3 hεcpos.le
          have h2 : δ ^ 2 / (6 * A) * (Nc : ℝ) ^ P.natDegree
              ≤ δ / (2 * A) * (δ * (N : ℝ) ^ P.natDegree / 3) := by
            have h3 : 0 ≤ δ / (2 * A) * (δ / 3) := by positivity
            calc δ ^ 2 / (6 * A) * (Nc : ℝ) ^ P.natDegree
                = δ / (2 * A) * (δ / 3) * (Nc : ℝ) ^ P.natDegree := by ring
              _ ≤ δ / (2 * A) * (δ / 3) * (N : ℝ) ^ P.natDegree :=
                  mul_le_mul_of_nonneg_left hNcdle h3
              _ = δ / (2 * A) * (δ * (N : ℝ) ^ P.natDegree / 3) := by ring
          linarith only [h1, h2]
      have hδcinv : δc⁻¹ ≤ 6 * A * (δ⁻¹) ^ 2 := by
        have hpos : (0 : ℝ) < δ ^ 2 / (6 * A) := by positivity
        have h1 : δc⁻¹ ≤ (δ ^ 2 / (6 * A))⁻¹ := (inv_le_inv₀ hδcpos hpos).mpr hδc_low
        rwa [inv_div, div_eq_mul_inv, ← inv_pow] at h1
      have hδcK : (δc⁻¹) ^ K ≤ (6 * A) ^ K * (δ⁻¹) ^ (2 * K) := by
        have h1 : (δc⁻¹) ^ K ≤ (6 * A * (δ⁻¹) ^ 2) ^ K :=
          pow_le_pow_left₀ (inv_nonneg.mpr hδcpos.le) hδcinv K
        rwa [mul_pow, ← pow_mul] at h1
      have hcrux_nd : A' * (δc⁻¹) ^ K ≤ (Nc : ℝ) := by
        have h1 : A' * (δc⁻¹) ^ K ≤ A' * ((6 * A) ^ K * (δ⁻¹) ^ (2 * K)) :=
          mul_le_mul_of_nonneg_left hδcK hA'pos.le
        rw [show A' * ((6 * A) ^ K * (δ⁻¹) ^ (2 * K))
            = A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K) by ring] at h1
        linarith only [h1, hYNc]
      have hN₀scale : (N₀ : ℝ) ≤ A' * (Nc : ℝ) ^ P.natDegree := by
        have h1 : (N : ℝ) ^ P.natDegree ≤ (4 * (Nc : ℝ)) ^ P.natDegree :=
          pow_le_pow_left₀ (by positivity) hN4 _
        have h2 : (4 * (Nc : ℝ)) ^ P.natDegree
            = 4 ^ P.natDegree * (Nc : ℝ) ^ P.natDegree := by rw [mul_pow]
        calc (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := hN₀A
          _ ≤ A * (4 ^ P.natDegree * (Nc : ℝ) ^ P.natDegree) := by
              rw [h2] at h1
              exact mul_le_mul_of_nonneg_left h1 hApos.le
          _ = A' * (Nc : ℝ) ^ P.natDegree := by rw [hA'def, mul_assoc]
      obtain ⟨q, N', hq1, hq2, hN'1, hN'Nc, hN'd, hN'sum⟩ :=
        hcrux Nc N₀ δc hh f g hd hNc1 hδcpos hδc1 hN₀1 hcrux_nd hN₀scale
          hsh hsf hsg hbh hbf hbg (by
            have h1 : δc * (Nc : ℝ) ^ P.natDegree ≤ εc * (N₀ : ℝ) := hδcNcd
            have h2 : εc * (N₀ : ℝ) ≤ ‖LambdaZ N₀ Nc P hh f g‖ * (N₀ : ℝ) :=
              mul_le_mul_of_nonneg_right hΛ hN₀pos.le
            linarith only [h1, h2])
      refine ⟨q, N', hq1, ?_, hN'1, le_trans hN'Nc hNcN, ?_, ?_⟩
      · have h1 : (C : ℝ) * (δc⁻¹) ^ K ≤ (C : ℝ) * ((6 * A) ^ K * (δ⁻¹) ^ (2 * K)) :=
          mul_le_mul_of_nonneg_left hδcK hCn
        have h2 : (C : ℝ) * ((6 * A) ^ K * (δ⁻¹) ^ (2 * K)) ≤ C1 * (δ⁻¹) ^ K1 := by
          rw [show (C : ℝ) * ((6 * A) ^ K * (δ⁻¹) ^ (2 * K))
              = ((C : ℝ) * (6 * A) ^ K) * (δ⁻¹) ^ (2 * K) by ring]
          have h3 : ((C : ℝ) * (6 * A) ^ K) * (δ⁻¹) ^ (2 * K) ≤ C1 * (δ⁻¹) ^ (2 * K) :=
            mul_le_mul_of_nonneg_right hc7 hY2Knn
          have h4 : (δ⁻¹) ^ (2 * K) ≤ (δ⁻¹) ^ K1 := pow_le_pow_right₀ hδinv1 (by omega)
          have h5 : C1 * (δ⁻¹) ^ (2 * K) ≤ C1 * (δ⁻¹) ^ K1 :=
            mul_le_mul_of_nonneg_left h4 hC1nn
          linarith only [h3, h5]
        linarith only [hq2, h1, h2]
      · have hδcK_low : (δ ^ 2 / (6 * A)) ^ K ≤ δc ^ K :=
          pow_le_pow_left₀ (by positivity) hδc_low K
        have h2 : δ ^ K1 = δ ^ (2 * K) * δ ^ (2 * K + 1) := by
          have h : 4 * K + 1 = 2 * K + (2 * K + 1) := by omega
          rw [hK1def, h, pow_add]
        have hb : δ ^ K1 * (N : ℝ) ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ)) := by
          have hN_le : δ ^ K1 * (N : ℝ) ≤ δ ^ K1 * (4 * (Nc : ℝ)) :=
            mul_le_mul_of_nonneg_left hN4 (by positivity)
          have hA1 : δ ^ K1 * (4 * (Nc : ℝ))
              ≤ 4 * δ ^ (2 * K + 1) * (δ ^ (2 * K) * (Nc : ℝ)) := by
            rw [h2]
            have he : δ ^ (2 * K) * δ ^ (2 * K + 1) * (4 * (Nc : ℝ))
                = 4 * δ ^ (2 * K + 1) * (δ ^ (2 * K) * (Nc : ℝ)) := by ring
            rw [he]
          have heq : (δ ^ 2 / (6 * A)) ^ K = δ ^ (2 * K) / (6 * A) ^ K := by
            rw [div_pow, ← pow_mul]
          have hbound : 4 * δ ^ (2 * K + 1) ≤ C1 / ((C : ℝ) * (6 * A) ^ K) := by
            rw [le_div_iff₀ (mul_pos hCpos h6ApowKpos)]
            have hδle1 : δ ^ (2 * K + 1) ≤ 1 := pow_le_one₀ hδ0.le hδ1
            have hCKnn : (0 : ℝ) ≤ (C : ℝ) * (6 * A) ^ K := mul_nonneg hCn h6ApowKnn
            calc 4 * δ ^ (2 * K + 1) * ((C : ℝ) * (6 * A) ^ K)
                ≤ 4 * ((C : ℝ) * (6 * A) ^ K) := by
                  have h5 : 4 * δ ^ (2 * K + 1) ≤ 4 * 1 := by
                    simpa using mul_le_mul_of_nonneg_left hδle1 (by norm_num : (0 : ℝ) ≤ 4)
                  simpa using mul_le_mul_of_nonneg_right h5 hCKnn
              _ = 4 * (C : ℝ) * (6 * A) ^ K := by ring
              _ ≤ C1 := hc4
          have hA2 : 4 * δ ^ (2 * K + 1) * (δ ^ (2 * K) * (Nc : ℝ))
              ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ)) := by
            have hfac : (0 : ℝ) ≤ δ ^ (2 * K) * (Nc : ℝ) := by positivity
            have h1 : (C1 / (C : ℝ)) * ((δ ^ 2 / (6 * A)) ^ K * (Nc : ℝ))
                ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hδcK_low hNcposR.le)
                (div_nonneg hC1nn hCn)
            have h2' : 4 * δ ^ (2 * K + 1) * (δ ^ (2 * K) * (Nc : ℝ))
                ≤ (C1 / (C : ℝ)) * ((δ ^ 2 / (6 * A)) ^ K * (Nc : ℝ)) := by
              rw [heq]
              rw [div_mul_div_mul' (ne_of_gt hCpos) h6ApowKne]
              exact mul_le_mul_of_nonneg_right hbound hfac
            linarith only [h1, h2']
          linarith only [hN_le, hA1, hA2]
        calc δ ^ K1 * (N : ℝ) ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ)) := hb
          _ ≤ (C1 / (C : ℝ)) * ((C : ℝ) * (N' : ℝ)) :=
              mul_le_mul_of_nonneg_left hN'd (div_nonneg hC1nn hCn)
          _ = C1 * (N' : ℝ) := div_mul_const (ne_of_gt hCpos)
      · have hδcK_low : (δ ^ 2 / (6 * A)) ^ K ≤ δc ^ K :=
          pow_le_pow_left₀ (by positivity) hδc_low K
        have h2 : δ ^ K1 = δ ^ (2 * K) * δ ^ (2 * K + 1) := by
          have h : 4 * K + 1 = 2 * K + (2 * K + 1) := by omega
          rw [hK1def, h, pow_add]
        have hNdpow : (N : ℝ) ^ P.natDegree ≤ 4 ^ P.natDegree * (Nc : ℝ) ^ P.natDegree := by
          have h1 : (N : ℝ) ^ P.natDegree ≤ (4 * (Nc : ℝ)) ^ P.natDegree :=
            pow_le_pow_left₀ (by positivity) hN4 _
          rwa [mul_pow] at h1
        have hb : δ ^ K1 * (N : ℝ) ^ P.natDegree
            ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ) ^ P.natDegree) := by
          have h1 : δ ^ K1 * (N : ℝ) ^ P.natDegree
              ≤ δ ^ K1 * (4 ^ P.natDegree * (Nc : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_left hNdpow (by positivity)
          have hA1 : δ ^ K1 * (4 ^ P.natDegree * (Nc : ℝ) ^ P.natDegree)
              ≤ 4 ^ P.natDegree * δ ^ (2 * K + 1)
                * (δ ^ (2 * K) * (Nc : ℝ) ^ P.natDegree) := by
            rw [h2]
            have he : δ ^ (2 * K) * δ ^ (2 * K + 1) * (4 ^ P.natDegree * (Nc : ℝ) ^ P.natDegree)
                = 4 ^ P.natDegree * δ ^ (2 * K + 1)
                  * (δ ^ (2 * K) * (Nc : ℝ) ^ P.natDegree) := by ring
            rw [he]
          have heq : (δ ^ 2 / (6 * A)) ^ K = δ ^ (2 * K) / (6 * A) ^ K := by
            rw [div_pow, ← pow_mul]
          have hbound : 4 ^ P.natDegree * δ ^ (2 * K + 1)
              ≤ C1 / ((C : ℝ) * (6 * A) ^ K) := by
            rw [le_div_iff₀ (mul_pos hCpos h6ApowKpos)]
            have hδle1 : δ ^ (2 * K + 1) ≤ 1 := pow_le_one₀ hδ0.le hδ1
            have hCKnn : (0 : ℝ) ≤ (C : ℝ) * (6 * A) ^ K := mul_nonneg hCn h6ApowKnn
            calc 4 ^ P.natDegree * δ ^ (2 * K + 1) * ((C : ℝ) * (6 * A) ^ K)
                ≤ 4 ^ P.natDegree * ((C : ℝ) * (6 * A) ^ K) := by
                  have h5 : 4 ^ P.natDegree * δ ^ (2 * K + 1) ≤ 4 ^ P.natDegree * 1 :=
                    mul_le_mul_of_nonneg_left hδle1 (by positivity)
                  simpa using mul_le_mul_of_nonneg_right h5 hCKnn
              _ = 4 ^ P.natDegree * (C : ℝ) * (6 * A) ^ K := by ring
              _ ≤ C1 := hc4d
          have hA2 : 4 ^ P.natDegree * δ ^ (2 * K + 1)
                * (δ ^ (2 * K) * (Nc : ℝ) ^ P.natDegree)
              ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ) ^ P.natDegree) := by
            have hfac : (0 : ℝ) ≤ δ ^ (2 * K) * (Nc : ℝ) ^ P.natDegree := by positivity
            have h1 : (C1 / (C : ℝ)) * ((δ ^ 2 / (6 * A)) ^ K * (Nc : ℝ) ^ P.natDegree)
                ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ) ^ P.natDegree) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hδcK_low hNcdnonneg) (div_nonneg hC1nn hCn)
            have h2' : 4 ^ P.natDegree * δ ^ (2 * K + 1)
                  * (δ ^ (2 * K) * (Nc : ℝ) ^ P.natDegree)
                ≤ (C1 / (C : ℝ)) * ((δ ^ 2 / (6 * A)) ^ K * (Nc : ℝ) ^ P.natDegree) := by
              rw [heq]
              rw [div_mul_div_mul' (ne_of_gt hCpos) h6ApowKne]
              exact mul_le_mul_of_nonneg_right hbound hfac
            linarith only [h1, h2']
          linarith only [h1, hA1, hA2]
        calc δ ^ K1 * (N : ℝ) ^ P.natDegree
            ≤ (C1 / (C : ℝ)) * (δc ^ K * (Nc : ℝ) ^ P.natDegree) := hb
          _ ≤ (C1 / (C : ℝ)) * ((C : ℝ) * progAvgSum N' (q : ℤ) f) :=
              mul_le_mul_of_nonneg_left hN'sum (div_nonneg hC1nn hCn)
          _ = C1 * progAvgSum N' (q : ℤ) f := div_mul_const (ne_of_gt hCpos)
    rcases half_le_of_pairing (by omega : 0 < N₀) (by omega : 0 < N) P hh f g hsh hsf hsg hε
      with hc | hc
    · -- the full scale `N`
      refine Or.inr (step N (δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ) / 2) hN (le_refl N) ?_ ?_ ?_ ?_ hc)
      · linarith only [hNpos]
      · linarith only [hY4, hY1]
      · have hgoal : δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ) / 2
            = δ * (N : ℝ) ^ P.natDegree / (2 * (N₀ : ℝ)) := by ring
        rw [hgoal, le_div_iff₀ (mul_pos (by norm_num) hN₀pos)]
        have h2 : (N₀ : ℝ) / A ≤ (N : ℝ) ^ P.natDegree := by
          rw [div_le_iff₀ hApos]; linarith only [hN₀A]
        have h1 : δ / (2 * A) * (2 * (N₀ : ℝ)) = δ * ((N₀ : ℝ) / A) := by
          rw [div_mul_eq_mul_div]
          rw [show δ * (2 * (N₀ : ℝ)) = (δ * (N₀ : ℝ)) * 2 by ring,
            show 2 * A = A * 2 by ring]
          rw [mul_div_mul_right _ _ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [mul_div_assoc]
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 hδpos.le
      · exact div_pos (div_pos (mul_pos hδpos (pow_pos hNpos _)) hN₀pos) (by norm_num)
    · -- the half scale `⌊N/2⌋`
      have hNhalf := half_div_cast_le N
      have hYNc : A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K) ≤ ((N / 2 : ℕ) : ℝ) := by
        have h1 : 4 * (A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K)) < (N : ℝ) - 1 := by
          linarith only [hY4]
        have h2 : 2 * (A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K)) < ((N : ℝ) - 1) / 2 := by
          linarith only [h1]
        have h3 : (1 : ℝ) / 2 ≤ A' * (6 * A) ^ K * (δ⁻¹) ^ (2 * K) := by
          linarith only [hY1]
        linarith only [hNhalf, h2, h3]
      have hN4B : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by
        have h1 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
          have hcast : (N : ℝ) ≤ ((2 * (N / 2) + 1 : ℕ) : ℝ) :=
            Nat.cast_le.mpr (nat_self_le_two_div_add_one N)
          push_cast at hcast
          linarith only [hcast]
        have h2 : (4 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hNc4
        linarith only [h1, h2]
      have hεclowB : δ / (2 * A) ≤ δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ) := by
        have h4 : (1 : ℝ) / A ≤ (N : ℝ) ^ P.natDegree / (N₀ : ℝ) := by
          rw [div_le_iff₀ hApos, div_mul_eq_mul_div, le_div_iff₀ hN₀pos]
          linarith only [hN₀A]
        have h5 : δ / A ≤ δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ) := by
          have e1 : δ / A = δ * ((1 : ℝ) / A) := by ring
          have e2 : δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ)
              = δ * ((N : ℝ) ^ P.natDegree / (N₀ : ℝ)) := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left h4 hδpos.le
        have h6 : δ / (2 * A) ≤ δ / A :=
          div_le_div_of_nonneg_left hδpos.le hApos (by linarith only [hApos])
        linarith only [h5, h6]
      exact Or.inr (step (N / 2) (δ * (N : ℝ) ^ P.natDegree / (N₀ : ℝ)) (by omega)
        (Nat.div_le_self N 2) hN4B hYNc hεclowB
        (div_pos (mul_pos hδpos (pow_pos hNpos _)) hN₀pos) hc)

end

end Work.Peluse
