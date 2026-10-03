/-
# `Work.FIChain.nuFI_VfB_le_zprime` — the `z`-prime bound on `VfB ν_Δ (yFI Δ)`

The sieve product of the Friedlander–Iwaniec density at the layer range `yFI Δ = ⌈Δ^{1/20}⌉₊ + 1`
is bounded by a constant times the same product at the *larger* `z`-level
`z = ⌈Δ^{1/19}⌉₊`:

    `VfB (nuFI Δ) (yFI Δ) ≤ 4·KFI · ∏_{p < ⌈Δ^{1/19}⌉₊} (1 - nuFI Δ p)`   (`Δ ≥ 3`).

Since `VfB ν w = ∏_{p < ⌈w⌉₊}(1 - ν p)` is *non-increasing* in `w`, and `yFI Δ < Δ^{1/19}` for all
but very small `Δ`, the content is the ratio bound `LinNormKup (nuFI Δ) KFI 2 Δ` of
`PerLayerAux`: the window `[yFI Δ, ⌈Δ^{1/19}⌉₊]` contributes

    `∏_{window} (1 - ν p)^{-1} ≤ KFI · (log ⌈Δ^{1/19}⌉₊ / log (yFI Δ))^2 ≤ 4·KFI`,

the last step because `⌈Δ^{1/19}⌉₊ ≤ (yFI Δ)^2` (`zprime_Z_le_yFI_sq`: both ceilings are dominated
by `Δ^{1/20}` resp. `Δ^{1/10}`, and `1/19 < 1/10`), so the logarithm ratio is at most `2` while the
exponent is `κ = 2`.  When `⌈Δ^{1/19}⌉₊ ≤ yFI Δ` (only very small `Δ`) the two products are
compared by monotonicity alone.  Everything is elementary; the one analytic input is the sharp
two-dimensional norm `nuFI_LinNormKup_aux` of the §6 sieve density.
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.PerLayerDefs
import Submission.Work.FIChain.PerLayerAux
import Submission.Work.FIChain.TnB_FIgtil_perLayer
import Submission.Work.FIChain.VfB_le_mul_ratio
import Submission.Work.FIChain.FIgtil_prime_le_third

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The arithmetic comparison of the two cutoffs -/

/-- `⌈Δ^{1/19}⌉₊ ≤ (yFI Δ)²`.  Both cutoffs are dominated by explicit powers of `Δ`: the left one by
`Δ^{1/19} ≤ Δ^{1/10}` and the right one by `(Δ^{1/20})² = Δ^{1/10}`. -/
lemma zprime_Z_le_yFI_sq (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ) ≤ (yFI Δ) ^ 2 := by
  have hnat : ⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ ≤ (yN Δ) ^ 2 := by
    rw [Nat.ceil_le]
    have hyN : ((yN Δ : ℕ) : ℝ) = (⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) + 1 := by
      rw [yN, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_pow, hyN]
    have hΔ0 : (0 : ℝ) < (Δ : ℝ) := by positivity
    have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Δ)
    have hx0 : (0 : ℝ) < (Δ : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hΔ0 _
    have hxc : (Δ : ℝ) ^ ((1 : ℝ) / 20) ≤ (⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) := Nat.le_ceil _
    have hz10 : (Δ : ℝ) ^ ((1 : ℝ) / 19) ≤ (Δ : ℝ) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow_of_exponent_le hΔ1 (by norm_num)
    have hx2 : ((Δ : ℝ) ^ ((1 : ℝ) / 20)) ^ 2 = (Δ : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hΔ0)]
      congr 1
      norm_num
    calc (Δ : ℝ) ^ ((1 : ℝ) / 19) ≤ (Δ : ℝ) ^ ((1 : ℝ) / 10) := hz10
      _ = ((Δ : ℝ) ^ ((1 : ℝ) / 20)) ^ 2 := hx2.symm
      _ ≤ (⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) ^ 2 := pow_le_pow_left₀ hx0.le hxc 2
      _ ≤ ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 20)⌉₊ : ℝ) + 1) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hy : (yFI Δ) ^ 2 = (((yN Δ) ^ 2 : ℕ) : ℝ) := by
    rw [yFI_eq_yN, Nat.cast_pow]
  rw [hy]
  exact_mod_cast hnat

/-- The logarithmic ratio of the two cutoffs is at most `2`, hence its square at most `4`, whenever
the `z`-level exceeds the layer range: `⌈Δ^{1/19}⌉₊ ≤ (yFI Δ)²` makes
`log ⌈Δ^{1/19}⌉₊ ≤ 2 log (yFI Δ)`. -/
lemma zprime_logratio_sq_le_four (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (hYZ : yFI Δ < ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ)) :
    (Real.log ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ) / Real.log (yFI Δ)) ^ 2 ≤ 4 := by
  have hZle : ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ) ≤ (yFI Δ) ^ 2 :=
    zprime_Z_le_yFI_sq Δ hΔ
  have hy2 : (2 : ℝ) ≤ yFI Δ := by rw [yFI_eq_yN]; exact_mod_cast yN_ge_two Δ hΔ
  have hylog : 0 < Real.log (yFI Δ) := Real.log_pos (by linarith)
  have hZ1 : (1 : ℝ) < ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ) := lt_trans (by linarith) hYZ
  have hZlog_nn : 0 ≤ Real.log (((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ)) :=
    Real.log_nonneg hZ1.le
  have hlog : Real.log (((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ)) ≤ 2 * Real.log (yFI Δ) := by
    have h := Real.log_le_log
      (by linarith : (0 : ℝ) < (((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ))) hZle
    rw [Real.log_pow] at h
    simpa using h
  have hq : Real.log (((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ)) / Real.log (yFI Δ) ≤ 2 := by
    rw [div_le_iff₀ hylog]
    linarith
  have hq0 : 0 ≤ Real.log (((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ)) / Real.log (yFI Δ) :=
    div_nonneg hZlog_nn hylog.le
  calc (Real.log ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ) / Real.log (yFI Δ)) ^ 2
      ≤ 2 ^ 2 := pow_le_pow_left₀ hq0 hq 2
    _ = 4 := by norm_num

/-! ## The main bound -/

/-- **The `z`-prime bound.**  For `Δ ≥ 3` the sieve product of the FI density at the layer range
`yFI Δ` is at most `4·KFI` times the product over the `z`-level primes `p < ⌈Δ^{1/19}⌉₊`. -/
theorem nuFI_VfB_le_zprime (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    Work.FIChain.VfB (Work.FIChain.nuFI Δ) (Work.FIChain.yFI Δ)
      ≤ (4 * Work.FIChain.KFI)
        * ∏ p ∈ Nat.primesBelow (⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊),
            (1 - Work.FIChain.nuFI Δ p) := by
  have hν0 : ∀ p : ℕ, p.Prime → 0 ≤ nuFI Δ p := fun p _ => nuFI_nonneg Δ p
  have hνhalf : ∀ p : ℕ, p.Prime → nuFI Δ p ≤ 1 / 2 :=
    fun p hp => nuFI_le_half_of FIgtil_prime_le_third Δ hΔ p hp
  have hν1 : ∀ p : ℕ, p.Prime → nuFI Δ p < 1 := fun p hp => by linarith [hνhalf p hp]
  set Z : ℕ := ⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ with hZdef
  have hVZ : VfB (nuFI Δ) ((Z : ℕ) : ℝ) = ∏ p ∈ Nat.primesBelow Z, (1 - nuFI Δ p) := by
    rw [VfB, Nat.ceil_natCast]
  have hVY : VfB (nuFI Δ) (yFI Δ) = ∏ p ∈ Nat.primesBelow (yN Δ), (1 - nuFI Δ p) := by
    rw [VfB, ceil_yFI]
  rw [hVY, ← hVZ]
  rcases lt_or_ge (yFI Δ) ((Z : ℕ) : ℝ) with hYZ | hZY
  · -- the window `[yFI Δ, Z]` is non-empty: apply the `Ω₂` ratio bound
    rw [← hVY]
    have hZd : Z ≤ Δ := by
      rw [hZdef, Nat.ceil_le]
      have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Δ)
      calc (Δ : ℝ) ^ ((1 : ℝ) / 19) ≤ (Δ : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hΔ1 (by norm_num)
        _ = (Δ : ℝ) := Real.rpow_one _
    have hZD : ((Z : ℕ) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hZd
    have hy2 : (2 : ℝ) ≤ yFI Δ := by
      rw [yFI_eq_yN]; exact_mod_cast yN_ge_two Δ hΔ
    have hratio := VfB_le_VfB_mul_LinNormKup_real (nuFI_LinNormKup_aux Δ hΔ) hν0 hν1 hy2
      (le_of_lt hYZ) hZD
    have hYZ' : yFI Δ < ((⌈(Δ : ℝ) ^ ((1 : ℝ) / 19)⌉₊ : ℕ) : ℝ) := by
      rw [← hZdef]; exact hYZ
    have hq : (Real.log ((Z : ℕ) : ℝ) / Real.log (yFI Δ)) ^ 2 ≤ 4 := by
      have h := zprime_logratio_sq_le_four Δ hΔ hYZ'
      rw [hZdef]
      exact h
    have hfac : KFI * (Real.log ((Z : ℕ) : ℝ) / Real.log (yFI Δ)) ^ (2 : ℝ) ≤ 4 * KFI := by
      have hp2 : (Real.log ((Z : ℕ) : ℝ) / Real.log (yFI Δ)) ^ (2 : ℝ)
          = (Real.log ((Z : ℕ) : ℝ) / Real.log (yFI Δ)) ^ 2 := by
        rw [← Real.rpow_natCast]; norm_num
      rw [hp2]
      nlinarith [hq, le_of_lt KFI_pos]
    have hVZnn : 0 ≤ VfB (nuFI Δ) ((Z : ℕ) : ℝ) :=
      VfB_nonneg (fun p hp => le_of_lt (hν1 p hp)) _
    calc VfB (nuFI Δ) (yFI Δ)
        ≤ VfB (nuFI Δ) ((Z : ℕ) : ℝ)
            * (KFI * (Real.log ((Z : ℕ) : ℝ) / Real.log (yFI Δ)) ^ (2 : ℝ)) := hratio
      _ ≤ VfB (nuFI Δ) ((Z : ℕ) : ℝ) * (4 * KFI) := mul_le_mul_of_nonneg_left hfac hVZnn
      _ = (4 * KFI) * VfB (nuFI Δ) ((Z : ℕ) : ℝ) := by ring
  · -- the `z`-level is the smaller cutoff: monotonicity suffices
    rw [← hVY]
    refine le_trans (VfB_antitone hν0 hνhalf hZY) ?_
    have h2 : 1 ≤ 4 * KFI := by linarith [KFI_one_le]
    have h3 : 0 ≤ VfB (nuFI Δ) ((Z : ℕ) : ℝ) :=
      VfB_nonneg (fun p hp => le_of_lt (hν1 p hp)) _
    calc VfB (nuFI Δ) ((Z : ℕ) : ℝ) = 1 * VfB (nuFI Δ) ((Z : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ (4 * KFI) * VfB (nuFI Δ) ((Z : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h2 h3

end

end Work.FIChain
