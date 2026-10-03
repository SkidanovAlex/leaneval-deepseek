/-
# `FIArea2/R6/tauSqBoxSelf` — the `τ(|z|²)²` second moment over the polar box (crude form)

`Σ_{z ∈ polar box} τ(|z|²)² ≤ C·u²·(log N + 2)^{131073}`, `u = θ√N`, in the regime
`u ≥ N^{3/8}`.

Two ingredients, both proved and axiom-clean:

* Lemma 2.2 at `k = 4` for `τ²` (`R6.tau_sq_le_sum_Icc_four`): with `K := ⌈(2N)^{1/4}⌉`,
  `τ(m)² ≤ 65536·Σ_{d ≤ K, d ∣ m} τ(d)^16` for `m ≤ K⁴`; every box point has
  `|z|² ≤ (1+θ)N ≤ 2N ≤ K⁴`.
* the lattice count `#{z ∈ polar box : d ∣ |z|²} ≤ πu²τ(d)/d + 80uτ(d)/√d + τ(d)`
  (`FIArea3.jointCountNoBox`, its primitive point instantiated by `z₁ = 1`), together with the
  divisor sums `sum_tau_pow_div_le 17`, `sum_tau_pow_div_sqrt_le 17`, `sum_tau_pow_le 16`.

The count turns the box sum into `Σ_{d ≤ K} τ(d)^16·#{…}`, i.e. into
`πu²·Σ τ(d)^17/d + 80u·Σ τ(d)^17/√d + Σ τ(d)^16`, with exponents `2^17`, `2^17`, `2^16`.  The
regime `u ≥ N^{3/8}` gives `K ≤ 4u^{2/3}` and `√K ≤ 2u^{1/3}`; with `u ≥ 1` this absorbs
everything into `u²`, and the logarithms cost a factor `4^{2^17}`.

The big log-powers are abstracted by `set` before any `ring`, so that no tactic ever expands a
power of a sum with exponent `2^17`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.pairFibre6Aux
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.jointCountNoBox
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea2.R6.BetaFacts6

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The polar-box count of the multiples of `d`:
`#{z ∈ box : d ∣ |z|²} ≤ πu²τ(d)/d + 80uτ(d)/√d + τ(d)`, from the joint count at `e = 1` and the
primitive point `z₁ = 1`. -/
theorem polarBox_div_count (Pa : Work.FITop.Params) (φ : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    ((((Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((((d.divisors.card : ℕ) : ℝ)) / (d : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * (((d.divisors.card : ℕ) : ℝ)) / Real.sqrt (d : ℝ)
        + (((d.divisors.card : ℕ) : ℝ)) := by
  have hcop : Nat.Coprime (1 : GaussianInt).re.natAbs (1 : GaussianInt).im.natAbs := by decide
  have h := Work.FIArea3.jointCountNoBox Pa φ (1 : GaussianInt) d 1 hcop hd (le_refl 1)
  have hfilter : ((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => d ∣ Work.FIPlan.gnorm z ∧ 1 ∣ Work.FIPlan.absDelta (1 : GaussianInt) z)).card
      = ((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card := by
    congr 1
    exact Finset.filter_congr fun z _ => ⟨fun h => h.1, fun h => ⟨h, one_dvd _⟩⟩
  rw [hfilter] at h
  simpa only [Nat.gcd_one_right, Nat.cast_one, mul_one, one_mul] using h

/-- `K := ⌈(2N)^{1/4}⌉` satisfies `K ≤ 4u^{2/3}`, `√K ≤ 2u^{1/3}` and
`log K + 2 ≤ 4(log N + 2)` in the regime `u = θ√N ≥ N^{3/8}`. -/
theorem K_arith (Pa : Work.FITop.Params) {u : ℝ}
    (hu : Pa.N ^ ((3 : ℝ) / 8) ≤ u) (hu1 : 1 ≤ u) (hN1 : (1 : ℝ) ≤ (Pa.N : ℝ)) :
    (⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℝ) ≤ 4 * u ^ ((2 : ℝ) / 3)
      ∧ Real.sqrt ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) ≤ 2 * u ^ ((1 : ℝ) / 3)
      ∧ Real.log ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) + 2
          ≤ 4 * (Real.log (Pa.N : ℝ) + 2) := by
  have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith only [hN1]
  have h2N0 : (0 : ℝ) ≤ 2 * (Pa.N : ℝ) := by linarith only [hN1]
  have hKge : (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) ≤ ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hKle : ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
      ≤ (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg h2N0 _))
  have h2q : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ (2 : ℝ) ^ ((1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hNq : (Pa.N : ℝ) ^ ((1 : ℝ) / 4) ≤ u ^ ((2 : ℝ) / 3) := by
    have h1 : (Pa.N : ℝ) ^ ((1 : ℝ) / 4) = ((Pa.N : ℝ) ^ ((3 : ℝ) / 8)) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_mul hN0]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hu (by norm_num)
  have hKbound : ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) ≤ 4 * u ^ ((2 : ℝ) / 3) := by
    have h2 : (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) ≤ 2 * u ^ ((2 : ℝ) / 3) := by
      calc (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)
          = (2 : ℝ) ^ ((1 : ℝ) / 4) * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.mul_rpow (by norm_num) hN0
        _ ≤ 2 * u ^ ((2 : ℝ) / 3) :=
            mul_le_mul h2q hNq (Real.rpow_nonneg hN0 _) (by norm_num)
    have h3 : (1 : ℝ) ≤ 2 * u ^ ((2 : ℝ) / 3) := by
      have h4 : (1 : ℝ) ≤ u ^ ((2 : ℝ) / 3) := Real.one_le_rpow hu1 (by norm_num)
      linarith only [h4]
    linarith only [hKle, h2, h3]
  refine ⟨hKbound, ?_, ?_⟩
  · have h2 : Real.sqrt ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
        ≤ Real.sqrt (4 * u ^ ((2 : ℝ) / 3)) := Real.sqrt_le_sqrt hKbound
    have h3 : Real.sqrt (4 * u ^ ((2 : ℝ) / 3)) = 2 * u ^ ((1 : ℝ) / 3) := by
      have hu13 : (u ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) = u ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast (u ^ ((1 : ℝ) / 3)) 2,
          ← Real.rpow_mul (le_trans zero_le_one hu1)]
        norm_num
      have h4 : 4 * u ^ ((2 : ℝ) / 3) = (2 * u ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
        rw [mul_pow, hu13]
        norm_num
      rw [h4, Real.sqrt_sq (by positivity)]
    rw [h3] at h2
    exact h2
  · have hlogN0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg hN1
    have hKpos : (0 : ℝ) < ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith only [hN1]) _) hKge
    have hKle' : ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
        ≤ 4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by
      have h2 : (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) ≤ 2 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by
        calc (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)
            = (2 : ℝ) ^ ((1 : ℝ) / 4) * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) :=
              Real.mul_rpow (by norm_num) hN0
          _ ≤ 2 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) :=
              mul_le_mul_of_nonneg_right h2q (Real.rpow_nonneg hN0 _)
      have h5 : (1 : ℝ) ≤ 2 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := by
        have h6 : (1 : ℝ) ≤ (Pa.N : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hN1 (by norm_num)
        linarith only [h6]
      linarith only [hKle, h2, h5]
    have h3 : Real.log ((⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℝ)
        ≤ Real.log (4 * (Pa.N : ℝ) ^ ((1 : ℝ) / 4)) := Real.log_le_log hKpos hKle'
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos (by linarith only [hN1]) _)),
      Real.log_rpow (by linarith only [hN1])] at h3
    have h4 : Real.log (4 : ℝ) ≤ 2 := by
      have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith only [h, Real.log_two_lt_d9]
    linarith only [h3, h4, hlogN0]

/-- The arithmetic of the crude second moment, with the two log-powers `P = (log K + 2)^{2^17}`,
`Q = (log N + 2)^{131073}` and the box scale `u = θ√N` left abstract (so that no tactic ever sees
a power of a sum with exponent `2^17`). -/
theorem tauSqBox_arith {Ca Cb Cc u W P Q A R Ks Kd S1 S2 S3 : ℝ}
    (hCa : 0 < Ca) (hCb : 0 < Cb) (hCc : 0 < Cc)
    (hu1 : 1 ≤ u) (hW0 : 0 ≤ W) (hW : W = u * u)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hA0 : 0 ≤ A) (hR0 : 0 ≤ R)
    (hS10 : 0 ≤ S1) (hS20 : 0 ≤ S2) (hS30 : 0 ≤ S3)
    (hKs0 : 0 ≤ Ks) (hKd0 : 0 ≤ Kd)
    (hKs : Ks ≤ 2 * u ^ ((1 : ℝ) / 3)) (hKd : Kd ≤ 4 * u ^ ((2 : ℝ) / 3))
    (hS1 : S1 ≤ Ca * P) (hS2 : S2 ≤ Cb * Ks * P) (hS3 : S3 ≤ Cc * Kd * P)
    (hPAR : P ≤ A * R) (hRQ : R ≤ Q) :
    65536 * (Real.pi * W * S1 + 80 * u * S2 + S3)
      ≤ (65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A + 1) + 1) * W * Q := by
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu1
  have h13 : u ^ ((1 : ℝ) / 3) ≤ u := by
    have h1 : u ^ ((1 : ℝ) / 3) ≤ u ^ ((1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    rwa [Real.rpow_one] at h1
  have h23 : u ^ ((2 : ℝ) / 3) ≤ u * u := by
    have h1 : u ^ ((2 : ℝ) / 3) ≤ u ^ ((2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    have h2 : u ^ ((2 : ℝ)) = u * u := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two]
    rw [h2] at h1
    exact h1
  have huW : u * u ≤ W := by rw [hW]
  have ht2 : 80 * u * S2 ≤ 160 * Cb * W * P := by
    have h1 : S2 ≤ Cb * (2 * u ^ ((1 : ℝ) / 3)) * P :=
      le_trans hS2 (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKs hCb.le) hP0)
    have h2 : 80 * u * (Cb * (2 * u ^ ((1 : ℝ) / 3)) * P)
        = 160 * Cb * (u * u ^ ((1 : ℝ) / 3)) * P := by ring
    have h3 : u * u ^ ((1 : ℝ) / 3) ≤ W :=
      le_trans (mul_le_mul_of_nonneg_left h13 hu0) huW
    have h4 : 160 * Cb * (u * u ^ ((1 : ℝ) / 3)) * P ≤ 160 * Cb * W * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by linarith only [hCb])) hP0
    calc 80 * u * S2 ≤ 80 * u * (Cb * (2 * u ^ ((1 : ℝ) / 3)) * P) :=
          mul_le_mul_of_nonneg_left h1 (by linarith only [hu0])
      _ = 160 * Cb * (u * u ^ ((1 : ℝ) / 3)) * P := h2
      _ ≤ 160 * Cb * W * P := h4
  have ht3 : S3 ≤ 4 * Cc * W * P := by
    have h1 : S3 ≤ Cc * (4 * u ^ ((2 : ℝ) / 3)) * P :=
      le_trans hS3 (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKd hCc.le) hP0)
    have h2 : Cc * (4 * u ^ ((2 : ℝ) / 3)) * P = 4 * Cc * u ^ ((2 : ℝ) / 3) * P := by ring
    have h3 : 4 * Cc * u ^ ((2 : ℝ) / 3) * P ≤ 4 * Cc * W * P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_trans h23 huW) (by linarith only [hCc])) hP0
    calc S3 ≤ Cc * (4 * u ^ ((2 : ℝ) / 3)) * P := h1
      _ = 4 * Cc * u ^ ((2 : ℝ) / 3) * P := h2
      _ ≤ 4 * Cc * W * P := h3
  have hT : Real.pi * W * S1 + 80 * u * S2 + S3
      ≤ (Real.pi * Ca + 160 * Cb + 4 * Cc) * W * P := by
    have h1 : Real.pi * W * S1 ≤ Real.pi * Ca * W * P := by
      calc Real.pi * W * S1 ≤ Real.pi * W * (Ca * P) :=
            mul_le_mul_of_nonneg_left hS1 (mul_nonneg Real.pi_nonneg hW0)
        _ = Real.pi * Ca * W * P := by ring
    have h2 : (Real.pi * Ca + 160 * Cb + 4 * Cc) * W * P
        = Real.pi * Ca * W * P + 160 * Cb * W * P + 4 * Cc * W * P := by ring
    rw [h2]
    exact add_le_add (add_le_add h1 ht2) ht3
  have h3 : (Real.pi * Ca + 160 * Cb + 4 * Cc) * W * P
      ≤ (Real.pi * Ca + 160 * Cb + 4 * Cc) * W * (A * Q) := by
    have hC0 : (0 : ℝ) ≤ Real.pi * Ca + 160 * Cb + 4 * Cc := by
      nlinarith only [hCa, hCb, hCc, Real.pi_pos]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hW0)
    exact le_trans hPAR (mul_le_mul_of_nonneg_left hRQ hA0)
  have h4 : (Real.pi * Ca + 160 * Cb + 4 * Cc) * W * (A * Q)
      = ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A) * W * Q := by ring
  have h9 : (Real.pi * Ca + 160 * Cb + 4 * Cc) * W * P
      ≤ ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A) * W * Q := le_trans h3 (le_of_eq h4)
  have h11 : (65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A)) * W * Q
      ≤ (65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A + 1) + 1) * W * Q := by
    have hC0 : (0 : ℝ) ≤ Real.pi * Ca + 160 * Cb + 4 * Cc := by
      nlinarith only [hCa, hCb, hCc, Real.pi_pos]
    have hCA : (0 : ℝ) ≤ (Real.pi * Ca + 160 * Cb + 4 * Cc) * A := mul_nonneg hC0 hA0
    have h1 : 65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A)
        ≤ 65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A + 1) + 1 := by
      linarith only [hCA]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hW0) hQ0
  calc 65536 * (Real.pi * W * S1 + 80 * u * S2 + S3)
      ≤ 65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * W * P) :=
        mul_le_mul_of_nonneg_left hT (by norm_num)
    _ ≤ 65536 * (((Real.pi * Ca + 160 * Cb + 4 * Cc) * A) * W * Q) :=
        mul_le_mul_of_nonneg_left h9 (by norm_num)
    _ = (65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A)) * W * Q := by ring
    _ ≤ (65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * A + 1) + 1) * W * Q := h11

theorem tauSqBoxSelf :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ 2 * (Real.log Pa.N + 2) ^ (131073 : ℕ) := by
  obtain ⟨Ca, hCapos, hCa⟩ := sum_tau_pow_div_le 17
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.FIArea3.sum_tau_pow_div_sqrt_le 17
  obtain ⟨Cc, hCcpos, hCc⟩ := sum_tau_pow_le 17
  refine ⟨65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc) * (4 : ℝ) ^ ((2 : ℕ) ^ (17 : ℕ)) + 1) + 1,
    by positivity, ?_⟩
  intro Pa φ hu
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith only [hN1]
  have hlogN0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg Pa.hN1
  have hu1 : (1 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 8) := (Real.one_rpow _).symm
      _ ≤ (Pa.N : ℝ) ^ ((3 : ℝ) / 8) := Real.rpow_le_rpow (by norm_num) hN1 (by norm_num)
      _ ≤ Pa.θ * Real.sqrt Pa.N := hu
  set K : ℕ := ⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have h2 : (1 : ℝ) ≤ 2 * (Pa.N : ℝ) := by linarith only [hN1]
    have h3 : (1 : ℝ) ≤ (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) := by
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
        _ ≤ (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
    exact_mod_cast (le_trans h3 (Nat.le_ceil _))
  have hKlog0 : (0 : ℝ) ≤ Real.log (K : ℝ) + 2 := by
    have h : (0 : ℝ) ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
    linarith only [h]
  obtain ⟨hKle, hKsqrt, hKlog⟩ := K_arith Pa hu hu1 hN1
  -- the two log comparisons
  have hPAR : (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ))
      ≤ (4 : ℝ) ^ ((2 : ℕ) ^ (17 : ℕ)) * (Real.log (Pa.N : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)) := by
    have h1 : (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ))
        ≤ (4 * (Real.log (Pa.N : ℝ) + 2)) ^ ((2 : ℕ) ^ (17 : ℕ)) :=
      pow_le_pow_left₀ (by linarith only [hKlog0]) hKlog _
    rw [mul_pow] at h1
    exact h1
  have hRQ : (Real.log (Pa.N : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ))
      ≤ (Real.log (Pa.N : ℝ) + 2) ^ (131073 : ℕ) :=
    pow_le_pow_right₀ (by linarith only [hlogN0]) (by norm_num)
  -- (1) Lemma 2.2 pointwise, then the swap of the two sums
  have hK4 : (2 * (Pa.N : ℝ)) ≤ (K : ℝ) ^ (4 : ℕ) := by
    have h2N0 : (0 : ℝ) ≤ 2 * (Pa.N : ℝ) := by linarith only [hN1]
    have hge : (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) ≤ (K : ℝ) := by
      rw [hKdef]; exact Nat.le_ceil _
    calc (2 * (Pa.N : ℝ)) = ((2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := by
          rw [← Real.rpow_natCast ((2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul h2N0]
          norm_num
      _ ≤ (K : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg h2N0 _) hge 4
  have hgn : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
      ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (K : ℝ) ^ (4 : ℕ) := by
    intro z hz
    have hin := (Work.FIArea3.mem_polarBoxFinset.mp hz).2
    have hθ1 : Pa.θ ≤ 1 := theta_le_one6 Pa
    have hle : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hin.2.2.1
    have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (Pa.N : ℝ) := by
      nlinarith only [hle, hθ1, hN0]
    exact le_trans h2 hK4
  have hpt : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
      ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
        ≤ 65536 * ∑ d ∈ Finset.Icc 1 K,
            (if d ∣ Work.FIPlan.gnorm z then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
    fun z hz => tau_sq_le_sum_Icc_four (Work.FIPlan.gnorm z) K hK1 (hgn z hz)
  have hswap : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
        ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ))
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
              (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
    calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ))
        ≤ ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ, 65536 *
            ∑ d ∈ Finset.Icc 1 K,
              (if d ∣ Work.FIPlan.gnorm z then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
          Finset.sum_le_sum hpt
      _ = 65536 * ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
            ∑ d ∈ Finset.Icc 1 K,
              (if d ∣ Work.FIPlan.gnorm z then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
          rw [Finset.mul_sum]
      _ = 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
              (if d ∣ Work.FIPlan.gnorm z then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
          rw [Finset.sum_comm]
      _ = 65536 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
            * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
          refine congrArg (fun x : ℝ => 65536 * x) ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          have h1 : (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
                (if d ∣ Work.FIPlan.gnorm z then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0))
              = ∑ _z ∈ (Work.FIArea3.polarBoxFinset Pa φ).filter
                  (fun z => d ∣ Work.FIPlan.gnorm z), ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) := by
            simp only [Finset.sum_filter]
          rw [h1, Finset.sum_const, nsmul_eq_mul]
          ring
  -- (2) the three divisor sums and the pointwise expansion of each summand
  have hS1 : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
      ≤ Ca * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)) := hCa K
  have hS2 : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
        / Real.sqrt (d : ℝ))
      ≤ Cb * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)) := hCb K
  have hS3 : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)))
      ≤ Cc * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ ((2 : ℕ) ^ (17 : ℕ)) := hCc K
  have hS10 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => div_nonneg (by positivity) (Nat.cast_nonneg d)
  have hS20 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
      ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / Real.sqrt (d : ℝ) :=
    Finset.sum_nonneg fun d _ => div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hS30 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) :=
    Finset.sum_nonneg fun d _ => by positivity
  have hU : (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
        * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
            (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ))
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N)
            * (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
                / Real.sqrt (d : ℝ))
        + (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))) := by
    have hsumEq : (∑ d ∈ Finset.Icc 1 K,
          (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
              * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
            + 80 * (Pa.θ * Real.sqrt Pa.N)
                * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / Real.sqrt (d : ℝ))
            + ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))))
        = Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
              * (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
          + 80 * (Pa.θ * Real.sqrt Pa.N)
              * (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
                  / Real.sqrt (d : ℝ))
          + (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [← hsumEq]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hcard := polarBox_div_count Pa φ (Finset.mem_Icc.mp hd).1
    have hc1 : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
              (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
        ≤ ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((((d.divisors.card : ℕ) : ℝ)) / (d : ℝ))
            + 80 * (Pa.θ * Real.sqrt Pa.N) * (((d.divisors.card : ℕ) : ℝ)) / Real.sqrt (d : ℝ)
            + (((d.divisors.card : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (pow_nonneg (Nat.cast_nonneg _) _)
    refine le_trans hc1 ?_
    have hdt : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) * (((d.divisors.card : ℕ) : ℝ))
        = ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) := by ring
    have h1 : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((((d.divisors.card : ℕ) : ℝ)) / (d : ℝ)))
        = Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ)) := by
      rw [← hdt]; ring
    have h2 : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * (80 * (Pa.θ * Real.sqrt Pa.N) * (((d.divisors.card : ℕ) : ℝ)) / Real.sqrt (d : ℝ))
        = 80 * (Pa.θ * Real.sqrt Pa.N)
            * (((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / Real.sqrt (d : ℝ)) := by
      rw [← hdt]; ring
    have h3 : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) * (((d.divisors.card : ℕ) : ℝ))
        = ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) := hdt
    have h4 : ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((((d.divisors.card : ℕ) : ℝ)) / (d : ℝ))
            + 80 * (Pa.θ * Real.sqrt Pa.N) * (((d.divisors.card : ℕ) : ℝ)) / Real.sqrt (d : ℝ)
            + (((d.divisors.card : ℕ) : ℝ)))
        = ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
            * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((((d.divisors.card : ℕ) : ℝ)) / (d : ℝ)))
          + ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
            * (80 * (Pa.θ * Real.sqrt Pa.N) * (((d.divisors.card : ℕ) : ℝ)) / Real.sqrt (d : ℝ))
          + ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) * (((d.divisors.card : ℕ) : ℝ)) := by ring
    rw [h4, h1, h2, h3]
  calc (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
        ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ))
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
          * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
              (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := hswap
    _ ≤ 65536 * (Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)) / (d : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N)
            * (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ))
                / Real.sqrt (d : ℝ))
        + (∑ d ∈ Finset.Icc 1 K, ((((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)))) :=
        mul_le_mul_of_nonneg_left hU (by norm_num)
    _ ≤ (65536 * ((Real.pi * Ca + 160 * Cb + 4 * Cc)
            * (4 : ℝ) ^ ((2 : ℕ) ^ (17 : ℕ)) + 1) + 1)
          * (Pa.θ * Real.sqrt Pa.N) ^ 2 * (Real.log Pa.N + 2) ^ (131073 : ℕ) :=
        tauSqBox_arith hCapos hCbpos hCcpos hu1 (sq_nonneg _) (by ring) (pow_nonneg hKlog0 _)
          (pow_nonneg (by linarith only [hlogN0]) _)
          (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 4) _))
          (pow_nonneg (by linarith only [hlogN0]) _)
          hS10 hS20 hS30 (Real.sqrt_nonneg _) (Nat.cast_nonneg K) hKsqrt hKle hS1 hS2 hS3 hPAR hRQ

end

end Work.FIArea2.R6
