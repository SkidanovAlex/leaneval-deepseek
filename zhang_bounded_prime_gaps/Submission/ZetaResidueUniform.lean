import Mathlib
import Submission.ZetaWN
import Submission.RealExpBounds
import Submission.Commons.NumberTheory.Zeta.riemannZeta_residue_uniform_bound
import Submission.Commons.NumberTheory.Zeta.removedFactors_ratio_error
import Submission.Commons.NumberTheory.Zeta.primeFactors_log_over_prime_sum_le

open scoped BigOperators Topology
open Filter
open Commons.NumberTheory.Zeta

/-!
# Per-modulus uniform residue of `ζ_q` at `1 + z` (P8 (41) input (a))

With the three commissioned commons lemmas (L14 quantitative residue of
`ζ`; L15 removed-Euler-factor error; L16 prime-log-sum bound) and the
totient Euler product of `Submission/ZetaWN.lean`, the uniform pole
asymptotic holds *per modulus*: for every `q ≠ 0` there are `0 < C_q, δ_q`
with

    ‖ζ_q(1+z)·z·(q/φ(q)) − 1‖ ≤ C_q·‖z‖      (z ≠ 0, ‖z‖ ≤ δ_q)

(`zetaWN_residue_uniform_local`).  The decomposition:
`ζ_q(1+z) = ζ(1+z)·∏_{p|q}(1−p^{−(1+z)})`, so
`ζ_q(1+z)·z·(q/φ(q)) = (z·ζ(1+z))·(P(z)/B)` with
`B := ∏_{p|q}(1−p⁻¹) = φ(q)/q`, i.e. `(1+R)·(1+E)` where `|R| ≤ C₀‖z‖`
(L14) and `|E| ≤ exp(S)−1` with `S := Σ_{p|q}4‖z‖(log p)/p ≤ 2‖z‖·log q`
(L15 + L16); `exp(S)−1 ≤ 2S ≤ 4‖z‖·log q` and the cross term is absorbed by
choosing `δ_q := min r₀ (1/(2(1+log q)))`, giving the linear bound
`C_q := 1 + 3C₀ + 4 log q + 2 C₀ log q`.

Substituting `z = (1+iξ)/log x` (so `‖z‖ ≤ 2/√(log x) → 0`) then yields the
family `UniformPoleAsymptotic W N` of `Submission/XiTruncation.lean`
(recorded as the next step), completing input (a) of the ξ-truncation.
-/

namespace Commons.NumberTheory.MaynardSieve


/-- `|(1+R)(1+E) − 1| ≤ |R| + |E| + |R||E|`. -/
lemma abs_prod_one_add_sub_one_tri (R E : ℂ) :
    ‖(1 + R) * (1 + E) - 1‖ ≤ ‖R‖ + ‖E‖ + ‖R‖ * ‖E‖ := by
  have hsplit : (1 + R) * (1 + E) - 1 = R + E + R * E := by ring
  rw [hsplit]
  rw [show R + E + R * E = R + (E + R * E) by ring]
  have h2 := norm_add_le R (E + R * E)
  have h3 := norm_add_le E (R * E)
  have h4 : ‖R * E‖ = ‖R‖ * ‖E‖ := by rw [norm_mul]
  nlinarith

/-- **Per-modulus uniform residue of `ζ_q` with *given* constants.**  From a
quantitative Riemann-zeta bound with constants `C0, r0` one gets the radius
`δ_q := min r₀ (1/(2(1 + log q)))` and the linear constant
`C_q := 1 + 3C₀ + 4log q + 2C₀log q` (uniform in `q` once `C0, r0` are fixed —
this is the form needed for families of moduli). -/
theorem zetaWN_residue_uniform_of (q : ℕ) (hq : q ≠ 0) {C0 r0 : ℝ}
    (hC0pos : 0 < C0) (hr0pos : 0 < r0)
    (hC0 : ∀ z : ℂ, ‖z‖ ≤ r0 → z ≠ 0 → ‖z * riemannZeta (1 + z) - 1‖ ≤ C0 * ‖z‖) :
    ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ min r0 (1 / (2 * (1 + Real.log (q : ℝ)))) →
      ‖zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)) - 1‖ ≤
        (1 + 3 * C0 + 4 * Real.log (q : ℝ) + 2 * C0 * Real.log (q : ℝ)) * ‖z‖ := by
  classical
  let Lq : ℝ := Real.log (q : ℝ)
  have hLq0 : 0 ≤ Lq := by
    dsimp [Lq]
    have hq1 : (1 : ℕ) ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq)
    exact Real.log_nonneg (by exact_mod_cast hq1)
  have h1Lq : 0 < 1 + Lq := by positivity
  let δq : ℝ := min r0 (1 / (2 * (1 + Lq)))
  have hδq0 : 0 < δq := by
    dsimp [δq]
    exact lt_min hr0pos (by positivity)
  have hδq_r0 : δq ≤ r0 := by dsimp [δq]; exact min_le_left r0 (1 / (2 * (1 + Lq)))
  have hδq_small : δq ≤ 1 / (2 * (1 + Lq)) := by
    dsimp [δq]; exact min_le_right r0 (1 / (2 * (1 + Lq)))
  have h21 : 0 < 2 * (1 + Lq) := mul_pos (by norm_num) h1Lq
  have hδq_half : δq ≤ 1 / 2 := by
    calc δq ≤ 1 / (2 * (1 + Lq)) := hδq_small
    _ ≤ 1 / 2 := by
      rw [one_div, one_div]
      exact (inv_le_inv₀ h21 (by norm_num)).mpr (by nlinarith [hLq0])
  let Cq : ℝ := 1 + 3 * C0 + 4 * Lq + 2 * C0 * Lq
  have hCq0 : 0 < Cq := by
    dsimp [Cq]
    nlinarith [hC0pos, hLq0, mul_nonneg (by positivity : 0 ≤ C0) hLq0]
  intro z hz0 hzδ
  have hzr : ‖z‖ ≤ r0 := le_trans hzδ hδq_r0
  have hzhalf : ‖z‖ ≤ 1 / 2 := le_trans hzδ hδq_half
  have hR : ‖z * riemannZeta (1 + z) - 1‖ ≤ C0 * ‖z‖ := hC0 z hzr hz0
  let P : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 + z)))
  let B : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)
  let S : ℝ := ∑ p ∈ q.primeFactors, 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ)
  have hz_Lq : ‖z‖ * Lq ≤ 1 / 2 := by
    have hle : ‖z‖ ≤ 1 / (2 * (1 + Lq)) := le_trans hzδ hδq_small
    rw [le_div_iff₀ (by positivity : 0 < 2 * (1 + Lq))] at hle
    nlinarith
  have hz15 : ∀ p ∈ q.primeFactors, ‖z‖ * Real.log (p : ℝ) ≤ 1 := by
    intro p hp
    have hpd : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
    have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpd
    have hlog_le : Real.log (p : ℝ) ≤ Lq := by
      dsimp [Lq]
      have hpR : 0 < (p : ℝ) := by
        exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
      have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hp_le_q
      exact Real.log_le_log hpR hpqR
    have hmul : ‖z‖ * Real.log (p : ℝ) ≤ ‖z‖ * Lq :=
      mul_le_mul_of_nonneg_left hlog_le (norm_nonneg z)
    nlinarith [hmul, hz_Lq]
  have hE15 := removedFactors_ratio_error q hq z hz15
  have hSle : S ≤ 2 * ‖z‖ * Lq := by
    dsimp [S]
    have hsum1 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤ Lq / 2 := by
      have hL := primeFactors_log_over_prime_sum_le q hq
      dsimp [Lq] at hL ⊢
      exact hL
    have hsummul : (∑ p ∈ q.primeFactors, (4 * ‖z‖) * (Real.log (p : ℝ) / (p : ℝ))) ≤
        (4 * ‖z‖) * (Lq / 2) := by
      have hm : (4 * ‖z‖) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤
          (4 * ‖z‖) * (Lq / 2) :=
        mul_le_mul_of_nonneg_left hsum1 (by positivity : 0 ≤ 4 * ‖z‖)
      calc
        (∑ p ∈ q.primeFactors, (4 * ‖z‖) * (Real.log (p : ℝ) / (p : ℝ)))
            = (4 * ‖z‖) * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) := by
                rw [Finset.mul_sum]
        _ ≤ (4 * ‖z‖) * (Lq / 2) := hm
    calc
      (∑ p ∈ q.primeFactors, 4 * ‖z‖ * Real.log (p : ℝ) / (p : ℝ))
          = ∑ p ∈ q.primeFactors, (4 * ‖z‖) * (Real.log (p : ℝ) / (p : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              field_simp
      _ ≤ (4 * ‖z‖) * (Lq / 2) := hsummul
      _ = 2 * ‖z‖ * Lq := by ring
  have hS0 : 0 ≤ S := by
    dsimp [S]
    refine Finset.sum_nonneg ?_
    intro p hp
    positivity
  have hS1 : S ≤ 1 := by nlinarith [hSle, hz_Lq]
  have hEexp : ‖P / B - 1‖ ≤ Real.exp S - 1 := by
    simpa [P, B, S] using hE15
  have hE : ‖P / B - 1‖ ≤ 2 * S := hEexp.trans (exp_sub_one_le_two_mul hS0 hS1)
  have hE2 : ‖P / B - 1‖ ≤ 4 * Lq * ‖z‖ := by
    have h2 : 2 * S ≤ 4 * Lq * ‖z‖ := by nlinarith [hSle]
    exact hE.trans h2
  -- totient: (q/φ(q)) = B⁻¹
  have hφ0 : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have htot : ((q.totient : ℂ) / (q : ℂ)) = B := by
    simpa [B] using (totient_div_self_eq_prod_one_sub_inv q hq)
  have hqφ : ((q : ℂ) / (q.totient : ℂ)) = B⁻¹ := by
    calc
      ((q : ℂ) / (q.totient : ℂ))
          = (((q.totient : ℂ) / (q : ℂ))⁻¹) := by field_simp [hφ0, hq0]
      _ = B⁻¹ := by rw [htot]
  -- decomposition: zetaWN q (1+z)·z·(q/φ) = (zζ(1+z))·(P/B)
  have hA : zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)) =
      (z * riemannZeta (1 + z)) * (P / B) := by
    unfold zetaWN
    dsimp [P]
    rw [hqφ]
    rw [div_eq_mul_inv]
    ring
  -- final bound: |(1+R)(1+E) − 1| ≤ Cq‖z‖
  have hmain : ‖(z * riemannZeta (1 + z)) * (P / B) - 1‖ ≤ Cq * ‖z‖ := by
    have htri := abs_prod_one_add_sub_one_tri (z * riemannZeta (1 + z) - 1) (P / B - 1)
    have hprod : ‖((1 + (z * riemannZeta (1 + z) - 1)) * (1 + (P / B - 1))) - 1‖ ≤
        ‖z * riemannZeta (1 + z) - 1‖ + ‖P / B - 1‖ +
          ‖z * riemannZeta (1 + z) - 1‖ * ‖P / B - 1‖ := htri
    have hident : (z * riemannZeta (1 + z)) * (P / B) =
        (1 + (z * riemannZeta (1 + z) - 1)) * (1 + (P / B - 1)) := by ring
    calc
      ‖(z * riemannZeta (1 + z)) * (P / B) - 1‖
          = ‖((1 + (z * riemannZeta (1 + z) - 1)) * (1 + (P / B - 1))) - 1‖ := by
              rw [hident]
      _ ≤ ‖z * riemannZeta (1 + z) - 1‖ + ‖P / B - 1‖ +
              ‖z * riemannZeta (1 + z) - 1‖ * ‖P / B - 1‖ := hprod
      _ ≤ C0 * ‖z‖ + 4 * Lq * ‖z‖ + (C0 * ‖z‖) * (4 * Lq * ‖z‖) := by
              have hb1 : ‖z * riemannZeta (1 + z) - 1‖ ≤ C0 * ‖z‖ := hR
              have hb2 : ‖P / B - 1‖ ≤ 4 * Lq * ‖z‖ := hE2
              have hb3 : ‖z * riemannZeta (1 + z) - 1‖ * ‖P / B - 1‖ ≤
                  (C0 * ‖z‖) * (4 * Lq * ‖z‖) :=
                mul_le_mul hb1 hb2 (norm_nonneg (P / B - 1))
                  (by positivity : 0 ≤ C0 * ‖z‖)
              nlinarith [hb1, hb2, hb3]
      _ ≤ Cq * ‖z‖ := by
              -- cross ≤ 2·C0·Lq·‖z‖ (uses ‖z‖ ≤ 1/2)
              have hcross : (C0 * ‖z‖) * (4 * Lq * ‖z‖) ≤ 2 * C0 * Lq * ‖z‖ := by
                have hz2 : ‖z‖ * ‖z‖ ≤ (1 / 2) * ‖z‖ :=
                  mul_le_mul_of_nonneg_right hzhalf (norm_nonneg z)
                have hrewrite : (C0 * ‖z‖) * (4 * Lq * ‖z‖) = 4 * C0 * Lq * (‖z‖ * ‖z‖) := by ring
                rw [hrewrite]
                calc
                  4 * C0 * Lq * (‖z‖ * ‖z‖) ≤ 4 * C0 * Lq * ((1 / 2) * ‖z‖) := by
                          exact mul_le_mul_of_nonneg_left hz2 (by positivity : 0 ≤ 4 * C0 * Lq)
                  _ = 2 * C0 * Lq * ‖z‖ := by ring
              nlinarith [hcross, norm_nonneg z]
  -- assemble
  calc
    ‖zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)) - 1‖
        = ‖(z * riemannZeta (1 + z)) * (P / B) - 1‖ := by rw [hA]
    _ ≤ Cq * ‖z‖ := hmain

/-- The Riemann-zeta quantitative bound with explicit constants, packaged. -/
theorem riemannZeta_residue_uniform_bound_explicit :
    ∃ C0 r0 : ℝ, 0 < C0 ∧ 0 < r0 ∧
      (∀ z : ℂ, ‖z‖ ≤ r0 → z ≠ 0 → ‖z * riemannZeta (1 + z) - 1‖ ≤ C0 * ‖z‖) := by
  obtain ⟨C0, hC0pos, r0, hr0pos, hC0⟩ := riemannZeta_residue_uniform_bound
  exact ⟨C0, r0, hC0pos, hr0pos, hC0⟩

/-- **Per-modulus uniform residue of `ζ_q`, explicit constants (existential form).** -/
theorem zetaWN_residue_uniform_explicit (q : ℕ) (hq : q ≠ 0) :
    ∃ C0 r0 : ℝ, 0 < C0 ∧ 0 < r0 ∧
      (∀ z : ℂ, ‖z‖ ≤ r0 → z ≠ 0 → ‖z * riemannZeta (1 + z) - 1‖ ≤ C0 * ‖z‖) ∧
      ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ min r0 (1 / (2 * (1 + Real.log (q : ℝ)))) →
        ‖zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)) - 1‖ ≤
          (1 + 3 * C0 + 4 * Real.log (q : ℝ) + 2 * C0 * Real.log (q : ℝ)) * ‖z‖ := by
  obtain ⟨C0, r0, hC0pos, hr0pos, hC0⟩ := riemannZeta_residue_uniform_bound_explicit
  exact ⟨C0, r0, hC0pos, hr0pos, hC0,
    zetaWN_residue_uniform_of q hq hC0pos hr0pos hC0⟩

/-- Per-modulus uniform residue of `ζ_q` in existential form (wrapper around
`zetaWN_residue_uniform_explicit`). -/
theorem zetaWN_residue_uniform_local (q : ℕ) (hq : q ≠ 0) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∃ δq : ℝ, 0 < δq ∧ δq ≤ 1 / 2 ∧
      ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ δq →
        ‖zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)) - 1‖ ≤ Cq * ‖z‖ := by
  obtain ⟨C0, r0, hC0pos, hr0pos, hC0, hmain⟩ := zetaWN_residue_uniform_explicit q hq
  have hLq0 : 0 ≤ Real.log (q : ℝ) := by
    have hq1 : (1 : ℕ) ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq)
    exact Real.log_nonneg (by exact_mod_cast hq1)
  refine ⟨1 + 3 * C0 + 4 * Real.log (q : ℝ) + 2 * C0 * Real.log (q : ℝ), ?_,
    min r0 (1 / (2 * (1 + Real.log (q : ℝ)))), ?_, ?_, hmain⟩
  · nlinarith [hC0pos, hLq0, mul_nonneg hC0pos.le hLq0]
  · exact lt_min hr0pos (by positivity)
  · calc min r0 (1 / (2 * (1 + Real.log (q : ℝ))))
        ≤ 1 / (2 * (1 + Real.log (q : ℝ))) := min_le_right _ _
      _ ≤ 1 / 2 := by
          rw [one_div, one_div]
          exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith [hLq0])
