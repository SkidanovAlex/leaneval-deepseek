/-
# Area 4 (round 6): the `τ³`-energy of a round-6 coefficient is admissible

This file proves the crude bound on the *frozen* `τ³`-energy of a round-6 coefficient

  `A6Ener3 Pa β = Σ_{z ∈ boxN Pa} τ(|Re z|)³ ‖β z‖²
      ≤ C · (θ²N + N^{5/6} + 1) · (log N + 1)^{2^20 - 30}`,

which is the energy bound the §15 reduction (`Work.FIArea4.A6RedProp`, `ExpBound6`,
`strUvarSum6` …) consumes and the one that the target `A6PieceBound` can absorb.

The proof is a short composition of three pieces, two of which already exist in the workspace:

* `IsBetaCoeff6.support` puts the support of `β` inside the polar box, so the sum over the frozen
  box `boxN Pa` is the sum over `S15polarBox Pa φ`; `IsBetaCoeff6_norm_le` gives the pointwise
  `‖β z‖ ≤ τ(|z|²)` (from `IsBetaCoeff6.exists_toBetaCoeff` and `IsBetaCoeff.toBoxCoeff`);
* the two-factor form `S15bea_stepA` of the box-energy estimate bounds the resulting *arithmetic*
  energy `Σ_{z ∈ S15polarBox Pa φ} τ(|Re z|)³ τ(|z|²)²` by
  `C_A 2^6 C_1 (log(K+2))^{64} (Aw + K^{1/4}) · 2^10 C_2 (log(K+2))^B (Aw + K^{1/3})`
  with `K = ⌈2N⌉`, `Aw = 10θ√N` and `B ≤ 900000`;
* the bookkeeping (`log_pow_le_900064`, `bea_arith30`) observes that this two-factor bound is
  already good enough for the *smaller* exponent `2^20 - 30`: `64 + B ≤ 900064 ≤ 2^20 - 30`, so
  the `30` powers of `log` need not be paid for.  (The same slack is what `S15rem_energy_log` uses
  for the remainder half of §15.)

Nothing here uses more of `β` than its support and the size `|β| ≤ τ(|z|²)`.
-/
import Mathlib
import Submission.Work.FIArea4.A6Defs
import Submission.Work.FIArea4.S15_box_energy_stepA

set_option maxHeartbeats 800000

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary logarithmic bounds -/

/-- The constant `3^{900064}` of the log bookkeeping: `900064 = 2^6 + 9·10^5` is the largest
exponent that the two-factor box-energy bound can produce (it is `2^6` from the `τ(|Re z|)³` half
plus `B ≤ 9·10^5` from the `τ(|z|²)²` half). -/
def C30 : ℝ := (3 : ℝ) ^ (900064 : ℕ)

lemma C30_pos : 0 < C30 := by unfold C30; positivity

/-- `1 ≤ log (⌈2x⌉ + 2)` for `x ≥ 1`: the argument is at least `4` and `log 4 ≥ 1`. -/
lemma one_le_log_ceil (x : ℝ) (hx : 1 ≤ x) :
    (1 : ℝ) ≤ Real.log (((⌈2 * x⌉₊ : ℕ) : ℝ) + 2) := by
  have h2x : (2 : ℝ) ≤ 2 * x := by linarith
  have hceil : (2 : ℝ) ≤ ((⌈2 * x⌉₊ : ℕ) : ℝ) := le_trans h2x (Nat.le_ceil (2 * x))
  have h4 : (4 : ℝ) ≤ ((⌈2 * x⌉₊ : ℕ) : ℝ) + 2 := by linarith
  have h1 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.exp_one_lt_three]
  exact le_trans h1 (Real.log_le_log (by norm_num) h4)

/-- `log (⌈2x⌉ + 2) ≤ 3 (log x + 1)` for `x ≥ 1`: `⌈2x⌉ + 2 ≤ 8x` and `log 8 = 3 log 2 ≤ 3`. -/
lemma log_ceil_two_mul_add_two_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log (((⌈2 * x⌉₊ : ℕ) : ℝ) + 2) ≤ 3 * (Real.log x + 1) := by
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * x by linarith)
  have hpos : 0 < ((⌈2 * x⌉₊ : ℕ) : ℝ) + 2 := by
    have h2x : (2 : ℝ) ≤ 2 * x := by linarith
    have hceil : (2 : ℝ) ≤ ((⌈2 * x⌉₊ : ℕ) : ℝ) := le_trans h2x (Nat.le_ceil (2 * x))
    linarith
  have hle : ((⌈2 * x⌉₊ : ℕ) : ℝ) + 2 ≤ 8 * x := by linarith
  have hmono : Real.log (((⌈2 * x⌉₊ : ℕ) : ℝ) + 2) ≤ Real.log (8 * x) :=
    Real.log_le_log hpos hle
  have hlog8 : Real.log (8 * x) = Real.log 8 + Real.log x :=
    Real.log_mul (by norm_num) (by linarith)
  have hlog8eq : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [hlog8, hlog8eq] at hmono
  linarith

/-- **The `2^20` of the box energy is `900064` in disguise.**  With `64 + B ≤ 900064 ≤ 2^20 - 30`
the `(log (⌈2N⌉ + 2))^{64+B}` factor of the two-factor box-energy bound already lands in the
`(log N + 1)^{2^20 - 30}` of the target. -/
lemma log_pow_le_900064 (x : ℝ) (hx : 1 ≤ x) (B : ℝ) (hB : B ≤ 900000) :
    (Real.log (((⌈2 * x⌉₊ : ℕ) : ℝ) + 2)) ^ ((2 : ℝ) ^ 6 + B)
      ≤ C30 * (Real.log x + 1) ^ (((2 : ℕ) ^ 20) - 30) := by
  set l : ℝ := Real.log (((⌈2 * x⌉₊ : ℕ) : ℝ) + 2) with hl
  set Lp : ℝ := Real.log x + 1 with hLp
  have hLp1 : 1 ≤ Lp := by rw [hLp]; linarith [Real.log_nonneg hx]
  have hl1 : 1 ≤ l := by rw [hl]; exact one_le_log_ceil x hx
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one hl1
  have hle : l ≤ 3 * Lp := by
    rw [hl, hLp]
    exact log_ceil_two_mul_add_two_le x hx
  have hexp : (2 : ℝ) ^ 6 + B ≤ (900064 : ℝ) := by
    have h : ((2 : ℝ) ^ 6 : ℝ) = 64 := by norm_num
    linarith
  have hC30 : (3 : ℝ) ^ (900064 : ℕ) = C30 := rfl
  calc l ^ ((2 : ℝ) ^ 6 + B) ≤ l ^ (900064 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hl1 hexp
    _ = l ^ (900064 : ℕ) := Real.rpow_natCast l 900064
    _ ≤ (3 * Lp) ^ (900064 : ℕ) := pow_le_pow_left₀ (le_of_lt hlpos) hle 900064
    _ = (3 : ℝ) ^ (900064 : ℕ) * Lp ^ (900064 : ℕ) := by rw [mul_pow]
    _ ≤ C30 * Lp ^ (((2 : ℕ) ^ 20) - 30) := by
        rw [hC30]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLp1 (by norm_num)) C30_pos.le

/-! ## 2. The final arithmetic of the box energy, with the target's exponent -/

/-- **The arithmetic half of the box-energy estimate, with the exponent `2^20 - 30`.**
The two-factor bound produced by `S15bea_stepA` (with `K = ⌈2N⌉`, `Aw = 10θ√N`, `B ≤ 900000`)

  `C_A · 2^6 C_1 (log(K+2))^{2^6} (Aw + K^{1/4}) · 2^10 C_2 (log(K+2))^B (Aw + K^{1/3})`

is at most `C_A 2^16 C_1 C_2 3^{900064} 200 · (θ²N + N^{5/6} + 1) · (log N + 1)^{2^20 - 30}`:
`(Aw + K^{1/4})(Aw + K^{1/3}) ≤ 200(θ²N + N^{5/6} + 1)` (`S15bea_Th_bound`) and
`(log(K+2))^{64+B} ≤ 3^{900064}(log N + 1)^{2^20-30}` (`log_pow_le_900064`). -/
lemma bea_arith30 (Pa : Work.FITop.Params)
    (C_A C_1 C_2 B : ℝ) (hC_A : 0 < C_A) (hC_1 : 0 < C_1) (hC_2 : 0 < C_2)
    (hB : B ≤ 900000) :
    C_A * (2 ^ 6 * (C_1 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ (2 ^ 6))
          * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 4 : ℝ)))
        * (2 ^ 10 * (C_2 * (Real.log ((((⌈2 * Pa.N⌉₊ : ℕ)) : ℝ) + 2)) ^ B)
          * (10 * Pa.θ * Real.sqrt Pa.N + (⌈2 * Pa.N⌉₊ : ℝ) ^ (1 / 3 : ℝ)))
      ≤ (C_A * 2 ^ 16 * C_1 * C_2 * C30 * 200)
        * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
        * (Real.log Pa.N + 1) ^ (((2 : ℕ) ^ 20) - 30) := by
  set K : ℕ := ⌈2 * Pa.N⌉₊ with hK
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hKpos : 0 < K := by
    have h : (1 : ℝ) ≤ 2 * Pa.N := by linarith
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by rw [hK]; exact le_trans h (Nat.le_ceil (2 * Pa.N))
    exact_mod_cast h2
  have hK1 : 1 ≤ K := hKpos
  have hKle : (K : ℝ) ≤ 2 * Pa.N + 1 := by
    rw [hK]; exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  set Aw : ℝ := 10 * Pa.θ * Real.sqrt Pa.N with hAw
  have hAw0 : 0 ≤ Aw := by
    rw [hAw]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg Pa.N)
  set l : ℝ := Real.log ((K : ℝ) + 2) with hl
  set Lp : ℝ := Real.log Pa.N + 1 with hLp
  set Th : ℝ := Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1 with hTh
  have hprod : (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) ≤ 200 * Th := by
    rw [hTh]
    exact S15bea_Th_bound Pa K Aw hAw hAw0 hK1 hKle hθ1 hN1
  have hl_pow : l ^ ((2 : ℝ) ^ 6 + B) ≤ C30 * Lp ^ (((2 : ℕ) ^ 20) - 30) := by
    rw [hl, hK, hLp]
    exact log_pow_le_900064 Pa.N hN1 B hB
  have hl1 : 1 ≤ l := by rw [hl, hK]; exact one_le_log_ceil Pa.N hN1
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one hl1
  have hlcomb : l ^ (2 ^ 6) * l ^ B = l ^ (2 ^ 6 + B) := by
    have h1 : l ^ (2 ^ 6) = l ^ ((64 : ℝ)) := by
      rw [← Real.rpow_natCast l (2 ^ 6)]; norm_num
    have h2 : (2 ^ 6 + B) = ((64 : ℝ) + B) := by norm_num
    rw [h1, h2, ← Real.rpow_add hlpos]
  calc C_A * (2 ^ 6 * (C_1 * l ^ (2 ^ 6)) * (Aw + (K : ℝ) ^ (1 / 4 : ℝ)))
        * (2 ^ 10 * (C_2 * l ^ B) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)))
      = C_A * 2 ^ 16 * C_1 * C_2 * (l ^ (2 ^ 6) * l ^ B)
          * ((Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ))) := by ring
    _ = C_A * 2 ^ 16 * C_1 * C_2 * l ^ (2 ^ 6 + B)
          * ((Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ))) := by rw [hlcomb]
    _ ≤ C_A * 2 ^ 16 * C_1 * C_2 * (C30 * Lp ^ (((2 : ℕ) ^ 20) - 30))
          * (200 * Th) := by
        have hA : 0 ≤ C_A * 2 ^ 16 * C_1 * C_2 := by positivity
        have hB2 : 0 ≤ (Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)) := by
          have h2 : (0 : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg K) _
          have h3 : (0 : ℝ) ≤ (K : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg K) _
          exact mul_nonneg (by linarith) (by linarith)
        have hLp0 : 0 ≤ Lp := by rw [hLp]; linarith [Real.log_nonneg hN1]
        have hLp30 : 0 ≤ Lp ^ (((2 : ℕ) ^ 20) - 30) := pow_nonneg hLp0 _
        have h30 : 0 ≤ C30 := C30_pos.le
        calc C_A * 2 ^ 16 * C_1 * C_2 * l ^ (2 ^ 6 + B)
              * ((Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ)))
            ≤ C_A * 2 ^ 16 * C_1 * C_2 * (C30 * Lp ^ (((2 : ℕ) ^ 20) - 30))
              * ((Aw + (K : ℝ) ^ (1 / 4 : ℝ)) * (Aw + (K : ℝ) ^ (1 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl_pow hA) hB2
          _ ≤ C_A * 2 ^ 16 * C_1 * C_2 * (C30 * Lp ^ (((2 : ℕ) ^ 20) - 30))
              * (200 * Th) := by
              apply mul_le_mul_of_nonneg_left hprod
              exact mul_nonneg hA (mul_nonneg h30 hLp30)
    _ = (C_A * 2 ^ 16 * C_1 * C_2 * C30 * 200) * Th
          * (Real.log Pa.N + 1) ^ (((2 : ℕ) ^ 20) - 30) := by
        rw [hLp, hTh]; ac_rfl

/-! ## 3. The two box-energy facts: support and size of a round-6 coefficient -/

/-- **A round-6 coefficient is bounded by `τ(|z|²)`**: `|q| ≤ 1`, `|p| ≤ 1`, `|μ| ≤ 1` and
`|γ(n;C)| ≤ τ(n)` (`abs_gammaTrunc_le`), through `IsBetaCoeff6.exists_toBetaCoeff` and
`IsBetaCoeff.toBoxCoeff`. -/
lemma IsBetaCoeff6_norm_le (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  obtain ⟨β', hβ', hβeq⟩ := h.exists_toBetaCoeff
  have hbox := hβ'.toBoxCoeff
  rw [hβeq z]
  split_ifs with hc
  · exact hbox.1 z
  · simp

/-! ## 4. The box energy with the target's exponent, and the target -/

/-- The box energy `Σ_{z ∈ S15polarBox Pa φ} τ(|Re z|)³ τ(|z|²)²` is
`≤ C(θ²N + N^{5/6} + 1)(log N + 1)^{2^20-30}` — the *sharper* form of `S15_box_energy2` in which
the `30` powers of `log` are absorbed by the slack `64 + B ≤ 900064 ≤ 2^20 - 30` inside the
two-factor bound `S15bea_stepA`. -/
theorem S15_box_energy2_30 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      (∑ z ∈ Work.FIArea4.S15polarBox Pa φ,
          ((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2)
        ≤ C * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
            * (Real.log Pa.N + 1) ^ (((2 : ℕ) ^ 20) - 30) := by
  obtain ⟨C_A, hC_A, hcount⟩ := S15_polar_joint_count
  obtain ⟨C_2, B, hC_2, hB, hsum⟩ := S15_tau10_d2_sum
  obtain ⟨C_1, hC_1pos, hC_1⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 6
  refine ⟨C_A * 2 ^ 16 * C_1 * C_2 * C30 * 200, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hC_A (by norm_num)) hC_1pos) hC_2)
      C30_pos) (by norm_num)
  · intro Pa φ
    exact le_trans
      (S15bea_stepA C_A hC_A hcount C_2 B hC_2 hB hsum C_1 hC_1pos hC_1 Pa φ)
      (bea_arith30 Pa C_A C_1 C_2 B hC_A hC_1pos hC_2 hB)

/-- **The requested lemma**: the `τ³`-energy of a round-6 coefficient is bounded by the bracket
of the target `A6PieceBound`.  The support of `β` lies in the polar box (so the sum over `boxN`
is the sum over `S15polarBox Pa φ`), `‖β z‖ ≤ τ(|z|²)`, and the arithmetic box energy
`Σ τ(|Re z|)³ τ(|z|²)²` is bounded by `S15_box_energy2_30`. -/
theorem A6Ener3_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      Work.FIArea4.A6Ener3 Pa β
        ≤ C * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
            * (Real.log Pa.N + 1) ^ (((2 : ℕ) ^ 20) - 30) := by
  obtain ⟨C, hC, hbox⟩ := S15_box_energy2_30
  refine ⟨C, hC, ?_⟩
  intro Pa φ z0 β h
  have hA6 : Work.FIArea4.A6Ener3 Pa β
      = ∑ z ∈ Work.FIArea4.S15polarBox Pa φ,
          ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z) := by
    have hsub : (∑ z ∈ Work.FIArea4.S15polarBox Pa φ,
          ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z))
        = ∑ z ∈ Work.FITop.boxN Pa,
          ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z) := by
      refine Finset.sum_subset (fun z hz => (Work.FIArea4.mem_S15polarBox.mp hz).1) ?_
      intro z hz hzs
      have hnp : ¬ Work.FITop3.InPolarBox Pa φ z :=
        fun hp => hzs (Work.FIArea4.mem_S15polarBox.mpr ⟨hz, hp⟩)
      have h0 : β z = 0 := by
        by_contra hne
        exact hnp (h.support hne)
      rw [h0]
      simp
    unfold Work.FIArea4.A6Ener3
    exact hsub.symm
  rw [hA6]
  calc (∑ z ∈ Work.FIArea4.S15polarBox Pa φ,
          ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3) * Complex.normSq (β z))
      ≤ ∑ z ∈ Work.FIArea4.S15polarBox Pa φ,
          ((((z.re.natAbs.divisors.card : ℕ) : ℝ)) ^ 3)
            * ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (IsBetaCoeff6_norm_le Pa φ z0 β h z) 2
    _ ≤ C * (Pa.θ ^ 2 * Pa.N + Pa.N ^ ((5 : ℝ) / 6) + 1)
          * (Real.log Pa.N + 1) ^ (((2 : ℕ) ^ 20) - 30) := hbox Pa φ

end

end Work.FIArea4
