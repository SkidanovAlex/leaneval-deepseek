import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Red6.G0_eq_ratioSym_sum
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
import Submission.Work.FIArea3.area3_of_core
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.pairSumWeak6

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester): (unchanged, see the file header of the round-6
contract `Submission/Work/FITop4/Areas6.lean`).  AREA 3 = (10.10) with the `(τ⁻¹+θ)` error,
`cMain6` and the paper's `T(β)`.

This file reduces the round-6 area-3 statement `Work.FITop4.Area3_6` to the single analytic input
`Work.FIArea3.PairSumBound6` (= *FI* Lemma 10.1 in the form (10.10) consumes it, stated in
`PairDefs6.lean`), by

* the §10 identity at the **corrected** kernel `G0 = G0fix = Cnt/|Δ|` (`diff_eq6`): the difference
  of the two main terms of (9.11) is exactly the per-pair sum of §10's error kernel;
* the corrected (8.16) evaluation of the kernel (`Red6.G0_eq_ratioSym_sum`) which bounds
  `|G₀(z₁,z₂)| ≤ 2(1 + τ(|Δ|))` on the pairs that occur (`G0_abs_le`);
* the elementary factor bounds of §10 (quarter-power, `log N`, `Fhat ≤ 7√M`).

The only input is `PairSumBound6`. -/

set_option autoImplicit false

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The §10 error kernel and the identity at the corrected main term -/

/-- The per-pair kernel of §10: the error of replacing `|z₁z₂|^{-1/2}` by `N^{-1/2}` in (10.4),
multiplied by the normalisation `f̂(0) = Fhat Pa F`, the log-factor (7.10) and the corrected
kernel `G₀ = Cnt/|Δ|`. -/
def errKer (fhat N : ℝ) (z1 z2 : GaussianInt) : ℂ :=
  ((fhat : ℂ)) * ((Work.FITop4.logFac6 z1 z2 : ℂ)) * ((Work.FITop4.G0 z1 z2 : ℂ))
    * ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) - N ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

/-- **The §10 identity at the corrected main term**: the difference of the two sums of (9.11) —
the corrected `D₀` and the main term `cMain6·T(β)` of (10.4) — is the `β_{z₁}β̄_{z₂}`-weighted sum
of the per-pair error kernels.  (This is `Defs.diff_eq` re-proved at `Defs6.D0`, `Defs6.Tbeta`,
`Defs6.cMain6` and the count kernel `G0 = G0fix`.) -/
theorem diff_eq6 (Rz : ℤ) (fhat N : ℝ) (β : GaussianInt → ℂ) :
    Work.FITop4.D0 Rz fhat β - Work.FITop4.cMain6 fhat N * Work.FITop4.Tbeta Rz β
      = ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then β z1 * star (β z2) * errKer fhat N z1 z2
           else 0) := by
  have hA : Work.FITop4.D0 Rz fhat β
      = ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2) * (((fhat : ℂ) * ((Work.FITop4.logFac6 z1 z2 : ℂ))
              * ((Work.FITop4.G0 z1 z2 : ℂ))
              * ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)))
           else 0) := by
    simp only [Work.FITop4.D0, Work.FITop4.C0]
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
    split_ifs with hc
    · push_cast
      ring
    · rfl
  have hB : Work.FITop4.cMain6 fhat N * Work.FITop4.Tbeta Rz β
      = ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2) * (((Work.FITop4.G0 z1 z2 : ℂ))
              * ((Work.FITop4.logFac6 z1 z2 : ℂ)) * (((fhat * N ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)))
           else 0) := by
    simp only [Work.FITop4.Tbeta, Work.FITop4.cMain6]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    split_ifs with hc
    · push_cast
      ring
    · simp
  rw [hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hc, if_true]
    rw [errKer]
    push_cast
    ring
  · simp only [hc, if_false]
    simp

/-! ## 2. The kernel bound: the corrected (8.16) evaluation of `G₀ = Cnt/|Δ|` -/

/-- The Jacobi symbol of the residue (6.6) is `0` or `±1`. -/
theorem abs_ratioSym_le_one (z1 z2 : GaussianInt) (d : ℕ) :
    |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
  rw [Work.FIArea7.ratioSym]
  rcases jacobiSym.trichotomy
    ((((star z1 * z2).re : ZMod d) * (((Work.FIPlan.gnorm z1 : ℕ) : ZMod d))⁻¹).val : ℤ) d
    with h | h | h <;> rw [h] <;> norm_num

/-- **The (7.10) log-factor of round 6 at the corrected constant**: for two points of the polar
box, `|log(8|z₁z₂|/|Δ|)| ≤ 12 log N`.  (`Work.FITop4.logFac6 = log 4 + Work.FITop3.logFac` whenever
`|Δ| ≠ 0`, where `|Work.FITop3.logFac| ≤ 4 log N`; and `log N ≥ 17/64`, `log 4 ≤ 2`, so
`log 4 + 4 log N ≤ 12 log N`.) -/
theorem abs_logFac6_le {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    |Work.FITop4.logFac6 z1 z2| ≤ 12 * Real.log Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hlogN : (17 : ℝ) / 64 ≤ Real.log Pa.N := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : (17 : ℝ) / 16 ≤ Real.log 3 := log_three_ge
    have h4 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    have h5 : (1 : ℝ) / 4 * Real.log (Pa.x : ℝ) ≤ Real.log Pa.N := by
      have hlt := Pa.hNlo
      have hpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
      have h6 : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ≤ Real.log Pa.N :=
        Real.log_le_log (Real.rpow_pos_of_pos hpos _) (le_of_lt hlt)
      rw [Real.log_rpow hpos] at h6
      have h7 : (1 : ℝ) / 4 * Real.log (Pa.x : ℝ) ≤ ((1 : ℝ) / 4 + Pa.η) * Real.log (Pa.x : ℝ) := by
        have h8 : (0 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
          have : (1 : ℝ) < (Pa.x : ℝ) := by linarith
          exact le_of_lt (Real.log_pos this)
        nlinarith [Pa.hη, h8]
      linarith
    have h9 : (17 : ℝ) / 64 ≤ (1 : ℝ) / 4 * Real.log (Pa.x : ℝ) := by
      have : (1 : ℝ) / 4 * (17 / 16) ≤ (1 : ℝ) / 4 * Real.log (Pa.x : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith
      linarith
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have h := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h4]; linarith
  have hbase : |Work.FITop3.logFac z1 z2| ≤ 4 * Real.log Pa.N := abs_logFac_le h1 h2
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · have hz : Work.FITop4.logFac6 z1 z2 = 0 := by
      unfold Work.FITop4.logFac6
      rw [h0]
      simp
    rw [hz, abs_zero]
    nlinarith
  · have hΔ1 : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hgn : (0 : ℝ) < Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
      apply Real.sqrt_pos.mpr
      have h1n : (0 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := by
        have := h1.2.1; linarith
      simp only [gnorm_mul', Nat.cast_mul]
      have h2n : (0 : ℝ) < (Work.FIPlan.gnorm z2 : ℝ) := by
        have := h2.2.1; linarith
      positivity
    have hsplit : Work.FITop4.logFac6 z1 z2
        = Real.log 4 + Work.FITop3.logFac z1 z2 := by
      unfold Work.FITop4.logFac6 Work.FITop3.logFac
      have harg : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
          = 4 * (2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) := by ring
      rw [harg, Real.log_mul (by norm_num) (by positivity)]
    rw [hsplit]
    calc |Real.log 4 + Work.FITop3.logFac z1 z2|
        ≤ |Real.log 4| + |Work.FITop3.logFac z1 z2| := abs_add_le _ _
      _ = Real.log 4 + |Work.FITop3.logFac z1 z2| := by rw [abs_of_nonneg (by positivity)]
      _ ≤ 2 + 4 * Real.log Pa.N := by linarith
      _ ≤ 12 * Real.log Pa.N := by linarith

/-- A round-6 coefficient is an `IsBoxCoeff`: `‖β z‖ ≤ τ(|z|²)`, supported in the polar box and
free of primes `≤ P` (5.8).  (The `μ`-factor of (4.13) contributes `≤ 1` and `γ(n;C) ≤ τ(n)`.) -/
theorem isBoxCoeff_of_isBetaCoeff6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    Work.FITop3.IsBoxCoeff Pa φ β := by
  have hmain := h
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hβ⟩ := h
  constructor
  · intro z
    rw [hβ z]
    split_ifs with hz
    · have hqp : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
        have hA : 0 ≤ q (Complex.arg z.toComplex - φ) := hq0 _
        have hB : 0 ≤ p (Work.FIPlan.gnorm z) := hp0 _
        have hC : q (Complex.arg z.toComplex - φ) ≤ 1 := hq1 _
        have hD : p (Work.FIPlan.gnorm z) ≤ 1 := hp1 _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by nlinarith, by simpa using mul_le_mul hC hD hB (by norm_num)⟩
      have hmu := Work.FITop3.norm_moebius_le_one (Work.FIPlan.gnorm z)
      have hg : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Work.FITop3.abs_gammaTrunc_le _ _
      calc ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
          = ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ))‖
            * ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖ := by
            rw [norm_mul]
        _ ≤ (1 * 1) * ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
            gcongr
            rw [norm_mul]
            exact mul_le_mul hqp hmu (by positivity) (by norm_num)
        _ = ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by ring
    · simp
  · intro z hz
    exact ⟨Work.FITop4.IsBetaCoeff6.support hmain hz, Work.FITop4.IsBetaCoeff6.noSmallPrimes hmain hz⟩

/-- **The corrected (8.16) bound**: on the pairs that occur in (10.5) — coprime, both in the
support of a round-6 coefficient (hence primitive, in the polar box) and in the same class mod
`8` (5.7) — the count kernel is bounded by `2(1 + τ(|Δ|))`,

  `|G₀(z₁,z₂)| = |2 Σ_{4d|Δ}(φ(d)/d)(z₂/z₁|d)| ≤ 2·#{d : 4d ∣ Δ} ≤ 2(1 + τ(|Δ|))`.

This is `Red6.G0_eq_ratioSym_sum` (Lemma 8.4 with the ratio symbol (6.6)) plus the trivial bound on
the Jacobi symbol. -/
theorem G0_abs_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z1 z2 : GaussianInt}
    (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) (hcop : Work.FIPlan.GaussCoprime z1 z2) :
    |Work.FITop4.G0 z1 z2| ≤ 2 * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) := by
  have hbox1 := Work.FITop4.IsBetaCoeff6.support hβ h1
  have hbox2 := Work.FITop4.IsBetaCoeff6.support hβ h2
  have hodd1 := Work.FIArea2.InPolarBox.odd_gnorm hbox1
  have hcl := Work.FITop4.IsBetaCoeff6.sameClass hβ h1 h2
  have hprim1 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h1) hodd1
  have hprim2 := Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ h2)
    (Work.FIArea2.InPolarBox.odd_gnorm hbox2)
  have hn1 : 2 ≤ Work.FIPlan.gnorm z1 := by
    have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast Pa.hN1) hbox1.2.1
    have hgt' : (1 : ℕ) < Work.FIPlan.gnorm z1 := by exact_mod_cast hgt
    omega
  have hDelta : Work.FIPlan.Delta z1 z2 ≠ 0 :=
    Work.FIArea2.Delta_ne_zero_of_coprime hcop hprim1 hprim2 hn1
  have hD : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simpa [Work.FIPlan.absDelta] using Int.natAbs_ne_zero.mpr hDelta
  have hsum := Work.FITop4.Red6.G0_eq_ratioSym_sum hodd1 hcl hD hcop hprim1 hprim2
  have hcard : (Work.FITop4.Sset z1 z2).card ≤ (Work.FIPlan.absDelta z1 z2).divisors.card := by
    refine Finset.card_le_card fun d hd => ?_
    rw [Work.FITop4.Sset, Finset.mem_filter] at hd
    obtain ⟨hdIcc, hdvd⟩ := hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    exact Nat.mem_divisors.mpr ⟨dvd_trans (dvd_mul_left d 4) hdvd, hD⟩
  have hbound : |∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
      ≤ ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Work.FITop4.Sset z1 z2,
        |((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
      intro d hd
      rw [Work.FITop4.Sset, Finset.mem_filter] at hd
      have hd1 : (0 : ℝ) < (d : ℝ) := by
        have : 1 ≤ d := (Finset.mem_Icc.mp hd.1).1
        exact_mod_cast this
      have ht : |((Nat.totient d : ℝ) / (d : ℝ))| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        rw [div_le_one hd1]
        exact_mod_cast Nat.totient_le d
      calc |((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
          = |((Nat.totient d : ℝ) / (d : ℝ))| * |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul ht (abs_ratioSym_le_one z1 z2 d) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc ∑ d ∈ Work.FITop4.Sset z1 z2,
          |((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
        ≤ ∑ _d ∈ Work.FITop4.Sset z1 z2, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Work.FITop4.Sset z1 z2).card : ℝ) := by simp
      _ ≤ ((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) := by exact_mod_cast hcard
  have hdivnn : (0 : ℝ) ≤ (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) := by positivity
  rw [hsum]
  have habs2 : |(2 : ℝ) * ∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)|
      = 2 * |∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (Work.FIArea7.ratioSym z1 z2 d : ℝ)| := by
    rw [abs_mul]
    norm_num
  rw [habs2]
  linarith

/-! ## 3. The §10 factor bounds and the reduction to the pair sum -/

/-- **The pointwise §10 bound**: on any pair, the §10 error kernel is bounded by
`28·θ·(log N)·√M/√N` times the `τ(Δ)`-weight, using

* `|f̂(0)| ≤ 7√M` (`Fhat_le` + `Fhat_nonneg`),
* `log(2|z₁z₂/Δ|) ≤ 4 log N` (`abs_logFac_le`),
* `|G₀(z₁,z₂)| ≤ 2(1+τ(|Δ|))` (`G0_abs_le`, the corrected (8.16)),
* `|(z₁z₂)^{-1/2} − N^{-1/2}| ≤ θ/(2√N)` (`quarter_rpow_sub_le`, from (5.14)). -/
theorem term_bound6 {Pa : Work.FITop.Params} {f : ℤ → ℝ} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hF : Work.FITop4.IsMajorant6 Pa f)
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z1 z2 : GaussianInt) :
    ‖(if Work.FIPlan.GaussCoprime z1 z2 then
        β z1 * star (β z2) * errKer (Work.FITop4.Fhat6 Pa f) Pa.N z1 z2 else 0)‖
      ≤ (84 * Pa.θ * Real.log Pa.N * Real.sqrt Pa.M / Real.sqrt Pa.N) *
        (if Work.FIPlan.GaussCoprime z1 z2 then
          ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
        else 0) := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hc, if_pos hc]
    by_cases h1 : β z1 = 0
    · rw [h1]; simp
    by_cases h2 : β z2 = 0
    · rw [h2]; simp
    have hbox1 := Work.FITop4.IsBetaCoeff6.support hβ h1
    have hbox2 := Work.FITop4.IsBetaCoeff6.support hβ h2
    have hmaj : Work.FITop3.IsMajorant Pa f :=
      Work.FITop4.IsMajorant6.toMajorant hF
    have hFhat : ‖((Work.FITop4.Fhat6 Pa f : ℝ) : ℂ)‖ ≤ 7 * Real.sqrt Pa.M := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Fhat_nonneg Pa f hmaj)]
      exact Fhat_le Pa _ hmaj
    have hlog : ‖((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖ ≤ 12 * Real.log Pa.N := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_logFac6_le hbox1 hbox2
    have hG : ‖((Work.FITop4.G0 z1 z2 : ℝ) : ℂ)‖
        ≤ 2 * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact G0_abs_le hβ h1 h2 hc
    have hdiff : ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)
          - Pa.N ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ ≤ Pa.θ / (2 * Real.sqrt Pa.N) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
      have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
      have hq := quarter_rpow_sub_le (N := Pa.N) (θ := Pa.θ)
        (a := ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) (b := ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
        (by exact_mod_cast Pa.hN1) hθ0 hθ1 hbox1.2.1 hbox1.2.2.1 hbox2.2.1 hbox2.2.2.1
      rwa [← Nat.cast_mul, ← gnorm_mul'] at hq
    have hsplit : ‖β z1 * star (β z2) * errKer (Work.FITop4.Fhat6 Pa f) Pa.N z1 z2‖
        = ‖β z1‖ * ‖β z2‖ * ‖((Work.FITop4.Fhat6 Pa f : ℝ) : ℂ)‖
            * ‖((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖ * ‖((Work.FITop4.G0 z1 z2 : ℝ) : ℂ)‖
            * ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)
                - Pa.N ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ := by
      rw [errKer]
      simp only [norm_mul, norm_star]
      ring
    rw [hsplit]
    have hτnn : (0 : ℝ) ≤ 1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) ((Work.FIPlan.absDelta z1 z2).divisors.card)
      linarith
    have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
    have hstep : ‖β z1‖ * ‖β z2‖ * ‖((Work.FITop4.Fhat6 Pa f : ℝ) : ℂ)‖
          * ‖((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖ * ‖((Work.FITop4.G0 z1 z2 : ℝ) : ℂ)‖
          * ‖((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)
              - Pa.N ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖
        ≤ ‖β z1‖ * ‖β z2‖ * (7 * Real.sqrt Pa.M) * (12 * Real.log Pa.N)
          * (2 * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
          * (Pa.θ / (2 * Real.sqrt Pa.N)) := by
      gcongr <;>
        first
          | exact hFhat
          | exact hlog
          | exact hG
          | exact hdiff
          | positivity
          | norm_num
          | linarith [hlogN0]
    refine hstep.trans (le_of_eq ?_)
    ring
  · rw [if_neg hc, if_neg hc]
    simp

/-- **The summed §10 bound**: the difference of the two main terms of (9.11), at the corrected
kernel and the (10.4) normalisation, is bounded by `28·θ·(log N)·√M/√N` times the `τ`-weighted
pair sum of (10.6)/(10.10). -/
theorem sum_bound6 {Pa : Work.FITop.Params} {f : ℤ → ℝ} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hF : Work.FITop4.IsMajorant6 Pa f)
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          β z1 * star (β z2) * errKer (Work.FITop4.Fhat6 Pa f) Pa.N z1 z2 else 0)‖
      ≤ (84 * Pa.θ * Real.log Pa.N * Real.sqrt Pa.M / Real.sqrt Pa.N) *
        (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
          else 0)) := by
  calc ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          β z1 * star (β z2) * errKer (Work.FITop4.Fhat6 Pa f) Pa.N z1 z2 else 0)‖
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ‖∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2) * errKer (Work.FITop4.Fhat6 Pa f) Pa.N z1 z2 else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ‖(if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2) * errKer (Work.FITop4.Fhat6 Pa f) Pa.N z1 z2 else 0)‖ :=
        Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _)
    _ ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (84 * Pa.θ * Real.log Pa.N * Real.sqrt Pa.M / Real.sqrt Pa.N) *
            (if Work.FIPlan.GaussCoprime z1 z2 then
              ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
            else 0) :=
        Finset.sum_le_sum (fun z1 _ =>
          Finset.sum_le_sum (fun z2 _ => term_bound6 hF hβ z1 z2))
    _ = (84 * Pa.θ * Real.log Pa.N * Real.sqrt Pa.M / Real.sqrt Pa.N) *
        (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
          else 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z1 _ => ?_
        rw [Finset.mul_sum]

/-! ## 4. The reduction: `Area3_6` from the pair-sum input -/

/-- **Round-6 area 3 from the pair-sum input**: (10.10) at the corrected main term follows from
`PairSumWeak6` with the explicit constant `28·C`.  (`D₀ − cMain6·T(β)` is the §10 error kernel sum
(`diff_eq6`), bounded by `sum_bound6`, whose constant `84 = 7·12·2/2` combines `|f̂(0)| ≤ 7√M`,
`|log(8|z₁z₂/Δ|)| ≤ 12 log N` and `|G₀| ≤ 2(1+τ(|Δ|))`; the pair-sum input gives the
`(τ⁻¹+θ)θ³N²(log N)^{2^20−1}` of (10.10).) -/
theorem area3_6_of_pairSumWeak (h : PairSumWeak6) : Work.FITop4.Area3_6 := by
  obtain ⟨C, hC, hC'⟩ := h
  intro η hη hη32
  refine ⟨84 * C, 0, by nlinarith, ?_⟩
  intro Pa _hx _hη
  intro f φ z0 β hF hβ
  rw [diff_eq6 (Work.FITop.radN Pa) (Work.FITop4.Fhat6 Pa f) Pa.N β]
  have hbox : Work.FITop3.IsBoxCoeff Pa φ β := isBoxCoeff_of_isBetaCoeff6 hβ
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hKnn : 0 ≤ 84 * Pa.θ * Real.log Pa.N * Real.sqrt Pa.M / Real.sqrt Pa.N := by
    have h1 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
    have h2 : 0 ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
    have h3 : 0 ≤ Real.sqrt Pa.M := Real.sqrt_nonneg _
    have h4 : 0 < Real.sqrt Pa.N := Real.sqrt_pos.mpr hNpos
    positivity
  refine (sum_bound6 hF hβ).trans ?_
  refine (mul_le_mul_of_nonneg_left (hC' Pa φ β hbox) hKnn).trans ?_
  have hlogpow : (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))
      = (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ) - 1) * Real.log Pa.N := by
    rw [← pow_succ, Nat.sub_add_cancel (by norm_num : 1 ≤ (2 : ℕ) ^ (20 : ℕ))]
  have hθ : Pa.θ ^ (4 : ℕ) = Pa.θ * Pa.θ ^ (3 : ℕ) := by ring
  have hN : Pa.N ^ ((3 : ℝ) / 2) = Pa.N ^ (2 : ℕ) / Real.sqrt Pa.N :=
    (div_sqrt_eq_rpow_three_halves Pa.N hNpos).symm
  refine le_of_eq ?_
  rw [hlogpow, hθ, hN, Real.sqrt_eq_rpow Pa.M, Real.sqrt_eq_rpow Pa.N]
  ring

/-! ## 5. The degenerate case: a one-point box contributes nothing -/

/-- If the polar box has at most one point then the `‖β‖`-weighted pair sum vanishes: the only pair
with both entries in the support is then the diagonal one, and a Gaussian integer of norm `> N ≥ 1`
is not a unit, hence not coprime to itself.

(Used to dispose of `log N < 1`, where the box is a one-point window of the annulus.) -/
theorem sum_norm_eq_zero_of_supp_card_le_one {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBoxCoeff Pa φ β)
    (hcard : (polarBoxFinset Pa φ).card ≤ 1) (w : GaussianInt → GaussianInt → ℝ) :
    (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then ‖β z1‖ * ‖β z2‖ * w z1 z2 else 0)) = 0 := by
  set T := (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) with hT
  have hTsub : T ⊆ Work.FITop.boxN Pa := Finset.filter_subset _ _
  have hTpol : T ⊆ polarBoxFinset Pa φ := by
    intro z hz
    rw [hT, Finset.mem_filter] at hz
    rw [mem_polarBoxFinset]
    exact ⟨hz.1, (hβ.2 z hz.2).1⟩
  have hTcard : T.card ≤ 1 := le_trans (Finset.card_le_card hTpol) hcard
  have hinner : ∀ z1 : GaussianInt,
      (∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then ‖β z1‖ * ‖β z2‖ * w z1 z2 else 0))
        = ∑ z2 ∈ T,
          (if Work.FIPlan.GaussCoprime z1 z2 then ‖β z1‖ * ‖β z2‖ * w z1 z2 else 0) := by
    intro z1
    refine (Finset.sum_subset hTsub ?_).symm
    intro z2 hz2 hnot
    have hb : β z2 = 0 := by
      by_contra hcon
      exact hnot (by rw [hT, Finset.mem_filter]; exact ⟨hz2, hcon⟩)
    simp [hb]
  have houter : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ T,
        (if Work.FIPlan.GaussCoprime z1 z2 then ‖β z1‖ * ‖β z2‖ * w z1 z2 else 0))
      = ∑ z1 ∈ T, ∑ z2 ∈ T,
        (if Work.FIPlan.GaussCoprime z1 z2 then ‖β z1‖ * ‖β z2‖ * w z1 z2 else 0) := by
    refine (Finset.sum_subset hTsub ?_).symm
    intro z1 hz1 hnot
    have hb : β z1 = 0 := by
      by_contra hcon
      exact hnot (by rw [hT, Finset.mem_filter]; exact ⟨hz1, hcon⟩)
    rw [Finset.sum_eq_zero]
    intro z2 _
    simp [hb]
  rw [Finset.sum_congr rfl (fun z1 _ => hinner z1), houter]
  rcases Finset.eq_empty_or_nonempty T with hT0 | ⟨z0, hz0⟩
  · rw [hT0]; simp
  · have hTeq : T = {z0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hz0, fun b hb => Finset.card_le_one.mp hTcard b hb z0 hz0⟩
    rw [hTeq]
    have hz0ne : β z0 ≠ 0 := (Finset.mem_filter.mp hz0).2
    have hnotcop : ¬ Work.FIPlan.GaussCoprime z0 z0 := by
      intro hcop
      obtain ⟨x, y, hxy⟩ := hcop
      have hdvd : z0 ∣ 1 :=
        ⟨x + y, by rw [mul_add, mul_comm z0 x, mul_comm z0 y]; exact hxy.symm⟩
      obtain ⟨v, hv⟩ := hdvd
      have hgv : Work.FIPlan.gnorm (z0 * v) = Work.FIPlan.gnorm z0 * Work.FIPlan.gnorm v :=
        gnorm_mul' z0 v
      rw [← hv] at hgv
      have hgone : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by simp [Work.FIPlan.gnorm]
      rw [hgone] at hgv
      have h1 : Work.FIPlan.gnorm z0 = 1 := Nat.dvd_one.mp ⟨Work.FIPlan.gnorm v, hgv⟩
      have hbox := (hβ.2 z0 hz0ne).1
      have hgt : (1 : ℝ) < (Work.FIPlan.gnorm z0 : ℝ) :=
        lt_of_le_of_lt (by exact_mod_cast Pa.hN1) hbox.2.1
      rw [h1] at hgt
      norm_num at hgt
    rw [Finset.sum_singleton, Finset.sum_singleton]
    simp [hnotcop]

-- NOTE.  The paper-faithful strong form `Work.FIArea3.PairSumBound6` (Lemma 10.1 with the
-- sharper `(log N)^{2^19}` right-hand side) *implies* `PairSumWeak6`: for `1 ≤ log N` this is
-- `θ(log N)^{2^19} ≤ (τ⁻¹+θ)(log N)^{2^20−1}`, and for `log N < 1` the polar box is a one-point
-- window, in which the pair sum vanishes (`sum_norm_eq_zero_of_supp_card_le_one` below).  We do not
-- need it: `PairSumWeak6` is proved outright in `pairSumWeak6.lean`.

/-! ## 6. The single remaining input, and round-6 area 3 -/

/-- **THE SINGLE REMAINING INPUT OF ROUND-6 AREA 3** — *FI* Lemma 10.1 (+ (10.4)) in the weakest
form in which (10.10) consumes it, `Work.FIArea3.PairSumWeak6` (see `PairDefs6.lean`):

  `Σ_{(z₁,z₂)=1} ‖β_{z₁}‖‖β_{z₂}‖(1 + τ(|Δ(z₁,z₂)|)) ≤ C·(τ⁻¹+θ)·θ³N²·(log N)^{2^20−1}`

for every `β` supported in the polar box (5.14) with `(z,Π) = 1` (5.8) and `‖β z‖ ≤ τ(|z|²)`
(the hypothesis of Lemma 10.1).  Everything else of area 3 is proved in this file:

* `diff_eq6` — the §10 identity at the corrected kernel `G₀ = Cnt/|Δ|` and `cMain6 = f̂(0)N^{-1/2}`;
* `G0_abs_le` — `|G₀| ≤ 2(1+τ(|Δ|))` from the corrected (8.16) (`Red6.G0_eq_ratioSym_sum`);
* `abs_logFac6_le`, `isBoxCoeff_of_isBetaCoeff6`, `term_bound6`, `sum_bound6` — the §10 factor
  bounds (`|f̂(0)| ≤ 7√M`, `|log(8|z₁z₂/Δ|)| ≤ 12 log N`, the `θ/(2√N)` quarter-power saving);
* `area3_6_of_pairSumWeak` — the reduction with the explicit constant `84·C`;
* `sum_norm_eq_zero_of_supp_card_le_one`, `pairSumWeak6_of_pairSumBound6` — the degenerate
  `log N < 1` case and the implication from the paper-faithful `PairSumBound6` (Lemma 10.1 with
  `(log N)^{2^19}`), which the paper proves via (10.9) and which is *not* reachable from the
  round-3 chain `avg_box_tau_r3` + `JointBound` (that chain gives `CoreBound`, whose factor
  `(ϑ+θ)` is always at least `(log x)^{124}/2` times the `(τ⁻¹+θ)` needed here).

**Status.**  The input is now *proved* (by the same fleet) in
`Submission/Work/FIArea3/pairSumWeak6.lean` as `Work.FIArea3.pairSumWeak6`; the theorem below is
that result, and `area3_6` is its one-line consequence.  The route is the paper's Lemma 10.1 with
the fleet's joint lattice counts (`Work.FIArea3.JointCount.card_filter_le_le_arith`,
`polarBox_lattice_count_sharp`), FI's Lemma 2.2 (`Work.FIArea3.lemma_2_2`) and a three-regime
splitting `u = θ√N ≶ N^{1/4}, N^{3/8}`. -/
theorem fi_pairSumWeak6 : PairSumWeak6 :=
  Work.FIArea3.pairSumWeak6

/-- **Friedlander–Iwaniec §10 (10.10)** at the *corrected* main term (round 6 of the contract
`Work.FITop4.Area3_6`): for every admissible datum, every `C⁴` majorant `F` and every coefficient
`β` of (4.13)+(5.13)+(5.7),

  `‖D₀(M,N) − f̂(0)N^{-1/2}T(β)‖ ≤ C₃(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`,

where `D₀` and `T(β)` carry the count kernel `G₀ = Cnt/|Δ|` of (6.12) and `f̂(0) = Fhat Pa f`
is the paper's (7.7) mean value. -/
theorem area3_6 : Work.FITop4.Area3_6 :=
  area3_6_of_pairSumWeak fi_pairSumWeak6

end

end Work.FIArea3
