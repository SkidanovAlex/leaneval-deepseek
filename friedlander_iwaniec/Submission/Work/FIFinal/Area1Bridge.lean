/-
# `Submission.Work.FITop4.Bridge.area1Sieve6` — the round-6 bridge for `Area1Sieve6`

`Work.FITop4.Area1Sieve6` is the round-4 §5 statement *(5.10)+(5.22)* at the round-6 hypotheses:
the coefficient is `Defs6.IsBetaCoeff6` — round 4's `IsBetaCoeff` of (4.13)+(5.13) with the (5.7)
restriction `SameClass8 z z0` added to the support `if` — and the majorant is `Defs6.IsMajorant6`,
which carries `IsMajorant Pa (seqOf F)` as its last conjunct.

**Route.**  The proof of `Submission/Work/FIArea1/area1s_r4.lean` is ported verbatim to these
hypotheses.  The round-4 file could not be re-used directly (`Areas4` and the round-3 shim copies
cannot share an environment), but `Defs6` is built on `Work.FIArea2.G0_defect` rather than on
`G0_fix`, so `Areas6` and the `FIArea1.shim.*` copies elaborate together and the *proof* can be
copied.  What is genuinely re-done:

* `IsBetaCoeff6.toBoxCoeff` (declared below in namespace `Work.FITop4`): the size bound
  `‖β z‖ ≤ τ(|z|²)`, ported from `Work.FITop4.IsBetaCoeff.toBoxCoeff` with the mollifier bounds
  `q ≤ 1`, `p ≤ 1`, `norm_moebius_le_one`, `abs_gammaTrunc_le`;
* the support data `IsBetaCoeff6.{support, noSmallPrimes, squarefree_gnorm}` (the round-4 code
  destructured the shape clause by hand; here the `Defs6` API is used);
* the realness of `β` (the shape clause with the extra `SameClass8` conjunct);
* the majorant is transferred by `IsMajorant6.toMajorant : IsMajorant Pa (seqOf F)`.

All other lemmas (`count_annulus`, `count_line_squares`, `offdiag_polar_count`, the arithmetic of
`Dform - Dstar`, …) are β-independent and are imported from the round-3 shims unchanged.  The
copied lemmas live in `Work.FIArea1` under `…_r6` names; the threshold of `Area1Sieve6` is taken
to be `x₀ = 0`.
-/

import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea1.conjunct1_le
import Submission.Work.FIArea1.conjunct2_le
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.Helpers
import Submission.Work.FIArea1.count_line_squares
import Submission.Work.FIArea1.offdiag_polar_count


namespace Work.FITop4

/-- **The size bound of `IsBetaCoeff6`**: a round-6 coefficient is a special case of the
support-and-size predicate `IsBoxCoeff` of §§10–17.  Ported from
`Work.FITop4.IsBetaCoeff.toBoxCoeff` with the (4.13)/(5.13) mollifier bounds `0 ≤ q, p ≤ 1`,
`‖μ‖ ≤ 1` and `|γ(n;C)| ≤ τ(n)`. -/
theorem IsBetaCoeff6.toBoxCoeff {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) : IsBoxCoeff Pa φ β := by
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
      have hmu := norm_moebius_le_one (Work.FIPlan.gnorm z)
      have hg : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_gammaTrunc_le _ _
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
    rw [hβ z] at hz
    have hcond : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
        ∧ IsAxisFree Pa z := by
      by_contra hc
      rw [if_neg hc] at hz
      exact hz rfl
    exact ⟨hcond.1, hcond.2.1⟩

end Work.FITop4

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 0. The interface of the round-4 coefficient -/

/-- The support structure of the round-6 coefficient: `β z ≠ 0` forces a squarefree norm, the
polar box (5.14) and freedom of primes `≤ P` (5.8). -/
lemma beta_ne_zero_structure_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    Squarefree (Work.FIPlan.gnorm z) ∧ Work.FITop3.InPolarBox Pa φ z ∧
      Work.FITop3.NoSmallPrimes Pa z :=
  ⟨h.squarefree_gnorm hz, h.support hz, h.noSmallPrimes hz⟩

/-- `‖β z‖ ≤ τ(|z|²)` for the round-6 coefficient, from `IsBetaCoeff6.toBoxCoeff`. -/
lemma norm_beta_le_divisors_card_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) :=
  h.toBoxCoeff.1 z

/-- The round-6 coefficient is real-valued. -/
lemma exists_real_of_IsBetaCoeff_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ∃ b : GaussianInt → ℝ, ∀ z, β z = (b z : ℂ) := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβz⟩ := hβ
  refine ⟨fun z => if Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
      ∧ Work.FITop4.IsAxisFree Pa z
    then (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z))
      * ((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℤ) : ℝ)
      * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)) else 0, fun z => ?_⟩
  by_cases h : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
      ∧ Work.FITop4.IsAxisFree Pa z
  · rw [hβz z]
    simp only []
    rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [hβz z]
    simp only []
    rw [if_neg h, if_neg h]
    simp

/-- The full support structure of the round-6 coefficient (cf. `Work.FIArea1.beta_structure`). -/
lemma beta_structure_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z) ∧
      Work.FITop3.NoSmallPrimes Pa z ∧ ‖β z‖ ≤ Pa.τ ∧
      (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
  have hcoeff := hβ
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβz⟩ := hβ
  have hcond : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
      Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z := by
    by_contra hc
    rw [hβz z, if_neg hc] at hz
    exact hz rfl
  have hsq := (beta_ne_zero_structure_r6 hcoeff hz).1
  refine ⟨hcond.1, hsq, hcond.2.1, ?_, ?_⟩
  · exact le_trans (norm_beta_le_divisors_card_r6 hcoeff z) hcond.2.2.1
  · obtain ⟨-, h1, h2, -⟩ := hcond.1
    have hθ1 := c2_theta_le_one Pa
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    nlinarith

/-! ## 1. The non-coprime count (round 4) -/

/-- Round-4 `Work.FIArea1.noncoprime_count`: identical proof, `beta_ne_zero_structure_r6`. -/
theorem noncoprime_count_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
      ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
  obtain ⟨hsq, hbox, hnsp⟩ := beta_ne_zero_structure_r6 hβ hz
  have hzhi : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := gnorm_le_two_mul_N hbox
  have hzlo : (Pa.N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := hbox.2.1
  set A : ℝ := (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) with hA
  set B : ℝ := Real.sqrt Pa.M / Real.sqrt Pa.N with hB
  have hMN0 : (0 : ℝ) ≤ Pa.M * Pa.N := by nlinarith [Pa.hM1, Pa.hN1]
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hMN0 _
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set n : ℕ := Work.FIPlan.gnorm z with hn
  have hnpos : 0 < n := by
    have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
    have : (0 : ℝ) < (n : ℝ) := by linarith [hzlo, hN1]
    exact_mod_cast this
  have hsub : (Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)
      ⊆ n.primeFactors.biUnion (fun p => (Work.FITop3.annM Pa).filter
          (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwann, hnc, c, hc⟩ := hw
    obtain ⟨p, hpp, hpw, hpz⟩ := common_prime_of_not_coprime hnc
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]; exact ⟨hpp, by rw [hn]; exact hpz, ne_of_gt hnpos⟩
    · rw [Finset.mem_filter]; exact ⟨hwann, hpw, c, hc⟩
  have hper : ∀ p ∈ n.primeFactors,
      (((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
        ≤ 200 * A * (1 + B / (p : ℝ)) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have hlt : Pa.Pz < p := by
      by_contra hle
      exact hnsp p hpp (le_of_not_gt hle) (by rw [← hn]; exact hpd)
    have hp2 : 2 < p := by have := Pa.hP2; omega
    have hmain := count_annulus (Pa := Pa) (z := z) (p := p) hpp hp2 hzlo hzhi hsq
      (by rw [← hn]; exact hpd)
    have heq : 200 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((p : ℝ) * Real.sqrt Pa.N)) = 200 * A * (1 + B / (p : ℝ)) := by
      rw [hA, hB]
      rw [show Real.sqrt Pa.M / ((p : ℝ) * Real.sqrt Pa.N)
            = (Real.sqrt Pa.M / Real.sqrt Pa.N) / (p : ℝ) by ring]
    rwa [heq] at hmain
  calc (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
      ≤ ((n.primeFactors.biUnion (fun p => (Work.FITop3.annM Pa).filter
          (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ p ∈ n.primeFactors, ((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ p ∈ n.primeFactors, (((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ) := by push_cast; ring
    _ ≤ ∑ p ∈ n.primeFactors, 200 * A * (1 + B / (p : ℝ)) := Finset.sum_le_sum hper
    _ = 200 * A * ∑ p ∈ n.primeFactors, (1 + B / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 200 * A * ((n.primeFactors.card : ℝ) * (1 + B / (Pa.Pz : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hPz0 : (0 : ℝ) < (Pa.Pz : ℝ) := by
          have := Pa.hP2; positivity
        calc ∑ p ∈ n.primeFactors, (1 + B / (p : ℝ))
            ≤ ∑ _p ∈ n.primeFactors, (1 + B / (Pa.Pz : ℝ)) := by
              apply Finset.sum_le_sum
              intro p hp
              obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
              have hlt : Pa.Pz < p := by
                by_contra hle
                exact hnsp p hpp (le_of_not_gt hle) (by rw [← hn]; exact hpd)
              have hle : (Pa.Pz : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlt.le
              have : B / (p : ℝ) ≤ B / (Pa.Pz : ℝ) :=
                div_le_div_of_nonneg_left hB0 hPz0 hle
              linarith
          _ = (n.primeFactors.card : ℝ) * (1 + B / (Pa.Pz : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ = 200 * (A * ((n.primeFactors.card : ℕ) : ℝ) * (1 + B / (Pa.Pz : ℝ))) := by ring
    _ ≤ 400 * (A * ((n.primeFactors.card : ℕ) : ℝ) * (1 + B / (Pa.Pz : ℝ))) :=
        mul_le_mul_of_nonneg_right (by norm_num : (200 : ℝ) ≤ 400)
          (mul_nonneg (mul_nonneg hA0 (by positivity)) (by positivity))
    _ = 400 * A * (1 + B / (Pa.Pz : ℝ)) * ((n.primeFactors.card : ℕ) : ℝ) := by ring
    _ = 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
        rw [hA, hB, hn]
        rw [show Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)
              = (Real.sqrt Pa.M / Real.sqrt Pa.N) / (Pa.Pz : ℝ) by ring]

/-- Round-4 `Work.FIArea1.conjunct1_count`. -/
theorem conjunct1_count_r6 :
    ∀ (Pa : Work.FITop.Params) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ z : GaussianInt, β z ≠ 0 →
      (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
        ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
            * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
  intro Pa z0 φ β hβ z hz
  exact noncoprime_count_r6 hβ hz

/-! ## 2. The size of the support of the round-4 coefficient -/

/-- Membership in the box `gBox R`: the coordinate box. -/
lemma r6_mem_gBox_iff {R : ℤ} {w : GaussianInt} :
    w ∈ Work.FIPlan.gBox R ↔ w.re ∈ Finset.Icc (-R) R ∧ w.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(w.re, w.im), Finset.mem_product.mpr ⟨h1, h2⟩, by
      exact Zsqrtd.ext (by simp) (by simp)⟩

/-- The box `gBox R` has at most `(2R+1)²` elements (`R ≥ 0`). -/
lemma r6_card_gBox_le (R : ℤ) (hR : 0 ≤ R) :
    (Work.FIPlan.gBox R).card ≤ (2 * R.natAbs + 1) ^ 2 := by
  rw [Work.FIPlan.gBox]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.product_eq_sprod, Finset.card_product]
  have h : (Finset.Icc (-R) R).card = 2 * R.natAbs + 1 := by
    rw [Int.card_Icc]
    omega
  rw [h, sq]

/-- Round-4 `Work.FIArea1.card_beta_support_le`: the support of `β` in `boxN` has `≤ 25N`
elements. -/
theorem card_beta_support_le_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ) ≤ 25 * Pa.N := by
  classical
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  set R : ℕ := ⌊Real.sqrt (2 * Pa.N)⌋₊ with hRdef
  have hsub : (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) ⊆ Work.FIPlan.gBox (R : ℤ) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hzβ⟩ := hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := (beta_ne_zero_structure_r6 hβ hzβ).2.1
    obtain ⟨-, -, hNle, -⟩ := hbox
    have hgnorm_le : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by nlinarith
    have hgnormR : (Work.FIPlan.gnorm z : ℝ)
        = (z.re.natAbs : ℝ) ^ 2 + (z.im.natAbs : ℝ) ^ 2 := by
      rw [Work.FIArea1.gnorm_coords]; push_cast; ring
    have hre_sq : (z.re.natAbs : ℝ) ^ 2 ≤ 2 * Pa.N := by
      nlinarith [sq_nonneg (z.im.natAbs : ℝ)]
    have him_sq : (z.im.natAbs : ℝ) ^ 2 ≤ 2 * Pa.N := by
      nlinarith [sq_nonneg (z.re.natAbs : ℝ)]
    have hre_floor : z.re.natAbs ≤ R := by
      rw [hRdef]
      exact Nat.le_floor ((Real.le_sqrt (by positivity) (by positivity)).mpr hre_sq)
    have him_floor : z.im.natAbs ≤ R := by
      rw [hRdef]
      exact Nat.le_floor ((Real.le_sqrt (by positivity) (by positivity)).mpr him_sq)
    have hreZ : (z.re.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hre_floor
    have himZ : (z.im.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast him_floor
    rw [r6_mem_gBox_iff]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · have h2 : -z.re ≤ ((-z.re).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h2
      linarith
    · have h2 : z.re ≤ (z.re.natAbs : ℤ) := Int.le_natAbs
      linarith
    · have h2 : -z.im ≤ ((-z.im).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h2
      linarith
    · have h2 : z.im ≤ (z.im.natAbs : ℤ) := Int.le_natAbs
      linarith
  have hcard : ((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card ≤ (2 * R + 1) ^ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    have h := r6_card_gBox_le (R : ℤ) (by positivity)
    rwa [show ((R : ℤ).natAbs) = R from Int.natAbs_natCast R] at h
  have hsq_bound : (((2 * R + 1) ^ 2 : ℕ) : ℝ) ≤ 25 * Pa.N := by
    have hcast : (((2 * R + 1) ^ 2 : ℕ) : ℝ) = (2 * (R : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [hcast]
    have hRle : (R : ℝ) ≤ Real.sqrt (2 * Pa.N) := by
      rw [hRdef]; exact Nat.floor_le (by positivity)
    have hle : 2 * (R : ℝ) + 1 ≤ 5 * Real.sqrt Pa.N := by
      have h2 : 2 * (R : ℝ) ≤ 2 * Real.sqrt (2 * Pa.N) := by linarith
      have h3 : 2 * Real.sqrt (2 * Pa.N) + 1 ≤ 5 * Real.sqrt Pa.N := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Pa.N]
        have hsN1 : (1 : ℝ) ≤ Real.sqrt Pa.N := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
        have hsqrt2 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        nlinarith [hsN1, hsqrt2, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg Pa.N]
      linarith
    have hnn : (0 : ℝ) ≤ 2 * (R : ℝ) + 1 := by positivity
    calc (2 * (R : ℝ) + 1) ^ 2 ≤ (5 * Real.sqrt Pa.N) ^ 2 := pow_le_pow_left₀ hnn hle 2
      _ = 25 * Pa.N := by rw [mul_pow, Real.sq_sqrt hN0]; norm_num
  calc (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ)
      ≤ (((2 * R + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 25 * Pa.N := hsq_bound

/-! ## 3. The diagonal half of (5.22) (round 4) -/

/-- `(b²·t²).re ≤ ‖b‖²t²` for a real `t ≥ 0`. -/
private lemma r6_re_sq_mul_le (b : ℂ) (n : ℕ) :
    (b ^ 2 * (((n : ℕ) : ℂ)) ^ 2).re ≤ ‖b‖ ^ 2 * (n : ℝ) ^ 2 := by
  have h1 : (b ^ 2).re = b.re ^ 2 - b.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hnorm : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : (((n : ℕ) : ℂ)) ^ 2 = (((n ^ 2 : ℕ)) : ℂ) := by push_cast; ring
  have hL : (b ^ 2 * (((n : ℕ) : ℂ)) ^ 2).re = (b ^ 2).re * (n : ℝ) ^ 2 := by
    rw [Complex.mul_re, h2, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    push_cast; ring
  rw [hL, h1, hnorm]
  have : b.re ^ 2 - b.im ^ 2 ≤ b.re ^ 2 + b.im ^ 2 := by nlinarith [sq_nonneg b.im]
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- `(Σ_z β_z²Z(wz)²).re ≤ Σ_z ‖β_z‖²‖Z(wz)‖²`. -/
private lemma r6_inner_re_le (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (w : GaussianInt) :
    (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re
      ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * ‖Work.FITop3.Zc w z‖ ^ 2 := by
  rw [Complex.re_sum]
  refine Finset.sum_le_sum (fun z _ => ?_)
  have h := r6_re_sq_mul_le (β z) (Work.FIPlan.Zint (Work.FIPlan.cForm w z))
  simpa only [Work.FITop3.Zc, Complex.norm_natCast] using h

/-- Exchange the two sums in the diagonal and use `f ≥ 0`. -/
private lemma r6_diag_swap (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ)
    (hf0 : ∀ u, 0 ≤ f u) :
    (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
        (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
      ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 *
        (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2) := by
  calc (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
        (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
      ≤ ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
          (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * ‖Work.FITop3.Zc w z‖ ^ 2) :=
        Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (r6_inner_re_le Pa β w) (hf0 _))
    _ = ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 *
          (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2) := by
        rw [show (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
              (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 * ‖Work.FITop3.Zc w z‖ ^ 2))
            = ∑ w ∈ Work.FITop.boxM Pa, ∑ z ∈ Work.FITop.boxN Pa,
                f (Work.FIPlan.gnorm w) * (‖β z‖ ^ 2 * ‖Work.FITop3.Zc w z‖ ^ 2) from
          Finset.sum_congr rfl (fun w _ => Finset.mul_sum _ _ _)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        ring

/-- The data supplied by the round-6 coefficient at a point where `β z ≠ 0`. -/
private lemma r6_beta_props {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    (Pa.N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧
      (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ ∧
      ‖β z‖ ≤ Pa.τ := by
  have hcoeff := h
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  have hcond : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
      Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z := by
    by_contra hc
    rw [hβ z, if_neg hc] at hz
    exact hz rfl
  obtain ⟨-, h1, h2, -⟩ := hcond.1
  refine ⟨h1, ?_, hcond.2.2.1, ?_⟩
  · have hθ1 := theta_le_one Pa
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    nlinarith [h2, hθ1, hN0]
  · exact le_trans (norm_beta_le_divisors_card_r6 hcoeff z) hcond.2.2.1

/-- The per-`z` bound `Σ_w f(|w|²)Z(wz)² ≤ 1200 (MN)^{1/4}(1+√M/√N)`. -/
private lemma r6_per_z_le {Pa : Work.FITop.Params} {f : ℤ → ℝ} {z : GaussianInt}
    (hf : Work.FITop3.IsMajorant Pa f)
    (hcount : ((((Work.FITop.boxM Pa).filter
        (fun w => ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ))
      ≤ 300 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt Pa.M / Real.sqrt Pa.N)) :
    (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
      ≤ 1200 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt Pa.M / Real.sqrt Pa.N)) := by
  set C : ℝ := (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt Pa.M / Real.sqrt Pa.N) with hC
  have hcount' : ((((Work.FITop.boxM Pa).filter
        (fun w => ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)) ≤ 300 * C := by
    rw [hC]
    calc ((((Work.FITop.boxM Pa).filter
          (fun w => ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ))
        ≤ 300 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt Pa.M / Real.sqrt Pa.N) := hcount
      _ = 300 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt Pa.M / Real.sqrt Pa.N)) :=
          by ring
  have hstep1 : (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
      = ∑ w ∈ (Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0),
          f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : Work.FITop3.Zc w z ≠ 0
    · rw [if_pos h]
    · rw [if_neg h]
      have h0 : Work.FITop3.Zc w z = 0 := not_ne_iff.mp h
      rw [h0]; simp
  have hstep2 : (∑ w ∈ (Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0),
        f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
      ≤ 4 * ((((Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0)).card : ℝ)) := by
    have hpt : ∀ w ∈ (Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0),
        f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2 ≤ 4 := by
      intro w _
      have h1 : f (Work.FIPlan.gnorm w) ≤ 1 := hf.2.1 _
      have h2 : ‖Work.FITop3.Zc w z‖ ^ 2 ≤ 4 := by
        have := Work.FIArea1.Zc_norm_le_two w z
        nlinarith [norm_nonneg (Work.FITop3.Zc w z)]
      calc f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2
          ≤ 1 * ‖Work.FITop3.Zc w z‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = ‖Work.FITop3.Zc w z‖ ^ 2 := one_mul _
        _ ≤ 4 := h2
    calc (∑ w ∈ (Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0),
            f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
        ≤ ∑ _w ∈ (Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0), (4 : ℝ) :=
          Finset.sum_le_sum hpt
      _ = 4 * ((((Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0)).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hstep3 : ((((Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0)).card : ℝ))
      ≤ ((((Work.FITop.boxM Pa).filter
          (fun w => ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)) := by
    have hsub : (Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0)
        ⊆ (Work.FITop.boxM Pa).filter (fun w => ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2) := by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, Work.FIArea1.Zc_ne_zero_imp_sq w z hw.2⟩
    exact_mod_cast Finset.card_le_card hsub
  calc (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
      = _ := hstep1
    _ ≤ 4 * ((((Work.FITop.boxM Pa).filter (fun w => Work.FITop3.Zc w z ≠ 0)).card : ℝ)) :=
        hstep2
    _ ≤ 4 * (300 * C) := by linarith [hstep3, hcount']
    _ = 1200 * C := by ring

/-- The closing arithmetic: `N(MN)^{1/4}(1 + √M/√N) ≤ 2M^{3/4}N^{3/4}` for `1 ≤ N ≤ M`. -/
private lemma r6_arith_diag {M N : ℝ} (hM1 : 1 ≤ M) (hN1 : 1 ≤ N) (hMN : N ≤ M) :
    N * ((M * N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt M / Real.sqrt N))
      ≤ 2 * (M ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN0 : 0 < M * N := mul_pos hM0 hN0
  set P : ℝ := (M * N) ^ ((1 : ℝ) / 4) with hP
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hMN0.le _
  have hsMN : (M * N) ^ ((1 : ℝ) / 2) = Real.sqrt (M * N) := (Real.sqrt_eq_rpow (M * N)).symm
  have hpow : P * (M * N) ^ ((1 : ℝ) / 2) = M ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4) := by
    rw [hP, ← Real.rpow_add hMN0, show ((1 : ℝ) / 4 + 1 / 2) = 3 / 4 by norm_num,
      Real.mul_rpow hM0.le hN0.le]
  have hNle : N ≤ (M * N) ^ ((1 : ℝ) / 2) := by
    rw [hsMN, Real.le_sqrt hN0.le hMN0.le]
    nlinarith
  have h1 : N * P ≤ P * (M * N) ^ ((1 : ℝ) / 2) := by
    calc N * P = P * N := by ring
      _ ≤ P * (M * N) ^ ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hNle hP0
  have hs : N * (Real.sqrt M / Real.sqrt N) = (M * N) ^ ((1 : ℝ) / 2) := by
    have hsN : N / Real.sqrt N = Real.sqrt N := by
      rw [div_eq_iff (by positivity)]
      nlinarith [Real.sq_sqrt hN0.le]
    have hstep : N * (Real.sqrt M / Real.sqrt N) = (N / Real.sqrt N) * Real.sqrt M := by ring
    rw [hstep, hsN, mul_comm, ← Real.sqrt_mul hM0.le N, hsMN]
  have h2 : N * P * (Real.sqrt M / Real.sqrt N) ≤ P * (M * N) ^ ((1 : ℝ) / 2) := by
    rw [show N * P * (Real.sqrt M / Real.sqrt N)
          = P * (N * (Real.sqrt M / Real.sqrt N)) by ring, hs]
  calc N * (P * (1 + Real.sqrt M / Real.sqrt N))
      = N * P + N * P * (Real.sqrt M / Real.sqrt N) := by ring
    _ ≤ P * (M * N) ^ ((1 : ℝ) / 2) + P * (M * N) ^ ((1 : ℝ) / 2) := add_le_add h1 h2
    _ = 2 * (M ^ ((3 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) := by rw [hpow]; ring

/-- Round-4 `Work.FIArea1.diagonal_le`: the diagonal half of (5.22). -/
theorem diagonal_le_r6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsMajorant Pa f → Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
          (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
        ≤ c * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
          * (1 + Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  refine ⟨60000, by norm_num, ?_⟩
  intro Pa f z0 φ β hf hβ
  set C : ℝ := (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) * (1 + Real.sqrt Pa.M / Real.sqrt Pa.N) with hC
  have hD0 : 0 ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [Pa.hM1]) _)
      (Real.rpow_nonneg (by linarith [Pa.hN1]) _)
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (Real.rpow_nonneg (by nlinarith [Pa.hM1, Pa.hN1]) _)
      (add_nonneg zero_le_one (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hper : ∀ z ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
      ‖β z‖ ^ 2 * (∑ w ∈ Work.FITop.boxM Pa,
          f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2) ≤ Pa.τ ^ 2 * (1200 * C) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hzβ⟩ := hz
    obtain ⟨hzlo, hzhi, -, hτβ⟩ := r6_beta_props hβ hzβ
    have hsq := (beta_ne_zero_structure_r6 hβ hzβ).1
    have hB : (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
        ≤ 1200 * C := by
      have := r6_per_z_le hf (count_line_squares hzlo hzhi hsq)
      rwa [← hC] at this
    have hb2 : ‖β z‖ ^ 2 ≤ Pa.τ ^ 2 := by
      nlinarith [norm_nonneg (β z), hτβ]
    have hB0 : (0 : ℝ) ≤ ∑ w ∈ Work.FITop.boxM Pa,
        f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2 :=
      Finset.sum_nonneg (fun w _ => mul_nonneg (hf.1 _) (sq_nonneg _))
    calc ‖β z‖ ^ 2 * (∑ w ∈ Work.FITop.boxM Pa,
            f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2)
        ≤ Pa.τ ^ 2 * (∑ w ∈ Work.FITop.boxM Pa,
            f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hb2 hB0
      _ ≤ Pa.τ ^ 2 * (1200 * C) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  calc (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
        (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
      ≤ ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 *
          (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2) :=
        r6_diag_swap Pa f β hf.1
    _ = ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ‖β z‖ ^ 2 *
          (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖Work.FITop3.Zc w z‖ ^ 2) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases h : β z ≠ 0
        · rw [if_pos h]
        · rw [if_neg h]
          have h0 : β z = 0 := not_ne_iff.mp h
          rw [h0]; simp
    _ ≤ ∑ _z ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), (Pa.τ ^ 2 * (1200 * C)) :=
        Finset.sum_le_sum hper
    _ = (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ) * (Pa.τ ^ 2 * (1200 * C)) :=
        by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (25 * Pa.N) * (Pa.τ ^ 2 * (1200 * C)) :=
        mul_le_mul_of_nonneg_right (card_beta_support_le_r6 hβ)
          (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hC0))
    _ = 30000 * Pa.τ ^ 2 * (Pa.N * C) := by ring
    _ ≤ 30000 * Pa.τ ^ 2 * (2 * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))) := by
        rw [hC]
        exact mul_le_mul_of_nonneg_left (r6_arith_diag Pa.hM1 Pa.hN1 Pa.hMge)
          (by positivity)
    _ = 60000 * Pa.τ ^ 2 * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)) := by ring
    _ ≤ 60000 * Pa.τ ^ 2 * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
          * (1 + Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
        have hL1 : (1 : ℝ) ≤ (1 + Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
          apply one_le_pow₀
          have h : (0 : ℝ) ≤ Real.log (Pa.M * Pa.N) :=
            Real.log_nonneg (by nlinarith [Pa.hM1, Pa.hN1])
          linarith
        have hfac : (0 : ℝ) ≤ 60000 * Pa.τ ^ 2 *
            (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)) := by
          have := sq_nonneg Pa.τ
          nlinarith [hD0]
        have := mul_le_mul_of_nonneg_left hL1 hfac
        simpa using this

/-! ## 4. The first conjunct of (5.10) (round 4) -/

/-- Round-4 `Work.FIArea1.conj1_diff_le` (its `IsBetaCoeff` argument is unused). -/
lemma conj1_diff_le_r6 (Pa : Work.FITop.Params) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ)
    (hcount : ∀ z : GaussianInt, β z ≠ 0 →
      (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
        ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
            * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
    (_hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ‖Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β‖
      ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
        * ∑ z ∈ Work.FITop.boxN Pa,
            (if β z ≠ 0 then
              ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := by
  refine (conj1_norm_le Pa β).trans ?_
  have hpt : ∀ z ∈ Work.FITop.boxN Pa,
      (2 * ‖β z‖) * (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ)
      ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * (if β z ≠ 0 then
              ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := by
    intro z _hz
    have hsub : ((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0))
        ⊆ ((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)) := by
      intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, hw.2.1, Zc_ne_zero_imp_sq w z hw.2.2⟩
    have hcard : ((((Work.FITop3.annM Pa).filter
            (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
              Work.FITop3.Zc w z ≠ 0)).card : ℝ))
        ≤ ((((Work.FITop3.annM Pa).filter
            (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
              ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsub
    by_cases hz0 : β z = 0
    · simp [hz0]
    · have hnc := hcount z hz0
      rw [if_pos hz0]
      calc (2 * ‖β z‖) * ((((Work.FITop3.annM Pa).filter
              (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ))
          ≤ (2 * ‖β z‖) * (400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
              * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
              * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hcard.trans hnc
        _ = 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
                * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
              * (‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)) := by ring
  calc ∑ z ∈ Work.FITop.boxN Pa, (2 * ‖β z‖) * (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧ Work.FITop3.Zc w z ≠ 0)).card : ℝ)
      ≤ ∑ z ∈ Work.FITop.boxN Pa, 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * (if β z ≠ 0 then
              ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * ∑ z ∈ Work.FITop.boxN Pa,
              (if β z ≠ 0 then
                ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]

/-- Round-4 `Work.FIArea1.conj1_beta_eq_zero_of_small_N`. -/
lemma conj1_beta_eq_zero_of_small_N_r6 (Pa : Work.FITop.Params) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hN : Pa.N ≤ 4 / 3) : ∀ z, β z = 0 := by
  intro z
  by_contra hz
  obtain ⟨-, hbox, hns⟩ := beta_ne_zero_structure_r6 hβ hz
  obtain ⟨-, hNlt, hNle, -, -⟩ := hbox
  have hn2 : 2 ≤ Work.FIPlan.gnorm z := by
    have h1 : (1 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith [Pa.hN1]
    have : (1 : ℕ) < Work.FIPlan.gnorm z := by exact_mod_cast h1
    omega
  have hnle : Work.FIPlan.gnorm z ≤ 2 := by
    have hθ1 := conj1_theta_le_one Pa
    have h2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
      have h3 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [Pa.hN1]
      linarith [hNle, h3]
    have h3 : (Work.FIPlan.gnorm z : ℝ) < 3 := by nlinarith [hN, h2]
    have : Work.FIPlan.gnorm z < 3 := by exact_mod_cast h3
    omega
  have hn : Work.FIPlan.gnorm z = 2 := le_antisymm hnle hn2
  have hcontra := hns 2 Nat.prime_two Pa.hP2
  rw [hn] at hcontra
  exact hcontra dvd_rfl

/-- Round-4 `Work.FIArea1.conj1_sum_bound_aux`. -/
lemma conj1_sum_bound_aux_r6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ),
      (4 / 3 : ℝ) < Pa.N → Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∑ z ∈ Work.FITop.boxN Pa,
          (if β z ≠ 0 then
            ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0))
        ≤ C * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := conj1_divisor_sum
  refine ⟨2000000 * C₀, by positivity, ?_⟩
  intro Pa z0 φ β hN hβ
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := by linarith
  have hlogN : (1/4 : ℝ) ≤ Real.log Pa.N := conj1_log_ge_quarter hN
  have hlogN0 : (0:ℝ) ≤ Real.log Pa.N := by linarith
  rw [Work.FITop.boxN, Work.FITop.radN]
  set R : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊ with hRdef
  have hRle : ((R:ℝ)) ≤ 4 * Real.sqrt Pa.N := by
    have h := conj1_radN_le Pa
    simpa [hRdef] using h
  have hτ := hC₀ (R : ℤ) (Int.natCast_nonneg R)
  have hτR : (∑ z ∈ Work.FIPlan.gBox (R : ℤ),
        (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2) := by
    have := hτ
    simpa [Int.natAbs_natCast] using this
  have hgnorm : ∀ z ∈ Work.FIPlan.gBox (R : ℤ), Work.FIPlan.gnorm z ≤ 2 * R ^ 2 := by
    intro z hz
    have hcast : ((2 * R ^ 2 : ℕ) : ℝ) = 2 * (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) ^ 2 := by
      rw [hRdef]; push_cast; ring
    have hle : (Work.FIPlan.gnorm z : ℝ) ≤ ((2 * R ^ 2 : ℕ) : ℝ) := by
      rw [hcast]
      exact conj1_gnorm_le_boxN hz
    exact_mod_cast hle
  have hpt : ∀ z ∈ Work.FIPlan.gBox (R : ℤ),
      (if β z ≠ 0 then ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0)
        ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
    intro z hz
    by_cases hz0 : β z = 0
    · simp only [hz0, ne_eq, not_true_eq_false, reduceIte]
      positivity
    · rw [if_pos hz0]
      have hnorm := norm_beta_le_divisors_card_r6 hβ z
      have homega : (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)
          ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) := by
        obtain ⟨-, hbox, -⟩ := beta_ne_zero_structure_r6 hβ hz0
        have h1 : 1 ≤ Work.FIPlan.gnorm z := by
          have h2 : (1:ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by
            have h3 := hbox.2.1
            linarith
          exact_mod_cast h2
        exact_mod_cast card_primeFactors_le_log_of_le h1 (hgnorm z hz)
      calc ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)
          ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hnorm (by positivity)
        _ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left homega (by positivity)
        _ = ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
  have hL0 : (0:ℝ) ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) := by positivity
  have hmain : (∑ z ∈ Work.FIPlan.gBox (R : ℤ),
        (if β z ≠ 0 then ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0))
      ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
          * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2)) := by
    calc _ ≤ ∑ z ∈ Work.FIPlan.gBox (R : ℤ),
            ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Finset.sum_le_sum hpt
      _ = ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
            * ∑ z ∈ Work.FIPlan.gBox (R : ℤ),
                (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
            * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hτR hL0
  have hsqN : (Real.sqrt Pa.N)^2 = Pa.N := Real.sq_sqrt (by linarith)
  have hA2 : ((R:ℝ)) ^ 2 ≤ 16 * Pa.N := by
    nlinarith [hRle, hsqN, Real.sqrt_nonneg Pa.N]
  have hR17 : ((R:ℝ) ^ 2 + 1) ≤ 17 * Pa.N := by nlinarith [hA2, hN1]
  have hlogR : Real.log ((R:ℝ) + 2) ≤ 21 * Real.log Pa.N := by
    have hsle : Real.sqrt Pa.N ≤ Pa.N := by
      have h1 : Pa.N ≤ Pa.N * Pa.N := by nlinarith [hN1]
      calc Real.sqrt Pa.N ≤ Real.sqrt (Pa.N * Pa.N) := Real.sqrt_le_sqrt h1
        _ = Pa.N := Real.sqrt_mul_self (by linarith)
    have h6N : (R:ℝ) + 2 ≤ 6 * Pa.N := by nlinarith [hRle, hsle]
    have h0 : 0 < (R:ℝ) + 2 := by positivity
    refine (Real.log_le_log h0 h6N).trans ?_
    have h6 := conj1_log_mul_le (c := 6) (N := Pa.N) (by norm_num) hN
    rwa [show (4 * ((6:ℝ) - 1) + 1) = 21 by norm_num] at h6
  have hL' : ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ) ≤ 250 * Real.log Pa.N := by
    have hm : 1 ≤ 2 * R ^ 2 := by
      have : 1 ≤ R := by
        have h1 : (2:ℝ) ≤ ((R:ℕ) : ℝ) := by
          have h2 : (2:ℝ) ≤ Real.sqrt (4 * Pa.N) := by
            rw [show (4:ℝ) * Pa.N = (2 * Real.sqrt Pa.N)^2 by
              rw [mul_pow, Real.sq_sqrt (by linarith)]; ring, Real.sqrt_sq (by positivity)]
            have h3 := Real.sqrt_le_sqrt hN1
            simp only [Real.sqrt_one] at h3
            linarith
          exact le_trans h2 (Nat.le_ceil _)
        have h1' : (1:ℝ) ≤ ((R:ℕ) : ℝ) := by linarith
        exact_mod_cast h1'
      nlinarith
    have h2 := cast_log_le_log_div (2 * R ^ 2) hm
    have h3 : Real.log (((2 * R ^ 2 : ℕ)) : ℝ) ≤ Real.log (32 * Pa.N) := by
      apply Real.log_le_log (by positivity)
      push_cast
      nlinarith [hRle, hsqN, Real.sqrt_nonneg Pa.N]
    have h4 : Real.log (32 * Pa.N) ≤ 125 * Real.log Pa.N := by
      have h32 := conj1_log_mul_le (c := 32) (N := Pa.N) (by norm_num) hN
      rwa [show (4 * ((32:ℝ) - 1) + 1) = 125 by norm_num] at h32
    have h5 : Real.log (32 * Pa.N) / Real.log 2 ≤ 250 * Real.log Pa.N := by
      have hlog2 : (1/2:ℝ) ≤ Real.log 2 := conj1_log_two_ge_half
      rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
      have hstep : Real.log Pa.N ≤ 2 * Real.log 2 * Real.log Pa.N := by
        nlinarith [mul_le_mul_of_nonneg_right hlog2 hlogN0]
      linarith [h4, hstep]
    have h3' : Real.log (((2 * R ^ 2 : ℕ)) : ℝ) / Real.log 2
        ≤ Real.log (32 * Pa.N) / Real.log 2 :=
      div_le_div_of_nonneg_right h3 (by linarith [conj1_log_two_ge_half])
    linarith [h2, h3', h5]
  have hY2 : (Real.log ((R:ℝ) + 2)) ^ 2 ≤ 441 * (Real.log Pa.N) ^ 2 := by
    have hY0 : 0 ≤ Real.log ((R:ℝ) + 2) := by
      apply Real.log_nonneg
      have h : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
      linarith
    have hsq := pow_le_pow_left₀ hY0 hlogR 2
    have h21 : ((21:ℝ) * Real.log Pa.N)^2 = 441 * (Real.log Pa.N)^2 := by ring
    rwa [h21] at hsq
  have hstep1 : ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
        * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2))
      ≤ (250 * Real.log Pa.N) * (C₀ * (17 * Pa.N * (441 * (Real.log Pa.N) ^ 2))) := by
    apply mul_le_mul hL' _ (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀pos.le
    exact mul_le_mul hR17 hY2 (by positivity) (by positivity)
  have hstep2 : (250 * Real.log Pa.N) * (C₀ * (17 * Pa.N * (441 * (Real.log Pa.N) ^ 2)))
      = 1874250 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := by ring
  have hstep3 : 1874250 * C₀ * Pa.N * (Real.log Pa.N) ^ 3
      ≤ 2000000 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := by
    have h1 : 0 ≤ C₀ * Pa.N * (Real.log Pa.N) ^ 3 :=
      mul_nonneg (mul_nonneg hC₀pos.le (by linarith)) (pow_nonneg hlogN0 3)
    nlinarith
  calc (∑ z ∈ Work.FIPlan.gBox (R : ℤ),
        (if β z ≠ 0 then ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0))
      ≤ ((Nat.log 2 (2 * R ^ 2) : ℕ) : ℝ)
          * (C₀ * (((R:ℝ) ^ 2 + 1) * (Real.log ((R:ℝ) + 2)) ^ 2)) := hmain
    _ ≤ (250 * Real.log Pa.N) * (C₀ * (17 * Pa.N * (441 * (Real.log Pa.N) ^ 2))) := hstep1
    _ = 1874250 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := hstep2
    _ ≤ 2000000 * C₀ * Pa.N * (Real.log Pa.N) ^ 3 := hstep3

/-- Round-4 `Work.FIArea1.conjunct1_le`: the first conjunct (5.10). -/
theorem conjunct1_le_r6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsMajorant Pa f → Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      ‖Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β‖
        ≤ c * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
            + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
          * (Real.log Pa.N) ^ (3 : ℕ) := by
  obtain ⟨C, hCpos, hC⟩ := conj1_sum_bound_aux_r6
  refine ⟨800 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro Pa f z0 φ β hf hβ
  by_cases hN : (4 / 3 : ℝ) < Pa.N
  · have hMpos : (0 : ℝ) < Pa.M := by linarith [Pa.hM1]
    have hNpos : (0 : ℝ) < Pa.N := by linarith
    have hL : 0 ≤ (Real.log Pa.N) ^ (3 : ℕ) := by
      have : 0 ≤ Real.log Pa.N := Real.log_nonneg (by linarith [Pa.hN1])
      positivity
    have hcount : ∀ z : GaussianInt, β z ≠ 0 →
        (((Work.FITop3.annM Pa).filter
          (fun w => ¬ Work.FIPlan.GaussCoprime w z ∧
            ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
          ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
              * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
              * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) :=
      fun z hz => conjunct1_count_r6 Pa z0 φ β hβ z hz
    have hdiff := conj1_diff_le_r6 Pa z0 φ β hcount hβ
    have hS := hC Pa z0 φ β hN hβ
    have harith := conj1_arith Pa.M Pa.N (Pa.Pz : ℝ) ((Real.log Pa.N) ^ (3 : ℕ)) hMpos hNpos hL
    calc ‖Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β‖
        ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * ∑ z ∈ Work.FITop.boxN Pa,
              (if β z ≠ 0 then
                ‖β z‖ * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) else 0) := hdiff
      _ ≤ 800 * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)))
          * (C * Pa.N * (Real.log Pa.N) ^ (3 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left hS
          exact conj1_factor_nonneg Pa
      _ = 800 * C * ((Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
            * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)) * Pa.N
            * (Real.log Pa.N) ^ (3 : ℕ)) := by ring
      _ ≤ 800 * C * ((Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
            + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
            * (Real.log Pa.N) ^ (3 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left harith
          exact mul_nonneg (by norm_num) hCpos.le
      _ = (800 * C) * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
            + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
          * (Real.log Pa.N) ^ (3 : ℕ) := by ring
  · have hz : ∀ z, β z = 0 := conj1_beta_eq_zero_of_small_N_r6 Pa z0 φ β hβ (le_of_not_gt hN)
    have hzero : ‖Work.FITop3.Bstar Pa β - Work.FITop3.Bfree Pa β‖ = 0 := by
      simp only [Work.FITop3.Bstar, Work.FITop3.Bfree]
      simp [hz]
    rw [hzero]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) hCpos.le
      · have hM0 : (0 : ℝ) ≤ Pa.M := by linarith [Pa.hM1]
        have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
        have hP0 : (0 : ℝ) < (Pa.Pz : ℝ) := by
          have : (0 : ℕ) < Pa.Pz := by linarith [Pa.hP2]
          exact_mod_cast this
        have hA : 0 ≤ Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4) :=
          mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hN0 _)
        have hB : 0 ≤ (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
          mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hM0 _))
            (Real.rpow_nonneg hN0 _)
        linarith
    · exact pow_nonneg (Real.log_nonneg (by linarith [Pa.hN1])) 3

/-! ## 5. The second conjunct of (5.22) (round 4) -/

/-- Round-4 `Work.FIArea1.mem_polarSupp_of_beta`. -/
lemma mem_polarSupp_of_beta_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hzN : z ∈ Work.FITop.boxN Pa)
    (hz : β z ≠ 0) : z ∈ polarSupp Pa φ := by
  obtain ⟨hbox, hsq, hns, -, -⟩ := beta_structure_r6 hβ hz
  rw [mem_polarSupp]
  exact ⟨hzN, hbox, hsq, hns⟩

/-- Round-4 `Work.FIArea1.beta_eq_zero_of_not_mem`. -/
lemma beta_eq_zero_of_not_mem_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hzN : z ∈ Work.FITop.boxN Pa)
    (hz : z ∉ polarSupp Pa φ) : β z = 0 := by
  by_contra h
  exact hz (mem_polarSupp_of_beta_r6 hβ hzN h)

/-- Round-4 `Work.FIArea1.norm_beta_le_tau`. -/
lemma norm_beta_le_tau_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) : ‖β z‖ ≤ Pa.τ := by
  by_cases hz : β z = 0
  · rw [hz, norm_zero]
    exact c2_tau_nonneg Pa
  · exact (beta_structure_r6 hβ hz).2.2.2.1

/-- Round-4 `Work.FIArea1.offdiag_w_le`. -/
lemma offdiag_w_le_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ))
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (w : GaussianInt) :
    ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖
      ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := by
  set n : GaussianInt → ℝ := fun z => ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ) with hn
  have hn0 : ∀ z, 0 ≤ n z := fun z => by positivity
  have hτ0 : 0 ≤ Pa.τ := c2_tau_nonneg Pa
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun z1 _ => norm_sum_le _ _) ?_
  have hterm : ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa,
      ‖(if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖
        ≤ (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
              ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
            then Pa.τ ^ 2 * (n z1 * n z2) else 0) := by
    intro z1 hz1 z2 hz2
    by_cases h1 : z1 ∈ polarSupp Pa φ
    · by_cases h2 : z2 ∈ polarSupp Pa φ
      · by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
        · rw [if_pos hc, if_pos ⟨h1, h2, hc⟩, norm_T_eq hb, hn]
          have hb1 := norm_beta_le_tau_r6 hβ z1
          have hb2 := norm_beta_le_tau_r6 hβ z2
          have hnn : 0 ≤ n z1 * n z2 := mul_nonneg (hn0 z1) (hn0 z2)
          calc ‖β z1‖ * ‖β z2‖ * (n z1 * n z2)
              ≤ Pa.τ * Pa.τ * (n z1 * n z2) := by
                refine mul_le_mul_of_nonneg_right ?_ hnn
                exact mul_le_mul hb1 hb2 (norm_nonneg _) hτ0
            _ = Pa.τ ^ 2 * (n z1 * n z2) := by ring
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.2.1, h.2.2.2⟩)]
          simp
      · have hz0 : β z2 = 0 := beta_eq_zero_of_not_mem_r6 hβ hz2 h2
        have hcond : ¬ (z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
            ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2) := by
          rintro ⟨-, h, -⟩
          exact h2 h
        rw [if_neg hcond]
        by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
        · rw [if_pos hc]
          have hzero : (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) = 0 := by
            rw [hz0]; simp
          rw [hzero, norm_zero]
        · rw [if_neg hc, norm_zero]
    · have hz0 : β z1 = 0 := beta_eq_zero_of_not_mem_r6 hβ hz1 h1
      have hcond : ¬ (z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
          ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2) := by
        rintro ⟨h, -⟩
        exact h1 h
      rw [if_neg hcond]
      by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
      · rw [if_pos hc]
        have hzero : (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) = 0 := by
          rw [hz0]; simp
        rw [hzero, norm_zero]
      · rw [if_neg hc, norm_zero]
  refine le_trans (Finset.sum_le_sum fun z1 hz1 => Finset.sum_le_sum fun z2 hz2 =>
    hterm z1 hz1 z2 hz2) ?_
  have hinner : ∀ z1 : GaussianInt,
      (∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
              ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
            then Pa.τ ^ 2 * (n z1 * n z2) else 0))
        = (if z1 ∈ polarSupp Pa φ then
            Pa.τ ^ 2 * (∑ z2 ∈ polarSupp Pa φ,
              (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0))
           else 0) := by
    intro z1
    by_cases h1 : z1 ∈ polarSupp Pa φ
    · rw [if_pos h1]
      have hstep : (∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
                ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
              then Pa.τ ^ 2 * (n z1 * n z2) else 0))
          = ∑ z2 ∈ Work.FITop.boxN Pa,
              (if z2 ∈ polarSupp Pa φ then
                (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
                  then Pa.τ ^ 2 * (n z1 * n z2) else 0) else 0) := by
        refine Finset.sum_congr rfl fun z2 _ => ?_
        simp only [h1, true_and]
        by_cases h2 : z2 ∈ polarSupp Pa φ <;>
          by_cases hp : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 <;> simp [h2, hp]
      rw [hstep, sum_polarSupp_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z2 _ => ?_
      by_cases hp : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 <;> simp [hp]
    · rw [if_neg h1]
      refine Finset.sum_eq_zero fun z2 _ => ?_
      rw [if_neg]
      tauto
  calc (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
            ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
          then Pa.τ ^ 2 * (n z1 * n z2) else 0))
      = ∑ z1 ∈ Work.FITop.boxN Pa,
          (if z1 ∈ polarSupp Pa φ then
            Pa.τ ^ 2 * (∑ z2 ∈ polarSupp Pa φ,
              (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0))
           else 0) := Finset.sum_congr rfl fun z1 _ => hinner z1
    _ = ∑ z1 ∈ polarSupp Pa φ,
          Pa.τ ^ 2 * (∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0)) :=
        sum_polarSupp_eq Pa φ _
    _ = Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0)) := by
        rw [Finset.mul_sum]
    _ ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) :=
        le_of_eq rfl

/-- Round-4 `Work.FIArea1.offdiag_sum_abs_le`. -/
lemma offdiag_sum_abs_le_r6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ))
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (f : ℤ → ℝ) (hf : Work.FITop3.IsMajorant Pa f) :
    (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
        * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|)
      ≤ Pa.τ ^ 2 * offdiagPairSum Pa φ := by
  have hτ0 : 0 ≤ Pa.τ := c2_tau_nonneg Pa
  have hf1 : ∀ u, f u ≤ 1 := hf.2.1
  have hS0 : ∀ w : GaussianInt, 0 ≤ (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
      (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
        ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
          * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := by
    intro w
    refine Finset.sum_nonneg fun z1 _ => Finset.sum_nonneg fun z2 _ => ?_
    by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc]; positivity
    · rw [if_neg hc]
  have hsum : ∀ w ∈ Work.FITop.boxM Pa,
      f (Work.FIPlan.gnorm w)
        * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|
      ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := by
    intro w _
    have h1 : |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|
        ≤ ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖
        ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) :=
      offdiag_w_le_r6 hb hβ w
    have hbnd : 0 ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) :=
      mul_nonneg (sq_nonneg _) (hS0 w)
    calc f (Work.FIPlan.gnorm w)
          * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|
        ≤ 1 * (Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0))) :=
          mul_le_mul (hf1 _) (le_trans h1 h2) (abs_nonneg _) zero_le_one
      _ = Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := one_mul _
  rw [offdiagPairSum_eq Pa φ, Finset.mul_sum]
  exact Finset.sum_le_sum fun w hw => hsum w hw

/-- Round-4 `Work.FIArea1.Dform_sub_Dstar_le`. -/
lemma Dform_sub_Dstar_le_r6 (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ)
    (hf : Work.FITop3.IsMajorant Pa f) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ)) :
    Work.FITop3.Dform Pa f β - Work.FITop3.Dstar Pa f β
      ≤ (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
          (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
        + Pa.τ ^ 2 * offdiagPairSum Pa φ := by
  rw [Dform_sub_Dstar_eq Pa f β]
  have hf0 : ∀ u, 0 ≤ f u := hf.1
  have hper : ∀ w : GaussianInt, f (Work.FIPlan.gnorm w)
        * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re
      ≤ f (Work.FIPlan.gnorm w)
          * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re
        + f (Work.FIPlan.gnorm w)
          * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
                (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re| := by
    intro w
    rw [noncop_split Pa w β, Complex.add_re]
    have h1 : (∑ z ∈ Work.FITop.boxN Pa,
          (if ¬ Work.FIPlan.GaussCoprime z z then
            (β z * Work.FITop3.Zc w z) * star (β z * Work.FITop3.Zc w z) else 0)).re
        ≤ (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re :=
      diag_sum_re_le hb w
    have h2 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re
        ≤ |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re| :=
      le_abs_self _
    have hf0' : 0 ≤ f (Work.FIPlan.gnorm w) := hf0 _
    nlinarith [h1, h2, hf0']
  calc (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
        * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re)
      ≤ ∑ w ∈ Work.FITop.boxM Pa, (f (Work.FIPlan.gnorm w)
            * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re
          + f (Work.FIPlan.gnorm w)
            * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
                (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
                  (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|) :=
        Finset.sum_le_sum fun w _ => hper w
    _ = (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
            * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
          + ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
            * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
                (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
                  (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re| :=
        Finset.sum_add_distrib
    _ ≤ (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
            * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
          + Pa.τ ^ 2 * offdiagPairSum Pa φ :=
        add_le_add (le_refl _) (offdiag_sum_abs_le_r6 hb hβ f hf)

/-- Round-4 `Work.FIArea1.conjunct2_le_of_offdiag`. -/
theorem conjunct2_le_of_offdiag_r6
    (hcount : ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Work.FIArea1.offdiagPairSum Pa φ
        ≤ c * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsMajorant Pa f → Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      Work.FITop3.Dform Pa f β
        ≤ Work.FITop3.Dstar Pa f β
          + c * Pa.τ ^ (2 : ℕ)
              * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := diagonal_le_r6
  obtain ⟨c₂, hc₂pos, hc₂⟩ := hcount
  refine ⟨c₁ * 2 ^ (516 : ℕ) + c₂, by positivity, ?_⟩
  intro Pa f z0 φ β hf hβ
  obtain ⟨b, hb⟩ := exists_real_of_IsBetaCoeff_r6 hβ
  by_cases hMN : Real.exp 1 ≤ Pa.M * Pa.N
  · have hlog1 : 1 ≤ Real.log (Pa.M * Pa.N) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hMN
    have hkey := Dform_sub_Dstar_le_r6 Pa f z0 φ β hf hβ hb
    have hdiag := hc₁ Pa f z0 φ β hf hβ
    have hcnt := hc₂ Pa φ
    have hM1 : (1 : ℝ) ≤ Pa.M := Pa.hM1
    have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
    have hA0 : 0 ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
    have hB0 : 0 ≤ (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) := by
      refine mul_nonneg (mul_nonneg ?_ (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (by linarith) _)
      exact inv_nonneg.mpr (by positivity)
    have hL0 : 0 ≤ (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) :=
      pow_nonneg (Real.log_nonneg (by nlinarith)) _
    have hY : (1 + Real.log (Pa.M * Pa.N)) ^ (516 : ℕ)
        ≤ 2 ^ (516 : ℕ) * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
      have h1 : (1 + Real.log (Pa.M * Pa.N)) ≤ 2 * Real.log (Pa.M * Pa.N) := by linarith
      calc (1 + Real.log (Pa.M * Pa.N)) ^ (516 : ℕ)
          ≤ (2 * Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) :=
            pow_le_pow_left₀ (by linarith) h1 516
        _ = 2 ^ (516 : ℕ) * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by rw [mul_pow]
    have harith := c2_arith (A := Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
      (B := (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
      (L := (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ))
      (Y := (1 + Real.log (Pa.M * Pa.N)) ^ (516 : ℕ))
      (X := Work.FITop3.Dform Pa f β - Work.FITop3.Dstar Pa f β)
      (Dg := ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
          * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
      (Do := Work.FIArea1.offdiagPairSum Pa φ)
      (τ := Pa.τ) (c₁ := c₁) (c₂ := c₂)
      hA0 hB0 hL0 (c2_tau_nonneg Pa) hc₁pos hc₂pos hY hdiag hcnt hkey
    linarith
  · have hMNlt : Pa.M * Pa.N < Real.exp 1 := not_le.mp hMN
    have hβ0 : ∀ z, β z = 0 := by
      intro z
      by_contra hz
      obtain ⟨hbox, -, hns, -, -⟩ := beta_structure_r6 hβ hz
      obtain ⟨-, hNlt, hNle, -⟩ := hbox
      have hθ := c2_theta_le_one Pa
      have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
      have hNsq : Pa.N ^ 2 ≤ Pa.M * Pa.N := by nlinarith [Pa.hMge, hN1]
      have hNsqrt : Pa.N < Real.sqrt (Real.exp 1) := by
        have h2 : Pa.N ^ 2 < Real.exp 1 := by linarith
        have h3 : (0 : ℝ) ≤ Pa.N := by linarith
        rw [← Real.sqrt_sq h3]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) h2
      have hexp : Real.sqrt (Real.exp 1) < 2 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
        have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      have hgn4 : (Work.FIPlan.gnorm z : ℝ) < 4 := by
        have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith
        linarith
      have hn2 : 2 ≤ Work.FIPlan.gnorm z := by
        have h1 : (1 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
        have h1' : (1 : ℕ) < Work.FIPlan.gnorm z := by exact_mod_cast h1
        omega
      have hn4 : Work.FIPlan.gnorm z ≤ 3 := by
        have h4 : Work.FIPlan.gnorm z < 4 := by exact_mod_cast hgn4
        omega
      interval_cases hg : Work.FIPlan.gnorm z
      · have hcontra := hns 2 Nat.prime_two Pa.hP2
        rw [hg] at hcontra
        exact hcontra dvd_rfl
      · have hsum : z.re ^ 2 + z.im ^ 2 = (3 : ℤ) := by
          have h := gnorm_int z
          rw [hg] at h
          push_cast at h
          linarith
        exact three_not_sum_two_squares ⟨z.re, z.im, hsum⟩
    have hzero1 : Work.FITop3.Dform Pa f β = 0 := by simp [Work.FITop3.Dform, hβ0]
    have hzero2 : Work.FITop3.Dstar Pa f β = 0 := by simp [Work.FITop3.Dstar, hβ0]
    rw [hzero1, hzero2]
    have hA0 : 0 ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
      mul_nonneg (Real.rpow_nonneg (by linarith [Pa.hM1]) _)
        (Real.rpow_nonneg (by linarith [Pa.hN1]) _)
    have hB0 : 0 ≤ (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) := by
      refine mul_nonneg (mul_nonneg ?_ (Real.rpow_nonneg (by linarith [Pa.hM1]) _))
        (Real.rpow_nonneg (by linarith [Pa.hN1]) _)
      exact inv_nonneg.mpr (by positivity)
    have hL0 : 0 ≤ (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) :=
      pow_nonneg (Real.log_nonneg (by nlinarith [Pa.hM1, Pa.hN1])) _
    exact add_nonneg (le_refl 0) (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (sq_nonneg _)) (add_nonneg hA0 hB0)) hL0)

/-- Round-4 `Work.FIArea1.conjunct2_le`: the second conjunct (5.22). -/
theorem conjunct2_le_r6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z0 : GaussianInt) (φ : ℝ) (β : GaussianInt → ℂ),
      Work.FITop3.IsMajorant Pa f → Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      Work.FITop3.Dform Pa f β
        ≤ Work.FITop3.Dstar Pa f β
          + c * Pa.τ ^ (2 : ℕ)
              * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) :=
  conjunct2_le_of_offdiag_r6 Work.FIArea1.offdiag_polar_count


/-! ## 6. Assembly: `Work.FITop4.Area1Sieve6` -/

/-- **The round-6 sieve area.**  The two conjuncts (5.10) and (5.22) with the maximum of their
constants give `Work.FITop4.Area1Sieve6`; the threshold is taken to be `x₀ = 0`. -/
theorem area1s_r6 : Work.FITop4.Area1Sieve6 := by
  obtain ⟨c1, hc1, H1⟩ := conjunct1_le_r6
  obtain ⟨c2, hc2, H2⟩ := conjunct2_le_r6
  refine ⟨max c1 c2, 0, lt_max_of_lt_left hc1, ?_⟩
  intro Pa hx F φ z0 β hF hβ
  have hf : Work.FITop3.IsMajorant Pa F :=
    Work.FITop4.IsMajorant6.toMajorant hF
  constructor
  · refine (H1 Pa F z0 φ β hf hβ).trans ?_
    have hB : 0 ≤ Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
        + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) := by
      have h1 : (0 : ℝ) ≤ Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4) :=
        mul_nonneg (Real.rpow_nonneg (by linarith [Pa.hM1] : (0:ℝ) ≤ Pa.M) (1 / 4))
          (Real.rpow_nonneg (by linarith [Pa.hN1] : (0:ℝ) ≤ Pa.N) (5 / 4))
      have h2 : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
        mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (Real.rpow_nonneg (by linarith [Pa.hM1] : (0:ℝ) ≤ Pa.M) (3 / 4)))
          (Real.rpow_nonneg (by linarith [Pa.hN1] : (0:ℝ) ≤ Pa.N) (3 / 4))
      linarith
    have hL : 0 ≤ (Real.log Pa.N) ^ (3 : ℕ) := pow_nonneg (Real.log_nonneg Pa.hN1) 3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hB) hL
  · refine (H2 Pa F z0 φ β hf hβ).trans ?_
    have hB : 0 ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
        + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) := by
      have h1 : (0 : ℝ) ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
        mul_nonneg (Real.rpow_nonneg (by linarith [Pa.hM1] : (0:ℝ) ≤ Pa.M) (3 / 4))
          (Real.rpow_nonneg (by linarith [Pa.hN1] : (0:ℝ) ≤ Pa.N) (3 / 4))
      have h2 : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) :=
        mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (Real.rpow_nonneg (by linarith [Pa.hM1] : (0:ℝ) ≤ Pa.M) (1 / 2)))
          (Real.rpow_nonneg (by linarith [Pa.hN1] : (0:ℝ) ≤ Pa.N) (3 / 2))
      linarith
    have hL : 0 ≤ (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) :=
      pow_nonneg (Real.log_nonneg (by
        have h1 : (1:ℝ) ≤ Pa.M := Pa.hM1
        have h2 : (1:ℝ) ≤ Pa.N := Pa.hN1
        nlinarith)) 516
    have hτ : 0 ≤ Pa.τ ^ (2 : ℕ) := sq_nonneg Pa.τ
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hτ) hB) hL)

end

end Work.FIArea1

namespace Work.FITop4.Bridge

attribute [local instance] Classical.propDecidable

/-- **ROUND 6 BRIDGE — `Area1Sieve6`.**  `Defs6.IsBetaCoeff6` is round 4's `IsBetaCoeff`
(4.13)+(5.13) with the (5.7) restriction `SameClass8 z z0` added to the support `if`, and
`IsMajorant6 Pa F` carries `IsMajorant Pa (seqOf F)` as a conjunct, so `Area1Sieve6` is the round-4
§5 statement ((5.10)+(5.22), the same two conclusions) for a sub-family of coefficients, plus a
harmless threshold `∃ x₀` (take `x₀ := 0`).

Route: port the *proof* of `Submission/Work/FIArea1/area1s_r4.lean` (proved:
`Work.FIArea1.area1s_r4 : Work.FITop4.Area1Sieve`) to the round-6 hypotheses.  **This file may now
import `Submission.Work.FIArea1.shim.*`**: `Defs6.G0` is defined from
`Work.FIArea2.G0_defect` (not from `G0_fix`), so `Areas6` and the `FIArea1.shim` copies elaborate
together (the previous clash — `Work.FITop3.Witness.gammaTrunc_one` declared both in `boxWitness`
and in `betaCoeff_witness` — is gone).  What must be re-done rather than re-used:

* the size bound `‖β z‖ ≤ τ(|z|²)` of `IsBetaCoeff6` — port it verbatim from
  `Work.FITop4.IsBetaCoeff.toBoxCoeff` (`Defs4.lean`) using the mollifier bounds `q ≤ 1`, `p ≤ 1`,
  `norm_moebius_le_one`, `abs_gammaTrunc_le`; call it `IsBetaCoeff6.toBoxCoeff` if you add it;
* the support data consumed by the estimates: `IsBetaCoeff6.{support, noSmallPrimes, sameClass,
  squarefree_gnorm}`;
* the majorant: `IsMajorant6.toMajorant : IsMajorant Pa (seqOf F)`. -/
theorem area1Sieve6 : Work.FITop4.Area1Sieve6 := Work.FIArea1.area1s_r6

end Work.FITop4.Bridge


