/-
# `FIArea2/R6/R6WProp` — ***FI* Lemma 10.1 at the exponent `θ³`** (`Work.FIArea2.R6.WProp`)

The proof splits on the polar-box scale `u = θ√N`.

* **`u ≥ N^{3/8}`** (the "sharp" regime): the WProp sum is bounded termwise by the per-`z₁` fibre
  sum of `R6/pairBracketSelf` (the per-`z₁` fibre bracket) times the `τ(|z|²)²`-moment
  `R6/tauSqBoxBound6`,
  and the `θ⁴` of that bound is absorbed by `θ ≤ 1` and `460000 < 2^19`.
* **`u < N^{3/8}`** (the degenerate regime): Cauchy–Schwarz against the `τ₃(Δ)²` pair sum
  (`polarBoxTau3Sq6` below, whose fibre input is `R6/tau3InnerSelf`), the pointwise bound
  `τ(|z|²)⁴ ≤ N^{1/16}` (`R6/beta6_tau4_le`) and the polar-box count.  When `u < 1/10` the polar
  box has at most one lattice point, no pair is coprime, and the sum vanishes
  (`R6/zeroPairSum_of_small_u`).
-/
import Mathlib
import Submission.Work.FIArea2.R6.area2_6e_B2
import Submission.Work.FIArea2.R6.WPropNormAux
import Submission.Work.FIArea2.R6.beta6_tau4_le
import Submission.Work.FIArea2.R6.pairBracketSelf
import Submission.Work.FIArea2.R6.tauSqBoxSelf
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea2.R6.tau3InnerSelf
import Submission.Work.FIArea2.R6.csSqrtArith6
import Submission.Work.FIArea2.R6.zeroPairSum_of_small_u
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea2.absDelta_lt_four_pi
import Submission.Work.FIArea2.R6.not_coprime_of_Delta_eq_zero
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.pairSumContent

set_option maxHeartbeats 4000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The sum whose bound `WProp` asserts. -/
def WSum (Pa : Work.FITop.Params) (phi : ℝ) (z0 : GaussianInt) (b : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
      * (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
      * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))

/-- The per-`z₁` fibre sum of `polarBox_pairFibre6`. -/
def FibreSum (Pa : Work.FITop.Params) (phi : ℝ) (z0 : GaussianInt) (b : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, (if b z1 ≠ 0 then
    (∑ z2 ∈ Work.FITop.boxN Pa,
      (if b z2 ≠ 0 then
        copInd z1 z2 * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
          * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
      else 0))
    * ((((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ) else 0)

/-- The `τ₃(Δ)²` pair sum of `polarBoxTau3Sq6`. -/
def Tau3SqSum (Pa : Work.FITop.Params) (phi : ℝ) (z0 : GaussianInt) (b : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if (b z1 ≠ 0 ∧ b z2 ≠ 0) then
      copInd z1 z2 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ) else 0)

/-- `τ(|z|²)` as a real number. -/
def tauN (z : GaussianInt) : ℝ := (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)

/-- `τ₃(|Δ(z₁,z₂)|)` as a real number. -/
def tauD (z1 z2 : GaussianInt) : ℝ := ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)

/-- The `WProp` summand on pairs. -/
def WPair (b : GaussianInt → ℂ) (p : GaussianInt × GaussianInt) : ℝ :=
  copInd p.1 p.2 * (‖b p.1‖ * ‖b p.2‖ * tauN p.1 * tauN p.2 * tauD p.1 p.2)

/-- `τ`-values on the support are `≥ 1`. -/
theorem one_le_tau_of_support {Pa : Work.FITop.Params} {phi : ℝ} {z0 z : GaussianInt}
    {b : GaussianInt → ℂ} (hb : Work.FITop4.IsBetaCoeff6 Pa phi z0 b) (hz : b z ≠ 0) :
    (1 : ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  have h := (IsBetaCoeff6.gnorm_bounds hb hz).1
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hg : (1 : ℕ) ≤ Work.FIPlan.gnorm z := by
    have : (1 : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hpos : 0 < (Work.FIPlan.gnorm z).divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  exact_mod_cast (show (1 : ℕ) ≤ _ by omega)

/-- `a * b ≤ a² * b²` for `a, b ≥ 1`. -/
theorem mul_le_sq_mul_sq {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b ≤ a ^ (2 : ℕ) * b ^ (2 : ℕ) := by
  have hab : 1 ≤ a * b := by nlinarith [ha, hb]
  have hsq : a * b ≤ (a * b) ^ 2 := by nlinarith [hab, sq_nonneg (a * b - 1)]
  calc a * b ≤ (a * b) ^ 2 := hsq
    _ = a ^ (2 : ℕ) * b ^ (2 : ℕ) := by ring

/-! ## The elementwise comparison with the fibre sum -/

theorem WSum_le_FibreSum {Pa : Work.FITop.Params} {phi : ℝ} {z0 : GaussianInt}
    {b : GaussianInt → ℂ} (hb : Work.FITop4.IsBetaCoeff6 Pa phi z0 b) :
    WSum Pa phi z0 b ≤ FibreSum Pa phi z0 b := by
  unfold WSum FibreSum
  refine Finset.sum_le_sum fun z1 _ => ?_
  by_cases h1 : b z1 = 0
  · rw [if_neg (by simp [h1])]
    simp [h1]
  · rw [if_pos h1, Finset.sum_mul]
    refine Finset.sum_le_sum fun z2 _ => ?_
    by_cases h2 : b z2 = 0
    · rw [if_neg (by simp [h2])]
      simp [h2]
    · rw [if_pos h2]
      set t1 : ℝ := (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ) with ht1
      set t2 : ℝ := (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ) with ht2
      set d : ℝ := ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) with hd
      have e1 : ‖b z1‖ ≤ t1 := beta6_norm_le_tau hb
      have e2 : ‖b z2‖ ≤ t2 := beta6_norm_le_tau hb
      have ht10 : 0 ≤ t1 := by positivity
      have ht20 : 0 ≤ t2 := by positivity
      have hd0 : 0 ≤ d := by positivity
      have hc : 0 ≤ copInd z1 z2 := copInd_nonneg z1 z2
      have ht11 : 1 ≤ t1 := by
        rw [ht1]; exact one_le_tau_of_support hb h1
      have ht21 : 1 ≤ t2 := by
        rw [ht2]; exact one_le_tau_of_support hb h2
      have h12 : ‖b z1‖ * ‖b z2‖ ≤ t1 * t2 := mul_le_mul e1 e2 (norm_nonneg _) ht10
      have hkey : ‖b z1‖ * ‖b z2‖ * t1 * t2 * d ≤ t1 ^ (2 : ℕ) * t2 ^ (2 : ℕ) * d := by
        have h3 : ‖b z1‖ * ‖b z2‖ * t1 * t2 ≤ (t1 * t2) * (t1 * t2) := by
          have h := mul_le_mul_of_nonneg_right h12 (mul_nonneg ht10 ht20)
          linarith only [h]
        calc ‖b z1‖ * ‖b z2‖ * t1 * t2 * d
            = (‖b z1‖ * ‖b z2‖ * t1 * t2) * d := by ring
          _ ≤ ((t1 * t2) * (t1 * t2)) * d := mul_le_mul_of_nonneg_right h3 hd0
          _ = t1 ^ (2 : ℕ) * t2 ^ (2 : ℕ) * d := by ring
      calc copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * t1 * t2 * d)
          ≤ copInd z1 z2 * (t1 ^ (2 : ℕ) * t2 ^ (2 : ℕ) * d) :=
            mul_le_mul_of_nonneg_left hkey hc
        _ = copInd z1 z2 * t2 ^ (2 : ℕ) * d * t1 ^ (2 : ℕ) := by ring

/-! ## The case `u ≥ N^{3/8}` -/

/-- **The sharp regime `u = θ√N ≥ N^{3/8}`.**  The double sum is decomposed into the per-`z₁`
fibre bracket `hbracket` (the `τ(|z|²)²τ₃(|Δ|)` sum, `R6/pairBracketSelf`) times the
`τ(|z|²)²`-moment of the support `htau` (`R6/tauSqBoxBound6`), giving
`WSum ≤ Cb·Cp·u⁴(log N + 2)^{262144 + 131073}`; the `θ⁴ = u⁴/N²` so obtained is absorbed into the
`θ³` of the statement at the cost of `3^{460000}` (`460000 < 2^19` and `log N ≥ 1`). -/
theorem WSum_le_of_ge {Pa : Work.FITop.Params} {phi : ℝ} {z0 : GaussianInt}
    {b : GaussianInt → ℂ} (hb : Work.FITop4.IsBetaCoeff6 Pa phi z0 b)
    (hu : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N)
    {Cb Cp : ℝ} (hCb : 0 ≤ Cb) (hCp : 0 ≤ Cp)
    (hbracket : ∀ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
      (∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
          copInd z1 z2 * tauN z2 ^ (2 : ℕ) * tauD z1 z2)
        ≤ Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ))
    (htau : (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0), tauN z ^ (2 : ℕ))
        ≤ Cp * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (131073 : ℕ)) :
    WSum Pa phi z0 b ≤ (Cb * Cp * 3 ^ (460000 : ℕ))
      * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) := by
  set S : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0) with hSdef
  have hmemS : ∀ z, z ∈ S ↔ z ∈ Work.FITop.boxN Pa ∧ b z ≠ 0 := by
    intro z; rw [hSdef, Finset.mem_filter]
  have hSsub : S ⊆ Work.FITop.boxN Pa := by rw [hSdef]; exact Finset.filter_subset _ _
  have hθ0 : (0 : ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
  have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith only [Pa.hN1]
  have hlogN0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg Pa.hN1
  have hL2 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) + 2 := by linarith only [hlogN0]
  have hL2one : (1 : ℝ) ≤ Real.log (Pa.N : ℝ) + 2 := by linarith only [hlogN0]
  have hu2nn : (0 : ℝ) ≤ (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) := sq_nonneg _
  have hu2 : (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) = Pa.θ ^ (2 : ℕ) * Pa.N := by
    rw [mul_pow, Real.sq_sqrt hN0]
  have hu4 : (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ) = Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu2]
    ring
  have hu22 : (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ)
      = (Pa.θ * Real.sqrt Pa.N) ^ (4 : ℕ) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  -- (1) restrict the double sum to the support
  have hW1 : WSum Pa phi z0 b = ∑ z1 ∈ S, ∑ z2 ∈ S,
      copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 * tauD z1 z2) := by
    have h1 : WSum Pa phi z0 b = ∑ z1 ∈ S, ∑ z2 ∈ Work.FITop.boxN Pa,
        copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 * tauD z1 z2) := by
      unfold WSum
      refine (Finset.sum_subset hSsub ?_).symm
      intro z1 hz1 hz1S
      have hb1 : b z1 = 0 := by
        by_contra h; exact hz1S ((hmemS z1).mpr ⟨hz1, h⟩)
      simp [hb1]
    rw [h1]
    refine Finset.sum_congr rfl fun z1 _ => ?_
    refine (Finset.sum_subset hSsub ?_).symm
    intro z2 hz2 hz2S
    have hb2 : b z2 = 0 := by
      by_contra h; exact hz2S ((hmemS z2).mpr ⟨hz2, h⟩)
    simp [hb2]
  rw [hW1]
  -- (2) pointwise: `‖β z‖ τ(|z|²) ≤ τ(|z|²)²` on the support
  have hpt : ∀ z1 ∈ S, ∀ z2 ∈ S,
      copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 * tauD z1 z2)
        ≤ copInd z1 z2 * (tauN z1 ^ (2 : ℕ) * tauN z2 ^ (2 : ℕ) * tauD z1 z2) := by
    intro z1 hz1 z2 hz2
    have hb1 : b z1 ≠ 0 := ((hmemS z1).mp hz1).2
    have hb2 : b z2 ≠ 0 := ((hmemS z2).mp hz2).2
    have e1 : ‖b z1‖ ≤ tauN z1 := beta6_norm_le_tau hb
    have e2 : ‖b z2‖ ≤ tauN z2 := beta6_norm_le_tau hb
    have t1 : (1 : ℝ) ≤ tauN z1 := one_le_tau_of_support hb hb1
    have t2 : (1 : ℝ) ≤ tauN z2 := one_le_tau_of_support hb hb2
    have n1 : (0 : ℝ) ≤ tauN z1 := le_trans zero_le_one t1
    have n2 : (0 : ℝ) ≤ tauN z2 := le_trans zero_le_one t2
    have hd : (0 : ℝ) ≤ tauD z1 z2 := Nat.cast_nonneg _
    have hc : (0 : ℝ) ≤ copInd z1 z2 := copInd_nonneg z1 z2
    have h1' : ‖b z1‖ * tauN z1 ≤ tauN z1 ^ (2 : ℕ) := by
      calc ‖b z1‖ * tauN z1 ≤ tauN z1 * tauN z1 := mul_le_mul_of_nonneg_right e1 n1
        _ = tauN z1 ^ (2 : ℕ) := by ring
    have h2' : ‖b z2‖ * tauN z2 ≤ tauN z2 ^ (2 : ℕ) := by
      calc ‖b z2‖ * tauN z2 ≤ tauN z2 * tauN z2 := mul_le_mul_of_nonneg_right e2 n2
        _ = tauN z2 ^ (2 : ℕ) := by ring
    have hprod : ‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2
        ≤ tauN z1 ^ (2 : ℕ) * tauN z2 ^ (2 : ℕ) := by
      have h := mul_le_mul h1' h2' (mul_nonneg (norm_nonneg (b z2)) n2) (pow_nonneg n1 2)
      have he : (‖b z1‖ * tauN z1) * (‖b z2‖ * tauN z2)
          = ‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 := by ring
      rwa [he] at h
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hd) hc
  -- (3) the fibre decomposition and the two inputs
  have hstep1 : (∑ z1 ∈ S, ∑ z2 ∈ S,
        copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 * tauD z1 z2))
      ≤ ∑ z1 ∈ S, tauN z1 ^ (2 : ℕ)
          * (∑ z2 ∈ S, copInd z1 z2 * tauN z2 ^ (2 : ℕ) * tauD z1 z2) := by
    calc (∑ z1 ∈ S, ∑ z2 ∈ S,
          copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 * tauD z1 z2))
        ≤ ∑ z1 ∈ S, ∑ z2 ∈ S,
            copInd z1 z2 * (tauN z1 ^ (2 : ℕ) * tauN z2 ^ (2 : ℕ) * tauD z1 z2) :=
          Finset.sum_le_sum fun z1 hz1 => Finset.sum_le_sum fun z2 hz2 => hpt z1 hz1 z2 hz2
      _ = ∑ z1 ∈ S, tauN z1 ^ (2 : ℕ)
            * (∑ z2 ∈ S, copInd z1 z2 * tauN z2 ^ (2 : ℕ) * tauD z1 z2) := by
          refine Finset.sum_congr rfl fun z1 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z2 _ => ?_
          ring
  have hstep2 : (∑ z1 ∈ S, tauN z1 ^ (2 : ℕ)
        * (∑ z2 ∈ S, copInd z1 z2 * tauN z2 ^ (2 : ℕ) * tauD z1 z2))
      ≤ (∑ z1 ∈ S, tauN z1 ^ (2 : ℕ))
          * (Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun z1 hz1 => ?_
    exact mul_le_mul_of_nonneg_left (hbracket z1 hz1) (pow_nonneg (Nat.cast_nonneg _) _)
  have hstep3 : (∑ z1 ∈ S, tauN z1 ^ (2 : ℕ))
        * (Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ))
      ≤ (Cb * Cp) * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ)) * (Real.log Pa.N + 2) ^ (460000 : ℕ) := by
    have hlogsum : (Real.log (Pa.N : ℝ) + 2) ^ (131073 : ℕ)
          * (Real.log (Pa.N : ℝ) + 2) ^ (262144 : ℕ)
        ≤ (Real.log (Pa.N : ℝ) + 2) ^ (460000 : ℕ) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hL2one (by norm_num)
    have hA0 : (0 : ℝ) ≤ Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ)
        * (Real.log Pa.N + 2) ^ (262144 : ℕ) :=
      mul_nonneg (mul_nonneg hCb hu2nn) (pow_nonneg hL2 _)
    have hfin0 : (0 : ℝ) ≤ Cb * Cp * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ)) :=
      mul_nonneg (mul_nonneg hCb hCp) (mul_nonneg (pow_nonneg hθ0 _) (pow_nonneg hN0 _))
    calc (∑ z1 ∈ S, tauN z1 ^ (2 : ℕ))
          * (Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ))
        ≤ (Cp * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (131073 : ℕ))
            * (Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ)
              * (Real.log Pa.N + 2) ^ (262144 : ℕ)) :=
          mul_le_mul_of_nonneg_right htau hA0
      _ = Cb * Cp * ((Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ))
            * ((Real.log Pa.N + 2) ^ (131073 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ)) := by
          generalize (Real.log Pa.N + 2) ^ (131073 : ℕ) = p
          generalize (Real.log Pa.N + 2) ^ (262144 : ℕ) = q
          generalize (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) = w
          ring
      _ = Cb * Cp * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ))
            * ((Real.log Pa.N + 2) ^ (131073 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ)) := by
          rw [hu22, hu4]
      _ ≤ Cb * Cp * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ))
            * (Real.log Pa.N + 2) ^ (460000 : ℕ) :=
          mul_le_mul_of_nonneg_left hlogsum hfin0
      _ = (Cb * Cp) * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ))
            * (Real.log Pa.N + 2) ^ (460000 : ℕ) := rfl
  have hmain : (∑ z1 ∈ S, ∑ z2 ∈ S,
        copInd z1 z2 * (‖b z1‖ * ‖b z2‖ * tauN z1 * tauN z2 * tauD z1 z2))
      ≤ (Cb * Cp) * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ)) * (Real.log Pa.N + 2) ^ (460000 : ℕ) :=
    le_trans hstep1 (le_trans hstep2 hstep3)
  -- (4) absorb the logarithm and `θ⁴ ≤ θ³`
  have htheta : Pa.θ ≤ 1 := theta_le_one6 Pa
  have hL1 : (1 : ℝ) ≤ Real.log Pa.N := Work.FIArea3.one_le_log_N_of_sharp hu
  have hL0 : (0 : ℝ) ≤ Real.log Pa.N := le_trans zero_le_one hL1
  have hpow : (Real.log Pa.N + 2) ^ (460000 : ℕ)
      ≤ 3 ^ (460000 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
    have h1' : Real.log Pa.N + 2 ≤ 3 * Real.log Pa.N := by linarith only [hL1]
    have h2 : (Real.log Pa.N + 2) ^ (460000 : ℕ) ≤ (3 * Real.log Pa.N) ^ (460000 : ℕ) :=
      pow_le_pow_left₀ (by linarith only [hL0]) h1' _
    have h3 : (3 * Real.log Pa.N) ^ (460000 : ℕ)
        = 3 ^ (460000 : ℕ) * (Real.log Pa.N) ^ (460000 : ℕ) := by rw [mul_pow]
    have h4 : (Real.log Pa.N) ^ (460000 : ℕ) ≤ (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
      pow_le_pow_right₀ hL1 (by norm_num)
    calc (Real.log Pa.N + 2) ^ (460000 : ℕ)
        ≤ 3 ^ (460000 : ℕ) * (Real.log Pa.N) ^ (460000 : ℕ) := by rw [← h3]; exact h2
      _ ≤ 3 ^ (460000 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
          mul_le_mul_of_nonneg_left h4 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hth4 : Pa.θ ^ (4 : ℕ) ≤ Pa.θ ^ (3 : ℕ) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hθ0 _) htheta
  have hN2 : (0 : ℝ) ≤ Pa.N ^ (2 : ℕ) := pow_nonneg hN0 _
  have hth : Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) ≤ Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right hth4 hN2
  have hstep : (Cb * Cp) * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ))
        * (Real.log Pa.N + 2) ^ (460000 : ℕ)
      ≤ (Cb * Cp * 3 ^ (460000 : ℕ)) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) := by
    have hleft : (Cb * Cp) * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ))
        ≤ (Cb * Cp) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hth (mul_nonneg hCb hCp)
    calc (Cb * Cp) * (Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ))
          * (Real.log Pa.N + 2) ^ (460000 : ℕ)
        ≤ (Cb * Cp) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ))
            * (3 ^ (460000 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) :=
          mul_le_mul hleft hpow (pow_nonneg (by linarith only [hL0]) _)
            (mul_nonneg (mul_nonneg hCb hCp)
              (mul_nonneg (pow_nonneg hθ0 _) (pow_nonneg hN0 _)))
      _ = (Cb * Cp * 3 ^ (460000 : ℕ)) * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) := by
          generalize (3 : ℝ) ^ (460000 : ℕ) = p
          generalize (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) = q
          generalize Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) = w
          ring
  exact le_trans hmain hstep

/-! ## The `τ₃(Δ)²` pair sum (the `B`-factor of Cauchy–Schwarz) -/

/-- The support of a round-6 coefficient lies in the polar box. -/
theorem beta6_support_subset_polarBoxFinset (Pa : Work.FITop.Params) (phi : ℝ)
    (z0 : GaussianInt) (b : GaussianInt → ℂ) (h : Work.FITop4.IsBetaCoeff6 Pa phi z0 b) :
    (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0) ⊆ Work.FIArea3.polarBoxFinset Pa phi := by
  intro z hz
  rw [Finset.mem_filter] at hz
  rw [Work.FIArea3.mem_polarBoxFinset]
  exact ⟨hz.1, Work.FITop4.IsBetaCoeff6.support h hz.2⟩

/-- A non-zero point of the support of a round-6 coefficient is primitive. -/
theorem beta6_isPrimitive_self {Pa : Work.FITop.Params} {phi : ℝ} {z0 : GaussianInt}
    {b : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa phi z0 b) {z : GaussianInt}
    (hz : b z ≠ 0) : Work.FIPlan.IsPrimitive z :=
  Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
    (Work.FITop4.IsBetaCoeff6.squarefree_gnorm h hz)
    (Work.FIArea2.InPolarBox.odd_gnorm (Work.FITop4.IsBetaCoeff6.support h hz))

/-- A double sum carrying the `β ≠ 0` indicators is the sum over the support. -/
theorem pairSum_beta_filter (s : Finset GaussianInt) (b : GaussianInt → ℂ)
    (g : GaussianInt → GaussianInt → ℝ) :
    (∑ z1 ∈ s, ∑ z2 ∈ s, (if b z1 ≠ 0 ∧ b z2 ≠ 0 then g z1 z2 else 0))
      = ∑ z1 ∈ s.filter (fun z => b z ≠ 0), ∑ z2 ∈ s.filter (fun z => b z ≠ 0), g z1 z2 := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  by_cases h1 : b z1 ≠ 0
  · rw [if_pos h1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    by_cases h2 : b z2 ≠ 0
    · rw [if_pos ⟨h1, h2⟩, if_pos h2]
    · rw [if_neg (by simp [h1, h2]), if_neg h2]
  · rw [if_neg h1]
    refine Finset.sum_eq_zero fun z2 _ => ?_
    rw [if_neg (by simp [h1])]

/-- **The `τ₃(Δ)²` pair sum.**  `τ₃(Δ)²` summed over the support of a round-6 coefficient, with
the coprimality indicator.  The fibre of `Δ(z₁,·)` being a two-point set at worst
(`delta_fibre_injective` for the two signs of `Δ`), the inner sum is at most
`∑_{n ≤ 4πθN} τ₃(n)² ≤ ∑ τ(n)⁴` (`R6/tau3InnerSelf`), and the outer sum has at most
`C(θ²N + θ√N + 1)` terms (`FIArea4.polarBox_card_le`).  When `4πθN < 1` every `Δ` vanishes, so
no pair is coprime and the sum is `0` (`not_coprime_of_Delta_eq_zero`); this is what makes the
factor `θN` on the right (rather than `θN + 1`) correct. -/
theorem polarBoxTau3Sq6 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (phi : ℝ) (z0 : GaussianInt) (b : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa phi z0 b →
      Tau3SqSum Pa phi z0 b
        ≤ C * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
            * (Real.log Pa.N + 2) ^ (16 : ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := tau3InnerSelf
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea4.polarBox_card_le
  refine ⟨C1 * C2 * (4 * Real.pi + 1) + 1, by positivity, ?_⟩
  intro Pa phi z0 b hb
  set A : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0) with hA
  have hθ0 : (0 : ℝ) < Pa.θ := Pa.hθ0
  have hN0 : (0 : ℝ) < (Pa.N : ℝ) := by linarith only [Pa.hN1]
  have hL0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) + 2 := by linarith only [Real.log_nonneg Pa.hN1]
  have hLp0 : (0 : ℝ) ≤ (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := pow_nonneg hL0 _
  have hX0 : (0 : ℝ) ≤ Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1 := by
    have h1 : (0 : ℝ) ≤ Pa.θ ^ (2 : ℕ) * Pa.N := mul_nonneg (pow_nonneg hθ0.le 2) hN0.le
    have h2 : (0 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg hθ0.le (Real.sqrt_nonneg _)
    linarith only [h1, h2]
  have hrew : Tau3SqSum Pa phi z0 b
      = ∑ z1 ∈ A, ∑ z2 ∈ A, copInd z1 z2
          * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ) := by
    unfold Tau3SqSum
    exact pairSum_beta_filter (Work.FITop.boxN Pa) b
      (fun z1 z2 => copInd z1 z2 * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
  rw [hrew]
  by_cases hcase : 4 * Real.pi * Pa.θ * Pa.N < 1
  · -- `4πθN < 1`: every `Δ` vanishes and no pair is coprime
    have hzero : (∑ z1 ∈ A, ∑ z2 ∈ A, copInd z1 z2
        * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ)) = 0 := by
      refine Finset.sum_eq_zero fun z1 hz1 => Finset.sum_eq_zero fun z2 hz2 => ?_
      have hb1 : b z1 ≠ 0 := (Finset.mem_filter.mp hz1).2
      have hb2 : b z2 ≠ 0 := (Finset.mem_filter.mp hz2).2
      have hin1 := Work.FITop4.IsBetaCoeff6.support hb hb1
      have hin2 := Work.FITop4.IsBetaCoeff6.support hb hb2
      have hlt := Work.FIArea2.absDelta_lt_four_pi hin1 hin2
      have hΔ0 : Work.FIPlan.Delta z1 z2 = 0 := by
        have hlt' : (Work.FIPlan.absDelta z1 z2 : ℝ) < 1 := lt_trans hlt hcase
        have h1' : Work.FIPlan.absDelta z1 z2 < 1 := by exact_mod_cast hlt'
        exact Int.natAbs_eq_zero.mp (Nat.lt_one_iff.mp h1')
      have hnc : ¬ Work.FIPlan.GaussCoprime z1 z2 :=
        Work.FIArea2.R6.not_coprime_of_Delta_eq_zero hin1 hin2
          (beta6_isPrimitive_self hb hb1) hΔ0
      rw [show copInd z1 z2 = 0 by unfold copInd; rw [if_neg hnc], zero_mul]
    rw [hzero]
    have hCn0 : (0 : ℝ) ≤ C1 * C2 * (4 * Real.pi + 1) + 1 := by
      have hπ : (0 : ℝ) ≤ 4 * Real.pi + 1 := by linarith only [Real.pi_pos]
      have : (0 : ℝ) ≤ C1 * C2 * (4 * Real.pi + 1) :=
        mul_nonneg (mul_nonneg hC1pos.le hC2pos.le) hπ
      linarith only [this]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCn0 hX0) hθ0.le) hN0.le) hLp0
  · -- `4πθN ≥ 1`
    have hge : 1 ≤ 4 * Real.pi * Pa.θ * Pa.N := not_lt.mp hcase
    have hP : Pa.θ * Pa.N + 1 ≤ (4 * Real.pi + 1) * (Pa.θ * Pa.N) := by linarith only [hge]
    have hQ0 : (0 : ℝ) ≤ C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) :=
      mul_nonneg (mul_nonneg hC1pos.le (by linarith only [mul_nonneg hθ0.le hN0.le])) hLp0
    have hinner : ∀ z1 ∈ A, (∑ z2 ∈ A, copInd z1 z2
        * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := by
      intro z1 hz1
      have hb1 : b z1 ≠ 0 := (Finset.mem_filter.mp hz1).2
      have hprim : Work.FIPlan.IsPrimitive z1 := beta6_isPrimitive_self hb hb1
      have hin : Work.FITop3.InPolarBox Pa phi z1 := Work.FITop4.IsBetaCoeff6.support hb hb1
      have hgn : (Pa.N : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := hin.2.1
      have hAsub : A ⊆ Work.FIArea3.polarBoxFinset Pa phi := by
        intro z hz
        rw [hA, Finset.mem_filter] at hz
        rw [Work.FIArea3.mem_polarBoxFinset]
        exact ⟨hz.1, Work.FITop4.IsBetaCoeff6.support hb hz.2⟩
      calc (∑ z2 ∈ A, copInd z1 z2
              * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
          ≤ ∑ z2 ∈ A, ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ) := by
            refine Finset.sum_le_sum fun z2 _ => ?_
            have ht : (0 : ℝ) ≤ ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ) :=
              pow_nonneg (Nat.cast_nonneg _) _
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (copInd_le_one z1 z2) ht
        _ ≤ ∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa phi,
              ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hAsub
              (fun z _ _ => pow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) :=
            hC1 Pa phi z1 hgn hprim hin
    have hsum1 : (∑ z1 ∈ A, ∑ z2 ∈ A, copInd z1 z2
        * ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ ∑ _z1 ∈ A, C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) :=
      Finset.sum_le_sum hinner
    rw [Finset.sum_const, nsmul_eq_mul] at hsum1
    have hcard : ((A.card : ℕ) : ℝ)
        ≤ C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
      have hsub : A ⊆ (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa phi z) := by
        intro z hz
        rw [hA, Finset.mem_filter] at hz
        rw [Finset.mem_filter]
        exact ⟨hz.1, Work.FITop4.IsBetaCoeff6.support hb hz.2⟩
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hC2 Pa phi)
    have hstep1 : ((A.card : ℕ) : ℝ)
          * (C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
        ≤ (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1))
          * (C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcard hQ0
    have hstep2 : (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1))
          * (C1 * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
        ≤ (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1))
          * (C1 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N))
              * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2pos.le hX0)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hC1pos.le) hLp0
    have hstep3 : (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1))
          * (C1 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N))
              * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
        ≤ (C1 * C2 * (4 * Real.pi + 1) + 1)
            * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
            * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := by
      have h3 : (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1))
          * (C1 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N))
              * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
          = (C1 * C2 * (4 * Real.pi + 1))
            * ((Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
                * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := by
        generalize (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) = P
        ring
      rw [h3]
      have hZ0 : (0 : ℝ) ≤ (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
          * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) :=
        mul_nonneg (mul_nonneg (mul_nonneg hX0 hθ0.le) hN0.le) hLp0
      have hexp : (C1 * C2 * (4 * Real.pi + 1) + 1)
            * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
            * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)
          = C1 * C2 * (4 * Real.pi + 1)
            * ((Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
                * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
            + ((Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
                * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := by
        generalize (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) = P
        ring
      rw [hexp]
      exact le_add_of_nonneg_right hZ0
    exact le_trans hsum1 (le_trans hstep1 (le_trans hstep2 hstep3))

/-! ## Cauchy–Schwarz in the degenerate regime -/

/-- The `β`-truncated `τ`-weight `‖β z‖ τ(|z|²)`, and `0` off the support. -/
def betaTau (b : GaussianInt → ℂ) (z : GaussianInt) : ℝ :=
  if b z ≠ 0 then ‖b z‖ * tauN z else 0

/-- The pair weight `1_{(z₁,z₂)=1} τ₃(|Δ(z₁,z₂)|)` of the Cauchy–Schwarz `B`-factor. -/
def pairW (z1 z2 : GaussianInt) : ℝ := copInd z1 z2 * tauD z1 z2

theorem tauN_nonneg (z : GaussianInt) : (0 : ℝ) ≤ tauN z := Nat.cast_nonneg _

theorem tauD_nonneg (z1 z2 : GaussianInt) : (0 : ℝ) ≤ tauD z1 z2 := Nat.cast_nonneg _

theorem betaTau_nonneg (b : GaussianInt → ℂ) (z : GaussianInt) : (0 : ℝ) ≤ betaTau b z := by
  unfold betaTau
  split
  · exact mul_nonneg (norm_nonneg _) (tauN_nonneg z)
  · exact le_refl 0

theorem betaTau_eq (b : GaussianInt → ℂ) {z : GaussianInt} (h : b z ≠ 0) :
    betaTau b z = ‖b z‖ * tauN z := by unfold betaTau; rw [if_pos h]

theorem betaTau_eq_zero (b : GaussianInt → ℂ) {z : GaussianInt} (h : b z = 0) :
    betaTau b z = 0 := by unfold betaTau; simp [h]

theorem copInd_sq (z1 z2 : GaussianInt) : copInd z1 z2 ^ (2 : ℕ) = copInd z1 z2 := by
  unfold copInd; split <;> norm_num

theorem pairW_nonneg (z1 z2 : GaussianInt) : (0 : ℝ) ≤ pairW z1 z2 :=
  mul_nonneg (copInd_nonneg _ _) (tauD_nonneg _ _)

theorem pairW_sq (z1 z2 : GaussianInt) :
    pairW z1 z2 ^ (2 : ℕ) = copInd z1 z2 * tauD z1 z2 ^ (2 : ℕ) := by
  unfold pairW; rw [mul_pow, copInd_sq]

/-- The `τ₃(Δ)²` summand with the support indicator is non-negative. -/
theorem ind_nonneg (b : GaussianInt → ℂ) (z1 z2 : GaussianInt) :
    (0 : ℝ) ≤ (if (b z1 ≠ 0 ∧ b z2 ≠ 0) then copInd z1 z2 * tauD z1 z2 ^ (2 : ℕ) else 0) := by
  by_cases hc : b z1 ≠ 0 ∧ b z2 ≠ 0
  · rw [if_pos hc]
    exact mul_nonneg (copInd_nonneg _ _) (pow_nonneg (tauD_nonneg _ _) _)
  · rw [if_neg hc]

/-- `‖β z‖ τ(|z|²) ≤ τ(|z|²)²` on the support (`beta6_norm_le_tau`), and `0` off it. -/
theorem betaTau_sq_le_tauN_four {Pa : Work.FITop.Params} {phi : ℝ} {z0 : GaussianInt}
    {b : GaussianInt → ℂ} (hb : Work.FITop4.IsBetaCoeff6 Pa phi z0 b) (z : GaussianInt) :
    betaTau b z ^ (2 : ℕ) ≤ tauN z ^ (4 : ℕ) := by
  by_cases h : b z = 0
  · rw [betaTau_eq_zero b h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact pow_nonneg (tauN_nonneg z) 4
  · rw [betaTau_eq b h]
    have h1 : ‖b z‖ ≤ tauN z := beta6_norm_le_tau hb
    have h2 : (0 : ℝ) ≤ tauN z := tauN_nonneg z
    have h3 : ‖b z‖ * tauN z ≤ tauN z * tauN z := mul_le_mul_of_nonneg_right h1 h2
    calc (‖b z‖ * tauN z) ^ (2 : ℕ) ≤ (tauN z * tauN z) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h2) h3 2
      _ = tauN z ^ (4 : ℕ) := by ring

/-- The `β`-truncated summand of the double sum: equal to `WPair` by construction. -/
theorem WSum_eq_pairSum {Pa : Work.FITop.Params} {phi : ℝ} {z0 : GaussianInt}
    {b : GaussianInt → ℂ} :
    WSum Pa phi z0 b
      = ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          (betaTau b p.1 * betaTau b p.2) * pairW p.1 p.2 := by
  have h1 : WSum Pa phi z0 b
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (betaTau b z1 * betaTau b z2) * pairW z1 z2 := by
    unfold WSum
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
    by_cases h1 : b z1 = 0
    · rw [h1, betaTau_eq_zero b h1]
      simp
    · by_cases h2 : b z2 = 0
      · rw [h2, betaTau_eq_zero b h2]
        simp
      · rw [betaTau_eq b h1, betaTau_eq b h2]
        unfold pairW tauN tauD
        ring
  rw [h1]
  exact (Finset.sum_product (Work.FITop.boxN Pa) (Work.FITop.boxN Pa)
    (fun p : GaussianInt × GaussianInt => (betaTau b p.1 * betaTau b p.2) * pairW p.1 p.2)).symm

/-- Cauchy–Schwarz in the degenerate regime: `WProp`'s sum is bounded by the `τ⁴`-moment of the
support times the square root of the `τ₃(Δ)²` pair sum. -/
theorem WSum_le_cs {Pa : Work.FITop.Params} {phi : ℝ} {z0 : GaussianInt}
    {b : GaussianInt → ℂ} (hb : Work.FITop4.IsBetaCoeff6 Pa phi z0 b)
    {C2 : ℝ} (hC2 : 0 ≤ C2)
    (h2 : Tau3SqSum Pa phi z0 b
      ≤ C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
          * (Real.log Pa.N + 2) ^ (16 : ℕ)) :
    WSum Pa phi z0 b
      ≤ (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
            ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ))
        * Real.sqrt (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
            * Pa.θ * Pa.N * (Real.log Pa.N + 2) ^ (16 : ℕ)) := by
  set S : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0) with hSdef
  have hmemS : ∀ z, z ∈ S ↔ z ∈ Work.FITop.boxN Pa ∧ b z ≠ 0 := by
    intro z; rw [hSdef, Finset.mem_filter]
  have hSsub : S ⊆ Work.FITop.boxN Pa := by rw [hSdef]; exact Finset.filter_subset _ _
  have hSτ : (∑ z ∈ S, tauN z ^ (4 : ℕ))
      = ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
          ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ) := by
    rw [hSdef]
    simp only [tauN]
  rw [WSum_eq_pairSum]
  -- restrict the double sum to the support
  have hsub : S.product S ⊆ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa) :=
    Finset.product_subset_product hSsub hSsub
  have hzero : ∀ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa), p ∉ S.product S →
      (betaTau b p.1 * betaTau b p.2) * pairW p.1 p.2 = 0 := by
    intro p hp hpS
    have hp' := Finset.mem_product.mp hp
    have hb0 : b p.1 = 0 ∨ b p.2 = 0 := by
      by_contra h
      push_neg at h
      exact hpS (Finset.mem_product.mpr
        ⟨(hmemS p.1).mpr ⟨hp'.1, h.1⟩, (hmemS p.2).mpr ⟨hp'.2, h.2⟩⟩)
    rcases hb0 with h | h
    · rw [betaTau_eq_zero b h]; simp
    · rw [betaTau_eq_zero b h]; simp
  rw [(Finset.sum_subset hsub hzero).symm]
  -- Cauchy–Schwarz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (S.product S)
      (fun p : GaussianInt × GaussianInt => betaTau b p.1 * betaTau b p.2)
      (fun p : GaussianInt × GaussianInt => pairW p.1 p.2)
  have hAeq : (∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
      = (∑ z ∈ S, betaTau b z ^ (2 : ℕ)) ^ (2 : ℕ) := by
    have h1 : (∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
        = ∑ z1 ∈ S, ∑ z2 ∈ S, (betaTau b z1 * betaTau b z2) ^ (2 : ℕ) :=
      Finset.sum_product S S
        (fun p : GaussianInt × GaussianInt => (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
    rw [h1, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
    ring
  have hA0 : (0 : ℝ) ≤ ∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun p _ =>
      pow_nonneg (mul_nonneg (betaTau_nonneg b p.1) (betaTau_nonneg b p.2)) _
  have hnA0 : (0 : ℝ) ≤ ∑ z ∈ S, betaTau b z ^ (2 : ℕ) :=
    Finset.sum_nonneg fun z _ => pow_nonneg (betaTau_nonneg b z) _
  have hAle : (∑ z ∈ S, betaTau b z ^ (2 : ℕ)) ≤ ∑ z ∈ S, tauN z ^ (4 : ℕ) :=
    Finset.sum_le_sum fun z _ => betaTau_sq_le_tauN_four hb z
  have hB0 : (0 : ℝ) ≤ ∑ p ∈ S.product S, pairW p.1 p.2 ^ (2 : ℕ) :=
    Finset.sum_nonneg fun p _ => pow_nonneg (pairW_nonneg p.1 p.2) _
  have hBeq : (∑ p ∈ S.product S, pairW p.1 p.2 ^ (2 : ℕ))
      = ∑ z1 ∈ S, ∑ z2 ∈ S, pairW z1 z2 ^ (2 : ℕ) :=
    Finset.sum_product S S (fun p : GaussianInt × GaussianInt => pairW p.1 p.2 ^ (2 : ℕ))
  have hBle : (∑ z1 ∈ S, ∑ z2 ∈ S, pairW z1 z2 ^ (2 : ℕ)) ≤ Tau3SqSum Pa phi z0 b := by
    have hTau3 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if (b z1 ≠ 0 ∧ b z2 ≠ 0) then copInd z1 z2 * tauD z1 z2 ^ (2 : ℕ) else 0))
        = Tau3SqSum Pa phi z0 b := by
      unfold Tau3SqSum tauD
      rfl
    rw [← hTau3]
    calc (∑ z1 ∈ S, ∑ z2 ∈ S, pairW z1 z2 ^ (2 : ℕ))
        ≤ ∑ z1 ∈ S, ∑ z2 ∈ S,
            (if (b z1 ≠ 0 ∧ b z2 ≠ 0) then copInd z1 z2 * tauD z1 z2 ^ (2 : ℕ) else 0) := by
          refine Finset.sum_le_sum fun z1 hz1 => Finset.sum_le_sum fun z2 hz2 => ?_
          rw [pairW_sq]
          have hb1 : b z1 ≠ 0 := ((hmemS z1).mp hz1).2
          have hb2 : b z2 ≠ 0 := ((hmemS z2).mp hz2).2
          rw [if_pos ⟨hb1, hb2⟩]
      _ ≤ ∑ z1 ∈ S, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if (b z1 ≠ 0 ∧ b z2 ≠ 0) then copInd z1 z2 * tauD z1 z2 ^ (2 : ℕ) else 0) := by
          apply Finset.sum_le_sum
          intro z1 _
          exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
            (fun z2 _ _ => ind_nonneg b z1 z2)
      _ ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if (b z1 ≠ 0 ∧ b z2 ≠ 0) then copInd z1 z2 * tauD z1 z2 ^ (2 : ℕ) else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
          intro z1 _ _
          exact Finset.sum_nonneg (fun z2 _ => ind_nonneg b z1 z2)
  have hg0 : (0 : ℝ) ≤ ∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) * pairW p.1 p.2 :=
    Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (betaTau_nonneg b p.1) (betaTau_nonneg b p.2)) (pairW_nonneg p.1 p.2)
  have hprod0 : (0 : ℝ) ≤ (∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
      * (∑ p ∈ S.product S, pairW p.1 p.2 ^ (2 : ℕ)) := mul_nonneg hA0 hB0
  have hsqrtA : Real.sqrt (∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
      = ∑ z ∈ S, betaTau b z ^ (2 : ℕ) := by
    rw [hAeq, Real.sqrt_sq hnA0]
  calc (∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) * pairW p.1 p.2)
      ≤ Real.sqrt ((∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
          * (∑ p ∈ S.product S, pairW p.1 p.2 ^ (2 : ℕ))) :=
        (Real.le_sqrt hg0 hprod0).mpr hcs
    _ = Real.sqrt (∑ p ∈ S.product S, (betaTau b p.1 * betaTau b p.2) ^ (2 : ℕ))
          * Real.sqrt (∑ p ∈ S.product S, pairW p.1 p.2 ^ (2 : ℕ)) := Real.sqrt_mul hA0 _
    _ ≤ (∑ z ∈ S, betaTau b z ^ (2 : ℕ))
          * Real.sqrt (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
              * (Real.log Pa.N + 2) ^ (16 : ℕ)) := by
        rw [hsqrtA, hBeq]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_trans hBle h2)) hnA0
    _ ≤ (∑ z ∈ S, tauN z ^ (4 : ℕ))
          * Real.sqrt (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
              * (Real.log Pa.N + 2) ^ (16 : ℕ)) :=
        mul_le_mul_of_nonneg_right hAle (Real.sqrt_nonneg _)
    _ = (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
            ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ))
          * Real.sqrt (C2 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
              * (Real.log Pa.N + 2) ^ (16 : ℕ)) := by
        rw [hSτ]

/-! ## The arithmetic of the degenerate regime -/

/-- `θ²N + θ√N + 1 = u² + u + 1` for `u = θ√N`. -/
theorem theta_sq_add_one_eq {θ N u : ℝ} (hN : 0 ≤ N) (hu : u = θ * Real.sqrt N) :
    θ ^ (2 : ℕ) * N + θ * Real.sqrt N + 1 = u ^ (2 : ℕ) + u + 1 := by
  rw [hu, mul_pow, Real.sq_sqrt hN]

/-- `u³√N = θ³N²` for `u = θ√N`. -/
theorem cube_sqrt_eq {θ N u : ℝ} (hN : 0 ≤ N) (hu : u = θ * Real.sqrt N) :
    u ^ (3 : ℕ) * Real.sqrt N = θ ^ (3 : ℕ) * N ^ (2 : ℕ) := by
  set r : ℝ := Real.sqrt N with hr
  have hrr : r * r = N := by rw [hr]; exact Real.mul_self_sqrt hN
  have hu' : u = θ * r := by rw [hu, hr]
  subst hu'
  rw [← hrr]
  ring

/-- The two sides of `csSqrtArith6` agree after substituting `u = θ√N`. -/
theorem csArithLHS_eq {C2 C3 θ N u L : ℝ} (hN : 0 ≤ N) (hu : u = θ * Real.sqrt N) :
    C3 * (u ^ (2 : ℕ) + u + 1) * N ^ ((1 : ℝ) / 16)
        * Real.sqrt (C2 * (u ^ (2 : ℕ) + u + 1) * u * Real.sqrt N * (L + 2) ^ (16 : ℕ))
      = C3 * (θ ^ (2 : ℕ) * N + θ * Real.sqrt N + 1) * N ^ ((1 : ℝ) / 16)
        * Real.sqrt (C2 * (θ ^ (2 : ℕ) * N + θ * Real.sqrt N + 1) * θ * N
            * (L + 2) ^ (16 : ℕ)) := by
  set r : ℝ := Real.sqrt N with hr
  have hrr : r * r = N := by rw [hr]; exact Real.mul_self_sqrt hN
  have hu' : u = θ * r := by rw [hu, hr]
  subst hu'
  rw [← hrr]
  generalize (L + 2) ^ (16 : ℕ) = P
  have hx : (θ * r) ^ (2 : ℕ) + θ * r + 1 = θ ^ (2 : ℕ) * (r * r) + θ * r + 1 := by ring
  have hy : C2 * (θ ^ (2 : ℕ) * (r * r) + θ * r + 1) * (θ * r) * r * P
      = C2 * (θ ^ (2 : ℕ) * (r * r) + θ * r + 1) * θ * (r * r) * P := by ring
  rw [hx, hy]

/-- The two right-hand sides of `csSqrtArith6` agree after substituting `u = θ√N`. -/
theorem csArithRHS_eq {C2 C3 θ N u L : ℝ} (hN : 0 ≤ N) (hu : u = θ * Real.sqrt N) :
    C3 * Real.sqrt C2 * (111 : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (8 : ℕ)
        * (u ^ (3 : ℕ) * Real.sqrt N * L ^ ((2 : ℕ) ^ (19 : ℕ)))
      = C3 * Real.sqrt C2 * (111 : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (8 : ℕ)
        * (θ ^ (3 : ℕ) * N ^ (2 : ℕ) * L ^ ((2 : ℕ) ^ (19 : ℕ))) := by
  set r : ℝ := Real.sqrt N with hr
  have hrr : r * r = N := by rw [hr]; exact Real.mul_self_sqrt hN
  have hu' : u = θ * r := by rw [hu, hr]
  subst hu'
  rw [← hrr]
  generalize L ^ ((2 : ℕ) ^ (19 : ℕ)) = q
  generalize (111 : ℝ) ^ ((3 : ℝ) / 2) = a
  ring

/-! ## The main theorem -/

theorem R6WProp : Work.FIArea2.R6.WProp := by
  obtain ⟨Cb, hCbpos, hbracket⟩ := pairBracketSelf
  obtain ⟨Cp, hCppos, htauB⟩ := tauSqBoxSelf
  obtain ⟨C3, hC3pos, h3⟩ := Work.FIArea4.polarBox_card_le
  obtain ⟨C4, hC4pos, h4⟩ := polarBoxTau3Sq6
  refine ⟨max (Cb * Cp * 3 ^ (460000 : ℕ))
      (C3 * Real.sqrt C4 * (111 : ℝ) ^ ((3 : ℝ) / 2) * 3 ^ (8 : ℕ)),
    lt_of_lt_of_le (mul_pos (mul_pos hCbpos hCppos) (pow_pos (by norm_num : (0 : ℝ) < 3) _))
      (le_max_left _ _), ?_⟩
  intro Pa phi z0 b hb
  show WSum Pa phi z0 b ≤ _
  have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith only [Pa.hN1]
  have hlogN0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg Pa.hN1
  have hZ0 : (0 : ℝ) ≤ Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
      * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt Pa.hθ0) _) (pow_nonneg hN0 _))
      (pow_nonneg hlogN0 _)
  by_cases huA : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N
  · -- Case A: the sharp regime `u ≥ N^{3/8}`
    set S : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0) with hSdef
    have hmemS : ∀ z, z ∈ S ↔ z ∈ Work.FITop.boxN Pa ∧ b z ≠ 0 := by
      intro z; rw [hSdef, Finset.mem_filter]
    have hSsub : S ⊆ Work.FIArea3.polarBoxFinset Pa phi := by
      rw [hSdef]; exact beta6_support_subset_polarBoxFinset Pa phi z0 b hb
    have hbr : ∀ z1 ∈ S,
        (∑ z2 ∈ S, copInd z1 z2 * tauN z2 ^ (2 : ℕ) * tauD z1 z2)
          ≤ Cb * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ) := by
      intro z1 hz1
      have hz1f : b z1 ≠ 0 := ((hmemS z1).mp hz1).2
      have hsf : Squarefree (Work.FIPlan.gnorm z1) :=
        Work.FITop4.IsBetaCoeff6.squarefree_gnorm hb hz1f
      have hcop : Nat.Coprime z1.re.natAbs z1.im.natAbs :=
        Work.FIArea1.coprime_coords_of_sqfree hsf
      have hin : Work.FITop3.InPolarBox Pa phi z1 := Work.FITop4.IsBetaCoeff6.support hb hz1f
      have hbox : z1 ∈ Work.FIArea3.polarBoxFinset Pa phi := by
        rw [Work.FIArea3.mem_polarBoxFinset]
        exact ⟨((hmemS z1).mp hz1).1, hin⟩
      have hSsq : ∀ z ∈ S, Squarefree (Work.FIPlan.gnorm z) := fun z hz =>
        Work.FITop4.IsBetaCoeff6.squarefree_gnorm hb ((hmemS z).mp hz).2
      exact hbracket Pa phi z1 S huA hbox hcop hsf hSsub hSsq
    have hta : (∑ z ∈ S, tauN z ^ (2 : ℕ))
        ≤ Cp * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (131073 : ℕ) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSsub
        (fun z _ _ => pow_nonneg (tauN_nonneg z) _)) (htauB Pa phi huA)
    have hA := WSum_le_of_ge hb huA (le_of_lt hCbpos) (le_of_lt hCppos) hbr hta
    refine le_trans hA (le_trans (mul_le_mul_of_nonneg_right (le_max_left _
      (C3 * Real.sqrt C4 * (111 : ℝ) ^ ((3 : ℝ) / 2) * 3 ^ (8 : ℕ))) hZ0) (le_of_eq ?_))
    simp only [mul_assoc]
  · push_neg at huA
    by_cases huB : (1 : ℝ) / 10 ≤ Pa.θ * Real.sqrt Pa.N
    · -- Case B1: `1/10 ≤ u < N^{3/8}`
      have hL1 : (1 : ℝ) ≤ Real.log (Pa.N : ℝ) := Work.FIArea2.R6.one_le_log_N_of_u_ge huB
      have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
      have hthis : Tau3SqSum Pa phi z0 b
          ≤ C4 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.θ * Pa.N
              * (Real.log Pa.N + 2) ^ (16 : ℕ) := h4 Pa phi z0 b hb
      have hCS := WSum_le_cs hb (le_of_lt hC4pos) hthis
      have hcount : ((((Work.FITop.boxN Pa).filter (fun z => b z ≠ 0)).card : ℕ) : ℝ)
          ≤ C3 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
        have hsub : (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0)
            ⊆ (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa phi z) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, Work.FITop4.IsBetaCoeff6.support hb hz.2⟩
        exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (h3 Pa phi)
      have hsum4 : (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
            ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ))
          ≤ C3 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
              * Pa.N ^ ((1 : ℝ) / 16) := by
        have hpt : ∀ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
            ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ)
              ≤ Pa.N ^ ((1 : ℝ) / 16) := by
          intro z hz
          rw [Finset.mem_filter] at hz
          exact beta6_tau4_le hb huB hz.2
        calc (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0),
              ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ))
            ≤ ∑ _z ∈ (Work.FITop.boxN Pa).filter (fun z => b z ≠ 0), Pa.N ^ ((1 : ℝ) / 16) :=
              Finset.sum_le_sum hpt
          _ = ((((Work.FITop.boxN Pa).filter (fun z => b z ≠ 0)).card : ℕ) : ℝ)
                * Pa.N ^ ((1 : ℝ) / 16) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ C3 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
                * Pa.N ^ ((1 : ℝ) / 16) :=
              mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hN0 _)
      have hstep : WSum Pa phi z0 b
          ≤ C3 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.N ^ ((1 : ℝ) / 16)
              * Real.sqrt (C4 * (Pa.θ ^ (2 : ℕ) * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
                  * Pa.θ * Pa.N * (Real.log Pa.N + 2) ^ (16 : ℕ)) :=
        le_trans hCS (mul_le_mul_of_nonneg_right hsum4 (Real.sqrt_nonneg _))
      have harith := csSqrtArith6 (C2 := C4) (C3 := C3) (u := Pa.θ * Real.sqrt Pa.N)
        (N := Pa.N) (L := Real.log Pa.N) (le_of_lt hC4pos) (le_of_lt hC3pos) huB huA hN1 hL1
      have hlhs := (csArithLHS_eq (C2 := C4) (C3 := C3) (θ := Pa.θ) (N := Pa.N)
        (u := Pa.θ * Real.sqrt Pa.N) (L := Real.log Pa.N) hN0 rfl).symm
      have hrhs := csArithRHS_eq (C2 := C4) (C3 := C3) (θ := Pa.θ) (N := Pa.N)
        (u := Pa.θ * Real.sqrt Pa.N) (L := Real.log Pa.N) hN0 rfl
      refine le_trans (le_trans (le_trans (le_trans hstep (le_of_eq hlhs)) harith)
        (le_of_eq hrhs)) ?_
      calc C3 * Real.sqrt C4 * (111 : ℝ) ^ ((3 : ℝ) / 2) * 3 ^ (8 : ℕ)
            * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)))
          ≤ max (Cb * Cp * 3 ^ (460000 : ℕ))
              (C3 * Real.sqrt C4 * (111 : ℝ) ^ ((3 : ℝ) / 2) * 3 ^ (8 : ℕ))
              * (Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hZ0
        _ = max (Cb * Cp * 3 ^ (460000 : ℕ))
              (C3 * Real.sqrt C4 * (111 : ℝ) ^ ((3 : ℝ) / 2) * 3 ^ (8 : ℕ))
              * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
              * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) := by
          generalize (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ)) = q
          generalize max (Cb * Cp * 3 ^ (460000 : ℕ))
              (C3 * Real.sqrt C4 * (111 : ℝ) ^ ((3 : ℝ) / 2) * 3 ^ (8 : ℕ)) = m
          ring
    · -- Case B2: `u < 1/10`
      push_neg at huB
      have hz : WSum Pa phi z0 b = 0 := by
        unfold WSum
        exact zeroPairSum_of_small_u hb huB
      rw [hz]
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (le_trans (le_of_lt
            (mul_pos (mul_pos hCbpos hCppos) (pow_pos (by norm_num : (0 : ℝ) < 3) _)))
          (le_max_left _ _)) (pow_nonneg (le_of_lt Pa.hθ0) _)) (pow_nonneg hN0 _))
        (pow_nonneg hlogN0 _)

end

end Work.FIArea2.R6
