/-
# `Submission.Work.FIArea2.R6.pairBracketSelf` — the per-`z₁` fibre bracket of *FI* Lemma 10.1

For a fixed primitive `z₁` in the polar box and any `S` inside the box whose points have squarefree
norm,

  `Σ_{z₂ ∈ S} [z₁ ⊥ z₂]·τ(|z₂|²)²·τ₃(|Δ(z₁,z₂)|) ≤ C·(θ√N)²·(log N + 2)^{2^18}`.

The argument is the one of the paper's Lemma 10.1, in the form recorded in the module comment
(round 6):

1. `R6.tau_sq_le_sum_Icc_four` at `K₁ = ⌈(2N)^{1/4}⌉` and `R6.tau3_le_sum_Icc_four` at
   `K₂ = ⌈(4πθN)^{1/4}⌉` replace `τ(|z₂|²)²` and `τ₃(|Δ|)` by divisor sums
   (`gnorm z₂ ≤ 2N ≤ K₁⁴`, `|Δ| < 4πθN ≤ K₂⁴`).
2. The `z₂`-sum is interchanged with the two divisor sums and each cardinality is bounded by
   `FIArea3.jointCountNoBox`.
3. The three resulting double divisor sums are evaluated by `R6.pairDivisorSums6` (exponents
   `2^17`, `2^16`) and the `K`-arithmetic by `KArith6Self` / `finalArith6Self`:
   `K ≍ N^{1/4}` and `θ√N ≥ N^{3/8}` give `K^{3/2} ≲ θ√N`, `K² ≲ (θ√N)²`, `log K ≤ log N + O(1)`.

**The coprimality input.**  The joint count carries a factor `gcd(d₁,d₂)` in its main term, and
`Σ_{d₁,d₂} τ(d₁)^{17}τ(d₂)^{16}/lcm(d₁,d₂)` is far larger than `(log N)^{2^18}` — so the gcd must be
removed.  It is: by `Work.FIArea7.coprime_gnorm_of_dvd_absDelta`, the two *squarefreeness*
hypotheses (`|z₁|²`, `|z₂|²` squarefree and `z₁ ⊥ z₂`) force `gcd(|z₂|², |Δ(z₁,z₂)|) = 1`, hence
`d₁ | |z₂|²` and `d₂ | |Δ|` imply `gcd(d₁,d₂) = 1`; the factor `[gcd(d₁,d₂)=1]` inserted into the
divisor sum therefore costs nothing (see `R6.perZ6Self`).
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.pairFibre6Aux
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.jointCountNoBox
import Submission.Work.FIArea2.absDelta_lt_four_pi
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea7.coprime_gnorm_of_dvd_absDelta
import Submission.Work.FIArea2.R6.KArithSelf
import Submission.Work.FIArea2.R6.pairDivSum6Self
import Submission.Work.FIArea2.R6.perZ6Self
import Submission.Work.FIArea2.R6.finalArith6Self

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

set_option maxHeartbeats 2000000

/-- An `if p then c else 0` sum is `c` times the cardinality of the filtered set. -/
private lemma sum_ite_const {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (c : ℝ) :
    (∑ x ∈ s, (if p x then c else 0)) = c * ((s.filter p).card : ℝ) := by
  rw [← Finset.sum_boole (s := s) (p := p) (R := ℝ)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x <;> simp [h]

theorem pairBracketSelf :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z1 : GaussianInt) (S : Finset GaussianInt),
      Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N →
      z1 ∈ Work.FIArea3.polarBoxFinset Pa φ →
      Nat.Coprime z1.re.natAbs z1.im.natAbs →
      Squarefree (Work.FIPlan.gnorm z1) →
      S ⊆ Work.FIArea3.polarBoxFinset Pa φ →
      (∀ z ∈ S, Squarefree (Work.FIPlan.gnorm z)) →
      (∑ z2 ∈ S, Work.FIArea2.R6.copInd z1 z2
          * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
          * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ) := by
  obtain ⟨Cdiv, hCdivpos, hCdiv⟩ := pairDivSum6Self
  obtain ⟨Cfin, hCfinpos, hCfin⟩ := finalArith6Self
  refine ⟨Cfin * Cdiv + 1, by positivity, ?_⟩
  intro Pa φ z1 S hu hz1box hcop hsq1 hSsub hSsq
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hudef
  set K1 : ℕ := ⌈(2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ with hK1def
  set K2 : ℕ := ⌈(4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)⌉₊ with hK2def
  set K : ℕ := max K1 K2 with hKdef
  obtain ⟨h1K1, h1K2, hK1K, hK2K, hsqrtK, hKK, hlogK⟩ :=
    KArithSelf Pa K1 K2 K hK1def hK2def hKdef hu
  have h1K : 1 ≤ K := le_trans h1K1 hK1K
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith only [hN1]
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hu1 : 1 ≤ u := by
    rw [hudef]
    have h1 : (1 : ℝ) ≤ Pa.N ^ ((3 : ℝ) / 8) := Real.one_le_rpow hN1 (by norm_num)
    exact le_trans h1 hu
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  have hu_ge : Pa.N ^ ((3 : ℝ) / 8) ≤ u := by rw [hudef]; exact hu
  have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hL0 : (0 : ℝ) ≤ Real.log Pa.N + 2 := by linarith only [hlogN0]
  -- arithmetic: K⁴ dominates the two moduli
  have hrpow4 : ∀ x : ℝ, 0 ≤ x → (x ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = x := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hK1ge : (2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) ≤ ((K1 : ℕ) : ℝ) := by
    rw [hK1def]; exact Nat.le_ceil _
  have hK2ge : (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4) ≤ ((K2 : ℕ) : ℝ) := by
    rw [hK2def]; exact Nat.le_ceil _
  have h2N : 2 * (Pa.N : ℝ) ≤ ((K1 : ℕ) : ℝ) ^ (4 : ℕ) := by
    have h := hrpow4 (2 * (Pa.N : ℝ)) (by positivity)
    calc 2 * (Pa.N : ℝ) = ((2 * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := h.symm
      _ ≤ ((K1 : ℕ) : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) hK1ge 4
  have h4piN : 4 * Real.pi * Pa.θ * (Pa.N : ℝ) ≤ ((K2 : ℕ) : ℝ) ^ (4 : ℕ) := by
    have h := hrpow4 (4 * Real.pi * Pa.θ * (Pa.N : ℝ)) (by positivity)
    calc 4 * Real.pi * Pa.θ * (Pa.N : ℝ)
        = ((4 * Real.pi * Pa.θ * (Pa.N : ℝ)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := h.symm
      _ ≤ ((K2 : ℕ) : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) hK2ge 4
  -- per-`z₂` bound
  have hper : ∀ z2 ∈ S, Work.FIArea2.R6.copInd z1 z2
        * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
        * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
      ≤ 65536 * (65536 * ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0)) := by
    intro z2 hz2
    have hz2box : z2 ∈ Work.FIArea3.polarBoxFinset Pa φ := hSsub hz2
    have hz2in : Work.FITop3.InPolarBox Pa φ z2 :=
      (Work.FIArea3.mem_polarBoxFinset.mp hz2box).2
    have hz1in : Work.FITop3.InPolarBox Pa φ z1 :=
      (Work.FIArea3.mem_polarBoxFinset.mp hz1box).2
    refine perZ6Self (Pa.N) z1 z2 K1 K2 hz1in.1 hz2in.1 hsq1 (hSsq z2 hz2) hN1 hz2in.2.1
      h1K1 h1K2 ?_ ?_
    · have h := hz2in.2.2.1
      linarith only [h, h2N, mul_le_mul_of_nonneg_right hθ1 hNpos.le]
    · have h := Work.FIArea2.absDelta_lt_four_pi hz1in hz2in
      linarith only [h, h4piN]
  -- sum the per-`z₂` bound and factor the constants
  have hsum : (∑ z2 ∈ S, Work.FIArea2.R6.copInd z1 z2
        * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
        * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
      ≤ 65536 * (65536 * (∑ z2 ∈ S, ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))) := by
    calc (∑ z2 ∈ S, Work.FIArea2.R6.copInd z1 z2
          * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
          * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
        ≤ ∑ z2 ∈ S, 65536 * (65536 * ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
            (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
              then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
                * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0)) :=
          Finset.sum_le_sum hper
      _ = 65536 * (65536 * (∑ z2 ∈ S, ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
            (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
              then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
                * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))) := by
          simp only [Finset.mul_sum]
  -- interchange the `z₂`-sum with the two divisor sums
  have hswap : (∑ z2 ∈ S, ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
        (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
          then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
      = ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2, ∑ z2 ∈ S,
        (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
          then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
  -- each inner `z₂`-sum is bounded by the coprime joint count
  have hinner : ∀ d1 ∈ Finset.Icc 1 K1, ∀ d2 ∈ Finset.Icc 1 K2,
      (∑ z2 ∈ S, (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2
            ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
          then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
      ≤ (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
        * (Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ)))
            + 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ)
            + (((d1.divisors.card : ℕ) : ℝ))) := by
    intro d1 hd1 d2 hd2
    obtain ⟨hd1', hd1K⟩ := Finset.mem_Icc.mp hd1
    obtain ⟨hd2', hd2K⟩ := Finset.mem_Icc.mp hd2
    set W : ℝ := (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
      * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) with hW
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    have hcard : (((S.filter (fun z => Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z
            ∧ d2 ∣ Work.FIPlan.absDelta z1 z)).card : ℕ) : ℝ)
        ≤ Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ)))
            + 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ)
            + (((d1.divisors.card : ℕ) : ℝ)) := by
      by_cases hgc : Nat.gcd d1 d2 = 1
      · have hsub : S.filter (fun z => Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z
              ∧ d2 ∣ Work.FIPlan.absDelta z1 z)
            ⊆ (Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d1 ∣ Work.FIPlan.gnorm z
              ∧ d2 ∣ Work.FIPlan.absDelta z1 z) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨hSsub hz.1, hz.2.2.1, hz.2.2.2⟩
        have h1 : (((S.filter (fun z => Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z
              ∧ d2 ∣ Work.FIPlan.absDelta z1 z)).card : ℕ) : ℝ)
            ≤ ((((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => d1 ∣ Work.FIPlan.gnorm z
              ∧ d2 ∣ Work.FIPlan.absDelta z1 z)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have h2 := Work.FIArea3.jointCountNoBox Pa φ z1 d1 d2 hcop hd1' hd2'
        rw [hgc, Nat.cast_one, mul_one] at h2
        exact le_trans h1 h2
      · have hempty : S.filter (fun z => Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z
              ∧ d2 ∣ Work.FIPlan.absDelta z1 z) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          exact fun z _ hcon => hgc hcon.1
        rw [hempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        have hτ0 : (0 : ℝ) ≤ (((d1.divisors.card : ℕ) : ℝ)) := Nat.cast_nonneg _
        have hπ0 : (0 : ℝ) ≤ Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ))) :=
          mul_nonneg (mul_nonneg Real.pi_pos.le (pow_nonneg hu0 2))
            (div_nonneg (Nat.cast_nonneg _) (by positivity))
        have h80 : (0 : ℝ) ≤ 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ) :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu0) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
        linarith only [hπ0, h80, hτ0]
    have hsum_eq : (∑ z2 ∈ S, (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2
            ∧ d2 ∣ Work.FIPlan.absDelta z1 z2 then W else 0))
        = W * (((S.filter (fun z => Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z
            ∧ d2 ∣ Work.FIPlan.absDelta z1 z)).card : ℕ) : ℝ) :=
      sum_ite_const S (fun z => Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z
        ∧ d2 ∣ Work.FIPlan.absDelta z1 z) W
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hcard hW0
  -- final assembly
  obtain ⟨hD1, hD2, hD3⟩ := hCdiv K1 K2 K h1K hK1K hK2K
  have hS1nn : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
      (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
        / ((d : ℝ) * (e : ℝ)) :=
    Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ =>
      div_nonneg (by positivity) (by positivity)
  have hS2nn : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
      (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
        / Real.sqrt (d : ℝ) :=
    Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ =>
      div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hS3nn : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
      (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) :=
    Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ => by positivity
  have hfin := hCfin Pa.θ Pa.N u (K : ℝ)
    (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
      (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
        / ((d : ℝ) * (e : ℝ)))
    (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
      (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
        / Real.sqrt (d : ℝ))
    (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
      (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))
    Cdiv hθ0 hθ1 hN1 hudef hu_ge (by exact_mod_cast h1K) hCdivpos hS1nn hS2nn hS3nn hlogK hsqrtK hKK hD1 hD2 hD3
  have hpt : ∀ d1 d2 : ℕ,
      ((((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
        * (Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ)))
            + 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ)
            + (((d1.divisors.card : ℕ) : ℝ)))
      = Real.pi * u ^ (2 : ℕ) * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
            * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d1 : ℝ) * (d2 : ℝ)))
        + 80 * u * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
            * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d1 : ℝ))
        + ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
            * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))) := by
    intro d1 d2
    ring
  have hsplit : (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
        ((((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
          * (Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ)))
              + 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ)
              + (((d1.divisors.card : ℕ) : ℝ))))
      = Real.pi * u ^ (2 : ℕ) * (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
            (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              / ((d : ℝ) * (e : ℝ)))
        + 80 * u * (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
            (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              / Real.sqrt (d : ℝ))
        + (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
            (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) := by
    have hstep1 : (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
        ((((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
          * (Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ)))
              + 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ)
              + (((d1.divisors.card : ℕ) : ℝ))))
        = ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
            (Real.pi * u ^ (2 : ℕ) * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d1 : ℝ) * (d2 : ℝ)))
              + 80 * u * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                  * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d1 : ℝ))
              + ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                  * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))) :=
      Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => hpt d1 d2
    rw [hstep1]
    have hstep2 : (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
            (Real.pi * u ^ (2 : ℕ) * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d1 : ℝ) * (d2 : ℝ)))
              + 80 * u * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                  * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d1 : ℝ))
              + ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                  * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))))
        = (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
            Real.pi * u ^ (2 : ℕ) * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d1 : ℝ) * (d2 : ℝ))))
          + (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
            80 * u * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d1 : ℝ)))
          + (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
              ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))) := by
      simp only [Finset.sum_add_distrib]
    rw [hstep2]
    have hA : (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          Real.pi * u ^ (2 : ℕ) * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
              * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / ((d1 : ℝ) * (d2 : ℝ))))
        = Real.pi * u ^ (2 : ℕ) * (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
            (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              / ((d : ℝ) * (e : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      exact (Finset.mul_sum _ _ _).symm
    have hB : (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          80 * u * ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
              * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) / Real.sqrt (d1 : ℝ)))
        = 80 * u * (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
            (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              / Real.sqrt (d : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d1 _ => ?_
      exact (Finset.mul_sum _ _ _).symm
    have hC : (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          ((((d1.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
            * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ))))
        = (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
            (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
              * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) := rfl
    rw [hA, hB, hC]
  calc (∑ z2 ∈ S, Work.FIArea2.R6.copInd z1 z2
        * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
        * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ))
      ≤ 65536 * (65536 * (∑ z2 ∈ S, ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))) := hsum
    _ = 65536 * (65536 * (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2, ∑ z2 ∈ S,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))) := by rw [hswap]
    _ ≤ 65536 * (65536 * (∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          ((((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) * ((((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))
            * (Real.pi * u ^ (2 : ℕ) * (((d1.divisors.card : ℕ) : ℝ) / ((d1 : ℝ) * (d2 : ℝ)))
                + 80 * u * (((d1.divisors.card : ℕ) : ℝ)) / Real.sqrt (d1 : ℝ)
                + (((d1.divisors.card : ℕ) : ℝ))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (by norm_num)
        exact Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => hinner d1 hd1 d2 hd2
    _ = 65536 * (65536 * (Real.pi * u ^ (2 : ℕ) * (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
              (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
                / ((d : ℝ) * (e : ℝ)))
            + 80 * u * (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
              (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ) * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
                / Real.sqrt (d : ℝ))
            + (∑ d ∈ Finset.Icc 1 K1, ∑ e ∈ Finset.Icc 1 K2,
              (((d.divisors.card : ℕ) : ℝ)) ^ (17 : ℕ)
                * (((e.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)))) := by rw [hsplit]
    _ ≤ Cfin * Cdiv * u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ) := hfin
    _ ≤ (Cfin * Cdiv + 1) * u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ) := by
        have h1 : Cfin * Cdiv ≤ Cfin * Cdiv + 1 := le_add_of_nonneg_right zero_le_one
        have h2 : (0 : ℝ) ≤ u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ) :=
          mul_nonneg (pow_nonneg hu0 2) (pow_nonneg hL0 262144)
        calc Cfin * Cdiv * u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ)
            = (Cfin * Cdiv) * (u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ)) := by
              rw [mul_assoc]
          _ ≤ (Cfin * Cdiv + 1) * (u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ)) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = (Cfin * Cdiv + 1) * u ^ (2 : ℕ) * (Real.log Pa.N + 2) ^ (262144 : ℕ) := by
              rw [mul_assoc]

end
end Work.FIArea2.R6
