/-
# `Work.FIArea3.JointCount.joint_sum_le_double`

The elementary reduction of the *joint* divisor average over the polar box to a double divisor
sum over the *counts* `#{z₂ ∈ box : d ∣ |z₂|², e ∣ |Δ(z₁,z₂)|}`.

FI Lemma 2.2 with `k = 4` produces, for every `m ≥ 1`, a divisor `d₀ ∣ m` with `d₀⁴ ≤ m` and
`τ(m) ≤ (2τ(d₀))⁸ = 256·τ(d₀)⁸`.  Since `τ(d₀)⁸` is one of the (nonnegative) terms of the full
divisor sum, this gives the *truncated* form

  `τ(m) ≤ 256 · Σ_{1 ≤ d ≤ K, d ∣ m} τ(d)⁸`   whenever `m ≤ K⁴`

(`tau_le_sum_Icc_aux` below).  Applying this to both factors `m = |z₂|² ≤ 2N` (with `K = ⌈(2N)^{1/4}⌉`)
and `m = |Δ(z₁,z₂)| ≤ 4πθN` (with `K'' = ⌈(4πθN)^{1/4}⌉`, the box form (6.2) of `absDelta_le_sector`)
and multiplying the two pointwise inequalities turns the summand into a product of two restricted
divisor sums; multiplying out and interchanging the (finite) sums gives exactly

  `Σ_{z₂ ∈ box} τ(|z₂|²)τ(|Δ|) ≤ 65536 Σ_{d ≤ K} Σ_{e ≤ K''} τ(d)⁸ τ(e)⁸ #{z₂ ∈ box : d ∣ |z₂|², e ∣ |Δ|}`.

Everything is elementary; the analytic content (the factorisation of the pointwise τ values and
the box bounds) enters through `tau_le_sum_Icc_aux`, `absDelta_lt_four_pi` and `theta_le_one`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.joint_tau_reduction
import Submission.Work.FIArea4.absDelta_le_sector
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea2.absDelta_lt_four_pi

namespace Work.FIArea3.JointCount

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **FI Lemma 2.2 with `k = 4`, truncated form.**  For `m ≤ K⁴`,

  `τ(m) ≤ 256 · Σ_{1 ≤ d ≤ K, d ∣ m} τ(d)⁸`.

Indeed Lemma 2.2 supplies `d₀ ∣ m` with `d₀⁴ ≤ m` and `τ(m) ≤ 256 τ(d₀)⁸`; from `d₀⁴ ≤ m ≤ K⁴` we
get `d₀ ≤ K`, so `τ(d₀)⁸` is one of the summed terms.  (`m = 0` is trivial: `τ(0) = 0`.) -/
lemma tau_le_sum_Icc_aux (m K : ℕ) (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    ((m.divisors.card : ℝ))
      ≤ 256 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h0 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ 0 then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
    rw [Nat.divisors_zero]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) h0
  · obtain ⟨d, hdvd, hdk, hbound⟩ := Work.FIArea3.lemma_2_2 (k := 4) (by norm_num) hm
    rw [Work.FIArea3.exp_eq_eight] at hbound
    rw [Real.rpow_natCast] at hbound
    have hd4 : ((d : ℝ)) ^ 4 ≤ (m : ℝ) := by exact_mod_cast hdk
    have hdK4 : ((d : ℝ)) ^ 4 ≤ (K : ℝ) ^ 4 := le_trans hd4 h
    have hdK : d ≤ K := by
      have := (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ (d : ℝ) by positivity)
        (show (0 : ℝ) ≤ (K : ℝ) by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp hdK4
      exact_mod_cast this
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm
    have hmem : d ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hd1, hdK⟩
    have hsingle : (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
        ≤ ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
      Finset.single_le_sum (s := Finset.Icc 1 K)
        (f := fun d' => if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
        (fun i _ => by split_ifs <;> positivity) hmem
    rw [if_pos hdvd] at hsingle
    have h2 : (2 * (d.divisors.card : ℝ)) ^ (8 : ℕ) = 256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ) := by
      ring
    rw [h2] at hbound
    calc (m.divisors.card : ℝ) ≤ 256 * ((d.divisors.card : ℝ)) ^ (8 : ℕ) := hbound
      _ ≤ 256 * ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
          mul_le_mul_of_nonneg_left hsingle (by norm_num)

/-- **The truncated rearrangement.**  If for every `z ∈ B` the two divisor functions satisfy the
truncated bounds of `tau_le_sum_Icc_aux`, then the product-sum over `B` is bounded by the double
sum over the *counts* of the pairs `(d,e)` of divisors of `(g z, δ z)`.  Purely combinatorial. -/
lemma joint_double_sum_bound_aux {α : Type*} [DecidableEq α] (B : Finset α) (g δ : α → ℕ)
    (K K2 : ℕ)
    (hτg : ∀ z ∈ B, ((g z).divisors.card : ℝ)
        ≤ 256 * ∑ d ∈ Finset.Icc 1 K,
            (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
    (hτδ : ∀ z ∈ B, ((δ z).divisors.card : ℝ)
        ≤ 256 * ∑ e ∈ Finset.Icc 1 K2,
            (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)) :
    (∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) * (((δ z).divisors.card : ℕ) : ℝ))
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K2,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((B.filter (fun z => d ∣ g z ∧ e ∣ δ z)).card : ℕ) : ℝ) := by
  classical
  have hsumg : ∀ z : α, (0 : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
    fun z => Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  have hsumδ : ∀ z : α, (0 : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 K2,
          (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) :=
    fun z => Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  -- step 1: the pointwise truncated bounds
  have hstep1 : (∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) * (((δ z).divisors.card : ℕ) : ℝ))
      ≤ ∑ z ∈ B,
          (256 * ∑ d ∈ Finset.Icc 1 K,
              (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
            * (256 * ∑ e ∈ Finset.Icc 1 K2,
              (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)) :=
    Finset.sum_le_sum (fun z hz =>
      mul_le_mul (hτg z hz) (hτδ z hz) (by positivity)
        (mul_nonneg (by norm_num) (hsumg z)))
  -- the product of the two truncated sums
  have hprod : ∀ z : α,
      (256 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
        * (256 * ∑ e ∈ Finset.Icc 1 K2,
          (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
      = 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K2,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
            * (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
    intro z
    have h1 : (256 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
        * (256 * ∑ e ∈ Finset.Icc 1 K2,
          (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
        = 65536 * ((∑ d ∈ Finset.Icc 1 K,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
          * (∑ e ∈ Finset.Icc 1 K2,
          (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))) := by ring
    rw [h1]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
  -- the inner double sum over the pairs
  have hinner : ∀ d ∈ Finset.Icc 1 K, ∀ e ∈ Finset.Icc 1 K2,
      (∑ z ∈ B,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
            * (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
        = ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((B.filter (fun z => d ∣ g z ∧ e ∣ δ z)).card : ℕ) : ℝ) := by
    intro d hd e he
    have hpt : ∀ z : α,
        (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
            * (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
          = (if d ∣ g z ∧ e ∣ δ z then
              ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
                * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
      intro z
      by_cases h1 : d ∣ g z <;> by_cases h2 : e ∣ δ z <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun z _ => hpt z)]
    rw [← Finset.sum_filter (p := fun z => d ∣ g z ∧ e ∣ δ z)
      (f := fun _ => ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
        * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)))]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc (∑ z ∈ B, (((g z).divisors.card : ℕ) : ℝ) * (((δ z).divisors.card : ℕ) : ℝ))
      ≤ ∑ z ∈ B,
          (256 * ∑ d ∈ Finset.Icc 1 K,
              (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
            * (256 * ∑ e ∈ Finset.Icc 1 K2,
              (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)) := hstep1
    _ = 65536 * ∑ z ∈ B, ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K2,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
            * (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
        rw [Finset.sum_congr rfl (fun z _ => hprod z)]
        exact (Finset.mul_sum (s := B)
          (f := fun z => ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K2,
            (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
              * (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0))
          (a := 65536)).symm
    _ = 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K2, ∑ z ∈ B,
          (if d ∣ g z then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0)
            * (if e ∣ δ z then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
        congr 1
        rw [Finset.sum_comm (s := B) (t := Finset.Icc 1 K)]
        apply Finset.sum_congr rfl
        intro d hd
        exact Finset.sum_comm (s := B) (t := Finset.Icc 1 K2)
    _ = 65536 * ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K2,
          ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) * ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ))
            * (((B.filter (fun z => d ∣ g z ∧ e ∣ δ z)).card : ℕ) : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        exact hinner d hd e he

/-- **The joint divisor average is bounded by the double divisor sum over the pair counts.** -/
theorem joint_sum_le_double (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ) (z₁ : GaussianInt)
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (hz₁ : β z₁ ≠ 0) :
    (∑ z₂ ∈ Work.FIArea3.polarBoxFinset Pa φ,
        (((Work.FIPlan.gnorm z₂).divisors.card : ℕ) : ℝ)
          * (((Work.FIPlan.absDelta z₁ z₂).divisors.card : ℕ) : ℝ))
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 (Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4))),
          ∑ e ∈ Finset.Icc 1 (Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4))),
            (((d.divisors.card : ℝ)) ^ (8 : ℕ)) * (((e.divisors.card : ℝ)) ^ (8 : ℕ))
              * ((((Work.FIArea3.polarBoxFinset Pa φ).filter
                  (fun z₂ => d ∣ Work.FIPlan.gnorm z₂ ∧ e ∣ Work.FIPlan.absDelta z₁ z₂)).card : ℕ) : ℝ) := by
  classical
  -- `β z₁ ≠ 0` puts `z₁` in the polar box
  have hz₁box : Work.FITop3.InPolarBox Pa φ z₁ :=
    ((Work.FITop3.IsBetaCoeff.toBoxCoeff hβ).2 z₁ hz₁).1
  set B : Finset GaussianInt := Work.FIArea3.polarBoxFinset Pa φ with hB
  set K : ℕ := Nat.ceil ((2 * Pa.N) ^ ((1 : ℝ) / 4)) with hK
  set K2 : ℕ := Nat.ceil ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) with hK2
  have h2N0 : (0 : ℝ) ≤ 2 * Pa.N := by linarith [Pa.hN1]
  have h4pi0 : (0 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
    have h1 : (0 : ℝ) < Pa.θ := Pa.hθ0
    have h2 : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
    positivity
  have hrpow : ((2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 * Pa.N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2N0]
    norm_num
  have hrpow2 : ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 4 * Real.pi * Pa.θ * Pa.N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h4pi0]
    norm_num
  have hτg : ∀ z ∈ B, ((Work.FIPlan.gnorm z).divisors.card : ℝ)
      ≤ 256 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ Work.FIPlan.gnorm z
            then ((((d.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
    intro z hz
    apply tau_le_sum_Icc_aux
    have hzbox : Work.FITop3.InPolarBox Pa φ z :=
      (Work.FIArea3.mem_polarBoxFinset.mp (hB ▸ hz)).2
    have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
    have hg : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
      have hle : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hzbox.2.2.1
      have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
      nlinarith [Pa.hN1]
    calc (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := hg
      _ = ((2 * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hrpow.symm
      _ ≤ (K : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg h2N0 _) (by rw [hK]; exact Nat.le_ceil _) 4
  have hτδ : ∀ z ∈ B, ((Work.FIPlan.absDelta z₁ z).divisors.card : ℝ)
      ≤ 256 * ∑ e ∈ Finset.Icc 1 K2,
          (if e ∣ Work.FIPlan.absDelta z₁ z
            then ((((e.divisors.card : ℕ) : ℝ)) ^ (8 : ℕ)) else 0) := by
    intro z hz
    apply tau_le_sum_Icc_aux
    have hzbox : Work.FITop3.InPolarBox Pa φ z :=
      (Work.FIArea3.mem_polarBoxFinset.mp (hB ▸ hz)).2
    have hδ : (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N :=
      le_of_lt (Work.FIArea2.absDelta_lt_four_pi hz₁box hzbox)
    calc (Work.FIPlan.absDelta z₁ z : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := hδ
      _ = ((4 * Real.pi * Pa.θ * Pa.N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hrpow2.symm
      _ ≤ (K2 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg h4pi0 _) (by rw [hK2]; exact Nat.le_ceil _) 4
  exact joint_double_sum_bound_aux B (fun z => Work.FIPlan.gnorm z)
    (fun z => Work.FIPlan.absDelta z₁ z) K K2 hτg hτδ

end

end Work.FIArea3.JointCount
