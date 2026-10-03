/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.InverseTheory.MajorArcs

/-!
# The duality and smoothing steps in the proof of Proposition `lip`

Krause–Mirek–Tao, §6.  This module contains the two elementary ingredients of the passage from
Theorem `pp` to Proposition `lip`, other than the smooth approximation `calc` itself:

* `exists_bounded_correlation` — the `ℓ¹`/`ℓ^∞` duality step: a function with large `ℓ¹` norm
  correlates with a bounded function;
* `bilinPair_smoothOp` — the reindexing which recognises the smoothing operator
  `x ↦ ∑_m w(m) G(x - Q m)` as the dual of the smoothed progression `m ↦ ∑_x f(x + Qm) G(x)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Analysis.InverseTheory

/-! ## The `ℓ¹`/`ℓ^∞` duality step -/

private lemma norm_coe_norm (z : ℂ) : ‖(((‖z‖ : ℝ)) : ℂ)‖ = ‖z‖ := by
  have h := RCLike.norm_ofReal (K := ℂ) (‖z‖)
  simp only [abs_of_nonneg (norm_nonneg z)] at h
  exact h

/-- For `z ≠ 0`, `z * (conj z / ‖z‖) = ‖z‖`. -/
private lemma mul_star_div_norm (z : ℂ) (hz : z ≠ 0) : z * (star z / (‖z‖ : ℂ)) = (‖z‖ : ℂ) := by
  rw [← mul_div_assoc]
  have h1 : z * star z = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [h1, ← Complex.ofReal_div]
  congr 1
  field_simp

/-- **Duality: a large `ℓ¹` norm produces a large correlation with a bounded function.**  For
finitely supported `b : ℤ → ℂ` there is a finitely supported `G` with `‖G‖_∞ ≤ 1` and
`⟨b, G⟩ = ‖b‖_{ℓ¹}` (take `G x = conj(b x)/‖b x‖` where `b x ≠ 0` and `G x = 0` otherwise).

This is the elementary step in the proof of Proposition `lip` where the lower bound
`∑_x |…| ≥ δ^{O(1)}N^d` is converted into a correlation with a bounded test function. -/
theorem exists_bounded_correlation (b : ℤ → ℂ) (hb : FinSupp b) :
    ∃ G : ℤ → ℂ, FinSupp G ∧ (∀ x : ℤ, ‖G x‖ ≤ 1) ∧ bilinPair b G = (ellOne b : ℂ) := by
  obtain ⟨s, hs⟩ := hb
  refine ⟨fun x => if b x = 0 then 0 else star (b x) / (‖b x‖ : ℂ), ?_, ?_, ?_⟩
  · exact ⟨s, fun x hx => by simp [hs x hx]⟩
  · intro x
    beta_reduce
    by_cases h : b x = 0
    · simp [h]
    · rw [if_neg h, norm_div, norm_star, norm_coe_norm]
      exact le_of_eq (div_self (norm_ne_zero_iff.mpr h))
  · rw [bilinPair, ellOne,
      tsum_eq_sum (s := s) (fun x hx => by rw [hs x hx, zero_mul]),
      tsum_eq_sum (s := s) (fun x hx => by rw [hs x hx, norm_zero]),
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : b x = 0
    · rw [h, zero_mul, norm_zero, Complex.ofReal_zero]
    · rw [if_neg h]
      exact mul_star_div_norm _ h

/-! ## Reindexing the smoothing operator -/

/-- **Reindexing the smoothing operator.**  For finitely supported `f` and `G`, nonzero `Q` and
any weight `w : ℤ → ℂ`, the pairing of `f` with the smoothing operator
`x ↦ ∑_m w(m) G(x - Q m)` rearranges into the weighted sum of correlations
`∑_x f(x) ∑_m w(m) G(x - Qm) = ∑_m w(m) ∑_x f(x + Qm) G(x)`.

Both sides are finite sums (the outer one because `f` is finitely supported and `Q ≠ 0`); this is
the identity used in the proof of Proposition `lip` to recognise the constructed `F` as the dual
of the smoothed progression. -/
theorem bilinPair_smoothOp {f G : ℤ → ℂ} (hf : FinSupp f) (hG : FinSupp G) {Q : ℤ} (hQ : Q ≠ 0)
    (w : ℤ → ℂ) :
    bilinPair f (fun x => ∑' m : ℤ, w m * G (x - Q * m))
      = ∑' m : ℤ, w m * (∑' x : ℤ, f (x + Q * m) * G x) := by
  obtain ⟨sf, hsf⟩ := hf
  obtain ⟨sG, hsG⟩ := hG
  set T : Finset ℤ :=
    sf.biUnion (fun x => sG.biUnion fun y => if Q ∣ x - y then {((x - y) / Q)} else ∅)
    with hT
  have hsupp : ∀ p : ℤ × ℤ, p ∉ sf.product T →
      f p.1 * (w p.2 * G (p.1 - Q * p.2)) = 0 := by
    rintro ⟨x, m⟩ hx
    have hx' : ¬ (x ∈ sf ∧ m ∈ T) := fun hc => hx (Finset.mem_product.mpr hc)
    by_cases hxs : x ∈ sf
    · have hmT : m ∉ T := fun hc => hx' ⟨hxs, hc⟩
      have hGx : G (x - Q * m) = 0 := by
        by_contra hc
        have hmem : x - Q * m ∈ sG := by
          by_contra h2; exact hc (hsG _ h2)
        have hdvd : Q ∣ x - (x - Q * m) := ⟨m, by ring⟩
        refine hmT (Finset.mem_biUnion.mpr ⟨x, hxs,
          Finset.mem_biUnion.mpr ⟨x - Q * m, hmem, ?_⟩⟩)
        rw [if_pos hdvd, Finset.mem_singleton,
          show x - (x - Q * m) = Q * m by ring]
        exact (Int.mul_ediv_cancel_left m hQ).symm
      rw [hGx, mul_zero, mul_zero]
    · rw [hsf x hxs, zero_mul]
  have hsumm : Summable (Function.uncurry fun x m : ℤ => f x * (w m * G (x - Q * m))) :=
    summable_of_ne_finset_zero hsupp
  have hstep1 : ∀ x : ℤ, f x * (∑' m : ℤ, w m * G (x - Q * m))
      = ∑' m : ℤ, f x * (w m * G (x - Q * m)) :=
    fun x => (tsum_mul_left (a := f x) (f := fun m : ℤ => w m * G (x - Q * m))).symm
  rw [bilinPair]
  simp only [hstep1]
  rw [← Summable.tsum_comm hsumm]
  refine tsum_congr fun m => ?_
  rw [← (Equiv.subRight (-(Q * m))).tsum_eq
    (fun x : ℤ => f x * (w m * G (x - Q * m)))]
  trans ∑' y : ℤ, w m * (f (y + Q * m) * G y)
  · refine tsum_congr fun y => ?_
    rw [Equiv.subRight_apply, show y - -(Q * m) - Q * m = y by ring]
    ring
  · exact tsum_mul_left

/-- **The smoothing operator as the dual of the smoothed progression.**  The companion form of
`bilinPair_smoothOp`, in the direction in which it is used in the proof of Proposition `lip`:
the correlation of `f` with the smoothing operator `y ↦ ∑_m w(m) G(y - Q m)` equals the pairing
of `G` with the smoothed progression `x ↦ ∑_m w(m) f(x + Q m)`. -/
theorem bilinPair_smoothOp' {f G : ℤ → ℂ} (hf : FinSupp f) (hG : FinSupp G) {Q : ℤ} (hQ : Q ≠ 0)
    (w : ℤ → ℂ) :
    bilinPair f (fun y => ∑' m : ℤ, w m * G (y - Q * m))
      = ∑' x : ℤ, G x * (∑' m : ℤ, w m * f (x + Q * m)) := by
  obtain ⟨sf, hsf⟩ := hf
  obtain ⟨sG, hsG⟩ := hG
  have hsupp1 : ∀ p : ℤ × ℤ, p ∉ sf.product
      (sf.biUnion (fun y => sG.biUnion (fun z => if Q ∣ y - z then {((y - z) / Q)} else ∅))) →
      f p.1 * (w p.2 * G (p.1 - Q * p.2)) = 0 := by
    rintro ⟨y, m⟩ hx
    have hx' : ¬ (y ∈ sf ∧ m ∈ sf.biUnion (fun y => sG.biUnion (fun z =>
        if Q ∣ y - z then {((y - z) / Q)} else ∅))) := fun hc => hx (Finset.mem_product.mpr hc)
    by_cases hys : y ∈ sf
    · have hmT : m ∉ sf.biUnion (fun y => sG.biUnion (fun z =>
          if Q ∣ y - z then {((y - z) / Q)} else ∅)) := fun hc => hx' ⟨hys, hc⟩
      have hGz : G (y - Q * m) = 0 := by
        by_contra hc
        have hmem : y - Q * m ∈ sG := by
          by_contra h2; exact hc (hsG _ h2)
        have hdvd : Q ∣ y - (y - Q * m) := ⟨m, by ring⟩
        refine hmT (Finset.mem_biUnion.mpr ⟨y, hys, Finset.mem_biUnion.mpr
          ⟨y - Q * m, hmem, ?_⟩⟩)
        rw [if_pos hdvd, Finset.mem_singleton, show y - (y - Q * m) = Q * m by ring]
        exact (Int.mul_ediv_cancel_left m hQ).symm
      rw [hGz, mul_zero, mul_zero]
    · rw [hsf y hys, zero_mul]
  have hsupp2 : ∀ p : ℤ × ℤ, p ∉ sG.product
      (sG.biUnion (fun x => sf.biUnion (fun z => if Q ∣ z - x then {((z - x) / Q)} else ∅))) →
      G p.1 * (w p.2 * f (p.1 + Q * p.2)) = 0 := by
    rintro ⟨x, m⟩ hx
    have hx' : ¬ (x ∈ sG ∧ m ∈ sG.biUnion (fun x => sf.biUnion (fun z =>
        if Q ∣ z - x then {((z - x) / Q)} else ∅))) := fun hc => hx (Finset.mem_product.mpr hc)
    by_cases hxs : x ∈ sG
    · have hmT : m ∉ sG.biUnion (fun x => sf.biUnion (fun z =>
          if Q ∣ z - x then {((z - x) / Q)} else ∅)) := fun hc => hx' ⟨hxs, hc⟩
      have hfz : f (x + Q * m) = 0 := by
        by_contra hc
        have hmem : x + Q * m ∈ sf := by
          by_contra h2; exact hc (hsf _ h2)
        have hdvd : Q ∣ (x + Q * m) - x := ⟨m, by ring⟩
        refine hmT (Finset.mem_biUnion.mpr ⟨x, hxs, Finset.mem_biUnion.mpr
          ⟨x + Q * m, hmem, ?_⟩⟩)
        rw [if_pos hdvd, Finset.mem_singleton, show x + Q * m - x = Q * m by ring]
        exact (Int.mul_ediv_cancel_left m hQ).symm
      rw [hfz, mul_zero, mul_zero]
    · rw [hsG x hxs, zero_mul]
  have hsumm1 : Summable (Function.uncurry fun y m : ℤ => f y * (w m * G (y - Q * m))) :=
    summable_of_ne_finset_zero hsupp1
  have hsumm2 : Summable (Function.uncurry fun x m : ℤ => G x * (w m * f (x + Q * m))) :=
    summable_of_ne_finset_zero hsupp2
  rw [bilinPair]
  have hstep1 : ∀ y : ℤ, f y * (∑' m : ℤ, w m * G (y - Q * m))
      = ∑' m : ℤ, f y * (w m * G (y - Q * m)) :=
    fun y => (tsum_mul_left (a := f y) (f := fun m : ℤ => w m * G (y - Q * m))).symm
  simp only [hstep1]
  rw [← Summable.tsum_comm hsumm1]
  trans ∑' m : ℤ, ∑' x : ℤ, G x * (w m * f (x + Q * m))
  · refine tsum_congr fun m => ?_
    rw [← (Equiv.subRight (-(Q * m))).tsum_eq
      (fun y : ℤ => f y * (w m * G (y - Q * m)))]
    refine tsum_congr fun x => ?_
    rw [Equiv.subRight_apply, show x - -(Q * m) - Q * m = x by ring]
    ring
  · rw [Summable.tsum_comm hsumm2]
    refine tsum_congr fun x => ?_
    exact tsum_mul_left

end Work.Analysis.InverseTheory
