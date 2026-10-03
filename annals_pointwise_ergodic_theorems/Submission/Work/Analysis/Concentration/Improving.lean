/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Analysis.Concentration.Fiber
import Submission.Work.Analysis.Concentration.young_zmod

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℓ^p`-improving estimates for the polynomial averaging operator

This file converts the concentration bounds of Appendix C (the `L^s` bound on the fibre counting
function, or the elementary maximal-fibre bound) into `ℓ^p → ℓ^{p'}` improving estimates for the
polynomial averaging operator `polyShiftAverageZMod P Q` on `ℤ/Qℤ`.  These are the estimates used
in Section 10 of Krause–Mirek–Tao (equations (avg-1), (avg-2), (avg-3), (avg-4)).

The mechanism is the identity `A f = h ∗ f` (`shift_average_eq_conv`) together with Young's
convolution inequality on `ℤ/Qℤ` (`young_zmod`).
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset MeasureTheory

noncomputable section

/-- The normalized `L^p` norm on `ℤ/Qℤ` is nonnegative. -/
lemma LpNormZMod_nonneg (Q : ℕ) [NeZero Q] (p : ℝ) (f : ZMod Q → ℂ) :
    0 ≤ LpNormZMod Q p f := by
  unfold LpNormZMod
  exact Real.rpow_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p)) _

/-- The norm of a nonnegative real, viewed as a complex number. -/
lemma norm_ofReal_complex {c : ℝ} (hc : 0 ≤ c) : ‖((c : ℝ) : ℂ)‖ = c := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hc]

/-- Monotonicity of the normalized `L^p` norm in the pointwise norm. -/
lemma LpNormZMod_mono (Q : ℕ) [NeZero Q] {s : ℝ} (hs : 0 < s) {u v : ZMod Q → ℂ}
    (h : ∀ x, ‖u x‖ ≤ ‖v x‖) : LpNormZMod Q s u ≤ LpNormZMod Q s v := by
  unfold LpNormZMod
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => ?_)) (by positivity)
  exact Real.rpow_le_rpow (norm_nonneg _) (h x) hs.le

/-- The normalized `L^p` norm is positively homogeneous. -/
lemma LpNormZMod_const_mul (Q : ℕ) [NeZero Q] {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (u : ZMod Q → ℂ) :
    LpNormZMod Q s (fun x => (c : ℂ) * u x) = c * LpNormZMod Q s u := by
  have hcn : ∀ x : ℂ, ‖((c : ℝ) : ℂ) * x‖ = c * ‖x‖ := by
    intro x
    rw [norm_mul, norm_ofReal_complex hc]
  unfold LpNormZMod
  have hterm : ∀ x : ZMod Q, ‖(c : ℂ) * u x‖ ^ s = c ^ s * ‖u x‖ ^ s := by
    intro x
    rw [hcn (u x), Real.mul_rpow hc (norm_nonneg _)]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  have hS : 0 ≤ ∑ x : ZMod Q, ‖u x‖ ^ s :=
    Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) s
  have hq : 0 ≤ (Q : ℝ)⁻¹ := by positivity
  rw [show (Q : ℝ)⁻¹ * (c ^ s * ∑ x, ‖u x‖ ^ s)
      = c ^ s * ((Q : ℝ)⁻¹ * ∑ x, ‖u x‖ ^ s) by ring]
  rw [Real.mul_rpow (Real.rpow_nonneg hc s) (mul_nonneg hq hS),
    ← Real.rpow_mul hc, one_div, mul_inv_cancel₀ (ne_of_gt hs), Real.rpow_one]

/-- The fibre counting function as a complex-valued function on `ℤ/Qℤ`. -/
def fiberFun (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] : ZMod Q → ℂ :=
  fun z => (polyFiberCard P Q z : ℂ)

/-- **The averaging operator is convolution with the fibre counting function.** -/
lemma shift_average_eq_conv (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) :
    polyShiftAverageZMod P Q f = convZMod Q (fiberFun P Q) f := by
  funext y
  simp only [polyShiftAverageZMod, convZMod, fiberFun, polyFiberCard]
  have hop : ∀ x : ZMod Q, f (y - polyEvalZMod P Q x)
      = ∑ z : ZMod Q, ite (polyEvalZMod P Q x = z) (f (y - z)) 0 := by
    intro x
    rw [Finset.sum_ite_eq]
    simp
  have hop2 : ∀ z : ZMod Q,
      ((Finset.univ.filter (fun x : ZMod Q => polyEvalZMod P Q x = z)).card : ℂ) * f (y - z)
        = ∑ x : ZMod Q, ite (polyEvalZMod P Q x = z) (f (y - z)) 0 := by
    intro z
    rw [← Finset.sum_filter, Finset.sum_const]
    simp
  simp only [hop, hop2]
  rw [Finset.sum_comm]

/-- **Maximal fibre bound implies the `L^s` concentration bound.** -/
lemma fiberLpBound_of_fiberMaxBound {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {M s : ℝ}
    (hM : FiberMaxBound P Q M) (hs : 1 ≤ s) :
    FiberLpBound P Q s (M ^ (1 - 1 / s)) := by
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  have hsne : s ≠ 0 := by linarith
  unfold FiberLpBound
  have hkey : ∀ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s
      ≤ (polyFiberCard P Q y : ℝ) * M ^ (s - 1) := by
    intro y
    have hy0 : (0 : ℝ) ≤ (polyFiberCard P Q y : ℝ) := by positivity
    have hyM : (polyFiberCard P Q y : ℝ) ≤ M := hM y
    have hspos : 0 ≤ s - 1 := by linarith
    rcases eq_or_lt_of_le hy0 with h | h
    · rw [← h, Real.zero_rpow hsne, zero_mul]
    · have hpow : (polyFiberCard P Q y : ℝ) ^ s
          = (polyFiberCard P Q y : ℝ) * (polyFiberCard P Q y : ℝ) ^ (s - 1) := by
        rw [show s = (s - 1) + 1 by ring, Real.rpow_add h, Real.rpow_one]
        ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0 hyM hspos) hy0
  have hC : (M ^ (1 - 1 / s)) ^ s = M ^ (s - 1) := by
    rw [← Real.rpow_mul hM0]
    congr 1
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hsne]
  calc ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s
      ≤ ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) * M ^ (s - 1) :=
        Finset.sum_le_sum (fun y _ => hkey y)
    _ = (∑ y : ZMod Q, (polyFiberCard P Q y : ℝ)) * M ^ (s - 1) := by rw [Finset.sum_mul]
    _ = Q * M ^ (s - 1) := by
        rw [← Nat.cast_sum, fiber_card_sum]
    _ = (M ^ (1 - 1 / s)) ^ s * Q := by rw [hC]; ring

/-- The `L^r` norm of the fibre counting function is at most the constant of the concentration
bound. -/
lemma LpNormZMod_fiberFun_le {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {r C : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (h : FiberLpBound P Q r C) :
    LpNormZMod Q r (fiberFun P Q) ≤ C := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  unfold LpNormZMod fiberFun
  simp_rw [Complex.norm_natCast]
  have h1 : (Q : ℝ)⁻¹ * ∑ z, (polyFiberCard P Q z : ℝ) ^ r ≤ C ^ r := by
    rw [inv_mul_le_iff₀ hQ0]
    calc ∑ z, (polyFiberCard P Q z : ℝ) ^ r ≤ C ^ r * Q := h
      _ = Q * C ^ r := by ring
  calc ((Q : ℝ)⁻¹ * ∑ z, (polyFiberCard P Q z : ℝ) ^ r) ^ (1 / r)
      ≤ (C ^ r) ^ (1 / r) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = C := by
        rw [← Real.rpow_mul hC, one_div, mul_inv_cancel₀ (by linarith : r ≠ 0), Real.rpow_one]

/-- **The `ℓ^p → ℓ^{p'}` improving estimate from the `L^s` concentration bound.**
With `1/r = 1 + 1/p' - 1/p` (so that `p ≤ p'` and `r > 1`), the averaging operator
`polyShiftAverageZMod P Q` maps `ℓ^p` boundedly into `ℓ^{p'}` with constant `C`. -/
theorem polyImproving_of_fiberLpBound {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {r C p p' : ℝ}
    (hr : 1 ≤ r) (hC : 0 ≤ C) (h : FiberLpBound P Q r C) (hp : 1 ≤ p) (hp' : 1 ≤ p')
    (hrel : 1 / r = 1 + 1 / p' - 1 / p) :
    PolyImprovingZMod P Q p p' C := by
  intro f
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [shift_average_eq_conv]
  calc LpNormZMod Q p' (convZMod Q (fiberFun P Q) f)
      ≤ LpNormZMod Q r (fiberFun P Q) * LpNormZMod Q p f :=
        young_zmod Q hr hp hp' (by linarith) _ f
    _ ≤ C * LpNormZMod Q p f :=
        mul_le_mul_of_nonneg_right (LpNormZMod_fiberFun_le (by linarith) hC h)
          (LpNormZMod_nonneg Q p f)

/-- Specialization of the improving estimate to `p = 1`: the `L^1 → L^s` bound of equation
(avg-4) of Section 10 of the paper. -/
theorem polyImproving_l1_ls {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {s C : ℝ}
    (hs : 1 < s) (hC : 0 ≤ C) (h : FiberLpBound P Q s C) :
    PolyImprovingZMod P Q 1 s C :=
  polyImproving_of_fiberLpBound (le_of_lt hs) hC h le_rfl (le_of_lt hs)
    (by ring)

/-- **Improving estimate from the maximal fibre bound.** -/
theorem polyImproving_of_fiberMaxBound {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {M p p' : ℝ}
    (hM : FiberMaxBound P Q M) (hp : 1 ≤ p) (hp_le : p ≤ p') :
    PolyImprovingZMod P Q p p' (M ^ (1 / p - 1 / p')) := by
  have hp' : 1 ≤ p' := le_trans hp hp_le
  set δ : ℝ := 1 / p - 1 / p' with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    have : 1 / p' ≤ 1 / p :=
      one_div_le_one_div_of_le (by linarith : (0:ℝ) < p) hp_le
    linarith
  have hδ1 : δ < 1 := by
    have h1 : 0 < 1 / p' := by positivity
    have h2 : 1 / p ≤ 1 := by rw [one_div]; exact inv_le_one_of_one_le₀ hp
    rw [hδdef]; linarith
  have hpos : 0 < 1 - δ := by linarith
  have hle1 : 1 - δ ≤ 1 := by linarith
  have hr1 : 1 ≤ (1 - δ)⁻¹ := (one_le_inv₀ hpos).mpr hle1
  have hrel : 1 / ((1 - δ)⁻¹) = 1 + 1 / p' - 1 / p := by
    rw [one_div, inv_inv, hδdef]; ring
  have hmul : M ^ (1 - 1 / ((1 - δ)⁻¹)) = M ^ δ := by
    congr 1
    rw [one_div, inv_inv]
    ring
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  have hCnn : 0 ≤ M ^ (1 - 1 / ((1 - δ)⁻¹)) := Real.rpow_nonneg hM0 _
  have hmain := polyImproving_of_fiberLpBound hr1 hCnn
    (fiberLpBound_of_fiberMaxBound hM hr1) hp hp' hrel
  rw [hmul, hδdef] at hmain
  exact hmain

/-! ## The unconditional prime-modulus case -/

/-- **Concentration estimate at a prime modulus.**  If `P` has degree `d ≥ 1` modulo the prime
`p`, then every fibre of `P : ℤ/pℤ → ℤ/pℤ` has at most `d` elements, hence the fibre counting
function satisfies the `L^s` concentration bound with constant `d^{1-1/s}`, uniformly in the
prime `p` and in `s ≥ 1`. -/
theorem fiberLpBound_prime (P : Polynomial ℤ) {p d : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) {s : ℝ} (hs : 1 ≤ s) :
    FiberLpBound P p s ((d : ℝ) ^ (1 - 1 / s)) :=
  fiberLpBound_of_fiberMaxBound
    (fun y => by exact_mod_cast fiber_card_le_prime P hd hdeg y) hs

/-- **`ℓ^p`-improving at a prime modulus** (unconditional, `q < q'`). -/
theorem polyImproving_prime (P : Polynomial ℤ) {p d : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) {q q' : ℝ} (hq : 1 ≤ q) (hqq' : q ≤ q') :
    PolyImprovingZMod P p q q' ((d : ℝ) ^ (1 / q - 1 / q')) := by
  exact polyImproving_of_fiberMaxBound
    (fun y => by exact_mod_cast fiber_card_le_prime P hd hdeg y) hq hqq'

/-- **Level-set counting at a prime modulus.**  For `P` of degree `d ≥ 1` modulo the prime `p`,
the number of `n < N` with `P(n) ≡ a (mod p)` is at most `d (⌈N/p⌉) ≤ d (N/p + 1)`. -/
theorem level_set_card_le_prime (P : Polynomial ℤ) {p d : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) (N : ℕ) (a : ZMod p) :
    (polyLevelSetCard P p N a : ℝ) ≤ (d : ℝ) * ((N / p + 1 : ℕ) : ℝ) :=
  level_set_card_le_of_fiber_max P p N a
    (fun y => by exact_mod_cast fiber_card_le_prime P hd hdeg y)

end

end Work.Analysis.Concentration
