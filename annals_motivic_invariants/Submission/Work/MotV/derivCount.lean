/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The Hurwitz count for the invariant derivation on an elliptic curve

This file proves the counting step of the Hurwitz-lite node `Work.MotV.hurwitz_five`
(the `countBound` step): if `D` is a derivation of `N(E)` whose order at every rational place
drops by at most one (`ord_Q (D f) ≥ ord_Q f - 1`, and `ord_Q f = 0` implies `ord_Q (D f) ≥ 0`),
if the divisor of a function has degree zero (`hDeg`), and if `r` is a function with `D r ≠ 0`
whose values `r(r-1)` have order divisible by `5` at all places where `r`, `r - 1` or `D r` can
be a zero or a pole, then `r` has order zero at *every* rational place: `r` is a unit everywhere.

The proof is the classical Riemann–Hurwitz count: at a zero of `r` (order `a ≥ 5`), at a zero of
`r - 1` (order `b ≥ 5`) and at a pole (order `a ≤ -5`, and `r - 1` has the same order there) the
order of `D r` drops by at most one, while everywhere else `D r` is regular.  Since the degree of
the divisor of `D r` is zero (`hDeg`), and the numbers of zeros of `r`, of zeros of `r - 1` and
of poles of `r` are each bounded by the degree `n` over `5`, one gets `0 ≥ 2n/5 ≥ 0`, hence
`n = 0`.
-/

import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.AffPlace
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

open Work.MotC2

noncomputable section

variable {N : Type*} [Field N]

/-! ## Elementary properties of the order at a place -/

/-- The order of `1` at any place, given a non-zero function. -/
lemma ordO_one_of_ne (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {f : Func E} (hf : f ≠ 0) : ordOfPlace E Q.1 Q.2 (1 : Func E) = 0 := by
  have h := H.ord_mul Q.1 Q.2 f f⁻¹ hf (inv_ne_zero hf)
  have h' := H.ord_inv Q.1 Q.2 f hf
  rw [mul_inv_cancel₀ hf] at h
  linarith

/-- The order of `-1` at any place is zero. -/
lemma ordO_neg_one (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E) :
    ordOfPlace E Q.1 Q.2 (-1 : Func E) = 0 := by
  have h := H.ord_mul Q.1 Q.2 (-1 : Func E) (-1 : Func E) (by norm_num) (by norm_num)
  have hone : (-1 : Func E) * (-1) = 1 := by ring
  rw [hone] at h
  have h1 : ordOfPlace E Q.1 Q.2 (1 : Func E) = 0 :=
    ordO_one_of_ne E H Q (f := (-1 : Func E)) (by norm_num)
  linarith

/-- The order is insensitive to negation. -/
lemma ordO_neg (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {f : Func E} (hf : f ≠ 0) : ordOfPlace E Q.1 Q.2 (-f) = ordOfPlace E Q.1 Q.2 f := by
  have h := H.ord_mul Q.1 Q.2 (-1 : Func E) f (by norm_num) hf
  have h1 : ordOfPlace E Q.1 Q.2 (-1 : Func E) = 0 := ordO_neg_one E H Q
  have h2 : (-1 : Func E) * f = -f := by ring
  rw [h2, h1, zero_add] at h
  exact h

/-- **Pointwise trichotomy.**  At any place, the orders `a = ord r` and `b = ord (r-1)` cannot
both be positive, cannot both be negative, and if `a < 0` then `b = a`.  These are the
ultrametric inequalities at the three functions `1 = r - (r-1)`, `r = (r-1) + 1` and
`r - 1 = r + (-1)`. -/
lemma ordO_trich (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {r : Func E} (hr0 : r ≠ 0) (hr1 : r - 1 ≠ 0) :
    min (ordOfPlace E Q.1 Q.2 r) (ordOfPlace E Q.1 Q.2 (r - 1)) ≤ 0 ∧
      min (ordOfPlace E Q.1 Q.2 (r - 1)) 0 ≤ ordOfPlace E Q.1 Q.2 r ∧
      min (ordOfPlace E Q.1 Q.2 r) 0 ≤ ordOfPlace E Q.1 Q.2 (r - 1) ∧
      (0 < ordOfPlace E Q.1 Q.2 r → ordOfPlace E Q.1 Q.2 (r - 1) = 0) ∧
      (0 < ordOfPlace E Q.1 Q.2 (r - 1) → ordOfPlace E Q.1 Q.2 r = 0) ∧
      (ordOfPlace E Q.1 Q.2 r < 0 → ordOfPlace E Q.1 Q.2 (r - 1) = ordOfPlace E Q.1 Q.2 r) ∧
      (ordOfPlace E Q.1 Q.2 r = 0 → 0 ≤ ordOfPlace E Q.1 Q.2 (r - 1)) := by
  have h1 : min (ordOfPlace E Q.1 Q.2 r) (ordOfPlace E Q.1 Q.2 (r - 1)) ≤ 0 := by
    have hne : r + -(r - 1) ≠ 0 := by
      have : r + -(r - 1) = (1 : Func E) := by ring
      rw [this]; exact one_ne_zero
    have h := H.ord_add Q.1 Q.2 r (-(r - 1)) hne
    rw [show r + -(r - 1) = (1 : Func E) from by ring, ordO_one_of_ne E H Q hr0,
      ordO_neg E H Q hr1] at h
    exact h
  have h2 : min (ordOfPlace E Q.1 Q.2 (r - 1)) 0 ≤ ordOfPlace E Q.1 Q.2 r := by
    have hne : (r - 1) + 1 ≠ 0 := by
      have h2 : (r - 1) + 1 = r := by ring
      rw [h2]; exact hr0
    have h := H.ord_add Q.1 Q.2 (r - 1) 1 hne
    rw [show (r - 1) + 1 = r from by ring, ordO_one_of_ne E H Q hr0] at h
    exact h
  have h3 : min (ordOfPlace E Q.1 Q.2 r) 0 ≤ ordOfPlace E Q.1 Q.2 (r - 1) := by
    have hne : r + (-1 : Func E) ≠ 0 := by
      have h2 : r + (-1 : Func E) = r - 1 := by ring
      rw [h2]; exact hr1
    have h := H.ord_add Q.1 Q.2 r (-1) hne
    rw [show r + (-1 : Func E) = r - 1 from by ring, ordO_neg_one E H Q] at h
    exact h
  have h4 : 0 < ordOfPlace E Q.1 Q.2 r → ordOfPlace E Q.1 Q.2 (r - 1) = 0 := by
    intro ha
    have hble : ordOfPlace E Q.1 Q.2 (r - 1) ≤ 0 := by
      by_contra hb
      push_neg at hb
      have : 0 < min (ordOfPlace E Q.1 Q.2 r) (ordOfPlace E Q.1 Q.2 (r - 1)) := lt_min ha hb
      linarith
    have hbge : 0 ≤ ordOfPlace E Q.1 Q.2 (r - 1) := by
      have h := h3
      rw [min_eq_right (le_of_lt ha)] at h
      linarith
    linarith
  have h5 : 0 < ordOfPlace E Q.1 Q.2 (r - 1) → ordOfPlace E Q.1 Q.2 r = 0 := by
    intro hb
    have hale : ordOfPlace E Q.1 Q.2 r ≤ 0 := by
      by_contra ha
      push_neg at ha
      have : 0 < min (ordOfPlace E Q.1 Q.2 r) (ordOfPlace E Q.1 Q.2 (r - 1)) := lt_min ha hb
      linarith
    have hage : 0 ≤ ordOfPlace E Q.1 Q.2 r := by
      have h := h2
      rw [min_eq_right (le_of_lt hb)] at h
      linarith
    linarith
  have h6 : ordOfPlace E Q.1 Q.2 r < 0 →
      ordOfPlace E Q.1 Q.2 (r - 1) = ordOfPlace E Q.1 Q.2 r := by
    intro ha
    have hbl : ordOfPlace E Q.1 Q.2 (r - 1) < 0 := by
      by_contra hb
      push_neg at hb
      have h := h2
      rw [min_eq_right hb] at h
      linarith
    have hba : ordOfPlace E Q.1 Q.2 (r - 1) ≤ ordOfPlace E Q.1 Q.2 r := by
      have h := h2
      rw [min_eq_left (le_of_lt hbl)] at h
      linarith
    have hab : ordOfPlace E Q.1 Q.2 r ≤ ordOfPlace E Q.1 Q.2 (r - 1) := by
      have h := h3
      rw [min_eq_left (le_of_lt ha)] at h
      linarith
    linarith
  have h7 : ordOfPlace E Q.1 Q.2 r = 0 → 0 ≤ ordOfPlace E Q.1 Q.2 (r - 1) := by
    intro ha
    have h := h3
    rw [ha, min_self] at h
    linarith
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The pointwise "indicator" identity for the order of `r`. -/
lemma ordO_self_eq (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {r : Func E} (hr0 : r ≠ 0) (hr1 : r - 1 ≠ 0) :
    ordOfPlace E Q.1 Q.2 r = (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r else 0) +
      (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r else 0) := by
  by_cases h : 0 < ordOfPlace E Q.1 Q.2 r
  · rw [if_pos h, if_neg (by omega : ¬ ordOfPlace E Q.1 Q.2 r < 0), add_zero]
  · rw [if_neg h]
    by_cases h' : ordOfPlace E Q.1 Q.2 r < 0
    · rw [if_pos h', zero_add]
    · rw [if_neg h', add_zero]
      exact le_antisymm (le_of_not_gt h) (le_of_not_gt h')

/-- The pointwise "indicator" identity for the order of `r - 1`, using the trichotomy: at a place
where `r` has a pole, `r - 1` has the same order. -/
lemma ordO_sub_one_eq (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {r : Func E} (hr0 : r ≠ 0) (hr1 : r - 1 ≠ 0) :
    ordOfPlace E Q.1 Q.2 (r - 1) =
      (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1) else 0) +
      (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r else 0) := by
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := ordO_trich E H Q hr0 hr1
  by_cases hb : 0 < ordOfPlace E Q.1 Q.2 (r - 1)
  · have ha0 : ordOfPlace E Q.1 Q.2 r = 0 := h5 hb
    rw [if_pos hb, ha0, if_neg (lt_irrefl (0:ℤ)), add_zero]
  · rw [if_neg hb]
    by_cases ha : ordOfPlace E Q.1 Q.2 r < 0
    · have hba : ordOfPlace E Q.1 Q.2 (r - 1) = ordOfPlace E Q.1 Q.2 r := h6 ha
      rw [if_pos ha, hba, zero_add]
    · rw [if_neg ha]
      rcases lt_or_eq_of_le (le_of_not_gt ha) with ha' | ha'
      · have hb0 : ordOfPlace E Q.1 Q.2 (r - 1) = 0 := h4 ha'
        rw [hb0]
        simp
      · have hb0 : ordOfPlace E Q.1 Q.2 (r - 1) = 0 :=
          le_antisymm (le_of_not_gt hb) (h7 ha'.symm)
        rw [hb0]
        first | refl_ring1 | ring

/-- **Pointwise bound for the order of `D r`.**  At a place where `r` has a zero of order `a > 0`
(so `r - 1` is a unit), where `r - 1` has a zero of order `b > 0` (so `r` is a unit), where `r`
has a pole of order `a < 0` (and `r - 1` has the same order), or where both are units, the order
of `D r` is bounded below by the corresponding order minus one (by `0` in the last case). -/
lemma ordO_Dr_bound (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (D : Derivation N (Func E) (Func E))
    (hb1 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      ordOfPlace E S hS f - 1 ≤ ordOfPlace E S hS (D f))
    (hb2 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      ordOfPlace E S hS f = 0 → 0 ≤ ordOfPlace E S hS (D f))
    (Q : Place N E) {r : Func E} (hr0 : r ≠ 0) (hr1 : r - 1 ≠ 0) :
    (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1 else 0) +
        (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) +
        (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0) ≤
      ordOfPlace E Q.1 Q.2 (D r) := by
  have hDsub : D (r - 1) = D r := by
    rw [map_sub, Derivation.map_one_eq_zero, sub_zero]
  have hb1' : ordOfPlace E Q.1 Q.2 r - 1 ≤ ordOfPlace E Q.1 Q.2 (D r) := hb1 Q.1 Q.2 r
  have hb1'' : ordOfPlace E Q.1 Q.2 (r - 1) - 1 ≤ ordOfPlace E Q.1 Q.2 (D r) := by
    have h := hb1 Q.1 Q.2 (r - 1)
    rwa [hDsub] at h
  have hb2' : ordOfPlace E Q.1 Q.2 r = 0 → 0 ≤ ordOfPlace E Q.1 Q.2 (D r) := hb2 Q.1 Q.2 r
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := ordO_trich E H Q hr0 hr1
  by_cases ha : 0 < ordOfPlace E Q.1 Q.2 r
  · have hb0 : ordOfPlace E Q.1 Q.2 (r - 1) = 0 := h4 ha
    have e1 : (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1 else 0)
        = ordOfPlace E Q.1 Q.2 r - 1 := if_pos ha
    have e2 : (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then
        ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) = 0 :=
      if_neg (show ¬ 0 < ordOfPlace E Q.1 Q.2 (r - 1) by rw [hb0]; exact lt_irrefl 0)
    have e3 : (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0)
        = 0 := if_neg (show ¬ ordOfPlace E Q.1 Q.2 r < 0 by omega)
    rw [e1, e2, e3]
    simpa using hb1'
  · by_cases hb : 0 < ordOfPlace E Q.1 Q.2 (r - 1)
    · have ha0 : ordOfPlace E Q.1 Q.2 r = 0 := h5 hb
      have e1 : (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1 else 0)
          = 0 := if_neg ha
      have e2 : (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then
          ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) = ordOfPlace E Q.1 Q.2 (r - 1) - 1 :=
        if_pos hb
      have e3 : (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0)
          = 0 := if_neg (show ¬ ordOfPlace E Q.1 Q.2 r < 0 by rw [ha0]; exact lt_irrefl 0)
      rw [e1, e2, e3]
      simpa using hb1''
    · rcases lt_or_eq_of_le (le_of_not_gt ha) with ha' | ha'
      · have e1 : (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1 else 0)
            = 0 := if_neg ha
        have e2 : (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then
            ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) = 0 := if_neg hb
        have e3 : (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0)
            = ordOfPlace E Q.1 Q.2 r - 1 := if_pos ha'
        rw [e1, e2, e3]
        simpa using hb1'
      · have hb0 : ordOfPlace E Q.1 Q.2 (r - 1) = 0 :=
          le_antisymm (le_of_not_gt hb) (h7 ha')
        have e1 : (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1 else 0)
            = 0 := if_neg ha
        have e2 : (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then
            ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) = 0 :=
          if_neg (show ¬ 0 < ordOfPlace E Q.1 Q.2 (r - 1) by rw [hb0]; exact lt_irrefl 0)
        have e3 : (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0)
            = 0 := if_neg (show ¬ ordOfPlace E Q.1 Q.2 r < 0 by rw [ha']; exact lt_irrefl 0)
        rw [e1, e2, e3]
        simpa using hb2' ha'

/-- **Divisibility of the orders at a zero or a pole.**  If `5 ∣ ord r(r-1)` at a place and
`r, r - 1 ≠ 0`, then the order of `r` at a zero of `r`, the order of `r - 1` at a zero of `r - 1`
and the order of `r` at a pole of `r` are all divisible by `5`. -/
lemma dvd_of_dvd_ordO_mul (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {r : Func E} (hr0 : r ≠ 0) (hr1 : r - 1 ≠ 0)
    (hdiv : 5 ∣ ordOfPlace E Q.1 Q.2 (r * (r - 1))) :
    (0 < ordOfPlace E Q.1 Q.2 r → (5:ℤ) ∣ ordOfPlace E Q.1 Q.2 r) ∧
      (0 < ordOfPlace E Q.1 Q.2 (r - 1) → (5:ℤ) ∣ ordOfPlace E Q.1 Q.2 (r - 1)) ∧
      (ordOfPlace E Q.1 Q.2 r < 0 → (5:ℤ) ∣ ordOfPlace E Q.1 Q.2 r) := by
  have hmul : ordOfPlace E Q.1 Q.2 (r * (r - 1)) =
      ordOfPlace E Q.1 Q.2 r + ordOfPlace E Q.1 Q.2 (r - 1) :=
    H.ord_mul Q.1 Q.2 r (r - 1) hr0 hr1
  rw [hmul] at hdiv
  obtain ⟨-, -, -, h4, h5, h6, -⟩ := ordO_trich E H Q hr0 hr1
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    rw [h4 ha, add_zero] at hdiv
    exact hdiv
  · intro hb
    rw [h5 hb, zero_add] at hdiv
    exact hdiv
  · intro ha
    have hb : ordOfPlace E Q.1 Q.2 (r - 1) = ordOfPlace E Q.1 Q.2 r := h6 ha
    rw [hb] at hdiv
    have h2 : (5:ℤ) ∣ 2 * ordOfPlace E Q.1 Q.2 r := by
      have : ordOfPlace E Q.1 Q.2 r + ordOfPlace E Q.1 Q.2 r =
          2 * ordOfPlace E Q.1 Q.2 r := by ring
      rwa [this] at hdiv
    have hp : Prime (5:ℤ) := by norm_num
    rcases (hp.dvd_mul.mp h2) with h | h
    · exact absurd h (by norm_num)
    · exact h

/-- **The Hurwitz count.**  Under the hypotheses of the count step (a derivation with the two
local bounds, a `deg div = 0` principle, and a function `r` with `D r ≠ 0` whose values
`r(r-1)` have order divisible by `5` at every place where `r`, `r - 1` or `D r` can have a zero
or a pole), `r` has order zero at every rational place. -/
theorem derivCount (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E) (D : Derivation N (Func E) (Func E))
    (hb1 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      ordOfPlace E S hS f - 1 ≤ ordOfPlace E S hS (D f))
    (hb2 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      ordOfPlace E S hS f = 0 → 0 ≤ ordOfPlace E S hS (D f))
    (hDeg : ∀ (f : Func E), f ≠ 0 → ∀ S : Finset (Place N E),
      (∀ Q : Place N E, ordP E Q f ≠ 0 → Q ∈ S) → ordSum E S f = 0)
    (r : Func E) (hDr : D r ≠ 0) (S : Finset (Place N E))
    (hS : ∀ Q : Place N E, Q ∉ S → ordP E Q r = 0 ∧ ordP E Q (r - 1) = 0 ∧
      ordP E Q (D r) = 0)
    (hdiv : ∀ Q ∈ S, 5 ∣ ordP E Q (r * (r - 1))) :
    ∀ Q : Place N E, ordP E Q r = 0 := by
  have hr0 : r ≠ 0 := fun h => hDr (by rw [h, Derivation.map_zero])
  have hr1 : r - 1 ≠ 0 := by
    intro h
    have hr : r = 1 := sub_eq_zero.mp h
    exact hDr (by rw [hr, Derivation.map_one_eq_zero])
  simp only [ordP] at hS hdiv
  have hsumR : ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 r = 0 := by
    have h := hDeg r hr0 S (fun Q hQ => by
      by_contra hnot
      exact hQ (hS Q hnot).1)
    simpa [ordSum, ordP] using h
  have hsumB : ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 (r - 1) = 0 := by
    have h := hDeg (r - 1) hr1 S (fun Q hQ => by
      by_contra hnot
      exact hQ (hS Q hnot).2.1)
    simpa [ordSum, ordP] using h
  have hsumM : ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 (D r) = 0 := by
    have h := hDeg (D r) hDr S (fun Q hQ => by
      by_contra hnot
      exact hQ (hS Q hnot).2.2)
    simpa [ordSum, ordP] using h
  let Z : Finset (Place N E) := S.filter (fun Q => 0 < ordOfPlace E Q.1 Q.2 r)
  let W : Finset (Place N E) := S.filter (fun Q => 0 < ordOfPlace E Q.1 Q.2 (r - 1))
  let P : Finset (Place N E) := S.filter (fun Q => ordOfPlace E Q.1 Q.2 r < 0)
  have memZ : ∀ Q : Place N E, Q ∈ Z ↔ Q ∈ S ∧ 0 < ordOfPlace E Q.1 Q.2 r := by
    intro Q; simp only [Z, Finset.mem_filter]
  have memW : ∀ Q : Place N E, Q ∈ W ↔ Q ∈ S ∧ 0 < ordOfPlace E Q.1 Q.2 (r - 1) := by
    intro Q; simp only [W, Finset.mem_filter]
  have memP : ∀ Q : Place N E, Q ∈ P ↔ Q ∈ S ∧ ordOfPlace E Q.1 Q.2 r < 0 := by
    intro Q; simp only [P, Finset.mem_filter]
  have hsumZr : ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 r =
      (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) + ∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r := by
    calc ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 r
        = ∑ Q ∈ S, ((if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r else 0) +
            (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r else 0)) :=
          Finset.sum_congr rfl (fun Q _ => ordO_self_eq E H Q hr0 hr1)
      _ = (∑ Q ∈ S, (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r else 0)) +
            ∑ Q ∈ S, (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r else 0) :=
          Finset.sum_add_distrib
      _ = (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) + ∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r := by
          simp only [Z, P, Finset.sum_filter]
  have hsumWb : ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 (r - 1) =
      (∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1)) + ∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r := by
    calc ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 (r - 1)
        = ∑ Q ∈ S, ((if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1)
              else 0) +
            (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r else 0)) :=
          Finset.sum_congr rfl (fun Q _ => ordO_sub_one_eq E H Q hr0 hr1)
      _ = (∑ Q ∈ S, (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1)
              else 0)) +
            ∑ Q ∈ S, (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r else 0) :=
          Finset.sum_add_distrib
      _ = (∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1)) + ∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r := by
          simp only [W, P, Finset.sum_filter]
  have hPrel : ∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r = -(∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) := by
    have h1 := hsumZr
    rw [hsumR] at h1
    linarith
  have hWrel : ∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1) = ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := by
    have h1 := hsumWb
    rw [hsumB] at h1
    linarith
  have hsum_bnd : ∑ Q ∈ S, ((if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1
        else 0) +
      (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) +
      (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0)) ≤
      ∑ Q ∈ S, ordOfPlace E Q.1 Q.2 (D r) :=
    Finset.sum_le_sum fun Q _ => ordO_Dr_bound E H D hb1 hb2 Q hr0 hr1
  have hsum_ind1 : ∑ Q ∈ S, (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1
        else 0) = (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) - (Z.card : ℤ) := by
    rw [← Finset.sum_filter (s := S) (p := fun Q => 0 < ordOfPlace E Q.1 Q.2 r)
      (f := fun Q => ordOfPlace E Q.1 Q.2 r - 1)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_ind2 : ∑ Q ∈ S, (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then
        ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) =
      (∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1)) - (W.card : ℤ) := by
    rw [← Finset.sum_filter (s := S) (p := fun Q => 0 < ordOfPlace E Q.1 Q.2 (r - 1))
      (f := fun Q => ordOfPlace E Q.1 Q.2 (r - 1) - 1)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_ind3 : ∑ Q ∈ S, (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1
        else 0) = (∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r) - (P.card : ℤ) := by
    rw [← Finset.sum_filter (s := S) (p := fun Q => ordOfPlace E Q.1 Q.2 r < 0)
      (f := fun Q => ordOfPlace E Q.1 Q.2 r - 1)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_ind : ∑ Q ∈ S, ((if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1
        else 0) +
      (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) +
      (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0)) =
      ((∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) - (Z.card : ℤ)) +
      ((∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1)) - (W.card : ℤ)) +
      ((∑ Q ∈ P, ordOfPlace E Q.1 Q.2 r) - (P.card : ℤ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_ind1, hsum_ind2, hsum_ind3]
  have hZn : 5 * (Z.card : ℤ) ≤ ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := by
    have hpt : ∀ Q ∈ Z, (5:ℤ) ≤ ordOfPlace E Q.1 Q.2 r := by
      intro Q hQ
      obtain ⟨hQ', ha⟩ := (memZ Q).mp hQ
      exact Int.le_of_dvd ha ((dvd_of_dvd_ordO_mul E H Q hr0 hr1 (hdiv Q hQ')).1 ha)
    calc 5 * (Z.card : ℤ) = ∑ _Q ∈ Z, (5:ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := Finset.sum_le_sum hpt
  have hWn : 5 * (W.card : ℤ) ≤ ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := by
    have hpt : ∀ Q ∈ W, (5:ℤ) ≤ ordOfPlace E Q.1 Q.2 (r - 1) := by
      intro Q hQ
      obtain ⟨hQ', hb⟩ := (memW Q).mp hQ
      exact Int.le_of_dvd hb ((dvd_of_dvd_ordO_mul E H Q hr0 hr1 (hdiv Q hQ')).2.1 hb)
    have hsumW : 5 * (W.card : ℤ) ≤ ∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1) := by
      calc 5 * (W.card : ℤ) = ∑ _Q ∈ W, (5:ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ Q ∈ W, ordOfPlace E Q.1 Q.2 (r - 1) := Finset.sum_le_sum hpt
    rwa [hWrel] at hsumW
  have hPn : 5 * (P.card : ℤ) ≤ ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := by
    have hpt : ∀ Q ∈ P, (5:ℤ) ≤ -ordOfPlace E Q.1 Q.2 r := by
      intro Q hQ
      obtain ⟨hQ', ha⟩ := (memP Q).mp hQ
      have hd : (5:ℤ) ∣ ordOfPlace E Q.1 Q.2 r :=
        (dvd_of_dvd_ordO_mul E H Q hr0 hr1 (hdiv Q hQ')).2.2 ha
      exact Int.le_of_dvd (by omega) (dvd_neg.mpr hd)
    have hsumP : 5 * (P.card : ℤ) ≤ ∑ Q ∈ P, -ordOfPlace E Q.1 Q.2 r := by
      calc 5 * (P.card : ℤ) = ∑ _Q ∈ P, (5:ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ Q ∈ P, -ordOfPlace E Q.1 Q.2 r := Finset.sum_le_sum hpt
    have hnegsum : ∑ Q ∈ P, -ordOfPlace E Q.1 Q.2 r = ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := by
      rw [Finset.sum_neg_distrib, hPrel]
      first | refl_ring1 | ring
    rwa [hnegsum] at hsumP
  have hcard_le : 5 * ((Z.card : ℤ) + (W.card : ℤ) + (P.card : ℤ)) ≤
      3 * (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) := by linarith
  have hnonneg : (0:ℤ) ≤ ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r := by
    refine Finset.sum_nonneg fun Q hQ => ?_
    exact le_of_lt ((memZ Q).mp hQ).2
  have hfinal : ∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r = 0 := by
    have h4 := hsum_bnd
    rw [hsumM] at h4
    rw [hsum_ind] at h4
    rw [hWrel, hPrel] at h4
    have hnle : (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) ≤
        (Z.card : ℤ) + (W.card : ℤ) + (P.card : ℤ) := by linarith
    have h5n : 5 * (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) ≤
        5 * ((Z.card : ℤ) + (W.card : ℤ) + (P.card : ℤ)) := by linarith
    have h2n : 2 * (∑ Q ∈ Z, ordOfPlace E Q.1 Q.2 r) ≤ 0 := by linarith
    linarith
  intro Q
  show ordP E Q r = 0
  by_cases hQ : Q ∈ S
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hQmem : Q ∈ P := (memP Q).mpr ⟨hQ, hlt⟩
      have hpos : 0 < ∑ Q' ∈ P, -ordOfPlace E Q'.1 Q'.2 r := by
        refine Finset.sum_pos (fun Q' hQ' => ?_) ⟨Q, hQmem⟩
        have := ((memP Q').mp hQ').2
        omega
      have hzero : ∑ Q' ∈ P, -ordOfPlace E Q'.1 Q'.2 r = 0 := by
        rw [Finset.sum_neg_distrib, hPrel, neg_neg]
        exact hfinal
      linarith
    · have hQmem : Q ∈ Z := (memZ Q).mpr ⟨hQ, hgt⟩
      have hpos : 0 < ∑ Q' ∈ Z, ordOfPlace E Q'.1 Q'.2 r := by
        refine Finset.sum_pos (fun Q' hQ' => ?_) ⟨Q, hQmem⟩
        exact ((memZ Q').mp hQ').2
      linarith
  · exact (hS Q hQ).1

end

end Work.MotV
