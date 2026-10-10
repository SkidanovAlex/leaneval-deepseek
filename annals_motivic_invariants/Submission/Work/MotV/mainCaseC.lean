import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.invDerivOnA
import Submission.Work.MotV.supportAff
import Submission.Work.MotV.supportInf
import Submission.Work.MotV.degreeZero
import Submission.Work.MotV.regularConst
import Submission.Work.MotV.derivMain
import Submission.Work.MotV.derivCount
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV.mainCaseC`: the counting case of the Hurwitz-lite node over an algebraically
closed field

`mainCaseC` is the critical-path node of route V: over an algebraically closed field, an element
`r` of the function field `N(E)` of an elliptic curve with `D r ≠ 0` (for the invariant
derivation `D`) whose value `r * (r - 1)` is a fifth power at every place is constant.

The proof has three parts.

* `exists_support_finset'`: the support of a non-zero element of `N(E)` is contained in a finite
  set of rational places (write it as `α / β` with `α, β` in the affine coordinate ring, and use
  `Work.MotV.suppAlg` for the two coordinate-ring elements).
* `derivCountCond'`: the Hurwitz count (`Work.MotV.derivCount`), in the form in which the local
  theory produces the bound on `D` — only for functions with `D f ≠ 0`.  It is the proof of
  `derivCount` with the single helper `ordO_Dr_bound` replaced by `ordO_Dr_bound_cond`.
* the value step (the body of `mainCaseC` below): if `r - c` were non-zero for the value `c` of
  `r` at the point at infinity, it would be regular everywhere with a zero at infinity, which the
  degree-zero principle `hDeg` forbids.
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

open Work.MotC2

noncomputable section

set_option linter.style.haveILetI false

variable {N : Type*} [Field N]

private lemma ordO_Dr_bound_cond (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (D : Derivation N (Func E) (Func E))
    (hb1 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      D f ≠ 0 → ordOfPlace E S hS f - 1 ≤ ordOfPlace E S hS (D f))
    (hb2 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      ordOfPlace E S hS f = 0 → 0 ≤ ordOfPlace E S hS (D f))
    (Q : Place N E) {r : Func E} (hr0 : r ≠ 0) (hr1 : r - 1 ≠ 0) (hDr : D r ≠ 0) :
    (if 0 < ordOfPlace E Q.1 Q.2 r then ordOfPlace E Q.1 Q.2 r - 1 else 0) +
        (if 0 < ordOfPlace E Q.1 Q.2 (r - 1) then ordOfPlace E Q.1 Q.2 (r - 1) - 1 else 0) +
        (if ordOfPlace E Q.1 Q.2 r < 0 then ordOfPlace E Q.1 Q.2 r - 1 else 0) ≤
      ordOfPlace E Q.1 Q.2 (D r) := by
  have hDsub : D (r - 1) = D r := by
    rw [map_sub, Derivation.map_one_eq_zero, sub_zero]
  have hb1' : ordOfPlace E Q.1 Q.2 r - 1 ≤ ordOfPlace E Q.1 Q.2 (D r) := hb1 Q.1 Q.2 r hDr
  have hb1'' : ordOfPlace E Q.1 Q.2 (r - 1) - 1 ≤ ordOfPlace E Q.1 Q.2 (D r) := by
    have h := hb1 Q.1 Q.2 (r - 1) (by rw [hDsub]; exact hDr)
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


/-- **The Hurwitz count.**  Under the hypotheses of the count step (a derivation with the two
local bounds, a `deg div = 0` principle, and a function `r` with `D r ≠ 0` whose values
`r(r-1)` have order divisible by `5` at every place where `r`, `r - 1` or `D r` can have a zero
or a pole), `r` has order zero at every rational place. -/
private theorem derivCountCond' (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E) (D : Derivation N (Func E) (Func E))
    (hb1 : ∀ (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (f : Func E),
      D f ≠ 0 → ordOfPlace E S hS f - 1 ≤ ordOfPlace E S hS (D f))
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
    Finset.sum_le_sum fun Q _ => ordO_Dr_bound_cond E H D hb1 hb2 Q hr0 hr1 hDr
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

private lemma mem_ptsOf_of_suppAlg (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E)
    (γ : CoordinateRing E) (hγ : γ ≠ 0) (Q : Place N E)
    (hQ : ordP E Q (algebraMap (CoordinateRing E) (Func E) γ) ≠ 0) :
    Q ∈ ptsOf E H.infRat (Algebra.norm (Polynomial N) γ) := by
  classical
  rcases suppAlg E H γ hγ Q hQ with h | ⟨a, ha, hQa⟩
  · rw [show Q = ⟨MotC2.infPlace E, H.infRat⟩ from Subtype.ext h]
    simp [ptsOf]
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨a, ha, hQa⟩))

private lemma exists_support_finset' (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E) (f : Func E) (hf : f ≠ 0) :
    ∃ S : Finset (Place N E), ∀ Q : Place N E, ordP E Q f ≠ 0 → Q ∈ S := by
  classical
  obtain ⟨a, b, hbmem, hfeq⟩ := IsFractionRing.div_surjective (CoordinateRing E) f
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbmem
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hfeq
    exact hf hfeq.symm
  refine ⟨ptsOf E H.infRat (Algebra.norm (Polynomial N) a) ∪
    ptsOf E H.infRat (Algebra.norm (Polynomial N) b), ?_⟩
  intro Q hQ
  have ha' : algebraMap (CoordinateRing E) (Func E) a ≠ 0 :=
    fun h => ha (IsFractionRing.injective (CoordinateRing E) (Func E) (by simpa using h))
  have hb' : algebraMap (CoordinateRing E) (Func E) b ≠ 0 :=
    fun h => hb (IsFractionRing.injective (CoordinateRing E) (Func E) (by simpa using h))
  have hord : ordP E Q f =
      ordP E Q (algebraMap (CoordinateRing E) (Func E) a) -
        ordP E Q (algebraMap (CoordinateRing E) (Func E) b) := by
    simp only [ordP]
    rw [← hfeq, div_eq_mul_inv,
      H.ord_mul Q.1 Q.2 _ _ ha' (inv_ne_zero hb'), H.ord_inv Q.1 Q.2 _ hb']
    first | refl_ring1 | ring
  rw [Finset.mem_union]
  by_cases hAa : ordP E Q (algebraMap (CoordinateRing E) (Func E) a) = 0
  · right
    have hb0 : ordP E Q (algebraMap (CoordinateRing E) (Func E) b) ≠ 0 := by
      intro hB0
      exact hQ (by rw [hord, hAa, hB0, sub_zero])
    exact mem_ptsOf_of_suppAlg E H b hb Q hb0
  · left
    exact mem_ptsOf_of_suppAlg E H a ha Q hAa

private lemma ordOfPlace_zero (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) : ordOfPlace E S hS (0 : MotC2.Func E) = 0 := by
  have : IsDiscreteValuationRing ↥S := hS.1.choose
  rw [ordOfPlace_eq_ordPlace E S hS (0 : MotC2.Func E)]
  exact ordPlace_zero E S hS

theorem mainCaseC {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N)
    [E.IsElliptic]
    (H : Work.MotV.H1Data N E)
    (hDeg : ∀ (f : Work.MotC2.Func E), f ≠ 0 → ∀ S : Finset (Work.MotV.Place N E),
      (∀ Q : Work.MotV.Place N E, Work.MotV.ordP E Q f ≠ 0 → Q ∈ S) →
        Work.MotV.ordSum E S f = 0)
    (hSupAff : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 → ∀ (c d : N)
      (h : WeierstrassCurve.Affine.Nonsingular E c d),
      0 ≤ Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) (Work.MotC2.AffPlace N E c d h).1
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) ∧
        (0 < Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d)
              (Work.MotC2.AffPlace N E c d h).1
              (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) →
          (Algebra.norm (Polynomial N) a).IsRoot c))
    (hSupInf : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 →
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a)
        = - ((Algebra.norm (Polynomial N) a).natDegree : ℤ))
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hDy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E)
    (hDA : ∀ a : WeierstrassCurve.Affine.CoordinateRing E,
      ∃ b : WeierstrassCurve.Affine.CoordinateRing E,
        algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) b =
          D (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a))
    (hb1 : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E), D f ≠ 0 →
      Work.MotV.ordOfPlace E S hS f - 1 ≤ Work.MotV.ordOfPlace E S hS (D f))
    (hb2 : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E),
      Work.MotV.ordOfPlace E S hS f = 0 → 0 ≤ Work.MotV.ordOfPlace E S hS (D f))
    (r : Work.MotC2.Func E) (hDr : D r ≠ 0)
    (hr : Work.MotV.FifthPowerValued N (r * (r - 1))) :
    ∃ c : N, algebraMap N (Work.MotC2.Func E) c = r := by
  classical
  have hr0 : r ≠ 0 := fun h => hDr (by rw [h, Derivation.map_zero])
  have hr1 : r - 1 ≠ 0 := fun h => hDr (by rw [sub_eq_zero.mp h, Derivation.map_one_eq_zero])
  obtain ⟨S₁, hS₁⟩ := exists_support_finset' E H r hr0
  obtain ⟨S₂, hS₂⟩ := exists_support_finset' E H (r - 1) hr1
  obtain ⟨S₃, hS₃⟩ := exists_support_finset' E H (D r) hDr
  let S : Finset (Work.MotV.Place N E) := S₁ ∪ S₂ ∪ S₃
  have hS : ∀ Q : Work.MotV.Place N E, Q ∉ S → Work.MotV.ordP E Q r = 0 ∧
      Work.MotV.ordP E Q (r - 1) = 0 ∧ Work.MotV.ordP E Q (D r) = 0 := by
    intro Q hQ
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      exact hQ (by simp only [S, Finset.mem_union]; exact Or.inl (Or.inl (hS₁ Q h)))
    · by_contra h
      exact hQ (by simp only [S, Finset.mem_union]; exact Or.inl (Or.inr (hS₂ Q h)))
    · by_contra h
      exact hQ (by simp only [S, Finset.mem_union]; exact Or.inr (hS₃ Q h))
  have hdiv : ∀ Q ∈ S, 5 ∣ Work.MotV.ordP E Q (r * (r - 1)) := fun Q _ =>
    H.fifth Q.1 Q.2 (r * (r - 1)) hr
  have hcount : ∀ Q : Work.MotV.Place N E, Work.MotV.ordP E Q r = 0 :=
    derivCountCond' E H D hb1 hb2 hDeg r hDr S hS hdiv
  have hmem : r ∈ Work.MotC2.infPlace E :=
    (H.ord_nonneg (Work.MotC2.infPlace E) H.infRat r).mp
      (by
        show (0:ℤ) ≤ Work.MotV.ordP E ⟨Work.MotC2.infPlace E, H.infRat⟩ r
        rw [hcount ⟨Work.MotC2.infPlace E, H.infRat⟩])
  obtain ⟨c, hc | hc⟩ := infValue E H hmem
  · exact ⟨c, hc.symm⟩
  · exfalso
    have hγne : r - algebraMap N (Work.MotC2.Func E) c ≠ 0 := by
      intro hz
      have h0 : Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
          (r - algebraMap N (Work.MotC2.Func E) c) = 0 := by
        rw [hz]
        exact ordOfPlace_zero E (Work.MotC2.infPlace E) H.infRat
      omega
    have hreg : ∀ Q : Work.MotV.Place N E,
        0 ≤ Work.MotV.ordP E Q (r - algebraMap N (Work.MotC2.Func E) c) := by
      intro Q
      have hne : r + (-(algebraMap N (Work.MotC2.Func E) c)) ≠ 0 := by
        rw [show r + (-(algebraMap N (Work.MotC2.Func E) c)) =
          r - algebraMap N (Work.MotC2.Func E) c from by ring]
        exact hγne
      have h1 := H.ord_add Q.1 Q.2 r (-(algebraMap N (Work.MotC2.Func E) c)) hne
      rw [show r + (-(algebraMap N (Work.MotC2.Func E) c)) =
        r - algebraMap N (Work.MotC2.Func E) c from by ring] at h1
      have h2 : (0:ℤ) ≤ Work.MotV.ordOfPlace E Q.1 Q.2 r := by
        show (0:ℤ) ≤ Work.MotV.ordP E Q r
        rw [hcount Q]
      have h3 : (0:ℤ) ≤ Work.MotV.ordOfPlace E Q.1 Q.2
          (-(algebraMap N (Work.MotC2.Func E) c)) :=
        (H.ord_nonneg Q.1 Q.2 _).mpr (Subalgebra.neg_mem _ (Subalgebra.algebraMap_mem _ c))
      exact le_trans (le_min h2 h3) h1
    obtain ⟨S', hS'⟩ := exists_support_finset' E H (r - algebraMap N (Work.MotC2.Func E) c) hγne
    have hpos : (0:ℤ) < Work.MotV.ordP E ⟨Work.MotC2.infPlace E, H.infRat⟩
        (r - algebraMap N (Work.MotC2.Func E) c) := by
      show (0:ℤ) < Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
        (r - algebraMap N (Work.MotC2.Func E) c)
      omega
    have hinfmem : (⟨Work.MotC2.infPlace E, H.infRat⟩ : Work.MotV.Place N E) ∈ S' :=
      hS' _ (ne_of_gt hpos)
    have hsumpos : 0 < Work.MotV.ordSum E S' (r - algebraMap N (Work.MotC2.Func E) c) := by
      rw [Work.MotV.ordSum]
      exact Finset.sum_pos' (fun Q _ => hreg Q)
        ⟨⟨Work.MotC2.infPlace E, H.infRat⟩, hinfmem, hpos⟩
    have hsum := hDeg (r - algebraMap N (Work.MotC2.Func E) c) hγne S' hS'
    rw [hsum] at hsumpos
    exact (lt_irrefl (0:ℤ)) hsumpos

end

end Work.MotV
