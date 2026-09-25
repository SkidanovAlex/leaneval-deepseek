import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.major_arc_bound_pre
import Submission.Commons.Analysis.ExponentialSums.weyl_minor_arc_decay

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

/-!
# The major-arc model approximates the polynomial Weyl kernel uniformly

This file proves `Work.BourgainPlan.Maximal.model_pre`: for an integer polynomial `P` of degree
`d ≥ 2` with `c = P.leadingCoeff > 0`, at every scale `N` and every `θ ∈ [0,1]`,

`‖polyWeylKernel P N θ − polyMajorArcModelPre P (1/4) N θ‖ ≤ C N^{-c₀}`

with `c₀, C > 0` depending on `P`.  The two inputs are

* the major-arc approximation `major_arc_bound_pre` (Bourgain (1989), (6.10)) on a single arc,
  and
* the minor-arc decay `model_minor_arc` (Bourgain (1989), (5.7)) off the arc family;

the combinatorial glue is that for `N ≥ 3` the arc family `a/q + l`, `q ≤ N^{1/4}`,
`a < q`, `gcd a q = 1`, `l ∈ [-1, c]` (of radius `N^{-(d-1/4)}` around `cθ`) contains at most one
element, so the model collapses to that single term (or vanishes).
-/

/-! ## Numbers: separation of two distinct arc centres and reduced-fraction uniqueness -/

/-- Two distinct arc centres `a/q + l` and `a'/q' + l'` (`q, q' > 0`, `a < q`, `a' < q'`,
`l, l' : ℤ`) are at distance at least `1/(q q')`. -/
private lemma mp_shift_sep {q q' : ℕ} {a a' : ℕ} {l l' : ℤ}
    (hq : 0 < q) (hq' : 0 < q')
    (h : ((a:ℝ)/q + (l:ℝ)) ≠ ((a':ℝ)/q' + (l':ℝ))) :
    ((q:ℝ)*(q':ℝ))⁻¹ ≤ |(a:ℝ)/q + (l:ℝ) - ((a':ℝ)/q' + (l':ℝ))| := by
  set n : ℤ := (a:ℤ)*q' - (a':ℤ)*q + (l-l')*(q*q') with hn
  have hden : (0:ℝ) < (q:ℝ)*(q':ℝ) := by
    have h1 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    have h2 : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
    positivity
  have hrewrite : (a:ℝ)/q + (l:ℝ) - ((a':ℝ)/q' + (l':ℝ)) = (n:ℝ)/((q:ℝ)*(q':ℝ)) := by
    rw [hn]; push_cast; field_simp; ring
  have hn0 : n ≠ 0 := by
    intro hz
    have hsub : (a:ℝ)/q + (l:ℝ) - ((a':ℝ)/q' + (l':ℝ)) = 0 := by rw [hrewrite, hz]; simp
    exact h (sub_eq_zero.mp hsub)
  have hn1 : (1:ℤ) ≤ |n| := Int.one_le_abs hn0
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have hcast : ((|n| : ℤ) : ℝ) ≤ |(n:ℝ)| := by rw [Int.cast_abs]
    exact le_trans (by exact_mod_cast hn1) hcast
  rw [hrewrite, abs_div, abs_of_pos hden]
  rw [show ((q:ℝ)*(q':ℝ))⁻¹ = 1/((q:ℝ)*(q':ℝ)) by rw [one_div]]
  exact div_le_div_of_nonneg_right h1 hden.le

/-- Two equal fractions in lowest terms with `a < q`, `a' < q'` have equal numerators and
denominators. -/
private lemma mp_frac_eq {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (h₁ : Nat.Coprime a q) (h₂ : Nat.Coprime a' q') (ha : a < q) (ha' : a' < q')
    (h : (a:ℝ)/q = (a':ℝ)/q') : q = q' ∧ a = a' := by
  have hnat : a * q' = a' * q := by
    have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
    have hq'r : (q':ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq'
    have hreal : (a:ℝ) * q' = (a':ℝ) * q := by
      field_simp at h
      rw [mul_comm (q:ℝ) (a':ℝ)] at h
      exact h
    exact_mod_cast hreal
  have hdvd₁ : q ∣ q' := by
    have hd : q ∣ a * q' := ⟨a', by rw [hnat, mul_comm]⟩
    exact h₁.symm.dvd_of_dvd_mul_left hd
  have hdvd₂ : q' ∣ q := by
    have hd : q' ∣ a' * q := ⟨a, by rw [← hnat, mul_comm]⟩
    exact h₂.symm.dvd_of_dvd_mul_left hd
  have hqq : q = q' := Nat.dvd_antisymm hdvd₁ hdvd₂
  refine ⟨hqq, ?_⟩
  rw [hqq] at hnat
  exact Nat.mul_right_cancel hq' hnat

/-- **Uniqueness of the major-arc representation** at the radius `N^{-(d-1/4)}` for the
`c`-scaled arc family. -/
theorem model_arc_unique (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {N : ℕ} (hN : 3 ≤ N) (θ : ℝ) {q q' : ℕ} {a a' : ℕ} {l l' : ℤ}
    (hq : (q:ℝ) ≤ (N:ℝ)^((1:ℝ)/4)) (ha : a < q) (hg : Nat.gcd a q = 1)
    (hq' : (q':ℝ) ≤ (N:ℝ)^((1:ℝ)/4)) (ha' : a' < q') (hg' : Nat.gcd a' q' = 1)
    (h₁ : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
        ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)))
    (h₂ : |(P.leadingCoeff:ℝ)*θ - (a':ℝ)/(q':ℝ) - (l':ℝ)|
        ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))) :
    q = q' ∧ a = a' ∧ l = l' := by
  set R : ℝ := (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; exact Real.rpow_nonneg (by positivity) _
  have hq0 : 0 < q := by omega
  have hq0' : 0 < q' := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have htri : |((a:ℝ)/(q:ℝ) + (l:ℝ)) - ((a':ℝ)/(q':ℝ) + (l':ℝ))| ≤ 2 * R := by
    have hsp : ((a:ℝ)/(q:ℝ) + (l:ℝ)) - ((a':ℝ)/(q':ℝ) + (l':ℝ))
        = ((a:ℝ)/(q:ℝ) + (l:ℝ) - (P.leadingCoeff:ℝ)*θ)
          + ((P.leadingCoeff:ℝ)*θ - (a':ℝ)/(q':ℝ) - (l':ℝ)) := by ring
    rw [hsp]
    have haux : |(a:ℝ)/(q:ℝ) + (l:ℝ) - (P.leadingCoeff:ℝ)*θ| ≤ R := by
      have : (a:ℝ)/(q:ℝ) + (l:ℝ) - (P.leadingCoeff:ℝ)*θ
          = -((P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)) := by ring
      rw [this, abs_neg]; exact h₁
    calc |(a:ℝ)/(q:ℝ) + (l:ℝ) - (P.leadingCoeff:ℝ)*θ
            + ((P.leadingCoeff:ℝ)*θ - (a':ℝ)/(q':ℝ) - (l':ℝ))|
        ≤ |(a:ℝ)/(q:ℝ) + (l:ℝ) - (P.leadingCoeff:ℝ)*θ|
            + |(P.leadingCoeff:ℝ)*θ - (a':ℝ)/(q':ℝ) - (l':ℝ)| := abs_add_le _ _
      _ ≤ R + R := add_le_add haux h₂
      _ = 2 * R := by ring
  have hRlt : 2 * R < ((q:ℝ)*(q':ℝ))⁻¹ := by
    have hprod : (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^((1:ℝ)/2) := by
      calc (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^((1:ℝ)/4) * (N:ℝ)^((1:ℝ)/4) :=
            mul_le_mul hq hq' (by positivity) (by positivity)
        _ = (N:ℝ)^((1:ℝ)/2) := by rw [← Real.rpow_add hNpos]; norm_num
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have h1 : (N:ℝ)^(-((1:ℝ)/2)) ≤ ((q:ℝ)*(q':ℝ))⁻¹ := by
      have h1' : ((N:ℝ)^((1:ℝ)/2))⁻¹ ≤ ((q:ℝ)*(q':ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) hpos).mpr hprod
      rwa [← Real.rpow_neg hNpos.le ((1:ℝ)/2)] at h1'
    have h2 : 2 * R ≤ 2 * (N:ℝ)^(-(7/4:ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [hRdef]
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      have hd' : (2:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd
      linarith
    have h3 : 2 * (N:ℝ)^(-((7:ℝ)/4)) < (N:ℝ)^(-((1:ℝ)/2)) := by
      have hN54 : (2:ℝ) < (N:ℝ)^((5:ℝ)/4) := by
        have h3' : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        have h5' : (3:ℝ) < (N:ℝ)^((5:ℝ)/4) :=
          calc (3:ℝ) = (3:ℝ)^(1:ℝ) := (Real.rpow_one 3).symm
            _ < (3:ℝ)^((5:ℝ)/4) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
            _ ≤ (N:ℝ)^((5:ℝ)/4) := Real.rpow_le_rpow (by norm_num) h3' (by norm_num)
        linarith
      have h4 : (N:ℝ)^(-((7:ℝ)/4)) = (N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)) := by
        rw [← Real.rpow_add hNpos]; congr 1; ring
      have h5 : (N:ℝ)^(-((5:ℝ)/4)) = ((N:ℝ)^((5:ℝ)/4))⁻¹ := Real.rpow_neg hNpos.le ((5:ℝ)/4)
      have h1' : 2 * (N:ℝ)^(-((5:ℝ)/4)) < 1 := by
        rw [h5, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hNpos _)]
        exact hN54
      have h2' : (0:ℝ) < (N:ℝ)^(-((1:ℝ)/2)) := Real.rpow_pos_of_pos hNpos _
      rw [h4]
      calc 2 * ((N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)))
          = (N:ℝ)^(-((1:ℝ)/2)) * (2 * (N:ℝ)^(-((5:ℝ)/4))) := by ring
        _ < (N:ℝ)^(-((1:ℝ)/2)) * 1 := mul_lt_mul_of_pos_left h1' h2'
        _ = (N:ℝ)^(-((1:ℝ)/2)) := by ring
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h1)
  have hkey : ((a:ℝ)/(q:ℝ) + (l:ℝ)) = ((a':ℝ)/(q':ℝ) + (l':ℝ)) := by
    by_contra hne
    have hsep := mp_shift_sep hq0 hq0' hne
    linarith [hsep, htri, hRlt]
  have hleq : l = l' := by
    have hlr : ((l:ℝ) - (l':ℝ)) = (a':ℝ)/(q':ℝ) - (a:ℝ)/(q:ℝ) := by linarith
    have hbnd : |(l:ℝ) - (l':ℝ)| < 1 := by
      have h1' : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
      have h2' : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq0'
      have ha1 : (a:ℝ)/(q:ℝ) < 1 := by rw [div_lt_one h1']; exact_mod_cast ha
      have ha1' : (0:ℝ) ≤ (a:ℝ)/(q:ℝ) := by positivity
      have ha2 : (0:ℝ) ≤ (a':ℝ)/(q':ℝ) := by positivity
      have ha2' : (a':ℝ)/(q':ℝ) < 1 := by rw [div_lt_one h2']; exact_mod_cast ha'
      rw [hlr, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hml : ((l - l' : ℤ) : ℝ) = (l:ℝ) - (l':ℝ) := by push_cast; ring
    have hlt : (l - l' : ℤ) < 1 := by
      have : ((l - l' : ℤ) : ℝ) < 1 := by rw [hml]; exact (abs_lt.mp hbnd).2
      exact_mod_cast this
    have hgt : (-1 : ℤ) < l - l' := by
      have : (-1 : ℝ) < ((l - l' : ℤ) : ℝ) := by rw [hml]; exact (abs_lt.mp hbnd).1
      exact_mod_cast this
    omega
  have hfrac : (a:ℝ)/(q:ℝ) = (a':ℝ)/(q':ℝ) := by
    rw [hleq] at hkey
    linarith
  obtain ⟨hqeq, haeq⟩ := mp_frac_eq hq0 hq0' (Nat.coprime_iff_gcd_eq_one.mpr hg)
    (Nat.coprime_iff_gcd_eq_one.mpr hg') ha ha' hfrac
  exact ⟨hqeq, haeq, hleq⟩

/-! ## Collapse of the model -/

/-- If a valid arc triple exists, the model is that single term. -/
theorem model_eq_single (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {N : ℕ} (hN : 3 ≤ N) (θ : ℝ)
    (h : ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ∧
        x.2.1 < x.1 ∧ Nat.gcd x.2.1 x.1 = 1 ∧
        x.2.2 ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff ∧
        |(P.leadingCoeff : ℝ) * θ - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)|
          ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4))) :
    polyMajorArcModelPre P ((1:ℝ)/4) N θ
      = polyModelTermPre P N h.choose.1 h.choose.2.1 h.choose.2.2 θ := by
  obtain ⟨hq1, hqfl, ha, hgcd, hl, hdist⟩ := h.choose_spec
  have hfloorR : ∀ q : ℕ, q ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) →
      (q:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := by
    intro q hq
    have h1 : (q:ℝ) ≤ ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) := by exact_mod_cast hq
    have h2 : ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) :=
      Nat.floor_le (by positivity)
    linarith
  have hqR : (h.choose.1 : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := hfloorR _ hqfl
  have hblk : polyMajorArcBlockPre P ((1:ℝ)/4) N θ h.choose.1
      = polyModelTermPre P N h.choose.1 h.choose.2.1 h.choose.2.2 θ := by
    rw [polyMajorArcBlockPre]
    rw [Finset.sum_eq_single (s := Finset.range h.choose.1) (f := fun a =>
      (if Nat.gcd a h.choose.1 = 1 then
        ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
            then polyModelTermPre P N h.choose.1 a l θ else 0
        else 0 : ℂ)) h.choose.2.1
      (fun a hamem hane => by
        by_cases hgc : Nat.gcd a h.choose.1 = 1
        · rw [if_pos hgc]
          refine Finset.sum_eq_zero (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
                ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
              then polyModelTermPre P N h.choose.1 a l θ else 0 : ℂ)) (fun l hlmem => ?_)
          by_cases hc : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
                ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
          · rw [if_pos hc]
            exact absurd (model_arc_unique P hd hN θ
              (q := h.choose.1) (q' := h.choose.1) (a := a) (a' := h.choose.2.1)
              (l := l) (l' := h.choose.2.2)
              hqR (Finset.mem_range.mp hamem) hgc hqR ha hgcd hc hdist).2.1 hane
          · rw [if_neg hc]
        · rw [if_neg hgc])
      (fun hnot => absurd (Finset.mem_range.mpr ha) hnot)]
    rw [if_pos hgcd]
    rw [Finset.sum_eq_single (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
      (if |(P.leadingCoeff:ℝ)*θ - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
          ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
        then polyModelTermPre P N h.choose.1 h.choose.2.1 l θ else 0 : ℂ)) h.choose.2.2
      (fun l hlmem hlne => by
        by_cases hc : |(P.leadingCoeff:ℝ)*θ - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
        · rw [if_pos hc]
          exact absurd (model_arc_unique P hd hN θ
            (q := h.choose.1) (q' := h.choose.1) (a := h.choose.2.1) (a' := h.choose.2.1)
            (l := l) (l' := h.choose.2.2)
            hqR ha hgcd hqR ha hgcd hc hdist).2.2 hlne
        · rw [if_neg hc])
      (fun hnot => absurd hl hnot)]
    rw [if_pos hdist]
  rw [polyMajorArcModelPre]
  rw [Finset.sum_eq_single (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))))
    (f := polyMajorArcBlockPre P ((1:ℝ)/4) N θ) h.choose.1
    (fun q hqmem hqne => by
      rw [polyMajorArcBlockPre]
      refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
        (if Nat.gcd a q = 1 then
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
                ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
              then polyModelTermPre P N q a l θ else 0
          else 0 : ℂ)) (fun a hamem => ?_)
      by_cases hgc : Nat.gcd a q = 1
      · rw [if_pos hgc]
        refine Finset.sum_eq_zero (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
          (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
            then polyModelTermPre P N q a l θ else 0 : ℂ)) (fun l hlmem => ?_)
        by_cases hc : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
        · rw [if_pos hc]
          exact absurd (model_arc_unique P hd hN θ
            (q := q) (q' := h.choose.1) (a := a) (a' := h.choose.2.1)
            (l := l) (l' := h.choose.2.2)
            (hfloorR q (Finset.mem_Icc.mp hqmem).2)
            (Finset.mem_range.mp hamem) hgc hqR ha hgcd hc hdist).1 hqne
        · rw [if_neg hc]
      · rw [if_neg hgc])
    (fun hnot => absurd (Finset.mem_Icc.mpr ⟨hq1, hqfl⟩) hnot)]
  exact hblk

/-- If no valid arc triple exists, the model vanishes. -/
theorem model_eq_zero (P : Polynomial ℤ) {N : ℕ} (θ : ℝ)
    (h : ¬ ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ∧
        x.2.1 < x.1 ∧ Nat.gcd x.2.1 x.1 = 1 ∧
        x.2.2 ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff ∧
        |(P.leadingCoeff : ℝ) * θ - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)|
          ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4))) :
    polyMajorArcModelPre P ((1:ℝ)/4) N θ = 0 := by
  rw [polyMajorArcModelPre]
  refine Finset.sum_eq_zero (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))))
    (f := polyMajorArcBlockPre P ((1:ℝ)/4) N θ) (fun q hqmem => ?_)
  rw [polyMajorArcBlockPre]
  refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
    (if Nat.gcd a q = 1 then
      ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
        if |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
            ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
          then polyModelTermPre P N q a l θ else 0
      else 0 : ℂ)) (fun a hamem => ?_)
  by_cases hg : Nat.gcd a q = 1
  · rw [if_pos hg]
    refine Finset.sum_eq_zero (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
      (if |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
          ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
        then polyModelTermPre P N q a l θ else 0 : ℂ)) (fun l hlmem => ?_)
    by_cases hc : |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
          ≤ (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4))
    · rw [if_pos hc]
      exact absurd ⟨(q, a, l), (Finset.mem_Icc.mp hqmem).1, (Finset.mem_Icc.mp hqmem).2,
        Finset.mem_range.mp hamem, hg, hlmem, hc⟩ h
    · rw [if_neg hc]
  · rw [if_neg hg]

/-! ## Minor-arc decay -/

/-- **Minor-arc decay of the polynomial Weyl kernel** (non-monic form): off the arc family the
kernel is `≲ N^{-ν}`.  Proven from
`Commons.Analysis.ExponentialSums.weyl_minor_arc_decay` applied to the real polynomial
`θ • toRealPoly P`, exactly as `Commons.Analysis.ExponentialSums.pow_kernel_minor_arc_bound` does
it for `P = X^d`; the `l ∈ Icc (-1) c` restriction is absorbed by the size bound
`|cθ - a/q| ≥ 1` for the remaining integer shifts. -/
theorem model_minor_arc (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
      (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) → a < q →
        Nat.gcd a q = 1 → l ∈ Finset.Icc (-1) P.leadingCoeff →
        (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) < |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|) →
      ‖polyWeylKernel P N θ‖ ≤ C * (N:ℝ)^(-ν) := by
  obtain ⟨C, ν, hC0, hν0, hdecay⟩ :=
    Commons.Analysis.ExponentialSums.weyl_minor_arc_decay P.natDegree hd ((1:ℝ)/4)
      (by norm_num) (by norm_num)
  refine ⟨ν, C, hν0, hC0, fun N hN θ hθ0 hθ1 hnoarc => ?_⟩
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNlt : (1:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hθne : θ ≠ 0 := by
    intro h0
    have h := hnoarc 1 0 0 (by norm_num)
      (Nat.le_floor (by simpa using Real.one_le_rpow hN1 (by norm_num : (0:ℝ) ≤ 1/4)))
      (by norm_num) (by norm_num) (Finset.mem_Icc.mpr ⟨by norm_num, le_of_lt hc⟩)
    rw [h0] at h
    simp at h
    have hR : (0:ℝ) < (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) := Real.rpow_pos_of_pos hNr _
    rw [show (4:ℝ)⁻¹ - (P.natDegree:ℝ) = -((P.natDegree:ℝ) - (1:ℝ)/4) by ring] at h
    linarith
  have hminor : ∀ (q : ℤ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) →
      (N : ℝ) ^ (-((P.natDegree:ℝ) - (1:ℝ)/4)) <
        |(P.leadingCoeff:ℝ) * θ - (a : ℝ) / (q : ℝ)| := by
    intro q a hq hqle
    have hqpos : (0:ℤ) < q := by omega
    set r : ℤ := a % q with hr
    have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg a (ne_of_gt hqpos)
    have hrlt : r < q := hr ▸ Int.emod_lt_of_pos a hqpos
    set m : ℤ := a / q with hm
    have hdecZ : a = q * m + r := by
      have h := Int.mul_ediv_add_emod a q
      rw [← hm, ← hr] at h
      exact h.symm
    set rn : ℕ := r.toNat with hrn
    have hrcast : (rn : ℤ) = r := hrn ▸ Int.toNat_of_nonneg hr0
    have hqnat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
    have hrnlt : rn < q.toNat := by
      have hh : ((rn : ℤ)) < q := by rw [hrcast]; exact hrlt
      rw [← hqnat] at hh
      exact_mod_cast hh
    have hqnatpos : 0 < q.toNat := by
      have hh : (0:ℤ) < q := hqpos
      rw [← hqnat] at hh
      omega
    set g : ℕ := Nat.gcd rn q.toNat with hgg
    have hgq : g ∣ q.toNat := hgg ▸ Nat.gcd_dvd_right rn q.toNat
    have hgr : g ∣ rn := hgg ▸ Nat.gcd_dvd_left rn q.toNat
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgq hqnatpos
    set q₁ : ℕ := q.toNat / g with hq1
    set r₁ : ℕ := rn / g with hr1
    have hq1g : q₁ * g = q.toNat := hq1 ▸ Nat.div_mul_cancel hgq
    have hr1g : r₁ * g = rn := hr1 ▸ Nat.div_mul_cancel hgr
    have hcop : Nat.gcd r₁ q₁ = 1 := by
      have hpos : 0 < Nat.gcd rn q.toNat := by rw [← hgg]; exact hgpos
      have h := Nat.coprime_div_gcd_div_gcd (m := rn) (n := q.toNat) hpos
      rw [hq1, hr1]
      exact Nat.coprime_iff_gcd_eq_one.mp h
    have hr1lt : r₁ < q₁ := by
      have h3 : rn / g < q.toNat / g := Nat.div_lt_div_of_lt_of_dvd hgq hrnlt
      rw [hq1, hr1]; exact h3
    have hq1le : q₁ ≤ q.toNat := hq1 ▸ Nat.div_le_self q.toNat g
    have hq1leN : q₁ ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) := by
      refine Nat.le_floor ?_
      have h1 : (q₁:ℝ) ≤ (q.toNat:ℝ) := by exact_mod_cast hq1le
      have h3 : (q.toNat:ℝ) = (q:ℝ) := by exact_mod_cast hqnat
      rw [h3] at h1
      linarith [h1, hqle]
    have hfr : (r₁:ℝ)/(q₁:ℝ) = (rn:ℝ)/(q.toNat:ℝ) := by
      have h1 : (rn:ℝ) = (r₁:ℝ) * (g:ℝ) := by rw [← hr1g]; push_cast; ring
      have h2 : (q.toNat:ℝ) = (q₁:ℝ) * (g:ℝ) := by rw [← hq1g]; push_cast; ring
      rw [h1, h2]
      have hgne : (g:ℝ) ≠ 0 := by positivity
      field_simp
    have hfr2 : (rn:ℝ)/(q:ℝ) = (r₁:ℝ)/(q₁:ℝ) := by
      have hq' : (q:ℝ) = (q.toNat:ℝ) := by exact_mod_cast hqnat.symm
      rw [hfr, hq']
    have haq : (a:ℝ)/(q:ℝ) = (m:ℝ) + (r₁:ℝ)/(q₁:ℝ) := by
      have h1 : (a:ℝ) = (q:ℝ) * (m:ℝ) + (rn:ℝ) := by
        have hZ : a = q * m + ((rn:ℤ)) := by rw [hrcast]; exact hdecZ
        exact_mod_cast hZ
      have hqR : (0:ℝ) < (q:ℝ) := by
        have : (0:ℤ) < q := hqpos
        exact_mod_cast this
      rw [h1, add_div, mul_div_cancel_left₀ _ (ne_of_gt hqR), hfr2]
    have hq1pos : 1 ≤ q₁ := by
      rcases Nat.eq_zero_or_pos q₁ with h0 | hp
      · rw [h0, zero_mul] at hq1g
        omega
      · exact hp
    by_cases hmI : m ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff
    · have hh := hnoarc q₁ r₁ m hq1pos hq1leN hr1lt hcop hmI
      have habs : |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ)|
          = |(P.leadingCoeff:ℝ) * θ - (r₁:ℝ)/(q₁:ℝ) - (m:ℝ)| := by
        rw [haq]; congr 1; ring
      rwa [habs]
    · have hmle : m < -1 ∨ P.leadingCoeff < m := by
        rw [Finset.mem_Icc] at hmI
        omega
      have hsmall : (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) < 1 := by
        have hd4 : (0:ℝ) < (P.natDegree:ℝ) - (1:ℝ)/4 := by
          have hd' : (2:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd
          linarith
        have hlt := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) hNlt hd4
        rw [Real.one_rpow] at hlt
        rw [Real.rpow_neg hNr.le]
        exact inv_lt_one_of_one_lt₀ hlt
      have hx1 : -1 < (P.leadingCoeff:ℝ) * θ - (r₁:ℝ)/(q₁:ℝ) := by
        have h4 : (r₁:ℝ)/(q₁:ℝ) < 1 := by
          rw [div_lt_one (by positivity)]; exact_mod_cast hr1lt
        have h5 : (0:ℝ) ≤ (P.leadingCoeff:ℝ) * θ := by
          have : (0:ℝ) ≤ (P.leadingCoeff:ℝ) := by exact_mod_cast (le_of_lt hc)
          positivity
        linarith
      have hx2 : (P.leadingCoeff:ℝ) * θ - (r₁:ℝ)/(q₁:ℝ) ≤ (P.leadingCoeff:ℝ) := by
        have h4 : (0:ℝ) ≤ (r₁:ℝ)/(q₁:ℝ) := by positivity
        have h5 : θ * (P.leadingCoeff:ℝ) ≤ 1 * (P.leadingCoeff:ℝ) :=
          mul_le_mul_of_nonneg_right hθ1 (by exact_mod_cast (le_of_lt hc))
        nlinarith
      have hval : (P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ)
          = ((P.leadingCoeff:ℝ) * θ - (r₁:ℝ)/(q₁:ℝ)) - (m:ℝ) := by
        rw [haq]; ring
      rcases hmle with hm | hm
      · have hm2 : (m:ℝ) ≤ -2 := by
          have : m ≤ (-2:ℤ) := by omega
          exact_mod_cast this
        have hge : 1 ≤ (P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) := by rw [hval]; linarith
        calc (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) < 1 := hsmall
          _ ≤ |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ)| := by
              rw [abs_of_nonneg (by linarith)]; exact hge
      · have hm2 : (P.leadingCoeff:ℝ) + 1 ≤ (m:ℝ) := by
          have : P.leadingCoeff + 1 ≤ m := by omega
          exact_mod_cast this
        have hle : (P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ) ≤ -1 := by rw [hval]; linarith
        calc (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) < 1 := hsmall
          _ ≤ |(P.leadingCoeff:ℝ) * θ - (a:ℝ)/(q:ℝ)| := by
              rw [abs_of_nonpos (by linarith)]; linarith
  have hlead : (Polynomial.C θ * toRealPoly P).leadingCoeff = θ * (P.leadingCoeff:ℝ) := by
    show (Polynomial.C θ * Polynomial.map (Int.castRingHom ℝ) P).leadingCoeff = _
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int (Int.castRingHom ℝ)) P]
    rfl
  have hdeg : (Polynomial.C θ * toRealPoly P).natDegree = P.natDegree := by
    show (Polynomial.C θ * Polynomial.map (Int.castRingHom ℝ) P).natDegree = _
    rw [Polynomial.natDegree_C_mul hθne,
      Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℝ)) P]
  have hkey := hdecay N (Polynomial.C θ * toRealPoly P) hdeg (by omega)
    (fun q a hq hqle => by
      have hh := hminor q a hq hqle
      rw [hlead]
      have hexp : -((P.natDegree:ℝ)) + (1:ℝ)/4 = -((P.natDegree:ℝ) - (1:ℝ)/4) := by ring
      rw [hexp]
      simpa only [mul_comm ((P.leadingCoeff:ℝ)) θ] using hh)
  have hNc : ((N:ℝ)⁻¹ : ℂ) = (N:ℂ)⁻¹ := by
    rw [show (N:ℂ) = ((N:ℝ):ℂ) by exact (Complex.ofReal_natCast N).symm]
  have hpt : ∀ x : ℕ, (θ * ((P.eval (x:ℤ) : ℤ) : ℝ))
      = Polynomial.eval (x:ℝ) (Polynomial.C θ * toRealPoly P) := by
    intro x
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    congr 1
    show ((P.eval (x:ℤ) : ℤ) : ℝ) = Polynomial.eval ((x:ℕ):ℝ) (P.map (Int.castRingHom ℝ))
    rw [show ((x:ℕ):ℝ) = (((x:ℤ)):ℝ) by push_cast; ring,
      Commons.Analysis.ExponentialSums.eval_map_int_cast]
  have hsum : polyWeylKernel P N θ
      = (N:ℂ)⁻¹ * ∑ x ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
          (((Polynomial.eval (x:ℝ) (Polynomial.C θ * toRealPoly P) : ℝ)) : ℂ)) := by
    rw [polyWeylKernel, hNc]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [hpt x]
  rw [hsum]
  exact hkey

/-! ## The target -/

/-- **The major-arc model approximates the polynomial Weyl kernel uniformly.**  For an integer
polynomial `P` of degree `d ≥ 2` with `c = P.leadingCoeff > 0`, at every scale `N` and every
frequency `θ ∈ [0,1]`,

`‖polyWeylKernel P N θ − polyMajorArcModelPre P (1/4) N θ‖ ≤ C N^{-c₀}`,

with `c₀, C > 0` depending on `P`.  This is the non-monic analogue of
`Commons.Analysis.ExponentialSums.pow_kernel_major_arc_model` (Bourgain (1989), Lemma 6.14,
equation (6.15)): on each `c`-scaled arc `|cθ − (a/q + l)| ≤ N^{-(d-1/4)}`, `q ≤ N^{1/4}`, the
kernel is approximated by the arc's model term (`major_arc_bound_pre`, i.e. (6.10)), while off the
arcs the kernel decays (`minor_arc_decay_pre`, i.e. the minor-arc case (5.7)); the combinatorial
input is that (for `N` large) the model collapses to at most ONE term on an arc and vanishes
elsewhere (the analogue of `powMajorArcModel_eq_single` / `powMajorArcModel_eq_zero`). -/
theorem model_pre (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ (N : ℕ) (θ : ℝ), 3 ≤ N → 0 ≤ θ → θ ≤ 1 →
      ‖Work.BourgainPlan.Maximal.polyWeylKernel P N θ
        - Work.BourgainPlan.Maximal.polyMajorArcModelPre P ((1 : ℝ)/4) N θ‖
        ≤ C * (N : ℝ) ^ (-c₀) := by
  obtain ⟨c1, C1, hc1, hC1, hmaj⟩ := major_arc_bound_pre P hc hd
  obtain ⟨ν, C2, hν, hC2, hmin⟩ := model_minor_arc P hc hd
  refine ⟨min c1 ν, max C1 C2 + 1, lt_min hc1 hν, by positivity, ?_⟩
  intro N θ hN hθ0 hθ1
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hstep : ∀ {c C : ℝ}, (c = c1 ∨ c = ν) → 0 ≤ C → C ≤ max C1 C2 →
      C * (N:ℝ)^(-c) ≤ (max C1 C2 + 1) * (N:ℝ)^(-(min c1 ν)) := by
    intro c C hcl hC0 hCle
    have hc' : min c1 ν ≤ c := by
      rcases hcl with h | h <;> rw [h]
      · exact min_le_left _ _
      · exact min_le_right _ _
    have h2 : (N:ℝ)^(-c) ≤ (N:ℝ)^(-(min c1 ν)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    exact mul_le_mul (by linarith) h2 (Real.rpow_nonneg hNr.le _) (by positivity)
  by_cases harc : ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ∧
        x.2.1 < x.1 ∧ Nat.gcd x.2.1 x.1 = 1 ∧
        x.2.2 ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff ∧
        |(P.leadingCoeff : ℝ) * θ - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)|
          ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4))
  · have hfloor : (harc.choose.1 : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := by
      have h1 : ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) :=
        Nat.floor_le (by positivity)
      have h2 : ((harc.choose.1 : ℕ) : ℝ)
          ≤ ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) := by
        exact_mod_cast harc.choose_spec.2.1
      linarith
    rw [model_eq_single P hd hN θ harc]
    exact le_trans (hmaj N harc.choose.1 harc.choose.2.1 harc.choose.2.2 θ
        harc.choose_spec.1 hfloor harc.choose_spec.2.2.1 harc.choose_spec.2.2.2.1
        harc.choose_spec.2.2.2.2.2)
      (hstep (Or.inl rfl) hC1.le (le_max_left _ _))
  · rw [model_eq_zero P θ harc, sub_zero]
    have hnoarc : ∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) →
        a < q → Nat.gcd a q = 1 → l ∈ Finset.Icc (-1) P.leadingCoeff →
        (N:ℝ)^(-((P.natDegree:ℝ) - (1:ℝ)/4)) <
          |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| := by
      intro q a l hq hqfl ha hgcd hl
      by_contra hcon
      exact harc ⟨(q,a,l), hq, hqfl, ha, hgcd, hl, not_lt.mp hcon⟩
    exact le_trans (hmin N hN θ hθ0 hθ1 hnoarc) (hstep (Or.inr rfl) hC2.le (le_max_right _ _))

end Work.BourgainPlan.Maximal
