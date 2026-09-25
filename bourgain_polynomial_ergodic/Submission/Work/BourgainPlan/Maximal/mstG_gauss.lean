import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.sigmaN_contains_farey
import Submission.Work.BourgainPlan.Maximal.poly_weight_cap_block

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators
open Work.BourgainPlan.IonescuWainger
open Commons.Analysis.ExponentialSums

set_option autoImplicit false

/-!
# Gauss/Weyl decay of the canonical weight `mstG` on the level differences

This file proves `mstG_gauss`: on the annulus `mstU l (s+1) ∖ mstU l s` — with the side condition
`s^l ≥ 2^{iwK (mstRho l)}` which makes the Farey fractions of denominator `≤ s^l` sit inside
`mstU l s` — the complete-sum weight `mstG P` decays like `(s^l)^{-δ}` for some `δ > 0`, uniformly
in `s` and in the point of the annulus.

The three ingredients are:

* `mstG_eq_polyWeight_of_rep`: the value of `mstG` at a point is the complete sum attached to any
  representative `arcPt q a` with `0 < q`, `0 ≤ a < q` (well-definedness of the `Classical.choose`
  definition in `mst_major_defs.lean`, proved here through the scale invariance
  `polyWeight_eq_of_dvd` of the complete sum);
* the reduction of a representative of a level point (`Nat.gcd` cancellation) and the fact that the
  *reduced* denominator of a point of `mstU l (s+1) ∖ mstU l s` exceeds `s^l`
  (`sigmaN_contains_farey`);
* Hua's bound `integer_poly_complete_sum_bound` for the complete sum of a reduced fraction.
-/

/-! ## Well-definedness of `mstG` -/

/-- **Two representatives of one circle point.**  If `a/q = a'/q'` in `𝕋` with numerators in
`[0,1)` and positive denominators, then `a·q' = a'·q` in `ℤ`: both numerators are put over the
common denominator `q·q'` (`arcPt_commonDenom`), the difference is divisible by `q·q'`
(`arcPt_eq_arcPt_iff_dvd`) but has absolute value `< q·q'`. -/
lemma mul_eq_of_arcPt_eq {q q' : ℕ} {a a' : ℤ}
    (hq : 0 < q) (hq' : 0 < q') (ha : 0 ≤ a) (haq : a < (q : ℤ))
    (ha' : 0 ≤ a') (ha'q : a' < (q' : ℤ))
    (hβ : arcPt q a = arcPt q' a') : a * (q' : ℤ) = a' * (q : ℤ) := by
  have hd : 0 < q * q' := Nat.mul_pos hq hq'
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne'
  have hq1' : 1 ≤ q' := Nat.one_le_iff_ne_zero.mpr hq'.ne'
  have h1 : arcPt (q * q') (a * (q' : ℤ)) = arcPt q a := by
    have h := arcPt_commonDenom hq1 (by omega) (Nat.dvd_mul_right q q') a
    rw [Nat.mul_div_right q' hq] at h
    exact h.symm
  have h2 : arcPt (q * q') (a' * (q : ℤ)) = arcPt q' a' := by
    have h := arcPt_commonDenom hq1' (by omega) (Nat.dvd_mul_left q' q) a'
    rw [Nat.mul_div_left q hq'] at h
    exact h.symm
  have hdvd : ((q * q' : ℕ) : ℤ) ∣ (a * (q' : ℤ) - a' * (q : ℤ)) :=
    (arcPt_eq_arcPt_iff_dvd hd.ne' _ _).mp (by rw [h1, hβ, h2])
  obtain ⟨n, hn⟩ := hdvd
  have hdZ : (0 : ℤ) < ((q * q' : ℕ) : ℤ) := by exact_mod_cast hd
  have haq' : (0 : ℤ) ≤ a * (q' : ℤ) := mul_nonneg ha (by positivity)
  have ha'q_nn : (0 : ℤ) ≤ a' * (q : ℤ) := mul_nonneg ha' (by positivity)
  have hlt1 : a * (q' : ℤ) < ((q * q' : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact mul_lt_mul_of_pos_right haq (by exact_mod_cast hq')
  have hlt2 : a' * (q : ℤ) < ((q * q' : ℕ) : ℤ) := by
    rw [Nat.cast_mul, mul_comm (q : ℤ) (q' : ℤ)]
    exact mul_lt_mul_of_pos_right ha'q (by exact_mod_cast hq)
  have hlo : -(((q * q' : ℕ) : ℤ)) < a * (q' : ℤ) - a' * (q : ℤ) := by
    linarith
  have hhi : a * (q' : ℤ) - a' * (q : ℤ) < ((q * q' : ℕ) : ℤ) := by
    linarith
  rcases lt_trichotomy n 0 with hnlt | hn0 | hngt
  · have hn1 : n ≤ -1 := by omega
    have hle := mul_le_mul_of_nonneg_left hn1 hdZ.le
    simp only [mul_neg, mul_one] at hle
    linarith [hn, hle, hlo]
  · rw [hn0, mul_zero] at hn
    linarith
  · have hn1 : 1 ≤ n := by omega
    have hle := mul_le_mul_of_nonneg_left hn1 hdZ.le
    simp only [mul_one] at hle
    linarith [hn, hle, hhi]

/-- **The complete sum depends only on the circle point** (for representatives with numerator in
`[0,1)`): two such representatives are put over the common denominator `q·q'`
(`polyWeight_eq_of_dvd`), where the numerators coincide by `mul_eq_of_arcPt_eq`. -/
lemma polyWeight_arcPt_congr (P : Polynomial ℤ) {q q' : ℕ} {a a' : ℤ}
    (hq : 0 < q) (hq' : 0 < q') (ha : 0 ≤ a) (haq : a < (q : ℤ))
    (ha' : 0 ≤ a') (ha'q : a' < (q' : ℤ))
    (hβ : arcPt q a = arcPt q' a') : polyWeight P q a = polyWeight P q' a' := by
  have hcross : a * (q' : ℤ) = a' * (q : ℤ) := mul_eq_of_arcPt_eq hq hq' ha haq ha' ha'q hβ
  have hd : 0 < q * q' := Nat.mul_pos hq hq'
  have hpw1 : polyWeight P (q * q') (a * (q' : ℤ)) = polyWeight P q a :=
    polyWeight_eq_of_dvd P hd hq (Nat.dvd_mul_right q q') (by push_cast; ring)
  have hpw2 : polyWeight P (q * q') (a' * (q : ℤ)) = polyWeight P q' a' :=
    polyWeight_eq_of_dvd P hd hq' (Nat.dvd_mul_left q' q) (by push_cast; ring)
  calc polyWeight P q a = polyWeight P (q * q') (a * (q' : ℤ)) := hpw1.symm
    _ = polyWeight P (q * q') (a' * (q : ℤ)) := by rw [hcross]
    _ = polyWeight P q' a' := hpw2

/-- **The value of `mstG` at a point given by a representative in `[0,1)`**: the `Classical.choose`
definition of `mstG` returns *some* representative, which by `polyWeight_arcPt_congr` gives the same
complete sum. -/
theorem mstG_eq_polyWeight_of_rep (P : Polynomial ℤ)
    {β : Work.BourgainPlan.IonescuWainger.Circle} {q : ℕ} {a : ℤ}
    (hq : 0 < q) (ha : 0 ≤ a) (haq : a < (q : ℤ)) (hβ : arcPt q a = β) :
    mstG P β = polyWeight P q a := by
  classical
  have hex : ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧ arcPt q a = β :=
    ⟨q, a, hq, ha, haq, hβ⟩
  have hval : mstG P β
      = polyWeight P (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)) := by
    rw [mstG]
    exact dif_pos hex
  rw [hval]
  obtain ⟨hq', ha', haq', hβ'⟩ := Classical.choose_spec (Classical.choose_spec hex)
  exact polyWeight_arcPt_congr P hq' hq ha' haq' ha haq (hβ'.trans hβ.symm)

/-! ## The decay on the level differences -/

/-- Gauss/Weyl decay of the canonical weight `mstG` on the level differences `mstU l (s+1) ∖ mstU l s`: there are `δ > 0` and `C > 0` such that for every `s` with `s^l ≥ 2^{iwK (mstRho l)}` and every point of the difference, `‖mstG P β‖ ≤ C (s^l)^{−δ}`.

Route: find the reduced representative `β = arcPt q a` (`0 < q`, `0 ≤ a < q`, `gcd a q = 1`; reduce a representative `arcPt Q b` of the `sigmaSubAFinset`-form, as in `mstU_rep`).  Then `mstG P β = polyWeight P q a` (the scale-invariance/well-definedness of `mstG`; prove it locally in your file if `Maximal/mstG_spec.lean` is not yet present), and `q > s^l`: otherwise `q ≤ s^l` with `gcd a q = 1` gives `arcPt q a ∈ iwSigma (mstRho l) (s^l) = mstU l s` by `sigmaN_contains_farey` (whose hypothesis `2^{iwK ρ} ≤ N` is exactly the side condition of this statement).  Finally `Commons.Analysis.ExponentialSums.integer_poly_complete_sum_bound` bounds a complete sum of modulus a prime power with `gcd a q = 1` by `C' q^{−1/2^{d−1}+ε}`; with `ε := 2^{-(d+1)}` and `δ := 2^{-d}` this is `≤ q^{−δ}` for `q ≥ 1`, and `q > s^l ≥ 1` with `δ > 0` gives `q^{−δ} < (s^l)^{−δ}`.  Put `δ := 2^{-d}`, `C := max C' 1` (the case `s^l = 1` is then still covered).

This is what is implemented below: `mul_eq_of_arcPt_eq` + `polyWeight_arcPt_congr` give the
well-definedness of `mstG` (`mstG_eq_polyWeight_of_rep`), the `Nat.gcd` cancellation produces the
reduced representative of a level point, `sigmaN_contains_farey` shows its denominator exceeds
`s^l`, and `integer_poly_complete_sum_bound` with `ε = 2^{-(d+1)}`, `δ = 2^{-d}` gives the decay. -/
theorem mstG_gauss (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 < C ∧ ∀ (s : ℕ)
      (β : Work.BourgainPlan.IonescuWainger.Circle),
      (2 : ℝ) ^ ((Work.BourgainPlan.Maximal.iwK (Work.BourgainPlan.Maximal.mstRho l) : ℕ) : ℝ)
          ≤ (s : ℝ) ^ l →
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ C * ((s : ℝ) ^ l) ^ (-δ) := by
  set d : ℕ := P.natDegree with hddef
  have hd2 : 2 ≤ d := hd
  have hd1 : 1 ≤ d := by omega
  set eps : ℝ := ((2 : ℝ) ^ (d + 1))⁻¹ with hepsdef
  set del : ℝ := ((2 : ℝ) ^ d)⁻¹ with hdeldef
  have hepspos : 0 < eps := by rw [hepsdef]; positivity
  have hdelpos : 0 < del := by rw [hdeldef]; positivity
  -- the exponent comparison `-1/2^{d-1} + ε ≤ -δ`, i.e. `ε + δ ≤ 1/2^{d-1}`
  have hcmp : -(1 / (2 : ℝ) ^ (d - 1)) + eps ≤ -del := by
    have h1 : (2 : ℝ) ^ (d + 1) = (2 : ℝ) ^ (d - 1) * 4 := by
      rw [show d + 1 = (d - 1) + 2 by omega, pow_add]; norm_num
    have h2 : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
      rw [show d = (d - 1) + 1 by omega, pow_add]; norm_num
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
    rw [hepsdef, hdeldef, h1, h2]
    have h3n : (2 : ℝ) ^ (d - 1) ≠ 0 := h3.ne'
    rw [one_div]
    field_simp
    linarith
  obtain ⟨C', hC'pos, hC'b⟩ :=
    integer_poly_complete_sum_bound d hd2 (ε := eps) hepspos P hddef.symm
  refine ⟨del, max C' 1, hdelpos, lt_max_iff.mpr (Or.inl hC'pos), ?_⟩
  intro s β hs hβm
  obtain ⟨hβU, hβnotU⟩ := Finset.mem_sdiff.mp hβm
  -- the side condition, as an inequality of natural numbers
  have hspow : (2 : ℝ) ^ (iwK (mstRho l)) ≤ (s : ℝ) ^ l := by
    rwa [Real.rpow_natCast] at hs
  have hspow_nat : 2 ^ iwK (mstRho l) ≤ s ^ l := by
    have hcast : ((2 ^ iwK (mstRho l) : ℕ) : ℝ) ≤ ((s ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_pow]
      exact hspow
    exact_mod_cast hcast
  have hsR : (0 : ℝ) < (s : ℝ) ^ l := by
    have : (0 : ℝ) < (2 : ℝ) ^ (iwK (mstRho l)) := by positivity
    linarith
  -- (1) a representative coming from the level set
  have hmem : β ∈ sigmaLeFinset (taoSetS (mstRho l) ((s + 1) ^ l)) (iwK (mstRho l)) := by
    simpa only [mstU, iwSigma] using hβU
  rw [sigmaLeFinset, Finset.mem_biUnion] at hmem
  obtain ⟨A, hA, hβA⟩ := hmem
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAsub, -⟩ := hA
  rw [sigmaSubAFinset, Finset.mem_image] at hβA
  obtain ⟨b, hb, hβb⟩ := hβA
  have hbB : b < QA A := Finset.mem_range.mp hb
  have hQA : QA A ≠ 0 := QA_ne_zero_of_subset_taoSetS hAsub
  have hQpos : 0 < QA A := Nat.pos_of_ne_zero hQA
  -- (2) cancellation of the common divisor
  set g : ℕ := Nat.gcd b (QA A) with hgdef
  set q : ℕ := QA A / g with hqdef
  set a : ℕ := b / g with hadef
  have hgposR : 0 < Nat.gcd b (QA A) := Nat.gcd_pos_of_pos_right b hQpos
  have hgpos : 0 < g := by rw [hgdef]; exact hgposR
  have hgQ : g ∣ QA A := by rw [hgdef]; exact Nat.gcd_dvd_right b (QA A)
  have hgb : g ∣ b := by rw [hgdef]; exact Nat.gcd_dvd_left b (QA A)
  have hQeq : QA A = q * g := by rw [hqdef]; exact (Nat.div_mul_cancel hgQ).symm
  have hbeq : b = a * g := by rw [hadef]; exact (Nat.div_mul_cancel hgb).symm
  have hqpos : 0 < q := by
    rw [hqdef]
    exact Nat.div_pos (Nat.le_of_dvd hQpos hgQ) hgpos
  have hq1 : 1 ≤ q := hqpos
  have haq : a < q := by
    have h1 : a * g < q * g := by rw [← hbeq, ← hQeq]; exact hbB
    exact Nat.lt_of_mul_lt_mul_right h1
  have hcop : Nat.Coprime a q := by
    rw [hadef, hqdef, hgdef]
    exact Nat.coprime_div_gcd_div_gcd hgposR
  have hbg : (a : ℤ) * (g : ℤ) = (b : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hbeq
    push_cast at h
    exact h.symm
  have hβqa : arcPt q (a : ℤ) = β := by
    have h := arcPt_commonDenom (Q := q) (L := QA A) hq1
      (Nat.one_le_iff_ne_zero.mpr hQA) ⟨g, hQeq⟩ (a : ℤ)
    have hQq : QA A / q = g := by rw [hQeq, Nat.mul_div_right g hqpos]
    rw [hQq] at h
    rw [← hβb, h, hbg]
  -- (3) the reduced denominator exceeds `s^l`
  have hq_gt : s ^ l < q := by
    by_contra hcon
    have hle : q ≤ s ^ l := le_of_not_gt hcon
    have hρ : 0 < mstRho l := by
      rw [mstRho]
      have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
      positivity
    have hin : arcPt q (a : ℤ) ∈ iwSigma (mstRho l) (s ^ l) :=
      sigmaN_contains_farey (mstRho l) hρ (s ^ l) hspow_nat q a hq1 hle hcop
    exact hβnotU (by simpa only [mstU, hβqa] using hin)
  -- (4) Hua's bound
  have hval : mstG P β = polyWeight P q (a : ℤ) :=
    mstG_eq_polyWeight_of_rep (P := P) (β := β) (q := q) (a := (a : ℤ))
      hqpos (by positivity) (by exact_mod_cast haq) hβqa
  have hgcdI : Int.gcd (a : ℤ) (q : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hHua : ‖polyWeight P q (a : ℤ)‖
      ≤ C' * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + eps) := by
    rw [polyWeight_apply]
    exact hC'b q (a : ℤ) hq1 hgcdI
  have hpow_le : (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + eps) ≤ (q : ℝ) ^ (-del) :=
    Real.rpow_le_rpow_of_exponent_le (x := (q : ℝ)) (by exact_mod_cast hq1) hcmp
  have hs_le_q : (s : ℝ) ^ l ≤ (q : ℝ) := by
    exact_mod_cast hq_gt.le
  have hmono : (q : ℝ) ^ (-del) ≤ ((s : ℝ) ^ l) ^ (-del) :=
    Real.rpow_le_rpow_of_nonpos hsR hs_le_q (by linarith)
  calc ‖mstG P β‖ = ‖polyWeight P q (a : ℤ)‖ := by rw [hval]
    _ ≤ C' * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + eps) := hHua
    _ ≤ C' * (q : ℝ) ^ (-del) := mul_le_mul_of_nonneg_left hpow_le hC'pos.le
    _ ≤ C' * ((s : ℝ) ^ l) ^ (-del) := mul_le_mul_of_nonneg_left hmono hC'pos.le
    _ ≤ max C' 1 * ((s : ℝ) ^ l) ^ (-del) :=
        mul_le_mul_of_nonneg_right (le_max_left C' 1) (Real.rpow_nonneg hsR.le _)

end Work.BourgainPlan.Maximal
