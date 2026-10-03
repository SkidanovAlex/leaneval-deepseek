import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Vflip.VflipAux
import Submission.Work.FIArea4.Vflip.FlipSetup
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve
import Submission.Work.FIArea4.Vflip.Vfd.numerics_dyadic_logs
import Submission.Work.FIArea4.Vflip.Vfd.Vvar_near_bound
import Submission.Work.FIArea4.Vflip.Vfd.Vvar_le_pairWeight
import Submission.Work.FIArea4.Vflip.Vfd.Vflip_far_bound

/-!
# Assembly of the dyadic Friedlander–Iwaniec Proposition 12.1

This module assembles the four quantitative inputs of the dyadic form of FI Proposition 12.1

* `Vvar_le_pairWeight` (smooth majorant + pair expansion),
* `Vvar_near_bound` (near-diagonal part, via `near_count_multi`),
* `Vflip_far_bound` (the flipped moduli, via the Fourier–Mellin separation and Proposition 11.1),
* `numerics_dyadic_logs` (the four brackets are dominated by `p14T12`),

into the estimate `Vvar R S D α ≤ C·p14T12 D R S ε·p14Ener R S α` for a vector supported in the
dyadic box `(R,2R]×(S,2S]` with `(r,2s)=1`, in the range `D ≤ RS < D²`; the mod-8 splitting
`Vvar_mod8` then removes the single-residue-class hypothesis (`Vflip_dyadic_of_class`).

The pair expansion `Vvar_le_pairWeight` produces the double sum over the full `Icc` box
`[1,2R]×[1,2S]`; since `α` is supported in the dyadic box `(R,2R]×(S,2S]`, the double sum may be
restricted to `boxF R S` (`sum_Icc_eq_sum_boxF`), which is the shape in which the near and far
bounds are stated.
-/

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The far bracket of the flipped moduli. -/
def farBracket (D R S : ℕ) (ε H : ℝ) : ℝ :=
  (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
      * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
    + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
      * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
          + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))

/-- The near bracket of the near-diagonal part. -/
def nearBracket (D R S : ℕ) (H : ℝ) : ℝ :=
  ((R : ℝ) * (S : ℝ) / H) * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
    + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H)

lemma boxF_eq (R S : ℕ) : boxF R S = Finset.Ioc R (2 * R) ×ˢ Finset.Ioc S (2 * S) := rfl

lemma farBracket_eq (D R S : ℕ) (ε H : ℝ) :
    farBracket D R S ε H =
      ((Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
          * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
        + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
          * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
              + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
              + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))) := rfl

lemma nearBracket_eq (D R S : ℕ) (H : ℝ) :
    nearBracket D R S H =
      (((R : ℝ) * (S : ℝ) / H) * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
        + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H)) := rfl

/-- Reduction of a double sum over the full `Icc`-box to the dyadic `boxF`, using that `α`
vanishes outside `boxF`. -/
lemma sum_Icc_eq_sum_boxF (R S : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) (α : ℕ → ℕ → ℂ)
    (hbox : ∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S)
    (W : ℕ × ℕ → ℕ × ℕ → ℂ) :
    (∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
        ∑ q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
          α p.1 p.2 * star (α q.1 q.2) * W p q)
      = ∑ p ∈ boxF R S, ∑ q ∈ boxF R S, α p.1 p.2 * star (α q.1 q.2) * W p q := by
  have hsub1 : Finset.Ioc R (2 * R) ⊆ Finset.Icc 1 (2 * R) := by
    intro x hx
    rw [Finset.mem_Ioc] at hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
  have hsub2 : Finset.Ioc S (2 * S) ⊆ Finset.Icc 1 (2 * S) := by
    intro x hx
    rw [Finset.mem_Ioc] at hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
  have hsub : boxF R S ⊆ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S) := by
    rw [boxF_eq]
    exact Finset.product_subset_product hsub1 hsub2
  have hmem : ∀ p : ℕ × ℕ, p ∈ boxF R S ↔
      (R < p.1 ∧ p.1 ≤ 2 * R ∧ S < p.2 ∧ p.2 ≤ 2 * S) := by
    intro p
    rw [boxF_eq, Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc]
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩,
      fun h => ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩⟩
  have hzero_p : ∀ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S), p ∉ boxF R S →
      (∑ q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
        α p.1 p.2 * star (α q.1 q.2) * W p q) = 0 := by
    intro p _ hp
    refine Finset.sum_eq_zero (fun q _ => ?_)
    have ha : α p.1 p.2 = 0 := by
      by_contra hc
      exact hp ((hmem p).mpr (hbox p.1 p.2 hc))
    simp [ha]
  have houter : (∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
        ∑ q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
          α p.1 p.2 * star (α q.1 q.2) * W p q)
      = ∑ p ∈ boxF R S, ∑ q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
          α p.1 p.2 * star (α q.1 q.2) * W p q :=
    (Finset.sum_subset hsub hzero_p).symm
  rw [houter]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hzero_q : ∀ q ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S), q ∉ boxF R S →
      α p.1 p.2 * star (α q.1 q.2) * W p q = 0 := by
    intro q _ hq
    have ha : α q.1 q.2 = 0 := by
      by_contra hc
      exact hq ((hmem q).mpr (hbox q.1 q.2 hc))
    simp [ha]
  exact (Finset.sum_subset hsub hzero_q).symm

/-- **The estimate for a vector supported in a single residue class modulo 8.** -/
theorem Vvar_class_bound (h11 : Work.FIArea4.p14Prop111All) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      (∀ r s, α r s ≠ 0 → ∀ r' s', α r' s' ≠ 0 → r % 8 = r' % 8) →
      Work.FIPlan.Vvar R S D α ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
  obtain ⟨Cfar, hCfarpos, hfar⟩ := Vfd.Vflip_far_bound h11 ε hε
  obtain ⟨Cnear, hCnearpos, hnear⟩ := Vfd.Vvar_near_bound
  obtain ⟨Cnum, hCnumpos, hnum⟩ := Vfd.numerics_dyadic_logs ε hε
  refine ⟨(Cfar + Cnear) * Cnum, by positivity, ?_⟩
  intro D R S α hD hR hS hDle hDsq hcop hbox hcls
  set H : ℝ := ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) with hHdef
  set a : ℝ := 2 * (S : ℝ) / (H * (R : ℝ)) with hadef
  set b : ℝ := 2 * (S : ℝ) / (R : ℝ) with hbdef
  have hodd : ∀ r s, α r s ≠ 0 → Odd r := by
    intro r s h
    have h2 : 2 ∣ 2 * s := ⟨s, rfl⟩
    exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 (hcop r s h))
  have hEner : 0 ≤ Work.FIArea4.p14Ener R S α := p14Ener_nonneg R S α
  have hexp := Vfd.Vvar_le_pairWeight R S D hD α hodd
  set Sg : ℂ := ∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          ((nearCut a b (xPair p q) : ℝ) * pairWeight D p q) with hSg
  set Sng : ℂ := ∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          (((1 - nearCut a b (xPair p q)) : ℝ) * pairWeight D p q) with hSng
  have hsplit : (∑ p ∈ boxF R S, ∑ q ∈ boxF R S,
          α p.1 p.2 * star (α q.1 q.2) * pairWeight D p q) = Sg + Sng := by
    rw [hSg, hSng, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    push_cast
    ring
  have hred := sum_Icc_eq_sum_boxF R S hR hS α hbox (fun p q => pairWeight D p q)
  have hexp2 : Work.FIPlan.Vvar R S D α ≤ (Sg + Sng).re := by
    rw [hred, hsplit] at hexp
    exact hexp
  have hfar' := hfar D R S H a b α hD hR hS hDle hDsq hHdef.symm hadef.symm hbdef.symm
    hcop hbox hcls
  have hnear' := hnear D R S H a b α hD hR hS hDle hDsq hHdef.symm hadef.symm hbdef.symm
    hcop hbox
  have hnum' := hnum D R S H hD hR hS hDsq hDle hHdef.symm
  have hle : nearBracket D R S H + farBracket D R S ε H
      ≤ Cnum * Work.FIArea4.p14T12 D R S ε := by
    rw [nearBracket_eq, farBracket_eq]
    convert hnum' using 1
    ring
  have hHnn : 0 ≤ H := by rw [hHdef]; exact Real.rpow_nonneg (by positivity) _
  have hDne : ((D : ℝ)) ≠ 0 := by positivity
  have hH3 : H ^ 3 = (R : ℝ) * (S : ℝ) / (D : ℝ) := by
    rw [hHdef, ← Real.rpow_natCast (((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by positivity) ((1 : ℝ) / 3) ((3 : ℕ) : ℝ),
      show ((1 : ℝ) / 3) * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hRS : (R : ℝ) * (S : ℝ) = (D : ℝ) * H ^ 3 := by
    rw [hH3, mul_div_cancel₀ _ hDne]
  have hH1 : 1 ≤ H := by
    rw [hHdef]
    refine Real.one_le_rpow ?_ (by norm_num)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < D)]
    have h : (D : ℝ) ≤ (R : ℝ) * (S : ℝ) := by exact_mod_cast hDle
    linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hy : 2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H) = 2 * H ^ 2 := by
    have h2 : 2 * (R : ℝ) * (S : ℝ) = 2 * ((R : ℝ) * (S : ℝ)) := by ring
    rw [h2, hRS]
    field_simp
  have hlog_nn : 0 ≤ Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2 := by
    rw [hy]
    have h2 : (1 : ℝ) ≤ 2 * H ^ 2 := by nlinarith [hH1]
    have := Real.log_nonneg h2
    linarith
  have hnb : 0 ≤ nearBracket D R S H := by
    rw [nearBracket_eq]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (div_nonneg (by positivity) hHnn) (by linarith [hlog_nn])
    · exact div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hfb : 0 ≤ farBracket D R S ε H := by
    rw [farBracket_eq]
    have h1 : (0:ℝ) ≤ (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2
        * ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2) := by positivity
    have h2 : (0:ℝ) ≤ (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
        * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
            + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)) := by
      positivity
    linarith
  have hstep : Work.FIPlan.Vvar R S D α
      ≤ Cfar * farBracket D R S ε H * Work.FIArea4.p14Ener R S α
        + Cnear * nearBracket D R S H * Work.FIArea4.p14Ener R S α := by
    refine le_trans hexp2 ?_
    rw [Complex.add_re]
    have h1 : Sg.re ≤ ‖Sg‖ := by simpa using Complex.re_le_norm Sg
    have h2 : Sng.re ≤ ‖Sng‖ := by simpa using Complex.re_le_norm Sng
    have h3 : ‖Sg‖ ≤ Cfar * farBracket D R S ε H * Work.FIArea4.p14Ener R S α := by
      rw [hSg, farBracket_eq]
      exact hfar'
    have h4 : ‖Sng‖ ≤ Cnear * nearBracket D R S H * Work.FIArea4.p14Ener R S α := by
      rw [hSng, nearBracket_eq]
      exact hnear'
    linarith
  refine le_trans hstep ?_
  have h3 : Cfar * farBracket D R S ε H
      ≤ Cfar * (nearBracket D R S H + farBracket D R S ε H) :=
    mul_le_mul_of_nonneg_left (by linarith [hfb]) hCfarpos.le
  have h4 : Cnear * nearBracket D R S H
      ≤ Cnear * (nearBracket D R S H + farBracket D R S ε H) :=
    mul_le_mul_of_nonneg_left (by linarith [hnb]) hCnearpos.le
  have hmid : (Cfar * farBracket D R S ε H + Cnear * nearBracket D R S H)
      * Work.FIArea4.p14Ener R S α
      ≤ ((Cfar + Cnear) * (nearBracket D R S H + farBracket D R S ε H))
        * Work.FIArea4.p14Ener R S α := by
    refine mul_le_mul_of_nonneg_right ?_ hEner
    calc Cfar * farBracket D R S ε H + Cnear * nearBracket D R S H
        ≤ Cfar * (nearBracket D R S H + farBracket D R S ε H)
          + Cnear * (nearBracket D R S H + farBracket D R S ε H) := add_le_add h3 h4
      _ = (Cfar + Cnear) * (nearBracket D R S H + farBracket D R S ε H) := by ring
  have hfinal : (Cfar + Cnear) * (nearBracket D R S H + farBracket D R S ε H)
      * Work.FIArea4.p14Ener R S α
      ≤ (Cfar + Cnear) * (Cnum * Work.FIArea4.p14T12 D R S ε)
        * Work.FIArea4.p14Ener R S α := by
    refine mul_le_mul_of_nonneg_right ?_ hEner
    exact mul_le_mul_of_nonneg_left hle (by linarith [hCfarpos, hCnearpos])
  calc Cfar * farBracket D R S ε H * Work.FIArea4.p14Ener R S α
        + Cnear * nearBracket D R S H * Work.FIArea4.p14Ener R S α
      = (Cfar * farBracket D R S ε H + Cnear * nearBracket D R S H)
          * Work.FIArea4.p14Ener R S α := by ring
    _ ≤ ((Cfar + Cnear) * (nearBracket D R S H + farBracket D R S ε H))
          * Work.FIArea4.p14Ener R S α := hmid
    _ ≤ (Cfar + Cnear) * (Cnum * Work.FIArea4.p14T12 D R S ε)
          * Work.FIArea4.p14Ener R S α := hfinal
    _ = ((Cfar + Cnear) * Cnum) * Work.FIArea4.p14T12 D R S ε
          * Work.FIArea4.p14Ener R S α := by ring

end

end Work.FIArea4.Vflip
