import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstG_gauss
import Submission.Work.BourgainPlan.Maximal.mstG_gauss_uniform

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators
open Work.BourgainPlan.IonescuWainger
open Commons.Analysis.ExponentialSums

set_option autoImplicit false

/-!
# The Gauss decay of `mstG` with a *fixed* exponent `δ`

`mstG_gauss` states that for every `l ≥ 1` there are `δ_l > 0` and `C_l > 0` with
`‖mstG P β‖ ≤ C_l (s^l)^{-δ_l}` on the annulus `mstU l (s+1) ∖ mstU l s`, under the side condition
`2^{iwK (mstRho l)} ≤ s^l`.  `mstG_gauss_uniform` removes the side condition by measuring the decay
against `(s+1)^{-δ_l l}`, but the exponent still depends on `l`.  Downstream arguments (the `ℓ²`
level bounds fed by `mst_level_l2`, cf. `probe_mst_level_l2`) need a *single* exponent `δ > 0` that
works simultaneously for all `l`, the constant being allowed to depend on `l`.

That is `mstG_gauss_delta`:

`∃ δ > 0, ∀ l ≥ 1, ∃ D > 0, ∀ s β, β ∈ mstU l (s+1) ∖ mstU l s → ‖mstG P β‖ ≤ D (s+1)^{-(δ l)}`.

It is not a formal consequence of `mstG_gauss` (the exponents `δ_l` could in principle tend to `0`),
but it is a consequence of the *proof* of `mstG_gauss`: there `δ = 2^{-d}` with `d = P.natDegree` and
`C = max C' 1` for Hua's constant `C'` of degree `d` — the only `l`-dependence in the argument is the
side condition `2^{iwK (mstRho l)} ≤ s^l`, which never enters the constants.  So we replay that proof
once, with `δ` and `C` pulled outside the quantifier over `l` (`mstG_gauss_fixed`), and then repeat
the two-regime argument of `mstG_gauss_uniform`:

* `2^{iwK (mstRho l)} ≤ s^l`: the fixed bound applies and `(s^l)^{-δ} = s^{-δ l} ≤ 2^{δ l}
  (s+1)^{-δ l}` for `s ≥ 1` (`rpow_neg_le_two_mul_rpow_neg`);
* `s^l < 2^{iwK (mstRho l)}`: the trivial bound `‖mstG P β‖ ≤ 1` applies and
  `(s+1)^{δ l} ≤ (2^{iwK (mstRho l)}+1)^{δ l}`.

Both constants are absorbed into the single `D`, which is allowed to depend on `l`.
-/

/-- **`mstG_gauss` with the constants pulled out of the `l`-quantifier**: there are `δ > 0` and
`C > 0` such that for *every* `l ≥ 1`, every `s` with `2^{iwK (mstRho l)} ≤ s^l` and every point `β`
of the annulus `mstU l (s+1) ∖ mstU l s`, `‖mstG P β‖ ≤ C (s^l)^{-δ}`.

This is the proof of `mstG_gauss` verbatim, with `δ = 2^{-d}` and `C = max C' 1` (`d = P.natDegree`,
`C'` Hua's constant of `integer_poly_complete_sum_bound d hd 2^{-(d+1)}`) fixed before `l` is
introduced; neither constant depends on `l`. -/
lemma mstG_gauss_fixed (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 < C ∧ ∀ (l : ℕ), 1 ≤ l → ∀ (s : ℕ)
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
  intro l hl s β hs hβm
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

/-- **Gauss/Weyl decay of `mstG` with a fixed exponent, uniformly in the level `l`.**

There is `δ > 0` such that for every `l ≥ 1` there is `D > 0` with
`‖mstG P β‖ ≤ D · ((s : ℝ) + 1) ^ (-(δ * l))` for every `s` and every point `β` of the annulus
`mstU l (s+1) ∖ mstU l s`.  No side condition on `s` is needed: the finitely many small values of `s`
are absorbed into `D` through the trivial bound `‖mstG P β‖ ≤ 1`. -/
theorem mstG_gauss_delta (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℕ, 1 ≤ l → ∃ D : ℝ, 0 < D ∧
      ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
        β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
        ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) := by
  obtain ⟨δ, C, hδpos, hCpos, hbound⟩ := mstG_gauss_fixed P hd hc
  refine ⟨δ, hδpos, fun l hl => ?_⟩
  have hlne : l ≠ 0 := by omega
  have hδl : 0 < δ * (l : ℝ) := mul_pos hδpos (by exact_mod_cast hl)
  set N : ℕ := 2 ^ iwK (mstRho l) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  set D : ℝ := C * (2 : ℝ) ^ (δ * (l : ℝ)) + ((N : ℝ) + 1) ^ (δ * (l : ℝ)) with hD
  have hDpos : 0 < D := by
    rw [hD]
    exact add_pos (mul_pos hCpos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _))
      (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨D, hDpos, ?_⟩
  intro s β hβ
  have hpos1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  rcases le_or_gt N (s ^ l) with hge | hlt
  · -- decay regime: the fixed Gauss bound applies
    have hs1 : 1 ≤ s := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      intro h0
      rw [h0, zero_pow hlne] at hge
      omega
    have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    have hgeR : (2 : ℝ) ^ ((iwK (mstRho l) : ℕ) : ℝ) ≤ (s : ℝ) ^ l := by
      rw [Real.rpow_natCast]
      have hnat : 2 ^ iwK (mstRho l) ≤ s ^ l := by rw [← hN]; exact hge
      exact_mod_cast hnat
    have hbs := hbound l hl s β hgeR hβ
    have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have hdecay : ((s : ℝ) ^ l) ^ (-δ) = (s : ℝ) ^ (-(δ * (l : ℝ))) := by
      rw [← Real.rpow_natCast (s : ℝ) l, ← Real.rpow_mul hsR.le (l : ℝ) (-δ)]
      congr 1
      ring
    have hkey := rpow_neg_le_two_mul_rpow_neg (a := (s : ℝ)) (x := δ * (l : ℝ)) hs1R hδl.le
    have hDle : C * (2 : ℝ) ^ (δ * (l : ℝ)) ≤ D := by
      rw [hD]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    calc ‖mstG P β‖
        ≤ C * ((s : ℝ) ^ l) ^ (-δ) := hbs
      _ = C * (s : ℝ) ^ (-(δ * (l : ℝ))) := by rw [hdecay]
      _ ≤ C * (2 ^ (δ * (l : ℝ)) * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ)))) :=
          mul_le_mul_of_nonneg_left hkey hCpos.le
      _ = (C * 2 ^ (δ * (l : ℝ))) * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) := by ring
      _ ≤ D * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) :=
          mul_le_mul_of_nonneg_right hDle (Real.rpow_nonneg hpos1.le _)
  · -- trivial regime: `‖mstG‖ ≤ 1` and `(s+1)^{δ l} ≤ (N+1)^{δ l}`
    have hsN : s < N := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0]; exact lt_of_lt_of_le Nat.zero_lt_one hN1
      · exact lt_of_le_of_lt (Nat.le_self_pow hlne s) hlt
    have hsN' : (s : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hsN.le
    have hcle : ((s : ℝ) + 1) ^ (δ * (l : ℝ)) ≤ ((N : ℝ) + 1) ^ (δ * (l : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hsN' hδl.le
    have hDle : ((N : ℝ) + 1) ^ (δ * (l : ℝ)) ≤ D := by
      rw [hD]
      exact le_add_of_nonneg_left
        (mul_nonneg hCpos.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
    have hxne : ((s : ℝ) + 1) ^ (δ * (l : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hpos1 _)
    have hone : (1 : ℝ) ≤ D * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) := by
      calc (1 : ℝ)
          = ((s : ℝ) + 1) ^ (δ * (l : ℝ)) * (((s : ℝ) + 1) ^ (δ * (l : ℝ)))⁻¹ := by
            rw [mul_inv_cancel₀ hxne]
        _ ≤ D * (((s : ℝ) + 1) ^ (δ * (l : ℝ)))⁻¹ :=
            mul_le_mul_of_nonneg_right (le_trans hcle hDle)
              (inv_nonneg.mpr (Real.rpow_nonneg hpos1.le _))
        _ = D * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) := by
            rw [Real.rpow_neg hpos1.le]
    exact le_trans (mstG_norm_le_one P β) hone

end Work.BourgainPlan.Maximal
