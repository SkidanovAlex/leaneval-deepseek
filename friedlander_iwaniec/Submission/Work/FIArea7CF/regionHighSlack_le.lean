import Mathlib
import Submission.Work.FIArea7.Area7Regions6b
import Submission.Work.FIArea7.Area7Char6
import Submission.Work.FIArea7CF.card_dvd_im_gBox_le
import Submission.Work.FIArea7.Section16Expansion
import Submission.Work.FIArea7.pair_sum_le_card_sqrt
import Submission.Work.FIArea7.norm_omegaDetect_le_one
import Submission.Work.FIArea7.pairMass_fibre_le
import Submission.Work.FIArea7.sum_inv_sq_filter_le
import Submission.Work.FIArea7.sum_inv_Icc_le_two_log
import Submission.Work.FIArea7.isCoprime_coords_of_squarefree_gnorm
import Submission.Work.FIArea7.params_theta_le_quarter
import Submission.Work.FIArea7.UniPairMassDefs
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.isBetaCoeff6_mass_caps
import Submission.Work.FIArea7CF.regionHighSlackAux
import Submission.Work.FIArea7CF.regionSlackSum_le

set_option maxHeartbeats 1600000
namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary norm and filter helpers -/

/-- `‖(n : ℂ)‖ ≤ 1` for an integer `n` with `|n| ≤ 1`. -/
private lemma slack_norm_intCast_le_one {n : ℤ} (h : |((n : ℤ) : ℝ)| ≤ 1) :
    ‖((n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]; exact h

/-- `((4be : ℕ) : ℤ) = (4be : ℤ)`. -/
private lemma slack_cast_four_mul (b e : ℕ) : (((4 * b * e : ℕ)) : ℤ) = (4 * b * e : ℤ) := by
  push_cast; ring

/-- `Im(z̄₂z₁) = -Im(z̄₁z₂)`: the divisibility `Q ∣ Im(z̄₁z₂)` is symmetric in `z₁, z₂`. -/
private lemma slack_im_star_mul_swap (z1 z2 : GaussianInt) :
    (star z2 * z1).im = -((star z1 * z2).im) := by
  rw [Zsqrtd.im_mul, Zsqrtd.im_mul]; simp; ring

/-! ## The two real-arithmetic comparisons closing the two cases

Both are the analogues of `final_cmp1`/`final_cmp2` of `regionHigh_clashfree_le.lean`, with the
slack factor `2K+L₀+2` (i.e. the constants `600 → 1200`, `1000000 → 1200000`). -/

/-- The comparison closing the sharp route (`3 ≤ N`). -/
private lemma slack_final_cmp {Lk E2 Ec A1 A2 Clat : ℝ} (hLk : 0 ≤ Lk) (hE2 : 0 ≤ E2)
    (hEle : E2 ≤ Ec) (hEc : 0 ≤ Ec) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hcl : 0 ≤ Clat) :
    2 * (500 * Lk) * E2 * (Clat * (1200 * A1 + 2 * A2))
      ≤ 1200000 * (1 + Clat) * Ec * Lk * (A1 + A2) := by
  have hAB : 0 ≤ A1 + A2 := add_nonneg hA1 hA2
  have hcl1' : (0 : ℝ) ≤ 1 + Clat := by linarith
  have hClatle : Clat ≤ 1 + Clat := by linarith
  have hLk2 : 0 ≤ 2 * (500 * Lk) := by linarith
  have hbase : 0 ≤ 2 * (500 * Lk) * E2 := mul_nonneg hLk2 hE2
  have hb0 : 0 ≤ 1200 * A1 + 2 * A2 := by linarith
  have h1 : Clat * (1200 * A1 + 2 * A2) ≤ (1 + Clat) * (1200 * (A1 + A2)) := by
    calc Clat * (1200 * A1 + 2 * A2) ≤ (1 + Clat) * (1200 * A1 + 2 * A2) :=
          mul_le_mul_of_nonneg_right hClatle hb0
      _ ≤ (1 + Clat) * (1200 * (A1 + A2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hcl1'
  have h2 : 2 * (500 * Lk) * E2 * ((1 + Clat) * (1200 * (A1 + A2)))
      ≤ 1200000 * ((1 + Clat) * Ec * Lk * (A1 + A2)) := by
    have h3 : 2 * (500 * Lk) * E2 ≤ 2 * (500 * Lk) * Ec := mul_le_mul_of_nonneg_left hEle hLk2
    calc 2 * (500 * Lk) * E2 * ((1 + Clat) * (1200 * (A1 + A2)))
        ≤ 2 * (500 * Lk) * Ec * ((1 + Clat) * (1200 * (A1 + A2))) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 1200000 * ((1 + Clat) * Ec * Lk * (A1 + A2)) := by ring
  calc 2 * (500 * Lk) * E2 * (Clat * (1200 * A1 + 2 * A2))
      ≤ 2 * (500 * Lk) * E2 * ((1 + Clat) * (1200 * (A1 + A2))) :=
        mul_le_mul_of_nonneg_left h1 hbase
    _ ≤ 1200000 * ((1 + Clat) * Ec * Lk * (A1 + A2)) := h2
    _ = 1200000 * (1 + Clat) * Ec * Lk * (A1 + A2) := by ring

/-- The comparison closing the crude route (`N < 3`). -/
private lemma slack_crude_cmp {Lk E2 Ec A1 A2 Clat : ℝ} (hLk : 0 ≤ Lk) (hE2 : 0 ≤ E2)
    (hEle : E2 ≤ Ec) (hEc : 0 ≤ Ec) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hcl : 0 ≤ Clat) :
    2 * (500 * Lk) * (81 * E2) * (2 * A2) ≤ 1200000 * (1 + Clat) * Ec * Lk * (A1 + A2) := by
  have hAB : 0 ≤ A1 + A2 := add_nonneg hA1 hA2
  have hcl1 : (1 : ℝ) ≤ 1 + Clat := by linarith
  have hcl1' : (0 : ℝ) ≤ 1 + Clat := by linarith
  have hE2' : E2 ≤ (1 + Clat) * Ec := le_trans hEle (le_mul_of_one_le_left hEc hcl1)
  have hZ : 0 ≤ (1 + Clat) * Ec * Lk * (A1 + A2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hcl1' hEc) hLk) hAB
  have hA2le : A2 ≤ A1 + A2 := by linarith
  have hEcLk : 0 ≤ (1 + Clat) * Ec * Lk := mul_nonneg (mul_nonneg hcl1' hEc) hLk
  calc 2 * (500 * Lk) * (81 * E2) * (2 * A2)
      = 162000 * (Lk * E2 * A2) := by ring
    _ ≤ 162000 * (Lk * ((1 + Clat) * Ec) * A2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE2' hLk) hA2
    _ ≤ 162000 * ((1 + Clat) * Ec * Lk * (A1 + A2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc Lk * ((1 + Clat) * Ec) * A2 = (1 + Clat) * Ec * Lk * A2 := by ring
          _ ≤ (1 + Clat) * Ec * Lk * (A1 + A2) := mul_le_mul_of_nonneg_left hA2le hEcLk
    _ ≤ 1200000 * ((1 + Clat) * Ec * Lk * (A1 + A2)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hZ
    _ = 1200000 * (1 + Clat) * Ec * Lk * (A1 + A2) := by ring

/-- ***FI* (17.13), region II with the angular-mode slack**: the part of the (17.10) main term with
`4be(2K + L₀ + 2) > N^{δ₁}`.

The present result proves a bound for `Work.FIArea7.charRegionHigh6 Pa X K L₀ δ₁ β ε`
(`Submission/Work/FIArea7/Area7Regions6b.lean`; import it — the definition is the same sum as
`Work.FIArea7.charRegionHigh` with the threshold `4be(2K+L₀+2)` in place of `4be(2K+1)`): there are
`C Clat > 0` such that for all `Pa`, `X K L₀ : ℕ`, `φ`, `z0`, `β : GaussianInt → ℂ`,
`ε : GaussianInt → ℤ` and `δ₁ : ℝ` with `1 ≤ X`, `1 ≤ K`, `(L₀ : ℝ) ≤ 2*(K:ℝ)+1`, `0 < δ₁`,
`δ₁ < 3/32`, `Work.FITop4.IsBetaCoeff6 Pa φ z0 β`, `∀ z, |(ε z : ℝ)| ≤ 1`, the support cap

  `#{z ∈ gBox (radN Pa) : β z ≠ 0} ≤ 200(θ²N + θ√N + 1)`

and the second-moment cap `Σ_z ‖β z‖² ≤ 1000(θN + √N + 1)(log(2+N))³`, one has

  `‖charRegionHigh6 Pa X K L₀ δ₁ β ε‖
     ≤ C(1+Clat)·[1000(θN+√N+1)(log(2+N))³]·(log(K+2))²
         ·( X·(2K + L₀ + 2)·N^{1-δ₁} + X·log(uniB Pa + 2) )`.

This is *FI* (17.13) for a modulus larger than `N^{δ₁}/(2K+L₀+2)`: no use is made of Proposition 17.2,
and the saving comes from the lattice count `Σ_{z₂ : Q ∣ Im(z̄₁z₂)} 1 ≤ N/Q + 1`
(`Work.FIArea7.card_dvd_im_gBox_le`).

PROOF ROUTE (as reviewed): the statement of `Work.FIArea7.regionHigh_clashfree_le`
(`Submission/Work/FIArea7/regionHigh_clashfree_le.lean`) is the model — same proof, with `(2K+1)`
replaced by `(2K+L₀+2)` throughout.  Since `L₀ ≤ 2K+1` one has `2K+L₀+2 ≤ 4K+3 = 2(2K+1)+1`, so
the existing `regionHighSum100` (or its `private` sibling of the same shape) applied at
`K' = 2K+1` covers the *enlarged* high region, and `fibreCountLocal`/`uniCharTerm_le` do not depend
on the threshold.  The only real differences are the definition of the region, the factor
`2*K+1 → 2*K+L₀+2` in the conclusion and the extra hypothesis `(L₀:ℝ) ≤ 2*(K:ℝ)+1`; the constants
`C`, `Clat` may be chosen larger (the reviewer notes the reduction inflates `A1` by a factor `≤ 2`).
The two caps are exactly `Work.FIArea7.isBetaCoeff6_mass_caps`. -/
theorem regionHighSlack_le :
    ∃ C Clat : ℝ, 0 < C ∧ 0 < Clat ∧
      ∀ {Pa : Work.FITop.Params} {X K L₀ : ℕ} {φ : ℝ} {z0 : GaussianInt}
        {β : GaussianInt → ℂ} {ε : GaussianInt → ℤ} (δ₁ : ℝ),
        1 ≤ X → 1 ≤ K → 0 < δ₁ → δ₁ < 3 / 32 →
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        (∀ z : GaussianInt, |(ε z : ℝ)| ≤ 1) →
        (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
          ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) →
        (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
          ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 →
        ‖Work.FIArea7.charRegionHigh6 Pa X K L₀ δ₁ β ε‖
          ≤ C * (1 + Clat)
              * (1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3)
              * (Real.log ((K : ℝ) + 2)) ^ 2
              * ((X : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * Pa.N ^ (1 - δ₁)
                  + (X : ℝ) * Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)) := by
  obtain ⟨C0, hC0pos, hC0lat⟩ := card_dvd_im_gBox_le
  refine ⟨1200000, C0, by norm_num, hC0pos, ?_⟩
  intro Pa X K L₀ φ z0 β ε δ₁ hX hK hδ₁ hδ₁lt hβ hεAbs hcapS hcapE2
  have hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1 := fun z => slack_norm_intCast_le_one (hεAbs z)
  have hδ₁le : δ₁ ≤ 1 := le_of_lt (lt_trans hδ₁lt (by norm_num))
  set F : Finset (ℕ × ℕ) := ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
      (fun p => ¬ (4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁)) with hF
  set E2 : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 with hE2
  set E2cap : ℝ := 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 with hE2cap
  set Lk : ℝ := (Real.log ((K : ℝ) + 2)) ^ 2 with hLk
  set A1 : ℝ := (X : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) * Pa.N ^ (1 - δ₁) with hA1
  set A2 : ℝ := (X : ℝ) * Real.log ((uniB Pa : ℝ) + 2) with hA2
  have hE2le : E2 ≤ E2cap := by rw [hE2, hE2cap]; exact hcapE2
  have hE20 : 0 ≤ E2 := by rw [hE2]; exact Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hE2cap0 : 0 ≤ E2cap := by
    rw [hE2cap]
    have hθN : (0 : ℝ) ≤ Pa.θ * Pa.N :=
      mul_nonneg (le_of_lt Pa.hθ0) (le_trans (by norm_num) Pa.hN1)
    have hlog : (0 : ℝ) ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [hθN, Real.sqrt_nonneg Pa.N]))
      (pow_nonneg hlog 3)
  have hLk0 : 0 ≤ Lk := by rw [hLk]; exact sq_nonneg _
  have hcl0 : 0 ≤ C0 := le_of_lt hC0pos
  have hA10 : 0 ≤ A1 := by
    rw [hA1]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Real.rpow_nonneg (le_trans (by norm_num) Pa.hN1) _)
  have hA20 : 0 ≤ A2 := by
    rw [hA2]
    refine mul_nonneg (by positivity) (Real.log_nonneg ?_)
    have : (0 : ℝ) ≤ (uniB Pa : ℝ) := Nat.cast_nonneg _
    linarith
  have hunfold : charRegionHigh6 Pa X K L₀ δ₁ β ε
      = 2 * ∑ p ∈ F, uniCharTerm Pa p.1 p.2 β K ε := by rw [charRegionHigh6, hF]
  have hmemb : ∀ p ∈ F, p.1 ∈ Finset.Icc 1 (uniB Pa) ∧ p.2 ∈ Finset.Icc 1 X := by
    intro p hp
    rw [hF, Finset.mem_filter] at hp
    exact Finset.mem_product.mp hp.1
  have hpt : ∀ p ∈ F, 1 ≤ p.1 ∧ 1 ≤ p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hmemb p hp
    exact ⟨(Finset.mem_Icc.mp h1).1, (Finset.mem_Icc.mp h2).1⟩
  by_cases hN3 : 3 ≤ Pa.N
  · -- ===== the sharp route (`3 ≤ N`) =====
    have hterm : ∀ p ∈ F, ‖uniCharTerm Pa p.1 p.2 β K ε‖
        ≤ (1 / (p.1 : ℝ)) * (500 * Lk)
            * ((C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1)) * E2) := by
      intro p hp
      obtain ⟨hp1a, hp2a⟩ := hpt p hp
      have hrow : ∀ z1 : GaussianInt, β z1 ≠ 0 →
          (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z2 => β z2 ≠ 0 ∧ (((4 * p.1 * p.2 : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card
            : ℝ) ≤ C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1) := by
        intro z1 hz1
        have h := fibreCountLocal_slack hβ hN3 hC0lat hp1a hp2a hz1
        have heq : ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z2 => β z2 ≠ 0 ∧ (((4 * p.1 * p.2 : ℕ)) : ℤ) ∣ (star z1 * z2).im))
            = ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z2 => β z2 ≠ 0 ∧ (4 * p.1 * p.2 : ℤ) ∣ (star z1 * z2).im)) := by
          refine Finset.filter_congr (fun z2 _ => ?_)
          rw [slack_cast_four_mul]
        rw [heq]
        exact h
      have hcol : ∀ z2 : GaussianInt, β z2 ≠ 0 →
          (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z1 => β z1 ≠ 0 ∧ (((4 * p.1 * p.2 : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card
            : ℝ) ≤ C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1) := by
        intro z2 hz2
        have h := fibreCountLocal_slack (z1 := z2) hβ hN3 hC0lat hp1a hp2a hz2
        have hfilter : ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z1 => β z1 ≠ 0 ∧ (((4 * p.1 * p.2 : ℕ)) : ℤ) ∣ (star z1 * z2).im))
            = ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun w => β w ≠ 0 ∧ (4 * p.1 * p.2 : ℤ) ∣ (star z2 * w).im)) := by
          refine Finset.filter_congr (fun w _ => ?_)
          refine and_congr_right (fun hw => ?_)
          rw [slack_cast_four_mul, slack_im_star_mul_swap w z2]
          constructor
          · intro hd; exact dvd_neg.mpr hd
          · intro hd; exact dvd_neg.mp hd
        rw [hfilter]
        exact h
      have h := uniCharTerm_le_slack Pa K β ε hK hε hp1a hp2a
        (C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1))
        (mul_nonneg hcl0 (by positivity)) hrow hcol
      simpa [hLk, hE2] using h
    have hsum : ∑ p ∈ F, (1 / (p.1 : ℝ)) * (C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1))
        ≤ C0 * (1200 * A1 + 2 * A2) := by
      rw [show (∑ p ∈ F, (1 / (p.1 : ℝ)) * (C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1)))
          = C0 * ∑ p ∈ F, (1 / (p.1 : ℝ))
              * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)]
      refine mul_le_mul_of_nonneg_left ?_ hcl0
      rw [hF, hA1, hA2]
      exact regionSlackSum_le (uniB Pa) X K L₀ Pa.N δ₁ Pa.hN1 hδ₁ hδ₁le
    calc ‖charRegionHigh6 Pa X K L₀ δ₁ β ε‖
        = 2 * ‖∑ p ∈ F, uniCharTerm Pa p.1 p.2 β K ε‖ := by rw [hunfold, norm_mul]; norm_num
      _ ≤ 2 * ∑ p ∈ F, ‖uniCharTerm Pa p.1 p.2 β K ε‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      _ ≤ 2 * ∑ p ∈ F, (1 / (p.1 : ℝ)) * (500 * Lk)
            * ((C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1)) * E2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      _ = 2 * (500 * Lk) * E2
            * (∑ p ∈ F, (1 / (p.1 : ℝ))
                * (C0 * (100 * Pa.N / (4 * (p.1 : ℝ) * (p.2 : ℝ)) + 1))) := by
          conv_lhs => rw [Finset.mul_sum]
          conv_rhs => rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ 2 * (500 * Lk) * E2 * (C0 * (1200 * A1 + 2 * A2)) :=
          mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hLk0)) hE20)
      _ ≤ 1200000 * (1 + C0) * E2cap * Lk * (A1 + A2) :=
          slack_final_cmp hLk0 hE20 hE2le hE2cap0 hA10 hA20 hcl0
  · -- ===== the crude route (`N < 3`) =====
    push_neg at hN3
    have hrad4 : Work.FITop.radN Pa ≤ 4 := by
      rw [Work.FITop.radN]
      have h : Real.sqrt (4 * Pa.N) < 4 := by
        rw [Real.sqrt_lt' (by norm_num)]
        linarith
      have h2 : Nat.ceil (Real.sqrt (4 * Pa.N)) ≤ 4 := Nat.ceil_le.mpr (le_of_lt h)
      exact_mod_cast h2
    have hcard81 : ((Work.FIPlan.gBox (Work.FITop.radN Pa)).card : ℝ) ≤ 81 := by
      have h9 : (2 * Work.FITop.radN Pa + 1).toNat ≤ 9 := by
        have h : (2 * Work.FITop.radN Pa + 1 : ℤ) ≤ 9 := by omega
        calc (2 * Work.FITop.radN Pa + 1).toNat ≤ (9 : ℤ).toNat := Int.toNat_le_toNat h
          _ = 9 := by decide
      rw [gBox_card_eq]
      have h9R : (((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) ≤ 9 := by exact_mod_cast h9
      have hnn : (0 : ℝ) ≤ (((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith [h9R, hnn]
    have hterm : ∀ p ∈ F, ‖uniCharTerm Pa p.1 p.2 β K ε‖
        ≤ (1 / (p.1 : ℝ)) * (500 * Lk) * (81 * E2) := by
      intro p hp
      obtain ⟨hp1a, hp2a⟩ := hpt p hp
      have hrow : ∀ z1 : GaussianInt, β z1 ≠ 0 →
          (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z2 => β z2 ≠ 0 ∧ (((4 * p.1 * p.2 : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card
            : ℝ) ≤ 81 := by
        intro z1 hz1
        refine le_trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) hcard81
      have hcol : ∀ z2 : GaussianInt, β z2 ≠ 0 →
          (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z1 => β z1 ≠ 0 ∧ (((4 * p.1 * p.2 : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card
            : ℝ) ≤ 81 := by
        intro z2 hz2
        refine le_trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) hcard81
      have h := uniCharTerm_le_slack Pa K β ε hK hε hp1a hp2a 81 (by norm_num) hrow hcol
      simpa [hLk, hE2] using h
    have hsum : ∑ p ∈ F, (1 / (p.1 : ℝ)) ≤ (X : ℝ) * (1 + Real.log (uniB Pa)) := by
      calc ∑ p ∈ F, (1 / (p.1 : ℝ))
          ≤ ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)), (1 / (p.1 : ℝ)) := by
            rw [hF]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun p _ _ => by positivity)
        _ = ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X, (1 / (b : ℝ)) := by
            rw [Finset.product_eq_sprod, Finset.sum_product]
        _ = (X : ℝ) * ∑ b ∈ Finset.Icc 1 (uniB Pa), (1 / (b : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
            simp
        _ ≤ (X : ℝ) * (1 + Real.log (uniB Pa)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h := harmonic_le_one_add_log (uniB Pa)
            rw [harmonic_eq_sum_Icc] at h
            simpa [one_div] using h
    have hlogB : 1 + Real.log (uniB Pa) ≤ 2 * Real.log ((uniB Pa : ℝ) + 2) := by
      rcases Nat.eq_zero_or_pos (uniB Pa) with h0 | h0
      · rw [h0]
        have h2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
          have := Real.log_two_gt_d9
          linarith
        simpa using h2
      · have hlog1 : 1 ≤ Real.log ((uniB Pa : ℝ) + 2) := by
          have h3 : (3 : ℝ) ≤ (uniB Pa : ℝ) + 2 := by
            have : (1 : ℝ) ≤ (uniB Pa : ℝ) := by exact_mod_cast h0
            linarith
          have hlog3 : 1 < Real.log 3 := by
            have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
            rwa [Real.log_exp] at h
          exact le_of_lt (lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) h3))
        have hlogle : Real.log (uniB Pa : ℝ) ≤ Real.log ((uniB Pa : ℝ) + 2) :=
          Real.log_le_log (by exact_mod_cast h0) (by linarith)
        linarith
    calc ‖charRegionHigh6 Pa X K L₀ δ₁ β ε‖
        = 2 * ‖∑ p ∈ F, uniCharTerm Pa p.1 p.2 β K ε‖ := by rw [hunfold, norm_mul]; norm_num
      _ ≤ 2 * ∑ p ∈ F, ‖uniCharTerm Pa p.1 p.2 β K ε‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      _ ≤ 2 * ∑ p ∈ F, (1 / (p.1 : ℝ)) * (500 * Lk) * (81 * E2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      _ = 2 * (500 * Lk) * (81 * E2) * (∑ p ∈ F, (1 / (p.1 : ℝ))) := by
          conv_lhs => rw [Finset.mul_sum]
          conv_rhs => rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ 2 * (500 * Lk) * (81 * E2) * ((X : ℝ) * (1 + Real.log (uniB Pa))) := by
          refine mul_le_mul_of_nonneg_left hsum ?_
          exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hLk0))
            (mul_nonneg (by norm_num) hE20)
      _ ≤ 2 * (500 * Lk) * (81 * E2) * ((X : ℝ) * (2 * Real.log ((uniB Pa : ℝ) + 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · have hX0 : 0 ≤ (X : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_left hlogB hX0
          · exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hLk0))
              (mul_nonneg (by norm_num) hE20)
      _ ≤ 1200000 * (1 + C0) * E2cap * Lk * (A1 + A2) := by
          have h2A2 : (X : ℝ) * (2 * Real.log ((uniB Pa : ℝ) + 2)) = 2 * A2 := by
            rw [hA2]; ring
          rw [h2A2]
          exact slack_crude_cmp hLk0 hE20 hE2le hE2cap0 hA10 hA20 hcl0

end

end Work.FIArea7
