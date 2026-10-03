/-
# `Submission.Work.FIArea7.regionHighSlackAux` — the clash-free analytic block of region II

`Submission/Work/FIArea7/regionHigh_clashfree_le.lean` proves, inside its (private) §1–§7, the two
analytic inputs of the region-II estimate:

* `uniCharTerm_le_slack`: the per-`(b,e)` bound
  `‖uniCharTerm Pa b e β K ε‖ ≤ (1/b)·500·(log(K+2))²·(M·Σ_z‖β z‖²)` from the row/column fibre bound
  `M` (via the §16 pair expansion and the pair-mass Cauchy–Schwarz of *NOTES* §59.3);
* `fibreCountLocal_slack`: the supported-`z₁` fibre count `Clat·(100·N/(4be) + 1)` from the lattice
  hypothesis `hlat`.

Both are `private` in that file and therefore not usable from a sibling module.  This module
re-publishes them under cluster-B-safe names (`cf_mem_gBox_iff` comes from
`card_gBox_filter_dvd_absDelta`; neither `R2countDefs` nor `charRegionHigh_le`, which carry the
duplicate public `Work.FIArea7.cf_mem_gBox_iff`/`Work.FIArea7.uniCharTerm_le`, is imported), so that
`Submission/Work/FIArea7/regionHighSlack_le.lean` can consume them.

The body of §1–§7 below is a verbatim copy of the corresponding block of
`regionHigh_clashfree_le.lean` (the two theorems renamed); all auxiliary declarations stay
`private`, so this module adds only `uniCharTerm_le_slack` and `fibreCountLocal_slack` to the
namespace.
-/
import Mathlib
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

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary norm bounds -/

/-! ## 1. Elementary norm bounds -/

/-- `‖(n : ℂ)‖ = |(n : ℝ)|` for an integer `n`. -/
private lemma norm_intCast_complex (n : ℤ) : ‖((n : ℤ) : ℂ)‖ = |((n : ℤ) : ℝ)| :=
  Complex.norm_intCast n

/-- `‖(n : ℂ)‖ ≤ 1` for an integer with `|n| ≤ 1`. -/
private lemma norm_intCast_complex_le_one {n : ℤ} (h : |((n : ℤ) : ℝ)| ≤ 1) : ‖((n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_intCast_complex]; exact h

/-- `‖uniPow z k‖ ≤ 1` for every `z` (including `z = 0`). -/
private lemma norm_uniPow_le_one (z : GaussianInt) (k : ℤ) : ‖uniPow z k‖ ≤ 1 := by
  rw [uniPow]
  by_cases hz : z.toComplex = 0
  · rw [hz, zero_div, norm_zpow, norm_zero, zero_zpow_eq]
    split <;> norm_num
  · have hnorm : ‖z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
    rw [norm_zpow, hnorm]
    simp

/-- `‖uniCoeff ε β k z‖ ≤ ‖β z‖` as soon as `‖ε z‖ ≤ 1` (`‖betaPrime‖ ≤ ‖β‖`, `‖uniPow‖ ≤ 1`). -/
private lemma uniCoeff_norm_le (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ)
    (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) (z : GaussianInt) :
    ‖uniCoeff ε β k z‖ ≤ ‖β z‖ := by
  rw [uniCoeff, norm_mul, norm_mul]
  calc ‖((ε z : ℤ) : ℂ)‖ * ‖betaPrime β z‖ * ‖uniPow z k‖
      ≤ 1 * ‖β z‖ * 1 := by
        gcongr
        · exact hε z
        · exact norm_betaPrime_le β z
        · exact norm_uniPow_le_one z k
    _ = ‖β z‖ := by ring

/-- `unitInd Q z` has norm at most `1`. -/
private lemma norm_unitInd_le_one' (Q : ℕ) (z : GaussianInt) : ‖unitInd Q z‖ ≤ 1 := by
  rw [unitInd]; split <;> simp
/-! ## 2. `uniModeCharSum` as a sum over the pairs of the box -/

/-- **The §16 expansion of `uniModeCharSum` as a pair sum.**  `uniModeCharSum` is the right-hand
side of the §16 identity `section16_omegaDetect_expansion` at `c = uniCoeff ε β k`, so it equals
the left-hand side, the box sum of the pairs `(z₁,z₂)` weighted by `unitInd` and the `ω`-detection
`omegaDetect`. -/
private theorem uniModeCharSum_eq_pairSum (Pa : Work.FITop.Params) (b e : ℕ) [NeZero (4 * b * e)]
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ) :
    uniModeCharSum Pa b e β k ε
      = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
              * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
              * omegaDetect (4 * b * e) e z1 z2 := by
  have hexp := section16_omegaDetect_expansion (Work.FITop.radN Pa) (4 * b * e) e
    (uniCoeff ε β k)
  rw [uniModeCharSum]
  rw [show (∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
        uniJChar (4 * b * e) e χ * (uniSChar Pa (4 * b * e) ε β k χ)
          * star (uniSChar Pa (4 * b * e) ε β k χ))
      = (∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
          (∑ p : GaussUnit (4 * b * e), ratWeight (4 * b * e) e p * χ (Additive.ofMul p)) *
            ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                unitCoeff (4 * b * e) (uniCoeff ε β k) z * χ (Additive.ofMul (unitClassD (4 * b * e) z))) *
             star (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                unitCoeff (4 * b * e) (uniCoeff ε β k) z
                  * χ (Additive.ofMul (unitClassD (4 * b * e) z))))) from by
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      simp only [uniJChar, uniSChar, mul_assoc]]
  rw [← hexp]
  refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
  rw [omegaDetect_unfold6]

/-! ## 3. The pointwise bound on a summand of the pair sum -/

/-- **The summand bound.**  A summand of the pair sum vanishes unless `β z₁ ≠ 0 ≠ β z₂` and
`4be ∣ Im(z̄₁z₂)`, and then its norm is at most `‖β z₁‖‖β z₂‖`. -/
private lemma uniModeCharSum_summand_le (b e : ℕ) [NeZero (4 * b * e)] (β : GaussianInt → ℂ) (k : ℤ)
    (ε : GaussianInt → ℤ) (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) (z1 z2 : GaussianInt) :
    ‖unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
        * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2)) * omegaDetect (4 * b * e) e z1 z2‖
      ≤ (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im
          then ‖β z1‖ * ‖β z2‖ else 0) := by
  by_cases h : β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im
  · rw [if_pos h]
    obtain ⟨h1, h2, hd⟩ := h
    by_cases hc1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e)
    · by_cases hc2 : Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e)
      · have key : ‖unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
            * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
            * omegaDetect (4 * b * e) e z1 z2‖
            ≤ 1 * 1 * (‖β z1‖ * ‖β z2‖) * 1 := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_star]
          gcongr
          · exact norm_unitInd_le_one' _ _
          · exact norm_unitInd_le_one' _ _
          · exact uniCoeff_norm_le β k ε hε z1
          · exact uniCoeff_norm_le β k ε hε z2
          · exact norm_omegaDetect_le_one (4 * b * e) e z1 z2 hc1 hc2
        simpa using key
      · have h0 : unitInd (4 * b * e) z2 = 0 := by rw [unitInd, if_neg hc2]
        rw [h0]; simp only [mul_zero, zero_mul, norm_zero]; positivity
    · have h0 : unitInd (4 * b * e) z1 = 0 := by rw [unitInd, if_neg hc1]
      rw [h0]; simp only [mul_zero, zero_mul, norm_zero]; positivity
  · rw [if_neg h]
    rw [norm_le_zero_iff]
    by_cases h1 : β z1 = 0
    · have h0 : uniCoeff ε β k z1 = 0 := by simp [uniCoeff, betaPrime, h1]
      rw [h0]; ring
    · by_cases h2 : β z2 = 0
      · have h0 : uniCoeff ε β k z2 = 0 := by simp [uniCoeff, betaPrime, h2]
        rw [h0]; simp
      · have hd : ¬ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im := fun hd => h ⟨h1, h2, hd⟩
        have hz : omegaDetect (4 * b * e) e z1 z2 = 0 := by
          by_contra hne
          exact hd (dvd_delta_of_omegaDetect_ne_zero (4 * b * e) e z1 z2 hne)
        rw [hz]; ring

/-! ## 4. The pair-mass estimate for `uniModeCharSum` -/

/-- The box sum of an `if`-then-else is the sum over the filtered product. -/
private lemma sum_box_ite (s : Finset GaussianInt) (P : GaussianInt → GaussianInt → Prop) [DecidableRel P]
    (g : GaussianInt → GaussianInt → ℝ) :
    (∑ z1 ∈ s, ∑ z2 ∈ s, (if P z1 z2 then g z1 z2 else 0))
      = ∑ p ∈ (s ×ˢ s).filter (fun p => P p.1 p.2), g p.1 p.2 := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]

/-- `Im(z̄₂z₁) = -Im(z̄₁z₂)`: the divisibility `Q ∣ Im(z̄₁z₂)` is symmetric in `z₁, z₂`. -/
private lemma im_star_mul_swap (z1 z2 : GaussianInt) : (star z2 * z1).im = -((star z1 * z2).im) := by
  rw [Zsqrtd.im_mul, Zsqrtd.im_mul]; simp; ring

/-- `((4be : ℕ) : ℤ) = (4be : ℤ)`. -/
private lemma cast_four_mul (b e : ℕ) : (((4 * b * e : ℕ)) : ℤ) = (4 * b * e : ℤ) := by
  push_cast; ring

/-- **The pair-mass estimate for one mode**, with an abstract fibre bound `M`: if every row and
every column of the pair set `{Q ∣ Im(z̄₁z₂)}` inside the support box has at most `M` elements,
then `‖uniModeCharSum‖ ≤ M·Σ_z‖β z‖²`. -/
private theorem uniModeCharSum_pairMass_le {Pa : Work.FITop.Params} (b e : ℕ) [NeZero (4 * b * e)]
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ)
    (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ z1 : GaussianInt, β z1 ≠ 0 →
      (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z2 => β z2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card : ℝ) ≤ M)
    (hcol : ∀ z2 : GaussianInt, β z2 ≠ 0 →
      (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z1 => β z1 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card : ℝ) ≤ M) :
    ‖uniModeCharSum Pa b e β k ε‖
      ≤ M * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) := by
  classical
  set s : Finset GaussianInt := Work.FIPlan.gBox (Work.FITop.radN Pa) with hs
  set T : Finset (GaussianInt × GaussianInt) := (s ×ˢ s).filter
      (fun p : GaussianInt × GaussianInt =>
        β p.1 ≠ 0 ∧ β p.2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star p.1 * p.2).im) with hT
  have hbound : ‖uniModeCharSum Pa b e β k ε‖ ≤ ∑ p ∈ T, ‖β p.1‖ * ‖β p.2‖ := by
    rw [uniModeCharSum_eq_pairSum Pa b e β k ε]
    calc ‖∑ z1 ∈ s, ∑ z2 ∈ s, unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
              * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
              * omegaDetect (4 * b * e) e z1 z2‖
        ≤ ∑ z1 ∈ s, ∑ z2 ∈ s, ‖unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
              * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
              * omegaDetect (4 * b * e) e z1 z2‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum (fun z1 _ => ?_)
          exact norm_sum_le _ _
      _ ≤ ∑ z1 ∈ s, ∑ z2 ∈ s, (if β z1 ≠ 0 ∧ β z2 ≠ 0
              ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im
              then ‖β z1‖ * ‖β z2‖ else 0) := by
          refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
          exact uniModeCharSum_summand_le b e β k ε hε z1 z2
      _ = ∑ p ∈ T, ‖β p.1‖ * ‖β p.2‖ := by
          rw [hT, hs]
          exact sum_box_ite _ _ _
  refine le_trans hbound (pairMass_fibre_le s (fun z => ‖β z‖) T M hM ?_ ?_ ?_ ?_)
  · intro p hp
    rw [hT] at hp; rw [Finset.mem_filter] at hp
    rw [hs] at hp ⊢; exact (Finset.mem_product.mp hp.1).1
  · intro p hp
    rw [hT] at hp; rw [Finset.mem_filter] at hp
    rw [hs] at hp ⊢; exact (Finset.mem_product.mp hp.1).2
  · intro z hz
    by_cases hzβ : β z = 0
    · have hcard0 : (T.filter (fun p => p.1 = z)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpT, hpz⟩ := hp
        rw [hT, Finset.mem_filter] at hpT
        exact hpT.2.1 (by rw [hpz]; exact hzβ)
      rw [hcard0]; simpa using hM
    · rw [hs] at hz
      have hrowz := hrow z hzβ
      have hinj : Set.InjOn (fun p : GaussianInt × GaussianInt => p.2)
          ↑(T.filter (fun p => p.1 = z)) := by
        intro p1 hp1 p2 hp2 heq
        rw [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
        exact Prod.ext (by rw [hp1.2, hp2.2]) heq
      have hcard : (T.filter (fun p => p.1 = z)).card
          = ((T.filter (fun p => p.1 = z)).image (fun p : GaussianInt × GaussianInt => p.2)).card :=
        (Finset.card_image_of_injOn hinj).symm
      have himg : (T.filter (fun p => p.1 = z)).image (fun p : GaussianInt × GaussianInt => p.2)
          ⊆ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z2 => β z2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z * z2).im) := by
        intro z2 hz2
        rw [Finset.mem_image] at hz2
        obtain ⟨p, hp, rfl⟩ := hz2
        rw [Finset.mem_filter] at hp
        obtain ⟨hpT, hpz⟩ := hp
        rw [hT, Finset.mem_filter] at hpT
        obtain ⟨hpmem, hb1, hb2, hdvd⟩ := hpT
        rw [Finset.mem_filter]
        refine ⟨(Finset.mem_product.mp hpmem).2, hb2, ?_⟩
        rw [hpz] at hdvd
        exact hdvd
      calc ((T.filter (fun p => p.1 = z)).card : ℝ)
          = (((T.filter (fun p => p.1 = z)).image
              (fun p : GaussianInt × GaussianInt => p.2)).card : ℝ) := by rw [hcard]
        _ ≤ (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z2 => β z2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z * z2).im)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card himg
        _ ≤ M := hrowz
  · intro z hz
    by_cases hzβ : β z = 0
    · have hcard0 : (T.filter (fun p => p.2 = z)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpT, hpz⟩ := hp
        rw [hT, Finset.mem_filter] at hpT
        exact hpT.2.2.1 (by rw [hpz]; exact hzβ)
      rw [hcard0]; simpa using hM
    · rw [hs] at hz
      have hcolz := hcol z hzβ
      have hinj : Set.InjOn (fun p : GaussianInt × GaussianInt => p.1)
          ↑(T.filter (fun p => p.2 = z)) := by
        intro p1 hp1 p2 hp2 heq
        rw [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
        exact Prod.ext heq (by rw [hp1.2, hp2.2])
      have hcard : (T.filter (fun p => p.2 = z)).card
          = ((T.filter (fun p => p.2 = z)).image (fun p : GaussianInt × GaussianInt => p.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
      have himg : (T.filter (fun p => p.2 = z)).image (fun p : GaussianInt × GaussianInt => p.1)
          ⊆ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z1 => β z1 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z).im) := by
        intro z1 hz1
        rw [Finset.mem_image] at hz1
        obtain ⟨p, hp, rfl⟩ := hz1
        rw [Finset.mem_filter] at hp
        obtain ⟨hpT, hpz⟩ := hp
        rw [hT, Finset.mem_filter] at hpT
        obtain ⟨hpmem, hb1, hb2, hdvd⟩ := hpT
        rw [Finset.mem_filter]
        refine ⟨(Finset.mem_product.mp hpmem).1, hb1, ?_⟩
        rw [hpz] at hdvd
        exact hdvd
      calc ((T.filter (fun p => p.2 = z)).card : ℝ)
          = (((T.filter (fun p => p.2 = z)).image
              (fun p : GaussianInt × GaussianInt => p.1)).card : ℝ) := by rw [hcard]
        _ ≤ (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z1 => β z1 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z).im)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card himg
        _ ≤ M := hcolz

/-- `gnorm z = re.natAbs ^ 2 + im.natAbs ^ 2`. -/
private lemma gnorm_eq_re_sq_add_im_sq (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simp only [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]

/-- `4√(5N/4) ≤ 5√N` for `N ≥ 1`. -/
private lemma four_sqrt_five_quarter_le (N : ℝ) (hN : 1 ≤ N) :
    4 * Real.sqrt (5 / 4 * N) ≤ 5 * Real.sqrt N := by
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : 4 * Real.sqrt (5 / 4 * N) = Real.sqrt (20 * N) := by
    rw [← h16, ← Real.sqrt_mul (show (0 : ℝ) ≤ 16 by norm_num)]
    congr 1
    ring
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h2 : Real.sqrt (20 * N) ≤ Real.sqrt (25 * N) := Real.sqrt_le_sqrt (by linarith)
  have h3 : Real.sqrt (25 * N) = 5 * Real.sqrt N := by
    rw [show (25 : ℝ) * N = 5 ^ 2 * N by ring, Real.sqrt_mul (show (0 : ℝ) ≤ 5 ^ 2 by norm_num),
        Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
  linarith [h1, h2, h3]

/-- **The fibre count needed by region II:** for a supported `z₁` the number of *supported* `z₂` of
the support box with `4be ∣ Im(z̄₁z₂)` is at most `Clat·(100·N/(4be) + 1)`.

SUGGESTED ROUTE (the lattice hypothesis `hlat` CANNOT be applied at `R = radN`: the side condition
`R² ≤ 4·gnorm z₁` may fail, e.g. `N = 4.5`, `z₁ = 1+2i`, `gnorm z₁ = 5`, `radN = 5`; the point is
that `hlat` is applied at the *smaller* radius `R₁ = ⌊2√(gnorm z₁)⌋`, which still contains every
*supported* `z₂`).

Let `g1 = gnorm z1`. From `hz1`, `hβ.support` gives `InPolarBox Pa φ z1`, hence `Pa.N < g1` and
`(g1:ℝ) ≤ (1+Pa.θ)*Pa.N ≤ 5/4*Pa.N` (`params_theta_le_quarter`); `hβ.squarefree_gnorm hz1` gives
`Squarefree g1`, hence `IsCoprime z1.re z1.im` (`isCoprime_coords_of_squarefree_gnorm`).
Set `R1 : ℤ := ⌊2 * Real.sqrt (g1 : ℝ)⌋₊`.  Apply `hlat` at `R = R1`, `m = 4*b*e`, `z1`:
`0 ≤ R1`, `1 ≤ 4*b*e`, `(R1:ℝ)² ≤ 4*(g1:ℝ)` (floor), `(g1:ℝ) ≤ 4*((R1:ℝ)+1)²` (as `R1+1 > 2√g1`).
It remains to prove the inclusion of filters: for `z2 ∈ gBox (radN Pa)` with `β z2 ≠ 0` and
`4be ∣ Im(z̄₁z₂)` one has `z2 ∈ gBox R1`, i.e. `|z2.re| ≤ R1` and `|z2.im| ≤ R1`: indeed
`|z2.re| ≤ √(gnorm z2) ≤ √((1+θ)N) ≤ √(5N/4)` and `R1 ≥ 2√N - 1 ≥ √(5N/4)` because `N ≥ 3`
(`0.882·√N ≥ 1`).  Finally `(2*R1+1)² ≤ 100*N` since `R1 ≤ 2√(5N/4) ≤ 2.24√N`. -/
theorem fibreCountLocal_slack {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hN3 : 3 ≤ Pa.N) {Clat : ℝ}
    (hlat : ∀ (R : ℤ) (m : ℕ) (z1 : GaussianInt),
        0 ≤ R → 1 ≤ m → IsCoprime z1.re z1.im →
        (R : ℝ) ^ 2 ≤ 4 * (Work.FIPlan.gnorm z1 : ℝ) →
        (Work.FIPlan.gnorm z1 : ℝ) ≤ 4 * ((R : ℝ) + 1) ^ 2 →
        (((Work.FIPlan.gBox R).filter (fun z2 => (m : ℤ) ∣ (star z1 * z2).im)).card : ℝ)
          ≤ Clat * (((2 * (R : ℝ) + 1) ^ 2) / (m : ℝ) + 1))
    {b e : ℕ} (hb : 1 ≤ b) (he : 1 ≤ e) {z1 : GaussianInt} (hz1 : β z1 ≠ 0) :
    (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
        (fun z2 => β z2 ≠ 0 ∧ (4 * b * e : ℤ) ∣ (star z1 * z2).im)).card : ℝ)
      ≤ Clat * (100 * Pa.N / (4 * b * e : ℝ) + 1) := by
  -- ## Step 0: `0 ≤ Clat`, from `hlat` at the trivial configuration `R = 0`, `m = 1`, `z1 = 1`.
  have hClat_nonneg : 0 ≤ Clat := by
    have h := hlat 0 1 1 (le_refl (0 : ℤ)) (le_refl (1 : ℕ))
      (show IsCoprime ((1 : GaussianInt).re) ((1 : GaussianInt).im) from isCoprime_one_left)
      (by norm_num [Work.FIPlan.gnorm]) (by norm_num [Work.FIPlan.gnorm])
    have h0 : (0 : ℝ) ≤ (((Work.FIPlan.gBox (0 : ℤ)).filter
        (fun z2 => ((1 : ℕ) : ℤ) ∣ (star (1 : GaussianInt) * z2).im)).card : ℝ) :=
      Nat.cast_nonneg _
    have h2 : Clat * (((2 * ((0 : ℤ) : ℝ) + 1) ^ 2) / (((1 : ℕ) : ℝ)) + 1) = 2 * Clat := by
      norm_num; ring
    rw [h2] at h
    linarith
  -- ## Step 1: the polar-box data for `z1`.
  obtain ⟨-, hg1gt, hg1le, -⟩ := hβ.support hz1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hN1 : (1 : ℝ) ≤ Pa.N := by linarith
  have hθq : Pa.θ ≤ 1 / 4 := params_theta_le_quarter Pa
  have hcop : IsCoprime z1.re z1.im :=
    isCoprime_coords_of_squarefree_gnorm (hβ.squarefree_gnorm hz1)
  -- ## Step 2: the radius `R1 = ⌊2√g1⌋`.
  set g1 : ℕ := Work.FIPlan.gnorm z1 with hg1
  set R1n : ℕ := ⌊2 * Real.sqrt (g1 : ℝ)⌋₊ with hR1n
  set R1 : ℤ := (R1n : ℤ) with hR1
  have hR1n_le : (R1n : ℝ) ≤ 2 * Real.sqrt (g1 : ℝ) := by
    rw [hR1n]; exact Nat.floor_le (by positivity)
  have hR1n_lt : 2 * Real.sqrt (g1 : ℝ) < (R1n : ℝ) + 1 := by
    rw [hR1n]; exact Nat.lt_floor_add_one _
  have hR1nonneg : (0 : ℤ) ≤ R1 := by rw [hR1]; exact Int.natCast_nonneg _
  have hR1nn : (0 : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hR1nonneg
  have hR1le : (R1 : ℝ) ≤ 2 * Real.sqrt (g1 : ℝ) := by
    rw [hR1]; push_cast; exact hR1n_le
  have hR1lt : 2 * Real.sqrt (g1 : ℝ) < (R1 : ℝ) + 1 := by
    rw [hR1]; push_cast; exact hR1n_lt
  have hsqR1 : (R1 : ℝ) ^ 2 ≤ 4 * (g1 : ℝ) := by
    have h := pow_le_pow_left₀ hR1nn hR1le 2
    have h2 : (2 * Real.sqrt (g1 : ℝ)) ^ 2 = 4 * (g1 : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    rw [h2] at h; exact h
  have hsqrtg1nn : (0 : ℝ) ≤ Real.sqrt (g1 : ℝ) := Real.sqrt_nonneg _
  have hgnR1 : (g1 : ℝ) ≤ 4 * ((R1 : ℝ) + 1) ^ 2 := by
    have hlt2 : Real.sqrt (g1 : ℝ) < ((R1 : ℝ) + 1) / 2 := by linarith [hR1lt]
    have hle2 : Real.sqrt (g1 : ℝ) ≤ 2 * ((R1 : ℝ) + 1) := by linarith [hR1nn]
    have h := pow_le_pow_left₀ hsqrtg1nn hle2 2
    rw [Real.sq_sqrt (by positivity)] at h
    have h2 : (2 * ((R1 : ℝ) + 1)) ^ 2 = 4 * ((R1 : ℝ) + 1) ^ 2 := by ring
    rw [h2] at h; exact h
  -- ## Step 3: apply `hlat` at radius `R1` and modulus `4be`.
  have h4be : 1 ≤ 4 * b * e := by
    have h : 4 * 1 * 1 ≤ 4 * b * e := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hb) he
    omega
  have hlatres := hlat R1 (4 * b * e) z1 hR1nonneg h4be hcop hsqR1 hgnR1
  -- ## Step 4: every supported `z₂` of the support box lies in the smaller box `gBox R1`.
  have hmem : ∀ z2 : GaussianInt, β z2 ≠ 0 → z2 ∈ Work.FIPlan.gBox R1 := by
    intro z2 hz2β
    obtain ⟨-, -, hg2le0, -, -⟩ := hβ.support hz2β
    have hg2le : (Work.FIPlan.gnorm z2 : ℝ) ≤ 5 / 4 * Pa.N := by
      have h1 : 1 + Pa.θ ≤ 1 + 1 / 4 := by linarith [hθq]
      have h2 : (1 + Pa.θ) * Pa.N ≤ (1 + 1 / 4) * Pa.N :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hNpos)
      linarith [hg2le0, h2]
    have h4g1 : 5 / 4 * Pa.N < 4 * (g1 : ℝ) := by linarith [hg1gt, hNpos]
    have hcoord : ∀ n : ℕ, n ^ 2 ≤ Work.FIPlan.gnorm z2 → n ≤ R1n := by
      intro n hn
      have hnR : ((n : ℝ)) ^ 2 ≤ 5 / 4 * Pa.N := by
        have h1 : ((n : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z2 : ℝ) := by
          exact_mod_cast hn
        linarith
      have h2 : (2 * Real.sqrt (g1 : ℝ)) ^ 2 = 4 * (g1 : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
      have hsq_lt : ((n : ℝ)) ^ 2 < (2 * Real.sqrt (g1 : ℝ)) ^ 2 := by
        rw [h2]; linarith
      have hlt : (n : ℝ) < 2 * Real.sqrt (g1 : ℝ) := by
        have h := sq_lt_sq.mp hsq_lt
        rw [abs_of_nonneg (Nat.cast_nonneg n), abs_of_nonneg (by positivity)] at h
        exact h
      rw [hR1n]; exact Nat.le_floor (le_of_lt hlt)
    have hre : z2.re.natAbs ≤ R1n :=
      hcoord _ (by rw [gnorm_eq_re_sq_add_im_sq]; exact Nat.le_add_right _ _)
    have him : z2.im.natAbs ≤ R1n :=
      hcoord _ (by rw [gnorm_eq_re_sq_add_im_sq]; exact Nat.le_add_left _ _)
    rw [cf_mem_gBox_iff]
    have hre' : |z2.re| ≤ R1 := by
      rw [Int.abs_eq_natAbs, hR1]; exact_mod_cast hre
    have him' : |z2.im| ≤ R1 := by
      rw [Int.abs_eq_natAbs, hR1]; exact_mod_cast him
    exact ⟨(abs_le.mp hre').1, (abs_le.mp hre').2,
      (abs_le.mp him').1, (abs_le.mp him').2⟩
  -- ## Step 5: the inclusion of filters and the cardinality comparison.
  have hsub : (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
        (fun z2 => β z2 ≠ 0 ∧ (4 * b * e : ℤ) ∣ (star z1 * z2).im)
      ⊆ (Work.FIPlan.gBox R1).filter
        (fun z2 => ((4 * b * e : ℕ) : ℤ) ∣ (star z1 * z2).im) := by
    intro z2 hz2
    simp only [Finset.mem_filter] at hz2 ⊢
    obtain ⟨-, hz2β, hdv⟩ := hz2
    exact ⟨hmem z2 hz2β,
      by rwa [show ((4 * b * e : ℕ) : ℤ) = (4 * b * e : ℤ) by push_cast; ring]⟩
  -- ## Step 6: the numeric comparison `(2R1+1)^2 ≤ 100N`.
  have hg1le54 : (g1 : ℝ) ≤ 5 / 4 * Pa.N := by
    have h1 : 1 + Pa.θ ≤ 1 + 1 / 4 := by linarith [hθq]
    have h2 : (1 + Pa.θ) * Pa.N ≤ (1 + 1 / 4) * Pa.N :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hNpos)
    linarith [hg1le, h2]
  have hnum : (2 * (R1 : ℝ) + 1) ^ 2 ≤ 100 * Pa.N := by
    have hsqrtg1_le : Real.sqrt (g1 : ℝ) ≤ Real.sqrt (5 / 4 * Pa.N) := Real.sqrt_le_sqrt hg1le54
    have hstep3 : 4 * Real.sqrt (5 / 4 * Pa.N) ≤ 5 * Real.sqrt Pa.N :=
      four_sqrt_five_quarter_le Pa.N hN1
    have h4g1le : 4 * Real.sqrt (g1 : ℝ) ≤ 5 * Real.sqrt Pa.N :=
      le_trans (mul_le_mul_of_nonneg_left hsqrtg1_le (by norm_num)) hstep3
    have hsqrtN1 : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
    have hstep : 2 * (R1 : ℝ) + 1 ≤ 10 * Real.sqrt Pa.N := by
      linarith [hR1le, h4g1le, hsqrtN1]
    have hnn : (0 : ℝ) ≤ 2 * (R1 : ℝ) + 1 := by linarith [hR1nn]
    have h := pow_le_pow_left₀ hnn hstep 2
    have h10 : (10 * Real.sqrt Pa.N) ^ 2 = 100 * Pa.N := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]; norm_num
    rw [h10] at h; exact h
  -- ## Step 7: assemble.
  have hmpos : (0 : ℝ) < ((4 * b * e : ℕ) : ℝ) := by
    have h : (0 : ℕ) < 4 * b * e := by omega
    exact_mod_cast h
  have hfrac : ((2 * (R1 : ℝ) + 1) ^ 2) / ((4 * b * e : ℕ) : ℝ) + 1
      ≤ 100 * Pa.N / (4 * b * e : ℝ) + 1 := by
    have h := div_le_div_of_nonneg_right hnum (le_of_lt hmpos)
    rw [show (4 * b * e : ℝ) = ((4 * b * e : ℕ) : ℝ) by push_cast; ring]
    linarith
  calc ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z2 => β z2 ≠ 0 ∧ (4 * b * e : ℤ) ∣ (star z1 * z2).im)).card : ℝ))
      ≤ ((((Work.FIPlan.gBox R1).filter
          (fun z2 => ((4 * b * e : ℕ) : ℤ) ∣ (star z1 * z2).im)).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ Clat * (((2 * (R1 : ℝ) + 1) ^ 2) / ((4 * b * e : ℕ) : ℝ) + 1) := hlatres
    _ ≤ Clat * (100 * Pa.N / (4 * b * e : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hfrac hClat_nonneg
/-! ## 6. The mode weights -/

/-- `(2log2 + log4) + Σ_{k ∈ evenFreq K} 1/|k| ≤ 500·(log(K+2))²`. -/
private lemma modeWeight_le (K : ℕ) (hK : 1 ≤ K) :
    (2 * Real.log 2 + Real.log 4) + ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ))
      ≤ 500 * (Real.log ((K : ℝ) + 2)) ^ 2 := by
  have hCstle : 2 * Real.log 2 + Real.log 4 ≤ 4 := by
    have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      have : (4:ℝ) = 2 * 2 := by norm_num
      rw [this, Real.log_mul (by norm_num) (by norm_num)]; ring
    rw [h4]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  have hWle : ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) ≤ 4 + 2 * Real.log ((K:ℝ)+2) := by
    refine le_trans (sum_inv_abs_evenFreq_le K) ?_
    have hlog : Real.log (2 * (K:ℝ) + 2) ≤ 1 + Real.log ((K:ℝ)+2) := by
      have h2 : 2 * (K:ℝ) + 2 = 2 * ((K:ℝ) + 1) := by ring
      rw [h2, Real.log_mul (by norm_num) (by positivity : (K:ℝ) + 1 ≠ 0)]
      have h3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      have h4 : Real.log ((K:ℝ)+1) ≤ Real.log ((K:ℝ)+2) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    linarith
  have hlog1 : 1 ≤ Real.log ((K:ℝ)+2) := by
    have h3 : (3:ℝ) ≤ (K:ℝ) + 2 := by
      have h : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      linarith
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    exact le_of_lt (lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) h3))
  have haux : (2 * Real.log 2 + Real.log 4) + ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ))
      ≤ 4 + (4 + 2 * Real.log ((K:ℝ)+2)) := by linarith
  nlinarith [haux, hlog1, sq_nonneg (Real.log ((K : ℝ) + 2) - 1)]

/-! ## 7. The per-`(b,e)` bound on `uniCharTerm` -/

/-- The Möbius weight: `‖μ(b)/b‖ ≤ 1/b`. -/
private lemma mobius_weight_bound (b : ℕ) :
    ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (b : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (b:ℝ))]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  · rw [div_le_div_iff_of_pos_right (by exact_mod_cast hb : (0:ℝ) < (b:ℝ))]
    have h1 : ((|ArithmeticFunction.moebius b| : ℤ) : ℝ) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
    rwa [Int.cast_abs] at h1

/-- **The per-`(b,e)` bound.**  With the fibre bound `M` for the modulus `Q = 4be`
(`hrow`/`hcol`), one has `‖uniCharTerm Pa b e β K ε‖ ≤ (1/b)·500·(log(K+2))²·(M·E₂)`. -/
theorem uniCharTerm_le_slack (Pa : Work.FITop.Params) (K : ℕ) (β : GaussianInt → ℂ) (ε : GaussianInt → ℤ)
    (hK : 1 ≤ K) (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1)
    {b e : ℕ} (hb : 1 ≤ b) (he : 1 ≤ e) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ z1 : GaussianInt, β z1 ≠ 0 →
      (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z2 => β z2 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card : ℝ) ≤ M)
    (hcol : ∀ z2 : GaussianInt, β z2 ≠ 0 →
      (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z1 => β z1 ≠ 0 ∧ (((4 * b * e : ℕ)) : ℤ) ∣ (star z1 * z2).im)).card : ℝ) ≤ M) :
    ‖uniCharTerm Pa b e β K ε‖
      ≤ (1 / (b : ℝ)) * (500 * (Real.log ((K : ℝ) + 2)) ^ 2)
          * (M * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)) := by
  have hb0 : 0 < b := by omega
  have he0 : 0 < e := by omega
  have hne : 4 * b * e ≠ 0 := by
    have hpos : 0 < 4 * b * e := Nat.mul_pos (Nat.mul_pos (by norm_num) hb0) he0
    omega
  haveI : NeZero (4 * b * e) := ⟨hne⟩
  set E2 : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 with hE2def
  have hmode : ∀ k : ℤ, ‖uniModeCharSum Pa b e β k ε‖ ≤ M * E2 :=
    fun k => uniModeCharSum_pairMass_le b e β k ε hε M hM hrow hcol
  set W : ℝ := ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) with hWdef
  have hCst0 : 0 ≤ 2 * Real.log 2 + Real.log 4 := by positivity
  have hme2 : 0 ≤ M * E2 := by
    refine mul_nonneg hM ?_
    rw [hE2def]; positivity
  rw [uniCharTerm, dif_neg hne]
  have hbody : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharSum Pa b e β 0 ε
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε‖
      ≤ ((2 * Real.log 2 + Real.log 4) + W) * (M * E2) := by
    have h1 : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharSum Pa b e β 0 ε‖
        ≤ (2 * Real.log 2 + Real.log 4) * (M * E2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCst0]
      exact mul_le_mul_of_nonneg_left (hmode 0) hCst0
    have h2 : ‖∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε‖
        ≤ W * (M * E2) := by
      calc ‖∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε‖
          ≤ ∑ k ∈ evenFreq K,
              ‖(1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) * (M * E2) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            have hden : ((|k| : ℤ) : ℝ) = |(k : ℝ)| := Int.cast_abs
            rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (abs_nonneg (k : ℝ)), ← hden]
            exact mul_le_mul_of_nonneg_left (hmode k)
              (div_nonneg zero_le_one (by exact_mod_cast abs_nonneg k))
        _ = W * (M * E2) := by rw [hWdef, Finset.sum_mul]
    calc ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharSum Pa b e β 0 ε
          + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε‖
        ≤ _ + _ := norm_add_le _ _
      _ ≤ (2 * Real.log 2 + Real.log 4) * (M * E2) + W * (M * E2) := add_le_add h1 h2
      _ = ((2 * Real.log 2 + Real.log 4) + W) * (M * E2) := by ring
  have hweight : ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (b : ℝ) :=
    mobius_weight_bound b
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hCstW : (2 * Real.log 2 + Real.log 4) + W
      ≤ 500 * (Real.log ((K : ℝ) + 2)) ^ 2 := modeWeight_le K hK
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb0
  calc ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
        * ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharSum Pa b e β 0 ε
          + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε)‖
      = ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖
        * ‖((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharSum Pa b e β 0 ε
          + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε)‖ :=
        norm_mul _ _
    _ ≤ (1 / (b : ℝ)) * (((2 * Real.log 2 + Real.log 4) + W) * (M * E2)) := by
        refine mul_le_mul hweight hbody (norm_nonneg _) (by positivity)
    _ ≤ (1 / (b : ℝ)) * (500 * (Real.log ((K : ℝ) + 2)) ^ 2) * (M * E2) := by
        have hLk0 : 0 ≤ (500 : ℝ) * (Real.log ((K : ℝ) + 2)) ^ 2 := by positivity
        have hstep : ((2 * Real.log 2 + Real.log 4) + W) * (M * E2)
            ≤ (500 * (Real.log ((K : ℝ) + 2)) ^ 2) * (M * E2) :=
          mul_le_mul_of_nonneg_right hCstW hme2
        calc (1 / (b : ℝ)) * (((2 * Real.log 2 + Real.log 4) + W) * (M * E2))
            ≤ (1 / (b : ℝ)) * ((500 * (Real.log ((K : ℝ) + 2)) ^ 2) * (M * E2)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = (1 / (b : ℝ)) * (500 * (Real.log ((K : ℝ) + 2)) ^ 2) * (M * E2) := by ring

end

end Work.FIArea7
