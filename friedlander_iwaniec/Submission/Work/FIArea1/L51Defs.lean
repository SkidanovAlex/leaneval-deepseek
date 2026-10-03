import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea2.hits_card_le

set_option maxHeartbeats 2000000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The boxes of the two-condition lattice count (*FI* Lemma 5.1)

This module only contains definitions and elementary facts about them, so that lemmas about the
count can be delegated to colleagues who import it. -/

/-- Radius of the outer box: `|w|² ≲ 4M`. -/
def KR (M : ℝ) : ℤ := (⌈Real.sqrt (4 * M)⌉₊ : ℤ)

/-- Radius of the inner box: `|z|² ≲ 2N`. -/
def KZ (N : ℝ) : ℤ := (⌈Real.sqrt (2 * N)⌉₊ : ℤ)

/-- The outer box `gBox (KR M)`. -/
def Wbox (M : ℝ) : Finset GaussianInt := Work.FIPlan.gBox (KR M)

/-- The inner set: **primitive** `z` with `N < |z|² ≤ 2N`. -/
def Zbox (N : ℝ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (KZ N)).filter
    (fun z => Work.FIPlan.IsPrimitive z ∧ N < (Work.FIPlan.gnorm z : ℝ)
      ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N)

/-- `G(w) = Σ_{z ∈ Zf} Z(Re wz)`, the inner sum of the two-condition count. -/
def Gw (N : ℝ) (w : GaussianInt) : ℕ :=
  ∑ z ∈ Zbox N, Work.FIPlan.Zint (Work.FIPlan.cForm w z)

lemma KR_nonneg (M : ℝ) : 0 ≤ KR M := by
  unfold KR; exact_mod_cast Nat.zero_le _

lemma KZ_nonneg (N : ℝ) : 0 ≤ KZ N := by
  unfold KZ; exact_mod_cast Nat.zero_le _

lemma card_gBox (R : ℤ) (hR : 0 ≤ R) :
    (Work.FIPlan.gBox R).card = (2 * R.natAbs + 1) ^ 2 := by
  have h1 : (Finset.Icc (-R) R).card = 2 * R.natAbs + 1 := by
    rw [Int.card_Icc]
    have h2 : R + 1 - -R = (2 * R.natAbs + 1 : ℕ) := by
      push_cast; rw [abs_of_nonneg hR]; ring
    rw [h2, Int.toNat_natCast]
  rw [Work.FIPlan.gBox, Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective,
    Finset.product_eq_sprod, Finset.card_product, h1]
  ring

lemma mem_Wbox_iff {M : ℝ} {w : GaussianInt} :
    w ∈ Wbox M ↔ w.re ∈ Finset.Icc (-(KR M)) (KR M) ∧
      w.im ∈ Finset.Icc (-(KR M)) (KR M) := by
  rw [Wbox, Work.FIArea2.mem_gBox_iff]

lemma abs_re_le_of_mem_Wbox {M : ℝ} {w : GaussianInt} (hw : w ∈ Wbox M) :
    |w.re| ≤ KR M :=
  Work.FIArea2.abs_re_le_of_mem_gBox (by rwa [Wbox] at hw)

lemma abs_im_le_of_mem_Wbox {M : ℝ} {w : GaussianInt} (hw : w ∈ Wbox M) :
    |w.im| ≤ KR M :=
  Work.FIArea2.abs_im_le_of_mem_gBox (by rwa [Wbox] at hw)

lemma gnorm_le_of_mem_Wbox {M : ℝ} {w : GaussianInt} (hw : w ∈ Wbox M) :
    Work.FIPlan.gnorm w ≤ 2 * (KR M).natAbs ^ 2 :=
  Work.FIArea2.gnorm_le_of_mem_gBox (KR_nonneg M) (by rwa [Wbox] at hw)

lemma mem_Zbox_iff {N : ℝ} {z : GaussianInt} :
    z ∈ Zbox N ↔ z ∈ Work.FIPlan.gBox (KZ N) ∧ Work.FIPlan.IsPrimitive z ∧
      N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N := by
  rw [Zbox, Finset.mem_filter]

lemma card_Zbox_le (N : ℝ) : (Zbox N).card ≤ (2 * (KZ N).natAbs + 1) ^ 2 := by
  calc (Zbox N).card ≤ (Work.FIPlan.gBox (KZ N)).card := Finset.card_filter_le _ _
    _ = (2 * (KZ N).natAbs + 1) ^ 2 := card_gBox _ (KZ_nonneg N)

end

end Work.FIArea1
