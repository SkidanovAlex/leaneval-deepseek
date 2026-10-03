import Mathlib
import Submission.Work.FITop3.Defs3

set_option autoImplicit false

namespace Work.FITop3.Assembly

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The cardinality of the dyadic annulus

The Cauchy–Schwarz step (5.17) of the paper multiplies `∑_{w} |X_w|²` by the number of `w`'s
summed, so it needs the count of the outer summation range `annM Pa`.  `annM Pa` sits inside the
square box `boxM Pa = gBox (radM Pa)` with `radM Pa = ⌈√(4M)⌉₊`, and `gBox R` is the image of the
`(2⌈|R|⌉+1)²` pairs `(re, im)` under an injection, so its cardinality is at most `(2|R|+1)²`. -/

/-- The box `gBox R` has at most `(2|R|+1)²` elements. -/
lemma card_gBox_le (R : ℤ) (hR : 0 ≤ R) :
    (Work.FIPlan.gBox R).card ≤ (2 * R.natAbs + 1) ^ 2 := by
  rw [Work.FIPlan.gBox]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.product_eq_sprod, Finset.card_product]
  have h : (Finset.Icc (-R) R).card = 2 * R.natAbs + 1 := by
    rw [Int.card_Icc]
    omega
  rw [h]
  exact le_of_eq (by ring)

/-- `annM Pa` has at most `100·M` elements (all `Pa.M ≥ 1`): with `n = ⌈√(4M)⌉₊` we have
`n < √(4M) + 1 ≤ 2√(4M)`, so `2n+1 < 5√(4M)` and `(2n+1)² < 100·M`. -/
lemma card_annM_le (Pa : Work.FITop.Params) : ((annM Pa).card : ℝ) ≤ 100 * Pa.M := by
  have h1 : (annM Pa).card ≤ (Work.FITop.boxM Pa).card :=
    Finset.card_le_card (annM_subset_boxM Pa)
  have hR0 : (0 : ℤ) ≤ Work.FITop.radM Pa := by
    rw [Work.FITop.radM]
    exact_mod_cast Nat.zero_le _
  have h2 : (Work.FITop.boxM Pa).card ≤ (2 * (Work.FITop.radM Pa).natAbs + 1) ^ 2 := by
    rw [Work.FITop.boxM]
    exact card_gBox_le _ hR0
  have hnat : (Work.FITop.radM Pa).natAbs = ⌈Real.sqrt (4 * Pa.M)⌉₊ := by
    rw [Work.FITop.radM]
    exact Int.natAbs_natCast _
  have hM1 : (1 : ℝ) ≤ Pa.M := Pa.hM1
  have h4M : (0 : ℝ) ≤ 4 * Pa.M := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (4 * Pa.M) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 4 * Pa.M by linarith)
    rwa [Real.sqrt_one] at h
  have hn : ((⌈Real.sqrt (4 * Pa.M)⌉₊ : ℕ) : ℝ) < Real.sqrt (4 * Pa.M) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg (4 * Pa.M))
  have hstep : (2 * ((⌈Real.sqrt (4 * Pa.M)⌉₊ : ℕ) : ℝ) + 1) ≤ 5 * Real.sqrt (4 * Pa.M) := by
    nlinarith [hn, hsq1]
  have h3 : ((2 * (Work.FITop.radM Pa).natAbs + 1) ^ 2 : ℝ) ≤ 100 * Pa.M := by
    rw [hnat]
    calc (2 * (⌈Real.sqrt (4 * Pa.M)⌉₊ : ℝ) + 1) ^ 2
        ≤ (5 * Real.sqrt (4 * Pa.M)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hstep 2
      _ = 100 * Pa.M := by
          rw [mul_pow, Real.sq_sqrt h4M]
          ring
  calc ((annM Pa).card : ℝ) ≤ ((Work.FITop.boxM Pa).card : ℝ) := by exact_mod_cast h1
    _ ≤ ((2 * (Work.FITop.radM Pa).natAbs + 1) ^ 2 : ℝ) := by exact_mod_cast h2
    _ ≤ 100 * Pa.M := h3

/-! ## 2. The Cauchy–Schwarz pair of §5: `‖B‖² ≤ c·M·D`

`Bfree` sums the inner blocks `X_w = ∑_z β_z Z(Re wz)` over the dyadic annulus `annM Pa` of
(4.18)/(5.6), while `Dform` is (5.18), the same blocks weighted by the smooth majorant `f`.  On
the annulus `f ≥ 1` (`IsMajorant`), so `∑_{annM} ‖X_w‖² ≤ Dform`, and Cauchy–Schwarz over the
finitely many `w`'s gives the factor `card (annM Pa) ≤ 100·M`. -/

theorem cauchy_exists : ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ)
    (β : GaussianInt → ℂ), Work.FITop3.IsMajorant Pa f →
    ‖Work.FITop3.Bfree Pa β‖ ^ 2 ≤ c * Pa.M * Work.FITop3.Dform Pa f β := by
  refine ⟨100, by norm_num, ?_⟩
  intro Pa f β hf
  obtain ⟨hf0, hf1, hfann, hfsupp, hfd1, hfd2⟩ := hf
  set X : GaussianInt → ℂ :=
    fun w => ∑ z ∈ Work.FITop.boxN Pa, β z * Zc w z with hX
  have hBfree : Bfree Pa β = ∑ w ∈ annM Pa, X w := by
    simp only [Bfree, hX]
  have hnorm : ‖Bfree Pa β‖ ≤ ∑ w ∈ annM Pa, ‖X w‖ := by
    rw [hBfree]
    exact norm_sum_le _ _
  have hsumnn : (0 : ℝ) ≤ ∑ w ∈ annM Pa, ‖X w‖ :=
    Finset.sum_nonneg fun w _ => norm_nonneg _
  have hcard : (0 : ℝ) ≤ ((annM Pa).card : ℝ) := by positivity
  have hCS : (∑ w ∈ annM Pa, ‖X w‖) ^ 2
      ≤ ((annM Pa).card : ℝ) * ∑ w ∈ annM Pa, ‖X w‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hDform_eq : Dform Pa f β
      = ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 := by
    simp only [Dform, Complex.normSq_eq_norm_sq, hX]
  have hDnn : (0 : ℝ) ≤ Dform Pa f β := by
    rw [hDform_eq]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (hf0 _) (sq_nonneg _)
  have hle : ∑ w ∈ annM Pa, ‖X w‖ ^ 2 ≤ Dform Pa f β := by
    rw [hDform_eq]
    have hsub : annM Pa ⊆ Work.FITop.boxM Pa := annM_subset_boxM Pa
    have hpt : ∀ w ∈ annM Pa,
        ‖X w‖ ^ 2 ≤ f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 := by
      intro w hw
      obtain ⟨_, hMlt, hMle⟩ := mem_annM.mp hw
      have h1 : 1 ≤ f (Work.FIPlan.gnorm w) := hfann w hMlt hMle
      nlinarith [sq_nonneg ‖X w‖]
    calc ∑ w ∈ annM Pa, ‖X w‖ ^ 2
        ≤ ∑ w ∈ annM Pa, f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 := Finset.sum_le_sum hpt
      _ ≤ ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun w _ _ => mul_nonneg (hf0 _) (sq_nonneg _))
  calc ‖Bfree Pa β‖ ^ 2
      ≤ (∑ w ∈ annM Pa, ‖X w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ ((annM Pa).card : ℝ) * ∑ w ∈ annM Pa, ‖X w‖ ^ 2 := hCS
    _ ≤ ((annM Pa).card : ℝ) * Dform Pa f β := mul_le_mul_of_nonneg_left hle hcard
    _ ≤ 100 * Pa.M * Dform Pa f β :=
        mul_le_mul_of_nonneg_right (card_annM_le Pa) hDnn

end

end Work.FITop3.Assembly
