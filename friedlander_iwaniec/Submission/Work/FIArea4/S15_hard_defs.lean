/-
# FI §15: the vocabulary of the *hard* branch of the remainder bound

This module collects the two objects in which the §15 remainder `S15_rem_hard` is proved:

* `S15polarBox Pa φ` — the polar box (5.14) as a `Finset` (so that statements about sums over it
  do not have to mention `DecidablePred` instances);
* `S15Psi` — a smooth cut-off `Ψ` with `0 ≤ Ψ ≤ 1`, supported in `(1/2, 5/2)`, which agrees with
  `1 - S15u` on `[1, 3/2]`.  Since `S15E t = S15u t - 1{1 < t}` and `1 - S15u ≡ 1` on `t ≤ 1`,
  the exact identity

  `S15E t = -Ψ t + R t`,      `R t = (1 - S15u t) * η t * 1{t ≤ 1}`,

  holds with `R` supported in `(1/2, 1]` and `0 ≤ R ≤ 1`.  This writes the non-smooth remainder
  cut (which has a jump at `t = 1`) as a *smooth* piece of the shape required by the §15
  reduction `S15_psi_cut_reduction`, plus a residual which is bounded by a plain count.
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea4.S15u

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The polar box (5.14) inside the inner box `boxN Pa`, as a `Finset`. -/
def S15polarBox (Pa : Work.FITop.Params) (φ : ℝ) : Finset GaussianInt :=
  (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z)

lemma mem_S15polarBox {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt} :
    z ∈ S15polarBox Pa φ ↔ z ∈ Work.FITop.boxN Pa ∧ Work.FITop3.InPolarBox Pa φ z :=
  Finset.mem_filter

/-- A smooth cut-off `η` which is `1` on `[3/4, 2]`, vanishes for `t ≤ 1/2` and for `t ≥ 5/2`,
and takes values in `[0,1]`. -/
def S15eta (t : ℝ) : ℝ :=
  Real.smoothTransition (4 * t - 2) * Real.smoothTransition (5 - 2 * t)

/-- The smooth cut-off `Ψ = (1 - S15u) · η` of the §15 remainder: it agrees with `1 - S15u` on
`[1,3/2]` and is supported in `(1/2, 5/2)`. -/
def S15Psi (t : ℝ) : ℝ := (1 - S15u t) * S15eta t

/-- The residual of the smooth approximation: `R t = S15E t + Ψ t`. -/
def S15R (t : ℝ) : ℝ := S15E t + S15Psi t

lemma S15eta_nonneg (t : ℝ) : 0 ≤ S15eta t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma S15eta_le_one (t : ℝ) : S15eta t ≤ 1 := by
  unfold S15eta
  have h1 := Real.smoothTransition.le_one (4 * t - 2)
  have h2 := Real.smoothTransition.le_one (5 - 2 * t)
  have h3 := Real.smoothTransition.nonneg (4 * t - 2)
  have h4 := Real.smoothTransition.nonneg (5 - 2 * t)
  nlinarith

lemma S15eta_eq_one {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 2) : S15eta t = 1 := by
  unfold S15eta
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma S15eta_zero_of_le {t : ℝ} (h : t ≤ 1 / 2) : S15eta t = 0 := by
  unfold S15eta
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 4 * t - 2 ≤ 0)]
  ring

lemma S15eta_zero_of_ge {t : ℝ} (h : 5 / 2 ≤ t) : S15eta t = 0 := by
  unfold S15eta
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 - 2 * t ≤ 0)]
  ring

lemma S15Psi_nonneg (t : ℝ) : 0 ≤ S15Psi t := by
  unfold S15Psi
  have h1 : 0 ≤ 1 - S15u t := by have := S15u_le_one t; linarith
  exact mul_nonneg h1 (S15eta_nonneg t)

lemma S15Psi_le_one (t : ℝ) : S15Psi t ≤ 1 := by
  unfold S15Psi
  have h2 : 1 - S15u t ≤ 1 := by have := S15u_nonneg t; linarith
  have h1 : 0 ≤ 1 - S15u t := by have := S15u_le_one t; linarith
  exact mul_le_one₀ h2 (S15eta_nonneg t) (S15eta_le_one t)

lemma S15Psi_zero_of_le_half {t : ℝ} (h : t ≤ 1 / 2) : S15Psi t = 0 := by
  unfold S15Psi; rw [S15eta_zero_of_le h]; ring

lemma S15Psi_zero_of_ge {t : ℝ} (h : 5 / 2 ≤ t) : S15Psi t = 0 := by
  unfold S15Psi; rw [S15eta_zero_of_ge h]; ring

lemma contDiff_S15eta : ContDiff ℝ (⊤ : ℕ∞) S15eta := by
  unfold S15eta; fun_prop

lemma contDiff_S15Psi : ContDiff ℝ (⊤ : ℕ∞) S15Psi := by
  unfold S15Psi
  exact ((contDiff_const.sub S15u_contDiff).mul contDiff_S15eta)

/-- On `[1, 3/2]` the smooth cut-off `Ψ` agrees with `1 - S15u`, hence with `-S15E`. -/
lemma S15Psi_eq_of_mem {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 3 / 2) :
    S15Psi t = 1 - S15u t := by
  unfold S15Psi
  rw [S15eta_eq_one (by linarith) (by linarith), mul_one]

/-- **The exact smooth-plus-residual identity for the §15 remainder cut.** -/
lemma S15E_eq_neg_Psi_add_R (t : ℝ) : S15E t = -S15Psi t + S15R t := by
  unfold S15R; ring

/-- On `(-∞,1]` the residual equals `η`. -/
lemma S15R_eq_eta_of_le_one {t : ℝ} (h : t ≤ 1) : S15R t = S15eta t := by
  unfold S15R S15E S15Psi
  have h1 : S15u t = 0 := S15u_zero h
  have h2 : (if 1 < t then (1 : ℝ) else 0) = 0 := by rw [if_neg (not_lt.mpr h)]
  rw [h1, h2]
  ring

/-- The residual vanishes for `t > 1`. -/
lemma S15R_zero_of_gt_one {t : ℝ} (h : 1 < t) : S15R t = 0 := by
  unfold S15R S15E S15Psi
  rw [if_pos h]
  by_cases h2 : t ≥ 3 / 2
  · rw [S15u_one h2]; ring
  · push_neg at h2
    rw [S15eta_eq_one (by linarith) (by linarith), mul_one]
    ring

/-- The residual vanishes for `t ≤ 1/2`. -/
lemma S15R_zero_of_le_half {t : ℝ} (h : t ≤ 1 / 2) : S15R t = 0 := by
  rw [S15R_eq_eta_of_le_one (by linarith), S15eta_zero_of_le h]

/-- `|S15R| ≤ 1` everywhere. -/
lemma abs_S15R_le_one (t : ℝ) : |S15R t| ≤ 1 := by
  by_cases h : t ≤ 1
  · rw [S15R_eq_eta_of_le_one h]
    rw [abs_le]
    exact ⟨by linarith [S15eta_nonneg t], S15eta_le_one t⟩
  · rw [S15R_zero_of_gt_one (by linarith)]
    norm_num

/-- The residual is supported in `(1/2, 1]`. -/
lemma S15R_eq_zero_of_not_mem {t : ℝ} (h : t ≤ 1 / 2 ∨ 1 < t) : S15R t = 0 := by
  rcases h with h | h
  · exact S15R_zero_of_le_half h
  · exact S15R_zero_of_gt_one h


/-- The residual cut of the §15 remainder: the `d`-sum with the cut `1{X < d}·S15R(|Δ|/(4Xd))`. -/
def S15resCut (X : ℕ) : GaussianInt → GaussianInt → ℕ → ℝ :=
  fun z1 z2 d => if X < d then S15R ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)))
    else 0

end

end Work.FIArea4
