import Mathlib
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.margulisPairDefs

/-!
# A near-identity boost through a point of the unit ball

For every point `W` of the hyperbolic chart with `hdist 0 W ≤ 1` there is an
element `B ∈ O(n,1)` (a matrix representative, not a class in `PO(n,1)`) with

* `actO B 0 = W`, and
* `Near1 B (3 * hdist 0 W)`: every matrix entry of `B` is within `3 * hdist 0 W`
  of the corresponding entry of the identity matrix.

The point is that the *explicit* boost `boostO e r t` of `BoostTransitive` sending
`0` to `W = r • e` uses `r = sinh d`, `t = cosh d` where `d = hdist 0 W`, so its
entries are bounded by `cosh d - 1` and `sinh d`, both of which are `≤ 3 d` for
`d ≤ 1`.  This is the elementary geometric input of the Margulis lemma: a point of
the unit ball is reached by an element whose distance from the identity is
controlled by the distance to the point.
-/

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix
open scoped Real

/-! ## Elementary bounds on `sinh` and `cosh` near `0` -/

/-- `cosh x - 1 ≤ 3 x` for `0 ≤ x ≤ 1`: from the quadratic Taylor bound
`|exp x - 1 - x| ≤ x²`. -/
lemma cosh_sub_one_le_three_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cosh x - 1 ≤ 3 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h1 : Real.exp x ≤ 1 + x + x ^ 2 := by
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2; linarith
  have h2 : Real.exp (-x) ≤ 1 - x + x ^ 2 := by
    have hx' : |-x| ≤ 1 := by rwa [abs_neg]
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx')).2; linarith
  rw [Real.cosh_eq]
  have h3 : x ^ 2 ≤ 3 * x := by nlinarith
  linarith

/-- `sinh x ≤ 3 x` for `0 ≤ x ≤ 1`. -/
lemma sinh_le_three_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sinh x ≤ 3 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h1 : Real.exp x ≤ 1 + x + x ^ 2 := by
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2; linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  rw [Real.sinh_eq]
  have h3 : x ^ 2 / 2 ≤ 2 * x := by nlinarith
  linarith

/-! ## The chart distance to `0` -/

lemma hdist_zero_eq_arcosh_tpart {n : ℕ} (W : E n) :
    hdist (0 : E n) W = Real.arcosh (tpart W) := by
  simp [hdist, tpart_zero]

lemma hdist_zero_nonneg {n : ℕ} (W : E n) : 0 ≤ hdist (0 : E n) W := by
  rw [hdist_zero_eq_arcosh_tpart]; exact Real.arcosh_nonneg (one_le_tpart W)

lemma tpart_eq_cosh_hdist {n : ℕ} (W : E n) :
    tpart W = Real.cosh (hdist (0 : E n) W) := by
  rw [hdist_zero_eq_arcosh_tpart, Real.cosh_arcosh (one_le_tpart W)]

lemma norm_eq_sinh_hdist {n : ℕ} (W : E n) :
    ‖W‖ = Real.sinh (hdist (0 : E n) W) := by
  have hd : hdist (0 : E n) W = Real.arcosh (tpart W) := hdist_zero_eq_arcosh_tpart W
  have h1 : ‖W‖ ^ 2 = (Real.sinh (hdist (0 : E n) W)) ^ 2 := by
    have hsq := tpart_sq W
    rw [show tpart W = Real.cosh (hdist (0:E n) W) from by
        rw [hd, Real.cosh_arcosh (one_le_tpart W)]] at hsq
    rw [Real.sinh_sq]
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact h
  · have h2 : 0 ≤ Real.sinh (hdist (0 : E n) W) :=
      Real.sinh_nonneg_iff.mpr (hd ▸ Real.arcosh_nonneg (one_le_tpart W))
    have h3 : 0 ≤ ‖W‖ := norm_nonneg W
    linarith

/-! ## The entrywise bound for a boost -/

/-- Every entry of the boost `boostMat e r t` is within `q` of the identity entry, provided
`r ≤ q`, `0 ≤ r` and `t - 1 ≤ q`, `1 ≤ t` (and `‖e‖ = 1`). -/
lemma boostMat_sub_dE_le {n : ℕ} (e : E n) (r t q : ℝ) (he : ‖e‖ = 1) (hr : 0 ≤ r) (hrq : r ≤ q)
    (ht : 1 ≤ t) (htq : t - 1 ≤ q) :
    ∀ i j : Fin n ⊕ Fin 1, |boostMat e r t i j - dE n i j| ≤ q := by
  have hei : ∀ i : Fin n, |e i| ≤ 1 := by
    intro i
    have := PiLp.norm_apply_le e i
    rw [he] at this
    simpa using this
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · rw [boostMat, Matrix.fromBlocks_apply₁₁]
    have hP : boostP e t i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j + (t - 1) * (e i * e j) := by
      simp [boostP, colVec, Matrix.mul_apply]
    have hd : dE n (Sum.inl i) (Sum.inl j) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      rw [dE_apply, Matrix.one_apply]; by_cases h : i = j <;> simp [h]
    rw [hP, hd, add_sub_cancel_left, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1)]
    have h1 : |e i * e j| ≤ 1 := by
      rw [abs_mul]
      have := mul_le_mul (hei i) (hei j) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      simpa using this
    calc (t - 1) * |e i * e j| ≤ (t - 1) * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = t - 1 := by ring
      _ ≤ q := htq
  · rw [boostMat, Matrix.fromBlocks_apply₁₂]
    have hB : (r • colVec e) i j = r * e i := by simp [colVec]
    have hd : dE n (Sum.inl i) (Sum.inr j) = 0 := by rw [dE_apply]; simp
    rw [hB, hd, sub_zero, abs_mul, abs_of_nonneg hr]
    calc r * |e i| ≤ r * 1 := mul_le_mul_of_nonneg_left (hei i) hr
      _ = r := by ring
      _ ≤ q := hrq
  · rw [boostMat, Matrix.fromBlocks_apply₂₁]
    have hB : (r • (colVec e)ᵀ) i j = r * e j := by simp [colVec]
    have hd : dE n (Sum.inr i) (Sum.inl j) = 0 := by rw [dE_apply]; simp
    rw [hB, hd, sub_zero, abs_mul, abs_of_nonneg hr]
    calc r * |e j| ≤ r * 1 := mul_le_mul_of_nonneg_left (hei j) hr
      _ = r := by ring
      _ ≤ q := hrq
  · have hij : i = j := Subsingleton.elim i j
    subst hij
    rw [boostMat, Matrix.fromBlocks_apply₂₂]
    have hB : boostD t i i = t := by simp [boostD]
    have hd : dE n (Sum.inr i) (Sum.inr i) = 1 := by rw [dE_apply]; simp
    rw [hB, hd, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1)]
    exact htq

/-! ## The target -/

theorem exists_boost_near (n : ℕ) (W : Submission.Mostow.E n)
    (hW : Submission.Mostow.hdist (0 : Submission.Mostow.E n) W ≤ 1) :
    ∃ B : Submission.Mostow.O1 n,
      Submission.Mostow.actO B (0 : Submission.Mostow.E n) = W ∧
        Work.Mostow.Near1 B (3 * Submission.Mostow.hdist (0 : Submission.Mostow.E n) W) := by
  by_cases hW0 : W = 0
  · subst hW0
    refine ⟨1, ?_, ?_⟩
    · rw [actO]
      have hts : tsign (1 : O1 n) = 1 := by rw [tsign_eq_one_iff]; simp
      rw [hts, mat_one_coe, Matrix.one_mulVec]
      ext i
      simp [hlift]
    · have h0 : hdist (0 : E n) (0 : E n) = 0 := by
        rw [hdist_zero_eq_arcosh_tpart, tpart_zero, Real.arcosh_zero]
      rw [h0, mul_zero]
      exact near1_one
  · have hnn : 0 ≤ hdist (0 : E n) W := hdist_zero_nonneg W
    have hnorm : 0 < ‖W‖ := norm_pos_iff.mpr hW0
    have he : ‖(‖W‖⁻¹ : ℝ) • W‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnorm), inv_mul_cancel₀ hnorm.ne']
    have htr : (tpart W) ^ 2 - ‖W‖ ^ 2 = 1 := by rw [tpart_sq]; ring
    have ht : 0 < tpart W := tpart_pos W
    refine ⟨boostO (‖W‖⁻¹ • W) ‖W‖ (tpart W) he htr, ?_, ?_⟩
    · rw [actO_boostO_zero _ _ _ he htr ht, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    · have hcosh : tpart W - 1 ≤ 3 * hdist (0 : E n) W := by
        rw [tpart_eq_cosh_hdist W]
        exact cosh_sub_one_le_three_mul hnn hW
      have hsinh : ‖W‖ ≤ 3 * hdist (0 : E n) W := by
        rw [norm_eq_sinh_hdist W]
        exact sinh_le_three_mul hnn hW
      have hnear : Work.Mostow.Near1 (boostO (‖W‖⁻¹ • W) ‖W‖ (tpart W) he htr)
          (3 * hdist (0 : E n) W) := by
        simp only [Work.Mostow.Near1, mat_boostO]
        exact boostMat_sub_dE_le (‖W‖⁻¹ • W) ‖W‖ (tpart W) (3 * hdist (0:E n) W)
          he (norm_nonneg W) hsinh (one_le_tpart W) hcosh
      exact hnear

end Work.Mostow.Margulis
