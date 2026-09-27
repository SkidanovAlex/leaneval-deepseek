import Mathlib
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.nearId_norm
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.abs_tpart_sub_le
import Submission.Work.Mostow.cosh_sub_one_quad
import Submission.Work.Mostow.entry_le_of_hlift_bound

namespace Work.Mostow

open scoped _root_.Matrix
open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- The time coordinate `tpart u = cosh (hdist 0 u)` is `sinh M`-Lipschitz on the ball of
radius `M` around the base point `0` (for `M ≥ 0`).  This is the radius-`M` version of
`abs_tpart_sub_le`. -/
lemma abs_tpart_sub_le_gen (hI : Submission.Mostow.HypIsometryProp n) {M : ℝ} (hM : 0 ≤ M)
    {u v : Submission.Mostow.E n}
    (hu : Submission.Mostow.hdist (0 : Submission.Mostow.E n) u ≤ M)
    (hv : Submission.Mostow.hdist (0 : Submission.Mostow.E n) v ≤ M) :
    |Submission.Mostow.tpart u - Submission.Mostow.tpart v|
      ≤ Real.sinh M * Submission.Mostow.hdist u v := by
  have hnn : ∀ x : E n, 0 ≤ hdist (0 : E n) x := fun x => hI.1 0 x
  have hsym : ∀ x y : E n, hdist x y = hdist y x := fun x y => hI.2.1 x y
  have htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z :=
    fun x y z => hI.2.2.2.1 x y z
  have hab : |hdist (0 : E n) u - hdist (0 : E n) v| ≤ hdist u v := by
    rw [abs_sub_le_iff]
    constructor
    · have h := htri (0 : E n) v u
      rw [hsym v u] at h
      linarith
    · have h := htri (0 : E n) u v
      linarith
  calc |tpart u - tpart v|
      = |Real.cosh (hdist (0 : E n) u) - Real.cosh (hdist (0 : E n) v)| := by
        rw [cosh_hdist_zero u, cosh_hdist_zero v]
    _ ≤ Real.sinh M * |hdist (0 : E n) u - hdist (0 : E n) v| :=
        absCoshSubCoshLe M _ _ (hnn u) (hnn v) hu hv
    _ ≤ Real.sinh M * hdist u v :=
        mul_le_mul_of_nonneg_left hab (Real.sinh_nonneg_iff.mpr hM)

/-- **Pointwise estimate with `η ≤ 1`.**  If `g` moves the unit hdist-ball around `0` by less
than `η` (with `η ≤ 1`), then the lift `LambdaMat g` moves each `hlift u`, `‖u‖ ≤ 1/4`, by at
most `K η`, `K = √(cosh 1 ^ 2 + 2 * sinh (5/4) ^ 2)`.  Here `5/4` is a bound for
`hdist 0 (g • u)` when `hdist 0 u ≤ 1/4` and `hdist u (g • u) < η ≤ 1`. -/
lemma nearId_pointwise_one (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hnear : NearIdAt g (0 : E n) η)
    {u : E n} (hu : ‖u‖ ≤ 1 / 4) :
    Real.sqrt (∑ i, ((LambdaMat g - 1) *ᵥ hlift u) i ^ 2)
      ≤ Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η := by
  have hdist0u : hdist (0 : E n) u ≤ 1 := by
    have := hdist_zero_le_norm u; linarith
  have hdu : hdist u (g • u) < η := hnear u hdist0u
  have hdist0u' : hdist (0 : E n) u ≤ 5 / 4 := by
    have := hdist_zero_le_norm u; linarith
  have hdist0gu' : hdist (0 : E n) (g • u) ≤ 5 / 4 := by
    have h1 := hI.2.2.2.1 (0 : E n) u (g • u)
    have h2 := hdist_zero_le_norm u
    linarith
  have hcc : Hyper.cc u (g • u) = Real.cosh (hdist u (g • u)) := by
    rw [← Real.cosh_arcosh (one_le_cc u (g • u)), ← Hyper.hdist_eq_cc]
  have hcc_le : 2 * (Hyper.cc u (g • u) - 1) ≤ Real.cosh 1 ^ 2 * η ^ 2 := by
    have hmono : Real.cosh (hdist u (g • u)) ≤ Real.cosh η := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (hI.1 u (g • u)), abs_of_nonneg (le_of_lt hη)]
      exact le_of_lt hdu
    have hq := cosh_sub_one_quad η (le_of_lt hη) hη1
    rw [hcc]
    linarith
  have hsinhpos : 0 < Real.sinh (5 / 4) := Real.sinh_pos_iff.mpr (by norm_num)
  have htime : |(hlift (g • u) - hlift u) (Sum.inr 0)| ≤ Real.sinh (5 / 4) * η := by
    rw [Pi.sub_apply, hlift_inr, hlift_inr]
    have h1 := abs_tpart_sub_le_gen hI (M := 5 / 4) (by norm_num) hdist0gu' hdist0u'
    rw [hI.2.1 (g • u) u] at h1
    have h2 : Real.sinh (5 / 4) * hdist u (g • u) ≤ Real.sinh (5 / 4) * η :=
      mul_le_mul_of_nonneg_left (le_of_lt hdu) (le_of_lt hsinhpos)
    linarith
  have htime_sq : ((hlift (g • u) - hlift u) (Sum.inr 0)) ^ 2 ≤ (Real.sinh (5 / 4) * η) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg (le_of_lt hsinhpos) (le_of_lt hη))]
    exact htime
  have hsqsum : (∑ i, (hlift (g • u) - hlift u) i ^ 2)
      = mform (hlift (g • u) - hlift u) (hlift (g • u) - hlift u)
        + 2 * ((hlift (g • u) - hlift u) (Sum.inr 0)) ^ 2 := by
    rw [mform_self_apply, Fintype.sum_sum_type, Fin.sum_univ_one]
    ring
  have hmform : mform (hlift (g • u) - hlift u) (hlift (g • u) - hlift u)
      = 2 * (Hyper.cc u (g • u) - 1) := by
    rw [mform_sub_left, mform_sub_right, mform_sub_right, mform_hlift_self, mform_hlift_hlift,
      mform_hlift_hlift, mform_hlift_self, Hyper.cc, real_inner_comm (g • u) u]
    ring
  have hcol : (LambdaMat g - 1) *ᵥ hlift u = hlift (g • u) - hlift u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hlift_LambdaMat hA]
  calc Real.sqrt (∑ i, ((LambdaMat g - 1) *ᵥ hlift u) i ^ 2)
      = Real.sqrt (∑ i, (hlift (g • u) - hlift u) i ^ 2) := by rw [hcol]
    _ = Real.sqrt (2 * (Hyper.cc u (g • u) - 1)
          + 2 * ((hlift (g • u) - hlift u) (Sum.inr 0)) ^ 2) := by rw [hsqsum, hmform]
    _ ≤ Real.sqrt (Real.cosh 1 ^ 2 * η ^ 2 + 2 * (Real.sinh (5 / 4) * η) ^ 2) := by
        apply Real.sqrt_le_sqrt
        linarith
    _ = Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η := by
        rw [show Real.cosh 1 ^ 2 * η ^ 2 + 2 * (Real.sinh (5 / 4) * η) ^ 2
              = (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η ^ 2 by ring]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hη)]

theorem nearId_entry_le_one (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : LeanEval.Geometry.MostowRigidity.PO n 1) (η : ℝ), 0 < η → η ≤ 1 →
      Submission.Mostow.NearIdAt g (0 : Submission.Mostow.E n) η →
      ∀ i j : Fin n ⊕ Fin 1, |(Work.Mostow.LambdaMat g - 1) i j| ≤ C * η := by
  refine ⟨4 * Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2), ?_, ?_⟩
  · have : (0 : ℝ) < Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    linarith
  · intro g η hη hη1 hnear i j
    have hK : 0 ≤ Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hη)
    have hpt : ∀ u : E n, ‖u‖ ≤ 1 / 4 →
        Real.sqrt (∑ i, ((LambdaMat g - 1) *ᵥ hlift u) i ^ 2)
          ≤ Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η :=
      fun u hu => nearId_pointwise_one hA hI g hη hη1 hnear hu
    have hentry := entry_le_of_hlift_bound n (LambdaMat g - 1)
      (Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η) hK hpt i j
    calc |(LambdaMat g - 1) i j|
        ≤ 4 * (Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2) * η) := hentry
      _ = (4 * Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh (5 / 4) ^ 2)) * η := by ring

end Work.Mostow
