import Mathlib
import Submission.Work.Mostow.gapAEvenDefs
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.cosh_hdist_fermi

/-!
# `Work.Mostow.nearId_rotN_bound`

Converse of the two-scale criterion `nearId_blk`: if the block isometry `blk j m 1 R` is
`η`-near the identity at an **arbitrary** point `z` of the chart `E (j + m)` (with `η ≤ 1`),
then its normal part `R` is within `4 η` of the identity in operator norm.  (The stratum
dimension `j` is arbitrary here — in particular `j = 0` is allowed, and the point `z` need not
be on the standard stratum.)

The proof is done in the raw chart coordinates `(tanC, nrmC)` of `E (j + m) = E j × E m`: the
block map `blk j m 1 R` fixes the tangential chart coordinate and acts by `R` on the normal one,
so that for `u = nrb_mk t W` the displacement is exactly

  `cosh (hdist u (blk j m 1 R • u)) = 1 + ‖R W - W‖²/2`.

Shifting the normal coordinate by `2 sinh (1/2)` keeps one inside the unit ball around `z`
(this uses that the "height" `1 + ‖t‖²` only makes the ball bigger), and the triangle inequality
then bounds `‖R y - y‖` for every unit `y`, hence `rotN R ≤ 4 η`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## The raw chart decomposition `E (k + m) = E k × E m` -/

/-- reassemble a chart point out of its tangential and normal coordinates -/
def nrb_mk (k m : ℕ) (t : E k) (W : E m) : E (k + m) :=
  WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => W i))

lemma nrb_tanC_mk (k m : ℕ) (t : E k) (W : E m) : tanC k m (nrb_mk k m t W) = t := by
  ext i; simp [tanC, nrb_mk]

lemma nrb_nrmC_mk (k m : ℕ) (t : E k) (W : E m) : nrmC k m (nrb_mk k m t W) = W := by
  ext i; simp [nrmC, nrb_mk]

lemma nrb_mk_tanC_nrmC (k m : ℕ) (u : E (k + m)) :
    nrb_mk k m (tanC k m u) (nrmC k m u) = u := by
  refine nib_eq_of_tanC_nrmC ?_ ?_
  · rw [nrb_tanC_mk]
  · rw [nrb_nrmC_mk]

lemma nrb_norm_sq_mk (k m : ℕ) (t : E k) (W : E m) :
    ‖nrb_mk k m t W‖ ^ 2 = ‖t‖ ^ 2 + ‖W‖ ^ 2 := by
  rw [nib_norm_sq_split k m (nrb_mk k m t W), nrb_tanC_mk, nrb_nrmC_mk]

lemma nrb_tpart_mk (k m : ℕ) (t : E k) (W : E m) :
    tpart (nrb_mk k m t W) = Real.sqrt (1 + ‖t‖ ^ 2 + ‖W‖ ^ 2) := by
  rw [tpart, nrb_norm_sq_mk]
  congr 1
  ring

lemma nrb_inner_mk (k m : ℕ) (t t' : E k) (W W' : E m) :
    inner ℝ (nrb_mk k m t W) (nrb_mk k m t' W') = inner ℝ t t' + inner ℝ W W' := by
  simp only [nib_inner_split, nrb_tanC_mk, nrb_nrmC_mk]

lemma nrb_cosh_hdist_mk (k m : ℕ) (t t' : E k) (W W' : E m) :
    Real.cosh (hdist (nrb_mk k m t W) (nrb_mk k m t' W'))
      = Real.sqrt (1 + ‖t‖ ^ 2 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖t'‖ ^ 2 + ‖W'‖ ^ 2)
        - inner ℝ t t' - inner ℝ W W' := by
  rw [nib_cosh_hdist, nrb_tpart_mk, nrb_tpart_mk, nrb_inner_mk]
  ring

/-! ## Real analysis of the normal-coordinate shift -/

lemma nrb_sqrt_le (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((A + a) * (A + b)) ≤ A + (a + b) / 2 := by
  have h : (A + a) * (A + b) ≤ (A + (a + b) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  calc Real.sqrt ((A + a) * (A + b)) ≤ Real.sqrt ((A + (a + b) / 2) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = A + (a + b) / 2 := Real.sqrt_sq (by linarith)

lemma nrb_sqrt_mul_le (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (A + a) * Real.sqrt (A + b) ≤ A + (a + b) / 2 := by
  rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ A + a)]
  exact nrb_sqrt_le A a b hA ha hb

/-! ## The two-scale estimate of the displacement -/

lemma nrb_cosh_hdist_mk_same_le (k m : ℕ) (t : E k) (W W' : E m) :
    Real.cosh (hdist (nrb_mk k m t W) (nrb_mk k m t W')) ≤ 1 + ‖W - W'‖ ^ 2 / 2 := by
  rw [nrb_cosh_hdist_mk]
  have hkey : Real.sqrt (1 + ‖t‖ ^ 2 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖t‖ ^ 2 + ‖W'‖ ^ 2)
      ≤ (1 + ‖t‖ ^ 2) + (‖W‖ ^ 2 + ‖W'‖ ^ 2) / 2 :=
    nrb_sqrt_mul_le _ _ _ (by positivity) (by positivity) (by positivity)
  have h1 : inner ℝ t t = ‖t‖ ^ 2 := real_inner_self_eq_norm_sq t
  have h2 : ‖W - W'‖ ^ 2 / 2 = (‖W‖ ^ 2 + ‖W'‖ ^ 2) / 2 - inner ℝ W W' := by
    rw [norm_sub_sq_real]; ring
  linarith

/-- shifting the normal coordinate by `2 sinh (1/2)` stays inside the unit ball -/
lemma nrb_hdist_spread (k m : ℕ) (t : E k) (W W' : E m)
    (h : ‖W - W'‖ ≤ 2 * Real.sinh (1 / 2)) :
    hdist (nrb_mk k m t W) (nrb_mk k m t W') ≤ 1 := by
  have hs : 0 ≤ Real.sinh (1 / 2) := Real.sinh_nonneg_iff.mpr (by norm_num)
  have hcosh : Real.cosh (hdist (nrb_mk k m t W) (nrb_mk k m t W')) ≤ Real.cosh 1 := by
    refine le_trans (nrb_cosh_hdist_mk_same_le k m t W W') ?_
    have hc : Real.cosh 1 = 1 + 2 * Real.sinh (1 / 2) ^ 2 := by
      have h2 := Real.cosh_two_mul (1 / 2)
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
      rw [h2, Real.cosh_sq]
      ring
    rw [hc]
    have hsq : ‖W - W'‖ ^ 2 ≤ (2 * Real.sinh (1 / 2)) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) h
    nlinarith [hsq]
  rw [Real.cosh_le_cosh, abs_of_nonneg (nib_hdist_nonneg _ _), abs_one] at hcosh
  exact hcosh

/-! ## The block isometry in raw chart coordinates -/

lemma nrb_blk_smul_chart (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    blk k m 1 R • u = nrb_mk k m (tanC k m u) (R (nrmC k m u)) := by
  obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi k m v w := ⟨_, _, ((fermi_inv k m).2.1 u).symm⟩
  rw [blk_smul_fermi k m hAk hIk hA hI (1 : PO k 1) R v w]
  obtain ⟨-, -, -, hone, -, -, -, -, -, -, -, -⟩ := hAk
  rw [hone v]
  refine nib_eq_of_tanC_nrmC ?_ ?_
  · rw [nrb_tanC_mk, nib_tanC_fermi, nib_tanC_fermi, R.norm_map]
  · rw [nrb_nrmC_mk, nib_nrmC_fermi, nib_nrmC_fermi, R.norm_map, map_smul]

lemma nrb_cosh_hdist_blk_mk (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (t : E k) (W : E m) :
    Real.cosh (hdist (nrb_mk k m t W) (blk k m 1 R • nrb_mk k m t W))
      = 1 + ‖R W - W‖ ^ 2 / 2 := by
  rw [nrb_blk_smul_chart k m hAk hIk hA hI R (nrb_mk k m t W), nrb_tanC_mk, nrb_nrmC_mk]
  rw [nrb_cosh_hdist_mk, R.norm_map]
  have h1 : Real.sqrt (1 + ‖t‖ ^ 2 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖t‖ ^ 2 + ‖W‖ ^ 2)
      = 1 + ‖t‖ ^ 2 + ‖W‖ ^ 2 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  rw [h1, real_inner_self_eq_norm_sq, norm_sub_sq_real, R.norm_map, real_inner_comm (R W) W]
  ring

lemma nrb_disp_lt_of_hdist_lt_mk (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (t : E k) (W : E m) (η : ℝ)
    (h : hdist (nrb_mk k m t W) (blk k m 1 R • nrb_mk k m t W) < η) :
    ‖R W - W‖ < 2 * Real.sinh (η / 2) := by
  have hDnn : 0 ≤ hdist (nrb_mk k m t W) (blk k m 1 R • nrb_mk k m t W) :=
    nib_hdist_nonneg _ _
  have hηpos : 0 < η := lt_of_le_of_lt hDnn h
  have hcosh : Real.cosh (hdist (nrb_mk k m t W) (blk k m 1 R • nrb_mk k m t W))
      < Real.cosh η := by
    rw [Real.cosh_lt_cosh]
    rwa [abs_of_nonneg hDnn, abs_of_pos hηpos]
  rw [nrb_cosh_hdist_blk_mk k m hAk hIk hA hI R t W] at hcosh
  have hcosh2 : Real.cosh η = 1 + 2 * Real.sinh (η / 2) ^ 2 := by
    have h2 := Real.cosh_two_mul (η / 2)
    rw [show (2 : ℝ) * (η / 2) = η by ring] at h2
    rw [h2, Real.cosh_sq]
    ring
  rw [hcosh2] at hcosh
  have hx : ‖R W - W‖ ^ 2 < (2 * Real.sinh (η / 2)) ^ 2 := by nlinarith [hcosh]
  have hS : 0 ≤ 2 * Real.sinh (η / 2) := by
    have : 0 ≤ η / 2 := by linarith
    have := Real.sinh_nonneg_iff.mpr this
    linarith
  have h4 := sq_lt_sq.mp hx
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hS] at h4

/-! ## The theorem -/

theorem nearId_rotN_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (j m : ℕ) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
      (z : Submission.Mostow.E (j + m)) (η : ℝ),
      Submission.Mostow.POActionProp j → Submission.Mostow.HypIsometryProp j →
      Submission.Mostow.POActionProp (j + m) → Submission.Mostow.HypIsometryProp (j + m) →
      2 ≤ m → 0 < η → η ≤ 1 →
      Submission.Mostow.NearIdAt (Submission.Mostow.blk j m 1 R) z η →
      Submission.Mostow.rotN R ≤ C * η := by
  refine ⟨4, by norm_num, ?_⟩
  intro j m R z η hAj hIj hA hI _hm hη0 hη1 hni
  set t : E j := tanC j m z with ht
  set W : E m := nrmC j m z with hW
  have hz : nrb_mk j m t W = z := by rw [ht, hW]; exact nrb_mk_tanC_nrmC j m z
  -- the displacement at the base point bounds `‖R W - W‖`
  have hbase : hdist (nrb_mk j m t W) (blk j m 1 R • nrb_mk j m t W) < η := by
    rw [hz]
    exact hni z (by rw [nib_hdist_self]; norm_num)
  have hWb : ‖R W - W‖ < 2 * Real.sinh (η / 2) :=
    nrb_disp_lt_of_hdist_lt_mk j m hAj hIj hA hI R t W η hbase
  -- a shifted point, still inside the unit ball, gives the same bound at `W + eps • y`
  have key : ∀ y : E m, ‖y‖ = 1 → ‖R y - y‖ ≤ 4 * η := by
    intro y hy
    set eps : ℝ := 2 * Real.sinh (1 / 2) with heps
    have hepspos : 0 < eps := by rw [heps]; positivity
    set W' : E m := W + eps • y with hW'
    have hnorm : ‖W - W'‖ ≤ 2 * Real.sinh (1 / 2) := by
      rw [hW']
      have hsub : W - (W + eps • y) = -(eps • y) := by abel
      rw [hsub, norm_neg, norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos hepspos, heps]
    have hspread : hdist (nrb_mk j m t W) (nrb_mk j m t W') ≤ 1 :=
      nrb_hdist_spread j m t W W' hnorm
    rw [hz] at hspread
    have h2' : hdist (nrb_mk j m t W') (blk j m 1 R • nrb_mk j m t W') < η := hni _ hspread
    have hWy : ‖R W' - W'‖ < 2 * Real.sinh (η / 2) :=
      nrb_disp_lt_of_hdist_lt_mk j m hAj hIj hA hI R t W' η h2'
    have hdecomp : R W' - W' = (R W - W) + eps • (R y - y) := by
      rw [hW', map_add, map_smul]
      module
    have h6 : eps * ‖R y - y‖ < 2 * (2 * Real.sinh (η / 2)) := by
      have h7 : eps * ‖R y - y‖ = ‖eps • (R y - y)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hepspos]
      have h8 : eps • (R y - y) = (R W' - W') - (R W - W) := by rw [hdecomp]; module
      rw [h7, h8]
      calc ‖(R W' - W') - (R W - W)‖ ≤ ‖R W' - W'‖ + ‖R W - W‖ := norm_sub_le _ _
        _ < 2 * Real.sinh (η / 2) + 2 * Real.sinh (η / 2) := by linarith
        _ = 2 * (2 * Real.sinh (η / 2)) := by ring
    have hs1 : (1 / 2 : ℝ) ≤ Real.sinh (1 / 2) := Real.self_le_sinh_iff.mpr (by norm_num)
    have hs2 := nib_sinh_half_le (le_of_lt hη0) hη1
    have h9a : (1 / 2) * ‖R y - y‖ ≤ Real.sinh (1 / 2) * ‖R y - y‖ :=
      mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    have h9b : eps * ‖R y - y‖ = 2 * (Real.sinh (1 / 2) * ‖R y - y‖) := by rw [heps]; ring
    have h9c : 2 * Real.sinh (η / 2) ≤ 3 * η / 2 := by linarith [hs2]
    nlinarith [h6, h9a, h9b, h9c]
  exact nib_rotN_le_of_unit (by linarith) key

end

end Work.Mostow
