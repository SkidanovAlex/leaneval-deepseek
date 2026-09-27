import Mathlib
import Submission.Work.Mostow.nearId_rotN_bound
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.finite_nearStab

/-!
# Auxiliary facts for the pivot lemma `ftbPivot`

Small, self-contained transport lemmas about the chart model, the dimension casts, and the
`NearIdAt` predicate, plus the fact that a fixed-point-free isometry of `E 1` is `-1`.
Used by `Work.Mostow.ftbPivot` and by the two lemmas delegated from it.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The dimension cast `e ▸ · : E a → E b` is an `hdist`-isometry. -/
lemma hdist_cast {a b : ℕ} (e : a = b) (u v : E a) :
    hdist (e ▸ u : E b) (e ▸ v : E b) = hdist u v := by
  cases e; rfl

/-- `rotN` vanishes in dimension `0`. -/
lemma rotN_e0 (R : E 0 ≃ₗᵢ[ℝ] E 0) : rotN R = 0 := by
  rw [rotN]; simp

/-- `NearIdAt` transports back along a dimension cast. -/
lemma nearIdAt_cast {a b : ℕ} (e : a = b) (B : PO a 1) (z : E b) (η : ℝ)
    (h : NearIdAt (e ▸ B : PO b 1) z η) : NearIdAt B (e.symm ▸ z : E a) η := by
  intro v hv
  have h1 : hdist z (e ▸ v : E b) = hdist (e.symm ▸ z : E a) v := by
    rw [← hdist_cast e (e.symm ▸ z : E a) v, cast_symm_cast]
  rw [← h1] at hv
  have h2 := h (e ▸ v) hv
  rw [cast_smul_po e B v, hdist_cast e v (B • v)] at h2
  exact h2

/-- A linear isometry of `E 1` without nonzero fixed vectors is `-1`. -/
lemma eq_neg_of_fixedFree (R : E 1 ≃ₗᵢ[ℝ] E 1) (hR : ∀ w : E 1, R w = w → w = 0) :
    ∀ w : E 1, R w = -w := by
  set e : E 1 := EuclideanSpace.single 0 (1 : ℝ) with he
  have hcoord : ∀ w : E 1, w = w 0 • e := by
    intro w
    ext i
    fin_cases i
    simp [e]
  have hene : e ≠ 0 := by
    intro h
    have := congrFun (congrArg WithLp.ofLp h) 0
    simp [e] at this
  have hnorm : ‖e‖ = 1 := by
    rw [he]
    simpa using PiLp.norm_single 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1) (1 : ℝ)
  set c : ℝ := (R e) 0 with hc
  have hRe : R e = c • e := by
    rw [← hcoord (R e)]
  have hcnorm : |c| = 1 := by
    have h1 : ‖R e‖ = 1 := by rw [R.norm_map, hnorm]
    rw [hRe, norm_smul, Real.norm_eq_abs, hnorm, mul_one] at h1
    exact h1
  have hcne : c ≠ 1 := by
    intro hc1
    have hall : ∀ w : E 1, R w = w := by
      intro w
      rw [hcoord w, map_smul, hRe, hc1, one_smul]
    exact hene (hR e (hall e))
  intro w
  have hcw : c = -1 := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hcnorm with h | h
    · exact absurd h hcne
    · exact h
  rw [hcoord w, map_smul, hRe, hcw, neg_one_smul, smul_neg]

/-! ## Finite point stabilisers -/

/-- A discrete subgroup of `PO n 1` has finite point stabilisers. -/
theorem ftbFiniteFixesPoint {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Λ)) (p : Submission.Mostow.E n) :
    {c : LeanEval.Geometry.MostowRigidity.PO n 1 | c ∈ Λ ∧ c • p = p}.Finite := by
  have hAb := POBasic.ofProp hA
  have hIb := HypIsoData.ofProp hI
  have hfin : {γ : Λ | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ 2 * hdist (0 : E n) p}.Finite :=
    finite_nearStab hAb hIb hdisc _
  refine (hfin.image (fun γ : Λ => (γ : PO n 1))).subset ?_
  rintro c ⟨hcΛ, hcp⟩
  refine ⟨⟨c, hcΛ⟩, ?_, rfl⟩
  have hcinv : c⁻¹ • p = p := by
    have h : c⁻¹ • (c • p) = c⁻¹ • p := by rw [hcp]
    rw [← hAb.mul_smul, inv_mul_cancel, hAb.one_smul] at h
    exact h.symm
  have e1 : hdist (0 : E n) (c • (0 : E n)) = hdist (c⁻¹ • (0 : E n)) (0 : E n) := by
    have h := hIb.isom_smul c⁻¹ (0 : E n) (c • (0 : E n))
    rw [← hAb.mul_smul, inv_mul_cancel, hAb.one_smul] at h
    exact h.symm
  have e2 : hdist (c⁻¹ • (0 : E n)) (0 : E n)
      ≤ hdist (c⁻¹ • (0 : E n)) (c⁻¹ • p) + hdist (c⁻¹ • p) (0 : E n) :=
    hIb.triangle _ _ _
  rw [hIb.isom_smul c⁻¹ (0 : E n) p, hcinv, hIb.symm p (0 : E n)] at e2
  calc hdist (0 : E n) (c • (0 : E n)) = hdist (c⁻¹ • (0 : E n)) (0 : E n) := e1
    _ ≤ hdist (0 : E n) p + hdist (0 : E n) p := e2
    _ = 2 * hdist (0 : E n) p := by ring

/-! ## The `m = 1` exclusion -/

/-- The unit vector `EuclideanSpace.single 0 1` of `E 1`. -/
private lemma norm_single_one : ‖(EuclideanSpace.single 0 (1 : ℝ) : E 1)‖ = 1 := by
  simpa using PiLp.norm_single 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1) (1 : ℝ)

/-- A block element with a fixed-point-free normal part in normal dimension `1` is far from the
identity at *every* point (its displacement in a unit ball is bounded below by
`arcosh (4 cosh 1 - 3) > 1`): it is never `η`-near-identity for `η ≤ 1`. -/
theorem ftbNotNearIdAtBlkOne (j : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hIj : Submission.Mostow.HypIsometryProp j) (hAj1 : Submission.Mostow.POActionProp (j + 1))
    (hIj1 : Submission.Mostow.HypIsometryProp (j + 1))
    (R : E 1 ≃ₗᵢ[ℝ] E 1)
    (hRfree : ∀ w : E 1, R w = w → w = 0)
    (z : E (j + 1)) (η : ℝ) (hη1 : η ≤ 1) :
    ¬ NearIdAt (blk j 1 1 R) z η := by
  intro hni
  have hR : ∀ w : E 1, R w = -w := eq_neg_of_fixedFree R hRfree
  set c : ℝ := 2 * Real.sinh (1 / 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcnonneg : 0 ≤ c := hcpos.le
  have hsnonneg : 0 ≤ Real.sinh (1 / 2 : ℝ) := Real.sinh_nonneg_iff.mpr (by norm_num)
  set t : E j := tanC j 1 z with ht
  set W : E 1 := nrmC j 1 z with hW
  have hz : nrb_mk j 1 t W = z := by rw [ht, hW]; exact nrb_mk_tanC_nrmC j 1 z
  -- a unit vector `y` with `c ≤ ‖W + c • y‖`
  obtain ⟨y, hyunit, hyge⟩ : ∃ y : E 1, ‖y‖ = 1 ∧ c ≤ ‖W + c • y‖ := by
    by_cases hW0 : W = 0
    · refine ⟨EuclideanSpace.single 0 (1 : ℝ), norm_single_one, ?_⟩
      rw [hW0, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, norm_single_one, mul_one]
    · have hWpos : 0 < ‖W‖ := by
        rw [norm_pos_iff]; exact hW0
      refine ⟨‖W‖⁻¹ • W, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hWpos)]
      · have hWs : W + c • (‖W‖⁻¹ • W) = (1 + c * ‖W‖⁻¹) • W := by module
        have hval : (1 + c * ‖W‖⁻¹) * ‖W‖ = ‖W‖ + c := by
          field_simp
        rw [hWs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hval]
        linarith [norm_nonneg W]
  set W' : E 1 := W + c • y with hW'def
  have hWnorm : c ≤ ‖W'‖ := by rw [hW'def]; exact hyge
  have hsub : W - W' = -(c • y) := by rw [hW'def]; abel
  have hspread : hdist z (nrb_mk j 1 t W') ≤ 1 := by
    rw [← hz]
    refine nrb_hdist_spread j 1 t W W' ?_
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hyunit, mul_one, hc]
  have hdisp : hdist (nrb_mk j 1 t W') (blk j 1 1 R • nrb_mk j 1 t W') < η := hni _ hspread
  have hcosh := nrb_cosh_hdist_blk_mk j 1 hAj hIj hAj1 hIj1 R t W'
  have hRnorm : ‖R W' - W'‖ = 2 * ‖W'‖ := by
    rw [hR W']
    have h2 : -W' - W' = (-2 : ℝ) • W' := by module
    rw [h2, norm_smul, Real.norm_eq_abs]
    rw [show |(-2 : ℝ)| = 2 by norm_num]
  have hc2 : Real.cosh 1 = 1 + 2 * Real.sinh (1 / 2) ^ 2 := by
    have h2 := Real.cosh_two_mul (1 / 2 : ℝ)
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
    rw [h2, Real.cosh_sq]
    ring
  have hge : 4 * Real.cosh 1 - 3
      ≤ Real.cosh (hdist (nrb_mk j 1 t W') (blk j 1 1 R • nrb_mk j 1 t W')) := by
    rw [hcosh, hRnorm, hc2]
    nlinarith [hWnorm, hcpos, norm_nonneg W']
  have h1lt : Real.cosh 1 < 4 * Real.cosh 1 - 3 := by
    have h1 : (1 : ℝ) < Real.cosh 1 := Real.one_lt_cosh.mpr (by norm_num)
    linarith
  have hdgt : 1 < hdist (nrb_mk j 1 t W') (blk j 1 1 R • nrb_mk j 1 t W') := by
    have h := Real.cosh_lt_cosh.mp (lt_of_lt_of_le h1lt hge)
    rwa [abs_one, abs_of_nonneg (nib_hdist_nonneg _ _)] at h
  linarith [hdisp, hdgt, hη1]

end Work.Mostow
