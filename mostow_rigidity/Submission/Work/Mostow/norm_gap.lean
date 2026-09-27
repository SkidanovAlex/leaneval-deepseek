import Mathlib
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.finite_nearStab

-- File: Submission/Work/Mostow/norm_gap.lean (module Submission.Work.Mostow.norm_gap).
-- Useful imports: import Submission.Work.Mostow.StabLift (Work.Mostow.LambdaMat, LambdaMat_isJOrth,
--   LambdaMat_isJOrth_row), import Submission.Work.Mostow.finite_nearStab (finite_nearStab) or
--   redo the finiteness argument: Subgroup.tendsto_coe_cofinite_of_isDiscrete +
--   tendsto_coe_cofinite_iff + compactness of matBallToPO.
-- IMPORTANT: do NOT import anything from the `visualDefs` cluster (visualDefs, visualAux,
-- visualMeasure, spherePolar, coneBasic, poTransitive, homoExt*, ...): those files define
-- `Work.Mostow.wvec` with a different type, clashing with `QIDefs` (which finite_nearStab needs).
-- Mathematical content: discreteness of Γ makes ‖LambdaMat γ - 1‖ bounded away from 0 on Γ∖{1}.
-- Suggested route: {γ : Γ | ‖LambdaMat γ - 1‖ ≤ 1} is finite (entries of LambdaMat γ are within 1
-- of those of 1, hence Λ(γ) ∈ matBall n 2, whose image in PO n 1 is compact; a discrete subgroup
-- meets a compact set in a finite set).  If the set {‖Λγ-1‖ : γ ≠ 1} had infimum 0, then keeping
-- only the elements with norm ≤ 1 (a finite set) would produce γ ≠ 1 with Λγ = 1, hence γ = 1
-- (use hlift_LambdaMat + injectivity of hlift + the faithfulness clause of POActionProp).
open scoped Matrix Matrix.Norms.Operator
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

/-- `hlift 0` is a unit vector for the sup norm on `Fin n ⊕ Fin 1 → ℝ`. -/
lemma norm_hlift_zero : ‖hlift (0 : E n)‖ = 1 := by
  rw [Submission.Mostow.Hyper.hlift_zero, Submission.Mostow.Hyper.etime, Pi.norm_single, norm_one]

/-- The time coordinate of `hlift 0` is `1`. -/
lemma hlift_zero_time : (hlift (0 : E n)) (Sum.inr 0) = 1 := by
  rw [Submission.Mostow.Hyper.hlift_zero, Submission.Mostow.Hyper.etime]
  simp

/-- The `tpart` (time) coordinate of `g • 0` is within `‖Λ(g) − 1‖` of `1`. -/
lemma abs_tpart_smul_zero_sub_one_le (hA : POActionProp n) (g : PO n 1) :
    |tpart (g • (0 : E n)) - 1| ≤ ‖LambdaMat g - 1‖ := by
  have hstep : ‖LambdaMat g *ᵥ hlift (0 : E n) - hlift (0 : E n)‖ ≤ ‖LambdaMat g - 1‖ := by
    have h1 : LambdaMat g *ᵥ hlift (0 : E n) - hlift (0 : E n)
        = (LambdaMat g - 1) *ᵥ hlift (0 : E n) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [h1]
    calc ‖(LambdaMat g - 1) *ᵥ hlift (0 : E n)‖
        ≤ ‖LambdaMat g - 1‖ * ‖hlift (0 : E n)‖ := Matrix.linfty_opNorm_mulVec _ _
      _ = ‖LambdaMat g - 1‖ := by rw [norm_hlift_zero, mul_one]
  have htime : tpart (g • (0 : E n)) - 1
      = (LambdaMat g *ᵥ hlift (0 : E n) - hlift (0 : E n)) (Sum.inr 0) := by
    have h3 : LambdaMat g *ᵥ hlift (0 : E n) - hlift (0 : E n)
        = hlift (g • (0 : E n)) - hlift (0 : E n) := by
      rw [hlift_LambdaMat hA g (0 : E n)]
    rw [h3, Pi.sub_apply, hlift_zero_time]
    rfl
  have h4 : ‖(LambdaMat g *ᵥ hlift (0 : E n) - hlift (0 : E n)) (Sum.inr 0)‖
      ≤ ‖LambdaMat g - 1‖ := le_trans (norm_le_pi_norm _ (Sum.inr 0)) hstep
  rwa [show ‖(LambdaMat g *ᵥ hlift (0:E n) - hlift (0:E n)) (Sum.inr 0)‖
      = |tpart (g • (0:E n)) - 1| from by rw [Real.norm_eq_abs, htime]] at h4

/-- If `‖Λ(g) − 1‖ ≤ 1` then `g` moves the origin by at most `arcosh 2`. -/
lemma hdist_zero_le_arcosh_two_of_norm_le (hA : POActionProp n) (g : PO n 1)
    (h : ‖LambdaMat g - 1‖ ≤ 1) :
    hdist (0 : E n) (g • (0 : E n)) ≤ Real.arcosh 2 := by
  have habs : |tpart (g • (0 : E n)) - 1| ≤ 1 :=
    le_trans (abs_tpart_smul_zero_sub_one_le hA g) h
  have ht : tpart (g • (0 : E n)) ≤ 2 := by
    have := (abs_le.mp habs).2; linarith
  have hu : hdist (0 : E n) (g • (0 : E n)) = Real.arcosh (tpart (g • (0 : E n))) := by
    rw [hdist, tpart, tpart]; simp
  rw [hu]
  exact (Real.arcosh_le_arcosh (tpart_pos _) (by norm_num)).mpr ht

/-- `Λ` is injective: an element whose lift is the identity acts trivially, hence is the identity. -/
lemma eq_one_of_LambdaMat_eq_one (hA : POActionProp n) {g : PO n 1} (h : LambdaMat g = 1) :
    g = 1 := by
  refine (POBasic.ofProp hA).faithful g (fun u => ?_)
  apply hlift_injective
  rw [hlift_LambdaMat hA g u, h, Matrix.one_mulVec]

/-- The set of elements of a discrete subgroup whose lift is within `1` of the identity is
finite.  Indeed those elements move the origin by at most `arcosh 2`, and the near-stabiliser of
the origin in a discrete subgroup is finite. -/
theorem finite_norm_le_one (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ)) :
    {γ : Γ | ‖LambdaMat (γ : PO n 1) - 1‖ ≤ 1}.Finite :=
  (finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc (Real.arcosh 2)).subset
    (fun γ hγ => hdist_zero_le_arcosh_two_of_norm_le hA (γ : PO n 1) hγ)

theorem norm_gap (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) :
    ∃ m : ℝ, 0 < m ∧ ∀ γ : Γ, (γ : PO n 1) ≠ 1 →
      m ≤ ‖Work.Mostow.LambdaMat (γ : PO n 1) - 1‖ := by
  classical
  set S : Set Γ := {γ | (γ : PO n 1) ≠ 1 ∧ ‖LambdaMat (γ : PO n 1) - 1‖ ≤ 1} with hS
  have hfin : S.Finite := (finite_norm_le_one hA hI hdisc).subset (fun γ hγ => hγ.2)
  have hpos : ∀ γ ∈ S, 0 < ‖LambdaMat (γ : PO n 1) - 1‖ := by
    intro γ hγ
    exact norm_pos_iff.mpr (fun h => hγ.1 (eq_one_of_LambdaMat_eq_one hA (sub_eq_zero.mp h)))
  by_cases hne : S.Nonempty
  · have hne' : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr hne
    refine ⟨hfin.toFinset.inf' hne' (fun γ => ‖LambdaMat (γ : PO n 1) - 1‖), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro γ hγ
      exact hpos γ (hfin.mem_toFinset.mp hγ)
    · intro γ hγne
      by_cases hle : ‖LambdaMat (γ : PO n 1) - 1‖ ≤ 1
      · exact Finset.inf'_le (s := hfin.toFinset) (fun γ => ‖LambdaMat (γ : PO n 1) - 1‖)
          (hfin.mem_toFinset.mpr ⟨hγne, hle⟩)
      · have hle1 : hfin.toFinset.inf' hne' (fun γ => ‖LambdaMat (γ : PO n 1) - 1‖) ≤ 1 := by
          obtain ⟨a, ha⟩ := hne
          exact le_trans (Finset.inf'_le (s := hfin.toFinset)
            (fun γ => ‖LambdaMat (γ : PO n 1) - 1‖) (hfin.mem_toFinset.mpr ha)) ha.2
        linarith [lt_of_not_ge hle]
  · refine ⟨1, one_pos, fun γ hγne => ?_⟩
    have hnot : γ ∉ S := fun h => hne ⟨γ, h⟩
    have hgt : ¬ ‖LambdaMat (γ : PO n 1) - 1‖ ≤ 1 := fun h => hnot ⟨hγne, h⟩
    linarith [lt_of_not_ge hgt]

end

end Work.Mostow
