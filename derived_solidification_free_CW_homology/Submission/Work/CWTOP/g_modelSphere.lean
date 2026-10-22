/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.CWTOP.Closed
import Submission.Work.CWTOP.contractible_capGt
import Submission.Work.CWTOP.homotopyEquiv_band_modelSphere
import Submission.Work.CWTOP.g_of_contractible
import Submission.Work.CWTOP.g_of_isEmpty

/-!
# The model sphere lies in every `CWClosed` class

`Work.CWTOP.modelSphere n` is the unit sphere of `Fin (n+1) → ℝ` for the max norm, i.e. the
boundary of the cube `[-1,1]^{n+1}`.  We prove that it lies in every class `G` of Hausdorff spaces
satisfying the closure axioms `CWClosed` (points, empty space, homotopy equivalences, small
coproducts, open Mayer–Vietoris and compact exhaustion).

The argument is the classical decomposition of the sphere into two contractible open caps

* `capLt n = {y | y 0 < 1}`  (the sphere with the point `y 0 = 1` removed), and
* `capGt n = {y | -1 < y 0}` (the sphere with the point `y 0 = -1` removed),

which cover the sphere and whose intersection is the open band `{|y 0| < 1}`.  In the max norm
this band is the product `(-1,1) × modelSphere (n-1)` up to homeomorphism, so it is homotopy
equivalent to `modelSphere (n-1)`; for `n = 0` it is empty.  Hence `G (modelSphere n)` follows by
induction on `n` using Mayer–Vietoris.

The topological inputs are proved in sibling files: the contractibility of the cap `{-1 < y 0}` in
`Submission/Work/CWTOP/contractible_capGt` and the homotopy equivalence between the band and
`modelSphere (n-1)` in `.../homotopyEquiv_band_modelSphere`.  The other cap `{y 0 < 1}` is the
antipodal image of `{-1 < y 0}`, hence contractible as well (see `capNegHomeo` below, which makes
the proof independent of the mirror statement).  The two general consequences of `CWClosed` used
here, `g_of_contractible` and `g_of_isEmpty`, are proved in their own files as well.
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

namespace ModelSphere

/-! ## The two caps -/

/-- The cap `{y | y 0 < 1}`: the model sphere with the point `y 0 = 1` removed. -/
def capLt (n : ℕ) : Set (modelSphere n) := {y | y.1 0 < 1}

/-- The cap `{y | -1 < y 0}`: the model sphere with the point `y 0 = -1` removed. -/
def capGt (n : ℕ) : Set (modelSphere n) := {y | -1 < y.1 0}

lemma isOpen_capLt (n : ℕ) : IsOpen (capLt n) :=
  isOpen_lt ((continuous_apply 0).comp continuous_subtype_val) continuous_const

lemma isOpen_capGt (n : ℕ) : IsOpen (capGt n) :=
  isOpen_lt continuous_const ((continuous_apply 0).comp continuous_subtype_val)

lemma capLt_union_capGt (n : ℕ) : capLt n ∪ capGt n = univ := by
  ext y
  simp only [capLt, capGt, mem_union, mem_ofPred_eq, mem_univ, iff_true]
  rcases lt_or_ge (y.1 0) 1 with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-! ## The band is empty in dimension `0` -/

/-- In dimension `0` the band `{|y 0| < 1}` of the model sphere `modelSphere 0` is empty, since
the sphere `{±1} ⊂ ℝ` consists of the two points `±1`. -/
lemma isEmpty_band_zero : IsEmpty {y : modelSphere 0 // y.1 0 < 1 ∧ -1 < y.1 0} := by
  refine ⟨fun y => ?_⟩
  have h3 : ‖y.1.1‖ = 1 := by
    have h := y.1.2
    simp only [Work.CWTOP.modelSphere, mem_sphere_iff_norm, sub_zero] at h
    exact h
  have hy : ‖y.1.1‖ = |y.1.1 0| := by rw [Pi.norm_def]; simp
  have habs : |y.1.1 0| = 1 := by rw [← hy]; exact h3
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h <;> linarith [y.2.1, y.2.2]

/-! ## The cap `{y 0 < 1}` is the antipodal image of the cap `{-1 < y 0}` -/

/-- Negation preserves the model sphere. -/
lemma neg_mem_modelSphere {n : ℕ} {f : Fin (n + 1) → ℝ} (hf : f ∈ modelSphere n) :
    -f ∈ modelSphere n := by
  rw [Work.CWTOP.modelSphere, mem_sphere_iff_norm, sub_zero] at hf ⊢
  rwa [norm_neg]

/-- The antipodal map is a homeomorphism from the cap `{y 0 < 1}` onto the cap `{-1 < y 0}`. -/
def capNegHomeo (n : ℕ) :
    {y : modelSphere n // y.1 0 < 1} ≃ₜ {y : modelSphere n // -1 < y.1 0} where
  toFun y := ⟨⟨-y.1.1, neg_mem_modelSphere y.1.2⟩, by
      have h := y.2
      show -1 < -(y.1.1 0)
      linarith⟩
  invFun y := ⟨⟨-y.1.1, neg_mem_modelSphere y.1.2⟩, by
      have h := y.2
      show -(y.1.1 0) < 1
      linarith⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

/-- The cap `{y 0 < 1}` is contractible, as the antipodal image of the cap `{-1 < y 0}`. -/
theorem capLt_contractible (n : ℕ) : ContractibleSpace {y : modelSphere n // y.1 0 < 1} :=
  (capNegHomeo n).contractibleSpace_iff.mpr (contractible_capGt n)

/-! ## `G` of the caps -/

lemma g_capLt (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) (n : ℕ) :
    G (TopCat.of (capLt n)) := by
  have : ContractibleSpace ↥(TopCat.of (capLt n)) := capLt_contractible n
  exact g_of_contractible G hG (TopCat.of (capLt n))

lemma g_capGt (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) (n : ℕ) :
    G (TopCat.of (capGt n)) := by
  have : ContractibleSpace ↥(TopCat.of (capGt n)) := contractible_capGt n
  exact g_of_contractible G hG (TopCat.of (capGt n))

/-! ## `G` of the band -/

lemma g_band_zero (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) :
    G (TopCat.of (capLt 0 ∩ capGt 0 : Set (modelSphere 0))) := by
  have : IsEmpty ↥(TopCat.of (capLt 0 ∩ capGt 0 : Set (modelSphere 0))) := isEmpty_band_zero
  exact g_of_isEmpty G hG _

lemma g_band_succ (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) (m : ℕ)
    (ih : G (TopCat.of (modelSphere m))) :
    G (TopCat.of (capLt (m + 1) ∩ capGt (m + 1) : Set (modelSphere (m + 1)))) := by
  obtain ⟨e⟩ := homotopyEquiv_band_modelSphere m
  exact hG.of_homotopyEquiv _ _ e ih

end ModelSphere

/-! ## The model sphere lies in `G` -/

/-- **The model sphere `Sⁿ` lies in every `CWClosed` class.** -/
theorem g_modelSphere (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G) (n : ℕ) :
    G (TopCat.of (Work.CWTOP.modelSphere n)) := by
  suffices h : ∀ k, G (TopCat.of (Work.CWTOP.modelSphere k)) from h n
  intro k
  induction k with
  | zero =>
    exact hG.mv (TopCat.of (Work.CWTOP.modelSphere 0)) (ModelSphere.capLt 0) (ModelSphere.capGt 0)
      (ModelSphere.isOpen_capLt 0) (ModelSphere.isOpen_capGt 0) (ModelSphere.capLt_union_capGt 0)
      (ModelSphere.g_capLt G hG 0) (ModelSphere.g_capGt G hG 0) (ModelSphere.g_band_zero G hG)
  | succ m ih =>
    exact hG.mv (TopCat.of (Work.CWTOP.modelSphere (m + 1))) (ModelSphere.capLt (m + 1))
      (ModelSphere.capGt (m + 1)) (ModelSphere.isOpen_capLt (m + 1))
      (ModelSphere.isOpen_capGt (m + 1)) (ModelSphere.capLt_union_capGt (m + 1))
      (ModelSphere.g_capLt G hG (m + 1)) (ModelSphere.g_capGt G hG (m + 1))
      (ModelSphere.g_band_succ G hG m ih)

end Work.CWTOP
