import Mathlib
import Submission.Work.Pi6.SQ.Defs
import Submission.Work.Pi6.SQ.cup1Coboundary
import Submission.Work.Pi6.SQ.cup2Coboundary
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cup)

/-! ## elementary helpers -/

private lemma F2_add_self (a : F2) : a + a = 0 := by
  have h2 : (2 : F2) = 0 := by decide
  calc a + a = 2 * a := by ring
    _ = 0 := by rw [h2, zero_mul]

private lemma cochain_add_self {X : SSet} {n : ℕ} (c : Cochain F2 X n) : c + c = 0 := by
  ext x
  exact F2_add_self (c x)

private lemma cochainDiff_add {X : SSet} {n : ℕ} (a b : Cochain F2 X n) :
    cochainDiff F2 X (a + b) = cochainDiff F2 X a + cochainDiff F2 X b := by
  have h := map_add (Work.Cohomology.cochainDiffLM F2 X n) a b
  simpa only [Work.Cohomology.cochainDiffLM_apply] using h

private lemma cochainDiff_cochainDiff {X : SSet} {k : ℕ} (α : Cochain F2 X k) :
    cochainDiff F2 X (cochainDiff F2 X α) = 0 := by
  rw [cochainDiff, cochainDiff, LinearMap.comp_assoc]
  have h : (((X.chainComplex (ModuleCat.of F2 F2)).d (k + 1) k).hom.comp
      ((X.chainComplex (ModuleCat.of F2 F2)).d (k + 2) (k + 1)).hom) = 0 := by
    rw [← ModuleCat.hom_comp, HomologicalComplex.d_comp_d, ModuleCat.hom_zero]
  rw [h, LinearMap.comp_zero]

private lemma cast_zero_cochain {X : SSet} {p q : ℕ} (h : p = q) :
    h ▸ (0 : Cochain F2 X p) = (0 : Cochain F2 X q) := by cases h; rfl

private lemma cast_self_cochain {X : SSet} {p : ℕ} (h : p = p) (x : Cochain F2 X p) :
    h ▸ x = x := by cases h; rfl

private lemma cast_add_cochain {X : SSet} {p q : ℕ} (h : p = q) (a b : Cochain F2 X p) :
    h ▸ (a + b) = (h ▸ a) + (h ▸ b) := by cases h; rfl

/-! ## bilinearity of the library's `cup1` -/

private lemma cup1_add_left {X : SSet} {n m : ℕ} (α α' : Cochain F2 X n) (β : Cochain F2 X m) :
    Work.Cohomology.cup1 F2 X n m (α + α') β =
      Work.Cohomology.cup1 F2 X n m α β + Work.Cohomology.cup1 F2 X n m α' β := by
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add, Work.Cohomology.genEval_cup1]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

private lemma cup1_add_right {X : SSet} {n m : ℕ} (α : Cochain F2 X n) (β β' : Cochain F2 X m) :
    Work.Cohomology.cup1 F2 X n m α (β + β') =
      Work.Cohomology.cup1 F2 X n m α β + Work.Cohomology.cup1 F2 X n m α β' := by
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add, Work.Cohomology.genEval_cup1]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

private lemma cup1_zero_left {X : SSet} (n m : ℕ) (β : Cochain F2 X m) :
    Work.Cohomology.cup1 F2 X n m 0 β = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  simp only [genEval, LinearMap.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

private lemma cup1_zero_right {X : SSet} (n m : ℕ) (α : Cochain F2 X n) :
    Work.Cohomology.cup1 F2 X n m α 0 = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  simp only [genEval, LinearMap.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

/-! ## bilinearity of `cup1m` -/

private lemma cup1m_add_left (X : SSet) (n m : ℕ) (u u' : Cochain F2 X n) (v : Cochain F2 X m) :
    cup1m X n m (u + u') v = cup1m X n m u v + cup1m X n m u' v := by
  rw [cup1m, cup1m, cup1m, cup1_add_right, cast_add_cochain]

private lemma cup1m_add_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v v' : Cochain F2 X m) :
    cup1m X n m u (v + v') = cup1m X n m u v + cup1m X n m u v' := by
  rw [cup1m, cup1m, cup1m, cup1_add_left, cast_add_cochain]

private lemma cup1m_zero_left (X : SSet) (n m : ℕ) (v : Cochain F2 X m) :
    cup1m X n m (0 : Cochain F2 X n) v = 0 := by
  rw [cup1m, cup1_zero_right, cast_zero_cochain]

private lemma cup1m_zero_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) :
    cup1m X n m u (0 : Cochain F2 X m) = 0 := by
  rw [cup1m, cup1_zero_left, cast_zero_cochain]

/-! ## bilinearity of `cup2` -/

private lemma cup2_add_left (X : SSet) (n m : ℕ) (u u' : Cochain F2 X n) (v : Cochain F2 X m) :
    cup2 X n m (u + u') v = cup2 X n m u v + cup2 X n m u' v := by
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add, genEval_cup2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma cup2_add_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v v' : Cochain F2 X m) :
    cup2 X n m u (v + v') = cup2 X n m u v + cup2 X n m u v' := by
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add, genEval_cup2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma cup2_zero_left (X : SSet) (n m : ℕ) (v : Cochain F2 X m) :
    cup2 X n m (0 : Cochain F2 X n) v = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_cup2]
  simp only [genEval, LinearMap.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

private lemma cup2_zero_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) :
    cup2 X n m u (0 : Cochain F2 X m) = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_cup2]
  simp only [genEval, LinearMap.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

/-! ## cast-free instances of the two coboundary formulas -/

private lemma cup1Cob12 (X : SSet) (u : Cochain F2 X 1) (v : Cochain F2 X 2) :
    cochainDiff F2 X (cup1m X 1 2 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u + cup1m X 2 2 (cochainDiff F2 X u) v
        + cup1m X 1 3 u (cochainDiff F2 X v) := by
  have h := cup1Coboundary X 1 2 u v (by omega) (by omega)
  simpa only [show (1:ℕ) + 1 = 2 from rfl, show (2:ℕ) + 1 = 3 from rfl] using h

private lemma cup1Cob21 (X : SSet) (u : Cochain F2 X 2) (v : Cochain F2 X 1) :
    cochainDiff F2 X (cup1m X 2 1 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u + cup1m X 3 1 (cochainDiff F2 X u) v
        + cup1m X 2 2 u (cochainDiff F2 X v) := by
  have h := cup1Coboundary X 2 1 u v (by omega) (by omega)
  simpa only [show (2:ℕ) + 1 = 3 from rfl, show (1:ℕ) + 1 = 2 from rfl] using h

private lemma cup1Cob22 (X : SSet) (u v : Cochain F2 X 2) :
    cochainDiff F2 X (cup1m X 2 2 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u + cup1m X 3 2 (cochainDiff F2 X u) v
        + cup1m X 2 3 u (cochainDiff F2 X v) := by
  have h := cup1Coboundary X 2 2 u v (by omega) (by omega)
  simpa only [show (2:ℕ) + 1 = 3 from rfl] using h

private lemma cup1Cob23 (X : SSet) (u : Cochain F2 X 2) (v : Cochain F2 X 3) :
    cochainDiff F2 X (cup1m X 2 3 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u + cup1m X 3 3 (cochainDiff F2 X u) v
        + cup1m X 2 4 u (cochainDiff F2 X v) := by
  have h := cup1Coboundary X 2 3 u v (by omega) (by omega)
  simpa only [show (2:ℕ) + 1 = 3 from rfl, show (3:ℕ) + 1 = 4 from rfl] using h

private lemma cup1Cob32 (X : SSet) (u : Cochain F2 X 3) (v : Cochain F2 X 2) :
    cochainDiff F2 X (cup1m X 3 2 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u + cup1m X 4 2 (cochainDiff F2 X u) v
        + cup1m X 3 3 u (cochainDiff F2 X v) := by
  have h := cup1Coboundary X 3 2 u v (by omega) (by omega)
  simpa only [show (3:ℕ) + 1 = 4 from rfl, show (2:ℕ) + 1 = 3 from rfl] using h

private lemma cup1Cob33 (X : SSet) (u v : Cochain F2 X 3) :
    cochainDiff F2 X (cup1m X 3 3 u v) =
      Work.Cohomology.cup F2 X u v + Work.Cohomology.cup F2 X v u + cup1m X 4 3 (cochainDiff F2 X u) v
        + cup1m X 3 4 u (cochainDiff F2 X v) := by
  have h := cup1Coboundary X 3 3 u v (by omega) (by omega)
  simpa only [show (3:ℕ) + 1 = 4 from rfl] using h

private lemma cup2Cob23 (X : SSet) (u : Cochain F2 X 2) (v : Cochain F2 X 3) :
    cochainDiff F2 X (cup2 X 2 3 u v) =
      cup1m X 2 3 u v + cup1m X 3 2 v u + cup2 X 3 3 (cochainDiff F2 X u) v
        + cup2 X 2 4 u (cochainDiff F2 X v) := by
  have h := cup2Coboundary X 2 3 u v (by omega) (by omega)
  simpa only [show (2:ℕ) + 1 = 3 from rfl, show (3:ℕ) + 1 = 4 from rfl] using h

private lemma cup2Cob32 (X : SSet) (u : Cochain F2 X 3) (v : Cochain F2 X 2) :
    cochainDiff F2 X (cup2 X 3 2 u v) =
      cup1m X 3 2 u v + cup1m X 2 3 v u + cup2 X 4 2 (cochainDiff F2 X u) v
        + cup2 X 3 3 u (cochainDiff F2 X v) := by
  have h := cup2Coboundary X 3 2 u v (by omega) (by omega)
  simpa only [show (3:ℕ) + 1 = 4 from rfl, show (2:ℕ) + 1 = 3 from rfl] using h

private lemma cup2Cob34 (X : SSet) (u : Cochain F2 X 3) (v : Cochain F2 X 4) :
    cochainDiff F2 X (cup2 X 3 4 u v) =
      cup1m X 3 4 u v + cup1m X 4 3 v u + cup2 X 4 4 (cochainDiff F2 X u) v
        + cup2 X 3 5 u (cochainDiff F2 X v) := by
  have h := cup2Coboundary X 3 4 u v (by omega) (by omega)
  simpa only [show (3:ℕ) + 1 = 4 from rfl, show (4:ℕ) + 1 = 5 from rfl] using h

private lemma cup2Cob43 (X : SSet) (u : Cochain F2 X 4) (v : Cochain F2 X 3) :
    cochainDiff F2 X (cup2 X 4 3 u v) =
      cup1m X 4 3 u v + cup1m X 3 4 v u + cup2 X 5 3 (cochainDiff F2 X u) v
        + cup2 X 4 4 u (cochainDiff F2 X v) := by
  have h := cup2Coboundary X 4 3 u v (by omega) (by omega)
  simpa only [show (4:ℕ) + 1 = 5 from rfl, show (3:ℕ) + 1 = 4 from rfl] using h

/-! ## Leibniz instances -/

private lemma cupLeibniz_11 (X : SSet) (w : Cochain F2 X 1) :
    cochainDiff F2 X (Work.Cohomology.cup F2 X w w) =
      Work.Cohomology.cup F2 X (cochainDiff F2 X w) w + Work.Cohomology.cup F2 X w (cochainDiff F2 X w) := by
  have h := Work.Cohomology.cupLeibniz F2 X w w
  rw [show (-1 : F2) ^ (1 : ℕ) = 1 from by decide, one_smul] at h
  exact h

private lemma cupLeibniz_22 (X : SSet) (w : Cochain F2 X 2) :
    cochainDiff F2 X (Work.Cohomology.cup F2 X w w) =
      Work.Cohomology.cup F2 X (cochainDiff F2 X w) w + Work.Cohomology.cup F2 X w (cochainDiff F2 X w) := by
  have h := Work.Cohomology.cupLeibniz F2 X w w
  rw [show (-1 : F2) ^ (2 : ℕ) = 1 from by decide, one_smul] at h
  exact h

private lemma cupLeibniz_33 (X : SSet) (w : Cochain F2 X 3) :
    cochainDiff F2 X (Work.Cohomology.cup F2 X w w) =
      Work.Cohomology.cup F2 X (cochainDiff F2 X w) w + Work.Cohomology.cup F2 X w (cochainDiff F2 X w) := by
  have h := Work.Cohomology.cupLeibniz F2 X w w
  rw [show (-1 : F2) ^ (3 : ℕ) = 1 from by decide, one_smul] at h
  exact h

/-! ## the four well-definedness statements -/

private lemma sqOps_case1 (X : SSet) (x : Cochain F2 X 2) (hx : cochainDiff F2 X x = 0)
    (w : Cochain F2 X 1) :
    ∃ y : Cochain F2 X 2, cochainDiff F2 X y =
      cup1m X 2 2 x x + cup1m X 2 2 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w) := by
  refine ⟨cup1m X 1 2 w x + cup1m X 2 1 x w + cup1m X 1 2 w (cochainDiff F2 X w)
    + Work.Cohomology.cup F2 X w w, ?_⟩
  simp only [cup1m_add_left, cup1m_add_right]
  simp only [cochainDiff_add]
  rw [cup1Cob12, cup1Cob21, cup1Cob12, cupLeibniz_11]
  simp only [hx, cochainDiff_cochainDiff, cup1m_zero_right, cup1m_zero_left, zero_add,
    add_zero]
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add]
  ring_nf
  simp only [show (2 : F2) = 0 from by decide, mul_zero, zero_mul, zero_add, add_zero]

private lemma sqOps_case2 (X : SSet) (x : Cochain F2 X 3) (hx : cochainDiff F2 X x = 0)
    (w : Cochain F2 X 2) :
    ∃ y : Cochain F2 X 4, cochainDiff F2 X y =
      cup1m X 3 3 x x + cup1m X 3 3 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w) := by
  refine ⟨cup1m X 2 3 w x + cup1m X 3 2 x w + cup1m X 2 3 w (cochainDiff F2 X w)
    + Work.Cohomology.cup F2 X w w, ?_⟩
  simp only [cup1m_add_left, cup1m_add_right]
  simp only [cochainDiff_add]
  rw [cup1Cob23, cup1Cob32, cup1Cob23, cupLeibniz_22]
  simp only [hx, cochainDiff_cochainDiff, cup1m_zero_right, cup1m_zero_left, zero_add,
    add_zero]
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add]
  ring_nf
  simp only [show (2 : F2) = 0 from by decide, mul_zero, zero_mul, zero_add, add_zero]

private lemma sqOps_case3 (X : SSet) (x : Cochain F2 X 3) (hx : cochainDiff F2 X x = 0)
    (w : Cochain F2 X 2) :
    ∃ y : Cochain F2 X 3, cochainDiff F2 X y =
      cup2 X 3 3 x x + cup2 X 3 3 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w) := by
  refine ⟨cup2 X 2 3 w x + cup2 X 3 2 x w + cup2 X 2 3 w (cochainDiff F2 X w)
    + cup1m X 2 2 w w, ?_⟩
  simp only [cup2_add_left, cup2_add_right]
  simp only [cochainDiff_add]
  rw [cup2Cob23, cup2Cob32, cup2Cob23, cup1Cob22]
  simp only [hx, cochainDiff_cochainDiff, cup2_zero_right, cup2_zero_left, zero_add,
    add_zero]
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add]
  ring_nf
  simp only [show (2 : F2) = 0 from by decide, mul_zero, zero_mul, zero_add, add_zero]

private lemma sqOps_case4 (X : SSet) (x : Cochain F2 X 4) (hx : cochainDiff F2 X x = 0)
    (w : Cochain F2 X 3) :
    ∃ y : Cochain F2 X 5, cochainDiff F2 X y =
      cup2 X 4 4 x x + cup2 X 4 4 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w) := by
  refine ⟨cup2 X 3 4 w x + cup2 X 4 3 x w + cup2 X 3 4 w (cochainDiff F2 X w)
    + cup1m X 3 3 w w, ?_⟩
  simp only [cup2_add_left, cup2_add_right]
  simp only [cochainDiff_add]
  rw [cup2Cob34, cup2Cob43, cup2Cob34, cup1Cob33]
  simp only [hx, cochainDiff_cochainDiff, cup2_zero_right, cup2_zero_left, zero_add,
    add_zero]
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [Work.Cohomology.genEval_add]
  ring_nf
  simp only [show (2 : F2) = 0 from by decide, mul_zero, zero_mul, zero_add, add_zero]

/-- The Steenrod-square classes `[x ∪₁ x]` (Sq¹ in degree 2, Sq² in degree 3) and `[x ∪₂ x]` (Sq¹ in degree 3, Sq² in degree 4) depend only on the cohomology class of `x`: replacing a cocycle `x` by `x + δw` changes the product by a coboundary. -/
theorem sqOps : (∀ (X : SSet) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2) (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X x = 0) (w : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 1), ∃ y : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2, Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X y = Work.Pi6.SQ.cup1m X 2 2 x x + Work.Pi6.SQ.cup1m X 2 2 (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w) (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w)) ∧ (∀ (X : SSet) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3) (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X x = 0) (w : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2), ∃ y : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 4, Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X y = Work.Pi6.SQ.cup1m X 3 3 x x + Work.Pi6.SQ.cup1m X 3 3 (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w) (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w)) ∧ (∀ (X : SSet) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3) (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X x = 0) (w : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 2), ∃ y : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3, Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X y = Work.Pi6.SQ.cup2 X 3 3 x x + Work.Pi6.SQ.cup2 X 3 3 (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w) (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w)) ∧ (∀ (X : SSet) (x : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 4) (hx : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X x = 0) (w : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 3), ∃ y : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X 5, Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X y = Work.Pi6.SQ.cup2 X 4 4 x x + Work.Pi6.SQ.cup2 X 4 4 (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w) (x + Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X w)) := by
  exact ⟨sqOps_case1, sqOps_case2, sqOps_case3, sqOps_case4⟩

end

end Work.Pi6.SQ
