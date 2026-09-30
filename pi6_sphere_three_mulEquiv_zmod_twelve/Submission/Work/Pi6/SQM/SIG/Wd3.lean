import Mathlib
import Submission.Work.Pi6.SQM.SIG.ClsAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

open Work.Cohomology (Cochain genEval genEval_ext genEval_add cochainDiff cohomologyClassOf
  cochainDiff_cochainDiff)

/-! ## Bilinearity of the cup-3 and cup-2 products -/

theorem cup3_add_left (X : SSet) (n m : ℕ) (u u' : Cochain F2 X n) (v : Cochain F2 X m) :
    Work.Pi6.SQM.cup3 X n m (u + u') v = Work.Pi6.SQM.cup3 X n m u v
      + Work.Pi6.SQM.cup3 X n m u' v := by
  apply genEval_ext
  intro σ
  simp only [genEval_add, Work.Pi6.SQM.genEval_cup3, Work.Pi6.SQM.cup3Val]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

theorem cup3_add_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v v' : Cochain F2 X m) :
    Work.Pi6.SQM.cup3 X n m u (v + v') = Work.Pi6.SQM.cup3 X n m u v
      + Work.Pi6.SQM.cup3 X n m u v' := by
  apply genEval_ext
  intro σ
  simp only [genEval_add, Work.Pi6.SQM.genEval_cup3, Work.Pi6.SQM.cup3Val]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

theorem cup3_zero_left (X : SSet) (n m : ℕ) (v : Cochain F2 X m) :
    Work.Pi6.SQM.cup3 X n m (0 : Cochain F2 X n) v = 0 := by
  apply genEval_ext
  intro σ
  rw [Work.Pi6.SQM.genEval_cup3]
  simp only [Work.Pi6.SQM.cup3Val, genEval, LinearMap.zero_apply, zero_mul]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  split_ifs <;> rfl

theorem cup3_zero_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQM.cup3 X n m u (0 : Cochain F2 X m) = 0 := by
  apply genEval_ext
  intro σ
  rw [Work.Pi6.SQM.genEval_cup3]
  simp only [Work.Pi6.SQM.cup3Val, genEval, LinearMap.zero_apply, mul_zero]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  split_ifs <;> rfl

theorem cup2_add_left (X : SSet) (n m : ℕ) (u u' : Cochain F2 X n) (v : Cochain F2 X m) :
    Work.Pi6.SQ.cup2 X n m (u + u') v = Work.Pi6.SQ.cup2 X n m u v
      + Work.Pi6.SQ.cup2 X n m u' v := by
  apply genEval_ext
  intro σ
  simp only [genEval_add, Work.Pi6.SQ.genEval_cup2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem cup2_add_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v v' : Cochain F2 X m) :
    Work.Pi6.SQ.cup2 X n m u (v + v') = Work.Pi6.SQ.cup2 X n m u v
      + Work.Pi6.SQ.cup2 X n m u v' := by
  apply genEval_ext
  intro σ
  simp only [genEval_add, Work.Pi6.SQ.genEval_cup2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem cup2_zero_left (X : SSet) (n m : ℕ) (v : Cochain F2 X m) :
    Work.Pi6.SQ.cup2 X n m (0 : Cochain F2 X n) v = 0 := by
  apply genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup2]
  simp only [genEval, LinearMap.zero_apply, zero_mul, Finset.sum_const_zero]

theorem cup2_zero_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQ.cup2 X n m u (0 : Cochain F2 X m) = 0 := by
  apply genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup2]
  simp only [genEval, LinearMap.zero_apply, mul_zero, Finset.sum_const_zero]

/-! ## Cast-free coboundary formulas at the degrees used -/

theorem cup3Cob43 (h3 : Cup3Cob) (X : SSet) (u : Cochain F2 X 4) (v : Cochain F2 X 3) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 4 3 u v) =
      Work.Pi6.SQ.cup2 X 4 3 u v + Work.Pi6.SQ.cup2 X 3 4 v u +
      Work.Pi6.SQM.cup3 X 5 3 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 4 4 u (cochainDiff F2 X v) := by
  have h := h3 X 4 3 u v (by omega) (by omega)
  simpa only [show (4:ℕ) + 1 = 5 from rfl, show (3:ℕ) + 1 = 4 from rfl] using h

theorem cup3Cob34 (h3 : Cup3Cob) (X : SSet) (u : Cochain F2 X 3) (v : Cochain F2 X 4) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 3 4 u v) =
      Work.Pi6.SQ.cup2 X 3 4 u v + Work.Pi6.SQ.cup2 X 4 3 v u +
      Work.Pi6.SQM.cup3 X 4 4 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 3 5 u (cochainDiff F2 X v) := by
  have h := h3 X 3 4 u v (by omega) (by omega)
  simpa only [show (3:ℕ) + 1 = 4 from rfl, show (4:ℕ) + 1 = 5 from rfl] using h

theorem cup3Cob54 (h3 : Cup3Cob) (X : SSet) (u : Cochain F2 X 5) (v : Cochain F2 X 4) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 5 4 u v) =
      Work.Pi6.SQ.cup2 X 5 4 u v + Work.Pi6.SQ.cup2 X 4 5 v u +
      Work.Pi6.SQM.cup3 X 6 4 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 5 5 u (cochainDiff F2 X v) := by
  have h := h3 X 5 4 u v (by omega) (by omega)
  simpa only [show (5:ℕ) + 1 = 6 from rfl, show (4:ℕ) + 1 = 5 from rfl] using h

theorem cup3Cob45 (h3 : Cup3Cob) (X : SSet) (u : Cochain F2 X 4) (v : Cochain F2 X 5) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 4 5 u v) =
      Work.Pi6.SQ.cup2 X 4 5 u v + Work.Pi6.SQ.cup2 X 5 4 v u +
      Work.Pi6.SQM.cup3 X 5 5 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 4 6 u (cochainDiff F2 X v) := by
  have h := h3 X 4 5 u v (by omega) (by omega)
  simpa only [show (4:ℕ) + 1 = 5 from rfl, show (5:ℕ) + 1 = 6 from rfl] using h

theorem cup3Cob44 (h3 : Cup3Cob) (X : SSet) (u v : Cochain F2 X 4) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 4 4 u v) =
      Work.Pi6.SQ.cup2 X 4 4 u v + Work.Pi6.SQ.cup2 X 4 4 v u +
      Work.Pi6.SQM.cup3 X 5 4 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 4 5 u (cochainDiff F2 X v) := by
  have h := h3 X 4 4 u v (by omega) (by omega)
  simpa only [show (4:ℕ) + 1 = 5 from rfl] using h

theorem cup3Cob55 (h3 : Cup3Cob) (X : SSet) (u v : Cochain F2 X 5) :
    cochainDiff F2 X (Work.Pi6.SQM.cup3 X 5 5 u v) =
      Work.Pi6.SQ.cup2 X 5 5 u v + Work.Pi6.SQ.cup2 X 5 5 v u +
      Work.Pi6.SQM.cup3 X 6 5 (cochainDiff F2 X u) v +
      Work.Pi6.SQM.cup3 X 5 6 u (cochainDiff F2 X v) := by
  have h := h3 X 5 5 u v (by omega) (by omega)
  simpa only [show (5:ℕ) + 1 = 6 from rfl] using h

theorem cup2Cob33 (h2 : Cup2Cob) (X : SSet) (u v : Cochain F2 X 3) :
    cochainDiff F2 X (Work.Pi6.SQ.cup2 X 3 3 u v) =
      Work.Pi6.SQ.cup1m X 3 3 u v + Work.Pi6.SQ.cup1m X 3 3 v u +
      Work.Pi6.SQ.cup2 X 4 3 (cochainDiff F2 X u) v +
      Work.Pi6.SQ.cup2 X 3 4 u (cochainDiff F2 X v) := by
  have h := h2 X 3 3 u v (by omega) (by omega)
  simpa only [show (3:ℕ) + 1 = 4 from rfl] using h

theorem cup2Cob44 (h2 : Cup2Cob) (X : SSet) (u v : Cochain F2 X 4) :
    cochainDiff F2 X (Work.Pi6.SQ.cup2 X 4 4 u v) =
      Work.Pi6.SQ.cup1m X 4 4 u v + Work.Pi6.SQ.cup1m X 4 4 v u +
      Work.Pi6.SQ.cup2 X 5 4 (cochainDiff F2 X u) v +
      Work.Pi6.SQ.cup2 X 4 5 u (cochainDiff F2 X v) := by
  have h := h2 X 4 4 u v (by omega) (by omega)
  simpa only [show (4:ℕ) + 1 = 5 from rfl] using h

/-! ## Well-definedness of the `∪₃`-square -/

theorem cup3Wd4 (h2 : Cup2Cob) (h3 : Cup3Cob) (X : SSet) (x : Cochain F2 X 4)
    (hx : cochainDiff F2 X x = 0) (w : Cochain F2 X 3) :
    ∃ y : Cochain F2 X 4, cochainDiff F2 X y = Work.Pi6.SQM.cup3 X 4 4 x x +
      Work.Pi6.SQM.cup3 X 4 4 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w) := by
  refine ⟨Work.Pi6.SQM.cup3 X 4 3 x w + Work.Pi6.SQM.cup3 X 3 4 w x
    + Work.Pi6.SQM.cup3 X 4 3 (cochainDiff F2 X w) w + Work.Pi6.SQ.cup2 X 3 3 w w, ?_⟩
  simp only [cup3_add_left, cup3_add_right]
  simp only [cochainDiff_add]
  rw [cup3Cob43 h3, cup3Cob34 h3, cup3Cob43 h3, cup2Cob33 h2]
  simp only [hx, cochainDiff_cochainDiff, cup3_zero_left, cup3_zero_right, cup2_zero_left,
    cup2_zero_right, zero_add, add_zero]
  apply genEval_ext
  intro σ
  simp only [genEval_add]
  ring_nf
  simp only [show (2 : F2) = 0 from by decide, mul_zero, zero_mul, zero_add, add_zero]

theorem cup3Wd5 (h2 : Cup2Cob) (h3 : Cup3Cob) (X : SSet) (x : Cochain F2 X 5)
    (hx : cochainDiff F2 X x = 0) (w : Cochain F2 X 4) :
    ∃ y : Cochain F2 X 6, cochainDiff F2 X y = Work.Pi6.SQM.cup3 X 5 5 x x +
      Work.Pi6.SQM.cup3 X 5 5 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w) := by
  refine ⟨Work.Pi6.SQM.cup3 X 5 4 x w + Work.Pi6.SQM.cup3 X 4 5 w x
    + Work.Pi6.SQM.cup3 X 5 4 (cochainDiff F2 X w) w + Work.Pi6.SQ.cup2 X 4 4 w w, ?_⟩
  simp only [cup3_add_left, cup3_add_right]
  simp only [cochainDiff_add]
  rw [cup3Cob54 h3, cup3Cob45 h3, cup3Cob54 h3, cup2Cob44 h2]
  simp only [hx, cochainDiff_cochainDiff, cup3_zero_left, cup3_zero_right, cup2_zero_left,
    cup2_zero_right, zero_add, add_zero]
  apply genEval_ext
  intro σ
  simp only [genEval_add]
  ring_nf
  simp only [show (2 : F2) = 0 from by decide, mul_zero, zero_mul, zero_add, add_zero]

/-! ## The `∪₃`-square depends only on the class -/

theorem cls_cup3_eq_4 (h2 : Cup2Cob) (h3 : Cup3Cob) {X : SSet} (u v : Cochain F2 X 4)
    (hu : cochainDiff F2 X u = 0) (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Pi6.SQM.cup3 X 4 4 u u) = 0)
    (hvv : cochainDiff F2 X (Work.Pi6.SQM.cup3 X 4 4 v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Pi6.SQM.cup3 X 4 4 u u) huu =
      cohomologyClassOf F2 X (Work.Pi6.SQM.cup3 X 4 4 v v) hvv := by
  obtain ⟨w, hw⟩ := exists_coboundary_of_class_eq u v hu hv h
  obtain ⟨y, hy⟩ := cup3Wd4 h2 h3 X u hu w
  have hvw : v = u + cochainDiff F2 X w := by
    rw [hw]
    calc v = (u + u) + v := by rw [add_self_eq_zero_f2 u, zero_add]
      _ = u + (u + v) := by abel
  subst v
  exact cls_eq_of_add_coboundary _ _ huu hvv y hy

theorem cls_cup3_eq_5 (h2 : Cup2Cob) (h3 : Cup3Cob) {X : SSet} (u v : Cochain F2 X 5)
    (hu : cochainDiff F2 X u = 0) (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Pi6.SQM.cup3 X 5 5 u u) = 0)
    (hvv : cochainDiff F2 X (Work.Pi6.SQM.cup3 X 5 5 v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Pi6.SQM.cup3 X 5 5 u u) huu =
      cohomologyClassOf F2 X (Work.Pi6.SQM.cup3 X 5 5 v v) hvv := by
  obtain ⟨w, hw⟩ := exists_coboundary_of_class_eq u v hu hv h
  obtain ⟨y, hy⟩ := cup3Wd5 h2 h3 X u hu w
  have hvw : v = u + cochainDiff F2 X w := by
    rw [hw]
    calc v = (u + u) + v := by rw [add_self_eq_zero_f2 u, zero_add]
      _ = u + (u + v) := by abel
  subst v
  exact cls_eq_of_add_coboundary _ _ huu hvv y hy

end

end Work.Pi6.SQM.SIG
