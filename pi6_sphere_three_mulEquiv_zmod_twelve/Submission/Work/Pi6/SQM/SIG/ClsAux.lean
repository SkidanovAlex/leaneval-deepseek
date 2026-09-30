import Mathlib
import Submission.Work.Pi6.SQM.SIG.Apply
import Submission.Work.Pi6.SQ.Bridge
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf cocycleOf
  SSetCochainComplex cochainDiffLM cochainDiffLM_apply iCycles_cocycleOf SSetCochainComplex_d
  homologyπ_eq_zero_of_d cupH'_apply cohomologyClassOf_congr cochainDiff_cochainDiff)

/-! ## Elementary algebra over `𝔽₂` -/

/-- In a module over `𝔽₂`, every element is its own additive inverse. -/
theorem add_self_eq_zero_f2 {M : Type} [AddCommGroup M] [Module F2 M] (a : M) : a + a = 0 := by
  have h2 : (2 : F2) = 0 := by decide
  have h : (2 : F2) • a = 0 := by rw [h2, zero_smul]
  simpa [two_smul] using h

/-- The coboundary is additive. -/
theorem cochainDiff_add {R : Type} [CommRing R] {X : SSet} {n : ℕ} (a b : Cochain R X n) :
    cochainDiff R X (a + b) = cochainDiff R X a + cochainDiff R X b := by
  have h := map_add (cochainDiffLM R X n) a b
  simpa only [cochainDiffLM_apply] using h

/-! ## Classes, coboundaries -/

/-- Adding a coboundary to a cocycle does not change the cohomology class. -/
theorem cls_add_coboundary {X : SSet} {n : ℕ} (β : Cochain F2 X (n + 1)) (v : Cochain F2 X n)
    (hβ : cochainDiff F2 X β = 0) (h : cochainDiff F2 X (β + cochainDiff F2 X v) = 0) :
    cohomologyClassOf F2 X (β + cochainDiff F2 X v) h = cohomologyClassOf F2 X β hβ := by
  have hz : ((SSetCochainComplex F2 X).iCycles (n + 1))
      (cocycleOf F2 X (β + cochainDiff F2 X v) h - cocycleOf F2 X β hβ)
      = ((SSetCochainComplex F2 X).d n (n + 1)).hom v := by
    rw [map_sub, iCycles_cocycleOf, iCycles_cocycleOf]
    simp only [SSetCochainComplex_d, cochainDiffLM_apply]
    abel
  have h0 := homologyπ_eq_zero_of_d F2 X (n + 1) n
    (cocycleOf F2 X (β + cochainDiff F2 X v) h - cocycleOf F2 X β hβ) v hz
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- Two cocycles whose sum is a coboundary have the same class. -/
theorem cls_eq_of_add_coboundary {X : SSet} {n : ℕ} (a b : Cochain F2 X (n + 1))
    (ha : cochainDiff F2 X a = 0) (hb : cochainDiff F2 X b = 0) (v : Cochain F2 X n)
    (hv : cochainDiff F2 X v = a + b) :
    cohomologyClassOf F2 X a ha = cohomologyClassOf F2 X b hb := by
  have hh : cochainDiff F2 X (b + cochainDiff F2 X v) = 0 := by
    rw [cochainDiff_add, hb, cochainDiff_cochainDiff, zero_add]
  have h1 := cls_add_coboundary b v hb hh
  have h2 : b + cochainDiff F2 X v = a := by
    rw [hv]
    calc b + (a + b) = a + (b + b) := by abel
      _ = a := by rw [add_self_eq_zero_f2 b, add_zero]
  subst h2
  exact h1

/-- Two cohomologous cocycles differ by a coboundary. -/
theorem exists_coboundary_of_class_eq {X : SSet} {n : ℕ} (a b : Cochain F2 X (n + 1))
    (ha : cochainDiff F2 X a = 0) (hb : cochainDiff F2 X b = 0)
    (h : cohomologyClassOf F2 X a ha = cohomologyClassOf F2 X b hb) :
    ∃ v : Cochain F2 X n, cochainDiff F2 X v = a + b := by
  obtain ⟨v, hv⟩ := Work.Cohomology.pd_us_cycles_eq_of_class_eq (K := SSetCochainComplex F2 X)
    (n := n) (cocycleOf F2 X a ha) (cocycleOf F2 X b hb) h
  refine ⟨(v : Cochain F2 X n), ?_⟩
  have h1 : (ModuleCat.Hom.hom ((SSetCochainComplex F2 X).d n (n + 1))) v =
      cochainDiff F2 X (v : Cochain F2 X n) := by
    rw [SSetCochainComplex_d]
    rfl
  have h2 : (ModuleCat.Hom.hom ((SSetCochainComplex F2 X).d n (n + 1))) v =
      (a : Cochain F2 X (n + 1)) - (b : Cochain F2 X (n + 1)) := by
    rw [hv, iCycles_cocycleOf, iCycles_cocycleOf]
  have h3 : (a : Cochain F2 X (n + 1)) - (b : Cochain F2 X (n + 1)) = a + b := by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (add_self_eq_zero_f2 b)]
  rw [← h1, h2, h3]

/-! ## The cup square depends only on the class -/

/-- Over `𝔽₂` the class of the cup square of a cocycle depends only on the class. -/
theorem cls_cup_eq {X : SSet} {n : ℕ} (u v : Cochain F2 X (n + 1))
    (hu : cochainDiff F2 X u = 0) (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Cohomology.cup F2 X u u) = 0)
    (hvv : cochainDiff F2 X (Work.Cohomology.cup F2 X v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Cohomology.cup F2 X u u) huu =
      cohomologyClassOf F2 X (Work.Cohomology.cup F2 X v v) hvv := by
  have h1 : cohomologyClassOf F2 X (Work.Cohomology.cup F2 X u u) huu =
      cupH' F2 X (n + 1) (n + 1) (cohomologyClassOf F2 X u hu) (cohomologyClassOf F2 X u hu) :=
    (cupH'_apply F2 X u u hu hu huu).symm
  have h2 : cohomologyClassOf F2 X (Work.Cohomology.cup F2 X v v) hvv =
      cupH' F2 X (n + 1) (n + 1) (cohomologyClassOf F2 X v hv) (cohomologyClassOf F2 X v hv) :=
    (cupH'_apply F2 X v v hv hv hvv).symm
  rw [h1, h2, h]

/-! ## Naturality of the products under pullback -/

theorem pb_cup1m (hN : Work.Pi6.SQM.CupINatural) {X Y : SSet} (f : X ⟶ Y) (n m : ℕ)
    (u : Cochain F2 Y n) (v : Cochain F2 Y m) :
    pb f (Work.Pi6.SQ.cup1m Y n m u v) = Work.Pi6.SQ.cup1m X n m (pb f u) (pb f v) :=
  (hN X Y f n m u v).1.symm

theorem pb_cup2 (hN : Work.Pi6.SQM.CupINatural) {X Y : SSet} (f : X ⟶ Y) (n m : ℕ)
    (u : Cochain F2 Y n) (v : Cochain F2 Y m) :
    pb f (Work.Pi6.SQ.cup2 Y n m u v) = Work.Pi6.SQ.cup2 X n m (pb f u) (pb f v) :=
  (hN X Y f n m u v).2.1.symm

theorem pb_cup3 (hN : Work.Pi6.SQM.CupINatural) {X Y : SSet} (f : X ⟶ Y) (n m : ℕ)
    (u : Cochain F2 Y n) (v : Cochain F2 Y m) :
    pb f (Work.Pi6.SQM.cup3 Y n m u v) = Work.Pi6.SQM.cup3 X n m (pb f u) (pb f v) :=
  (hN X Y f n m u v).2.2.symm

theorem pb_cup {X Y : SSet} (f : X ⟶ Y) (n m : ℕ)
    (u : Cochain F2 Y n) (v : Cochain F2 Y m) :
    pb f (Work.Cohomology.cup F2 Y u v) = Work.Cohomology.cup F2 X (pb f u) (pb f v) :=
  (Work.Cohomology.cupNatural F2 f u v).symm

/-! ## Restriction versus pullback along the inclusion -/

/-- The library's `cup1` vanishes with a zero left argument. -/
theorem cup1_zero_left (X : SSet) (n m : ℕ) (v : Cochain F2 X m) :
    Work.Cohomology.cup1 F2 X n m (0 : Cochain F2 X n) v = 0 := by
  apply genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  simp [Work.Cohomology.genEval]

/-- A cast of `0` along an equality of degrees. -/
theorem cast_zero_cochain {X : SSet} {p q : ℕ} (h : p = q) :
    h ▸ (0 : Cochain F2 X p) = (0 : Cochain F2 X q) := by cases h; rfl

/-- `cup1m` vanishes with a zero right argument. -/
theorem cup1m_zero_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQ.cup1m X n m u (0 : Cochain F2 X m) = 0 := by
  rw [Work.Pi6.SQ.cup1m, cup1_zero_left, cast_zero_cochain]

/-- The pullback along a map of simplicial sets is additive. -/
theorem pb_add {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (u v : Cochain F2 Y n) :
    pb f (u + v) = pb f u + pb f v := by
  unfold pb
  exact map_add _ u v

/-- The restriction of cochains to a subspace is the pullback along the inclusion. -/
theorem restr_eq_pb {X : TopCat} (A : Set X) {n : ℕ} (u : Cochain F2 (SX X) n) :
    ((restr F2 X A).f n).hom u = pb (TopCat.toSSet.map (subtypeIncl X A)) u := by
  rw [restr, Work.Cohomology.dualChainMap_f_hom, Work.Cohomology.chainMap_f_eq]
  rfl

theorem relKern_restr_eq_zero {X : TopCat} {A : Set X} {n : ℕ} (u : relKern F2 X A n) :
    pb (TopCat.toSSet.map (subtypeIncl X A)) u.1 = 0 := by
  rw [← restr_eq_pb A u.1]
  exact u.2

/-- The pullback of a relative cochain to the path space, restricted to the loop space, is zero. -/
theorem pb_loop_ev_relKern {K : Type} [TopologicalSpace K] (k₀ : K) {n : ℕ}
    (ã : relKern F2 (TopCat.of K) ({k₀} : Set K) n) :
    pb (loopSSet K k₀) (pb (evSSet K k₀) ã.1) = 0 := by
  rw [← pbComp (loopSSet K k₀) (evSSet K k₀) n ã.1, comp_loop_ev, constSSet, pbComp,
    relKern_restr_eq_zero ã, pb_zero]

/-! ## The relative cocycle square operations depend only on the class -/

/-- `[x ∪₁ x]` at degree 3 depends only on the class of `x`. -/
theorem cls_cup1m_eq_3 {X : SSet} (u v : Cochain F2 X 3) (hu : cochainDiff F2 X u = 0)
    (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 3 3 u u) = 0)
    (hvv : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 3 3 v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Pi6.SQ.cup1m X 3 3 u u) huu =
      cohomologyClassOf F2 X (Work.Pi6.SQ.cup1m X 3 3 v v) hvv := by
  obtain ⟨w, hw⟩ := exists_coboundary_of_class_eq u v hu hv h
  obtain ⟨y, hy⟩ := Work.Pi6.SQ.sqOpsProp.2.1 X u hu w
  have hvw : v = u + cochainDiff F2 X w := by
    rw [hw]
    calc v = (u + u) + v := by rw [add_self_eq_zero_f2 u, zero_add]
      _ = u + (u + v) := by abel
  subst v
  exact cls_eq_of_add_coboundary _ _ huu hvv y hy

/-- `[x ∪₁ x]` at degree 2 depends only on the class of `x`. -/
theorem cls_cup1m_eq_2 {X : SSet} (u v : Cochain F2 X 2) (hu : cochainDiff F2 X u = 0)
    (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 2 2 u u) = 0)
    (hvv : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 2 2 v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Pi6.SQ.cup1m X 2 2 u u) huu =
      cohomologyClassOf F2 X (Work.Pi6.SQ.cup1m X 2 2 v v) hvv := by
  obtain ⟨w, hw⟩ := exists_coboundary_of_class_eq u v hu hv h
  obtain ⟨y, hy⟩ := Work.Pi6.SQ.sqOpsProp.1 X u hu w
  have hvw : v = u + cochainDiff F2 X w := by
    rw [hw]
    calc v = (u + u) + v := by rw [add_self_eq_zero_f2 u, zero_add]
      _ = u + (u + v) := by abel
  subst v
  exact cls_eq_of_add_coboundary _ _ huu hvv y hy

/-- `[x ∪₂ x]` at degree 3 depends only on the class of `x`. -/
theorem cls_cup2_eq_3 {X : SSet} (u v : Cochain F2 X 3) (hu : cochainDiff F2 X u = 0)
    (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 3 3 u u) = 0)
    (hvv : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 3 3 v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Pi6.SQ.cup2 X 3 3 u u) huu =
      cohomologyClassOf F2 X (Work.Pi6.SQ.cup2 X 3 3 v v) hvv := by
  obtain ⟨w, hw⟩ := exists_coboundary_of_class_eq u v hu hv h
  obtain ⟨y, hy⟩ := Work.Pi6.SQ.sqOpsProp.2.2.1 X u hu w
  have hvw : v = u + cochainDiff F2 X w := by
    rw [hw]
    calc v = (u + u) + v := by rw [add_self_eq_zero_f2 u, zero_add]
      _ = u + (u + v) := by abel
  subst v
  exact cls_eq_of_add_coboundary _ _ huu hvv y hy

/-- `[x ∪₂ x]` at degree 4 depends only on the class of `x`. -/
theorem cls_cup2_eq_4 {X : SSet} (u v : Cochain F2 X 4) (hu : cochainDiff F2 X u = 0)
    (hv : cochainDiff F2 X v = 0)
    (huu : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 4 4 u u) = 0)
    (hvv : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 4 4 v v) = 0)
    (h : cohomologyClassOf F2 X u hu = cohomologyClassOf F2 X v hv) :
    cohomologyClassOf F2 X (Work.Pi6.SQ.cup2 X 4 4 u u) huu =
      cohomologyClassOf F2 X (Work.Pi6.SQ.cup2 X 4 4 v v) hvv := by
  obtain ⟨w, hw⟩ := exists_coboundary_of_class_eq u v hu hv h
  obtain ⟨y, hy⟩ := Work.Pi6.SQ.sqOpsProp.2.2.2 X u hu w
  have hvw : v = u + cochainDiff F2 X w := by
    rw [hw]
    calc v = (u + u) + v := by rw [add_self_eq_zero_f2 u, zero_add]
      _ = u + (u + v) := by abel
  subst v
  exact cls_eq_of_add_coboundary _ _ huu hvv y hy

end

end Work.Pi6.SQM.SIG
