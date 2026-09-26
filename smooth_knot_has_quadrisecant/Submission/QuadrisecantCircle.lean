import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap

open LeanEval.KnotTheory.Quadrisecant

/-!
# The quadrisecant statement on the parameter circle

`HasQuadrisecant r` asks for four distinct parameters inside one period with
collinear images.  Since the knot factors through the parameter circle
(`KnotMap.lean`), this is *equivalent* to asking for four distinct points of
the circle `AddCircle period` whose `knotMap` images are collinear.  This
module proves that equivalence

    hasQuadrisecant_iff_circle (h : IsSmoothKnot r) :
        HasQuadrisecant r ↔ CircleQuadrisecant r

The circle form is the natural one for the secant/trisecant geometry of
Kuperberg's proof (chords are parametrized by pairs of points of the circle
of parameters), while `HasQuadrisecant` is the trusted statement of the
challenge.  The bridge will be used at the very end of the assembly to
transfer the double point of the trisecant locus back to the four-parameter
statement.
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- Four pairwise distinct elements. -/
def QuadDistinct {α : Type*} (x0 x1 x2 x3 : α) : Prop :=
  x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3

/-- Pairwise distinct real parameters are a `List.Nodup` list. -/
lemma nodup_of_QuadDistinct {α : Type*} [DecidableEq α] (x0 x1 x2 x3 : α)
    (h : QuadDistinct x0 x1 x2 x3) : [x0, x1, x2, x3].Nodup := by
  rcases h with ⟨h01, h02, h03, h12, h13, h23⟩
  rw [List.nodup_cons]
  constructor
  · simp [List.mem_cons, h01, h02, h03]
  · rw [List.nodup_cons]
    constructor
    · simp [List.mem_cons, h12, h13]
    · rw [List.nodup_cons]
      constructor
      · simp [h23]
      · simp

/-- A `List.Nodup` list of four parameters gives pairwise distinct elements. -/
lemma QuadDistinct_of_nodup {α : Type*} [DecidableEq α] (x0 x1 x2 x3 : α)
    (h : [x0, x1, x2, x3].Nodup) : QuadDistinct x0 x1 x2 x3 := by
  rw [List.nodup_cons] at h
  rcases h with ⟨h0, h123⟩
  rw [List.nodup_cons] at h123
  rcases h123 with ⟨h1, h23⟩
  rw [List.nodup_cons] at h23
  rcases h23 with ⟨h2, h3⟩
  simp [List.mem_cons] at h0 h1
  rcases h0 with ⟨h01, h02, h03⟩
  rcases h1 with ⟨h12, h13⟩
  simp [List.mem_cons] at h2
  exact ⟨h01, h02, h03, h12, h13, h2⟩

/-- The quotient map `ℝ → AddCircle period` is injective on the half-open
period. -/
lemma coe_injective_on_Ico : Set.InjOn (fun t : ℝ => (t : AddCircle period))
    (Set.Ico 0 period) := by
  intro x hx y hy h
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := period) (a := 0) (x := x) (y := y)
    (by simpa [zero_add] using hx) (by simpa [zero_add] using hy)).mp h

/-- Two representatives in the half-open period are equal as circle points iff
they are equal as reals. -/
lemma coe_eq_coe_iff_of_mem_period_Ico {t s : ℝ}
    (ht : t ∈ Set.Ico 0 period) (hs : s ∈ Set.Ico 0 period) :
    ((t : AddCircle period) = s) ↔ t = s := by
  simpa [zero_add] using
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := period) (a := 0) (x := t) (y := s)
      (by simpa [zero_add] using ht) (by simpa [zero_add] using hs))

/-- Two representatives in the half-open period are distinct as circle points
iff they are distinct as reals. -/
lemma coe_ne_coe_iff_of_mem_period_Ico {t s : ℝ}
    (ht : t ∈ Set.Ico 0 period) (hs : s ∈ Set.Ico 0 period) :
    ((t : AddCircle period) ≠ s) ↔ t ≠ s :=
  not_congr (coe_eq_coe_iff_of_mem_period_Ico ht hs)

/-- Distinct parameters in one period give distinct points of the circle. -/
lemma QuadDistinct_coe_of_QuadDistinct {t0 t1 t2 t3 : ℝ}
    (ht0 : t0 ∈ Set.Ico 0 period) (ht1 : t1 ∈ Set.Ico 0 period)
    (ht2 : t2 ∈ Set.Ico 0 period) (ht3 : t3 ∈ Set.Ico 0 period)
    (hd : QuadDistinct t0 t1 t2 t3) :
    QuadDistinct (t0 : AddCircle period) (t1 : AddCircle period)
      (t2 : AddCircle period) (t3 : AddCircle period) := by
  simpa [QuadDistinct, coe_ne_coe_iff_of_mem_period_Ico ht0 ht1,
    coe_ne_coe_iff_of_mem_period_Ico ht0 ht2, coe_ne_coe_iff_of_mem_period_Ico ht0 ht3,
    coe_ne_coe_iff_of_mem_period_Ico ht1 ht2, coe_ne_coe_iff_of_mem_period_Ico ht1 ht3,
    coe_ne_coe_iff_of_mem_period_Ico ht2 ht3] using hd

/-- Distinct points of the circle have distinct representatives in the
half-open period. -/
lemma QuadDistinct_of_QuadDistinct_coe {t0 t1 t2 t3 : ℝ}
    (ht0 : t0 ∈ Set.Ico 0 period) (ht1 : t1 ∈ Set.Ico 0 period)
    (ht2 : t2 ∈ Set.Ico 0 period) (ht3 : t3 ∈ Set.Ico 0 period)
    (hd : QuadDistinct (t0 : AddCircle period) (t1 : AddCircle period)
      (t2 : AddCircle period) (t3 : AddCircle period)) :
    QuadDistinct t0 t1 t2 t3 := by
  simpa [QuadDistinct, coe_ne_coe_iff_of_mem_period_Ico ht0 ht1,
    coe_ne_coe_iff_of_mem_period_Ico ht0 ht2, coe_ne_coe_iff_of_mem_period_Ico ht0 ht3,
    coe_ne_coe_iff_of_mem_period_Ico ht1 ht2, coe_ne_coe_iff_of_mem_period_Ico ht1 ht3,
    coe_ne_coe_iff_of_mem_period_Ico ht2 ht3] using hd

/-- Four collinear image points of the knot, expressed on the circle. -/
def CircleQuadrisecant (r : ℝ → Space) : Prop :=
  ∃ (x0 x1 x2 x3 : AddCircle period) (p v : Space) (a0 a1 a2 a3 : ℝ),
    QuadDistinct x0 x1 x2 x3 ∧ v ≠ 0 ∧
      knotMap r x0 = p + a0 • v ∧ knotMap r x1 = p + a1 • v ∧
      knotMap r x2 = p + a2 • v ∧ knotMap r x3 = p + a3 • v

/-- A quadrisecant in the trusted (parameter) sense is one in the circle
sense. -/
lemma hasQuadrisecant_imp_circle {r : ℝ → Space} (_h : IsSmoothKnot r)
    (hq : HasQuadrisecant r) : CircleQuadrisecant r := by
  rcases hq with ⟨t0, t1, t2, t3, p, v, a0, a1, a2, a3,
    ht0, ht1, ht2, ht3, hnod, hv, hi0, hi1, hi2, hi3⟩
  have hd : QuadDistinct t0 t1 t2 t3 := QuadDistinct_of_nodup t0 t1 t2 t3 hnod
  refine ⟨(t0 : AddCircle period), (t1 : AddCircle period),
    (t2 : AddCircle period), (t3 : AddCircle period), p, v, a0, a1, a2, a3,
    QuadDistinct_coe_of_QuadDistinct ht0 ht1 ht2 ht3 hd, hv, ?_, ?_, ?_, ?_⟩
  · simpa [knotMap_coe r ht0] using hi0
  · simpa [knotMap_coe r ht1] using hi1
  · simpa [knotMap_coe r ht2] using hi2
  · simpa [knotMap_coe r ht3] using hi3

/-- A quadrisecant in the circle sense is one in the trusted (parameter)
sense. -/
lemma circle_imp_hasQuadrisecant {r : ℝ → Space} (_h : IsSmoothKnot r)
    (hq : CircleQuadrisecant r) : HasQuadrisecant r := by
  rcases hq with ⟨x0, x1, x2, x3, p, v, a0, a1, a2, a3, hd, hv,
    hi0, hi1, hi2, hi3⟩
  rcases knotMap_representative x0 with ⟨t0, ht0, hx0⟩
  rcases knotMap_representative x1 with ⟨t1, ht1, hx1⟩
  rcases knotMap_representative x2 with ⟨t2, ht2, hx2⟩
  rcases knotMap_representative x3 with ⟨t3, ht3, hx3⟩
  have hc : QuadDistinct (t0 : AddCircle period) (t1 : AddCircle period)
      (t2 : AddCircle period) (t3 : AddCircle period) := by
    simpa [← hx0, ← hx1, ← hx2, ← hx3] using hd
  have hd0 : QuadDistinct t0 t1 t2 t3 :=
    QuadDistinct_of_QuadDistinct_coe ht0 ht1 ht2 ht3 hc
  refine ⟨t0, t1, t2, t3, p, v, a0, a1, a2, a3, ht0, ht1, ht2, ht3,
    nodup_of_QuadDistinct t0 t1 t2 t3 hd0, hv, ?_, ?_, ?_, ?_⟩
  · rw [← knotMap_coe r ht0, hx0]; exact hi0
  · rw [← knotMap_coe r ht1, hx1]; exact hi1
  · rw [← knotMap_coe r ht2, hx2]; exact hi2
  · rw [← knotMap_coe r ht3, hx3]; exact hi3

/-- `HasQuadrisecant r` (four distinct parameters in one period with
collinear images) is equivalent to its parameter-circle form. -/
lemma hasQuadrisecant_iff_circle {r : ℝ → Space} (h : IsSmoothKnot r) :
    HasQuadrisecant r ↔ CircleQuadrisecant r :=
  ⟨hasQuadrisecant_imp_circle h, circle_imp_hasQuadrisecant h⟩

end LeanEval.KnotTheory.Quadrisecant
