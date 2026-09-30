import Mathlib
import Submission.Work.EMFG.torusDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# The four `circlePatch`es are a good cover of the circle

`Work.EMFG.circlePatch j` is the open piece `{x ∈ S¹ | 0 < ⟪x, circleVec j⟫}` of the circle,
where `circleVec 0, 1, 2, 3 = ±e₀, ±e₁`.  This file proves that the family
`circlePatch : Fin 4 → Set (Sph 1)` is a *good family* in the sense of
`Work.ThomBordism.IsGoodFam` (every member is open and every nonempty finite intersection is
contractible) and that the four pieces cover the circle.

## The geometry

Writing `x = (a, b) : ℝ²` for a point of `S¹`, the four pieces are the four (open) semicircles
`a > 0`, `a < 0`, `b > 0`, `b < 0`; the union is everything since `a² + b² = 1` forces `a` or `b`
to be nonzero.  A finite intersection is `{x ∈ S¹ | x ∈ C}` where
`C = ⋂_{i} {y | 0 < ⟪y, circleVec (f i)⟫}` is an intersection of open half-planes through the
origin.  Such a `C` is a convex cone with `0 ∉ C`, and `C ∩ S¹` is a deformation retract of `C`
(radial projection `y ↦ ‖y‖⁻¹ • y`); since `C` is convex and nonempty it is contractible, so
`C ∩ S¹` is contractible.

## Main results

* `Work.EMFG.halfSpace` — the open half-plane `{y : ℝ² | 0 < ⟪y, circleVec j⟫}`;
* `Work.EMFG.contractibleSpace_of_retract` — a retract of a contractible space is contractible;
* `Work.EMFG.contractibleSpace_convexCone_inter_sphere` — `C ∩ S¹` is contractible for a convex
  cone `C` not containing the origin;
* `Work.EMFG.circlePatch_isGoodFam` — the target statement.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.EMFG

noncomputable section

/-- The open half-plane `{y : ℝ² | 0 < ⟪y, circleVec j⟫}` cut out by the `j`-th vector. -/
def halfSpace (j : Fin 4) : Set Plane := {y | 0 < inner ℝ y (circleVec j)}

@[simp] theorem mem_halfSpace {j : Fin 4} {y : Plane} :
    y ∈ halfSpace j ↔ 0 < inner ℝ y (circleVec j) := Iff.rfl

/-! ## A general fact: a retract of a contractible space is contractible -/

/-- If `A` is a retract of a contractible space `B` (a continuous `i : A → B` admitting a
continuous retraction `r : B → A` with `r ∘ i = id`), then `A` is contractible. -/
theorem contractibleSpace_of_retract {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [ContractibleSpace B] (i : C(A, B)) (r : C(B, A)) (h : r.comp i = ContinuousMap.id A) :
    ContractibleSpace A := by
  rw [contractible_iff_id_nullhomotopic]
  have hi : i.Nullhomotopic := by
    have h1 := (id_nullhomotopic B).comp_left i
    simpa using h1
  have h2 := hi.comp_right r
  rwa [h] at h2

/-! ## Intersecting a convex cone with the circle -/

/-- **The circle cut out by a convex cone is contractible.**  If `C ⊆ ℝ²` is convex, closed under
positive scaling (`hcone`) and does not contain the origin, and `C` is nonempty, then
`C ∩ S¹` is contractible: `C` is a nonempty convex set, hence contractible, and `C ∩ S¹` is a
retract of it via radial projection `y ↦ ‖y‖⁻¹ • y` (which lands back in `C` because `C` is a
cone, and fixes the points of the circle). -/
theorem contractibleSpace_convexCone_inter_sphere {C : Set Plane}
    (hC : Convex ℝ C) (hcone : ∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C)
    (h0 : (0 : Plane) ∉ C) (hne : C.Nonempty) :
    ContractibleSpace ↥{x : Work.Serre.Sph 1 | (x : Plane) ∈ C} := by
  haveI : ContractibleSpace ↥C := hC.contractibleSpace hne
  set A : Set (Work.Serre.Sph 1) := {x | (x : Plane) ∈ C} with hA
  have hne0 : ∀ y : ↥C, (y.1 : Plane) ≠ 0 := by
    intro y h
    exact h0 (h ▸ y.2)
  have hpos : ∀ y : ↥C, 0 < ‖(y.1 : Plane)‖ := fun y => norm_pos_iff.mpr (hne0 y)
  -- the inclusion `A ↪ C`
  let i : C(↥A, ↥C) :=
    ⟨fun x => ⟨(x.1 : Plane), x.2⟩,
     Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)⟩
  -- radial projection `C → A`
  let r : C(↥C, ↥A) :=
    ⟨fun y => ⟨⟨(‖(y.1 : Plane)‖)⁻¹ • (y.1 : Plane), by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
            abs_of_pos (hpos y), inv_mul_cancel₀ (ne_of_gt (hpos y))]⟩,
      hcone y.1 y.2 _ (inv_pos.mpr (hpos y))⟩,
     by
       have hg : Continuous fun y : ↥C => ‖(y.1 : Plane)‖ :=
         continuous_norm.comp continuous_subtype_val
       have hinv : Continuous fun y : ↥C => (‖(y.1 : Plane)‖)⁻¹ :=
         hg.inv₀ (fun y => ne_of_gt (hpos y))
       exact Continuous.subtype_mk (Continuous.subtype_mk (hinv.smul continuous_subtype_val) _) _⟩
  refine contractibleSpace_of_retract i r ?_
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  show (‖((x : ↥A).1 : Plane)‖)⁻¹ • ((x : ↥A).1 : Plane) = ((x : ↥A).1 : Plane)
  have hx : ‖((x : ↥A).1 : Plane)‖ = 1 := by
    have h := (x : ↥A).1.2
    rwa [Metric.mem_sphere, dist_zero_right] at h
  rw [hx]
  simp

/-! ## The half-planes `halfSpace j` -/

theorem isOpen_halfSpace (j : Fin 4) : IsOpen (halfSpace j) := by
  have hc : Continuous fun y : Plane => inner ℝ y (circleVec j) := by fun_prop
  exact isOpen_lt continuous_const hc

theorem isOpen_circlePatch (j : Fin 4) : IsOpen (circlePatch j) :=
  (isOpen_halfSpace j).preimage continuous_subtype_val

/-- An intersection of the half-planes `halfSpace (f i)` is convex. -/
theorem convex_iInter_halfSpace {β : Type*} (f : β → Fin 4) :
    Convex ℝ (⋂ i, halfSpace (f i)) := by
  apply convex_iInter
  intro i
  exact convex_halfSpace_gt
    ⟨fun x y => by rw [inner_add_left], fun c x => by rw [inner_smul_left]; simp⟩ 0

/-- An intersection of the half-planes `halfSpace (f i)` is a cone. -/
theorem smul_mem_iInter_halfSpace {β : Type*} (f : β → Fin 4)
    {y : Plane} (hy : y ∈ ⋂ i, halfSpace (f i)) {t : ℝ} (ht : 0 < t) :
    t • y ∈ ⋂ i, halfSpace (f i) := by
  rw [Set.mem_iInter] at hy ⊢
  intro i
  show 0 < inner ℝ (t • y) (circleVec (f i))
  have hyi : 0 < inner ℝ y (circleVec (f i)) := hy i
  rw [inner_smul_left]
  simpa using mul_pos ht hyi

/-- A nonempty intersection of the half-planes `halfSpace (f i)` does not contain the origin. -/
theorem zero_notMem_iInter_halfSpace {β : Type*} [Nonempty β] (f : β → Fin 4) :
    (0 : Plane) ∉ ⋂ i, halfSpace (f i) := by
  intro h
  have hb : 0 < inner ℝ (0 : Plane) (circleVec (f (Classical.arbitrary β))) :=
    Set.mem_iInter.mp h _
  rw [inner_zero_left] at hb
  exact lt_irrefl 0 hb

/-! ## The cover -/

/-- The four `circlePatch`es cover the circle. -/
theorem circlePatch_cover : (⋃ j, circlePatch j) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hnorm : (x : Plane).ofLp 0 ^ 2 + (x : Plane).ofLp 1 ^ 2 = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    have h2 := EuclideanSpace.norm_sq_eq (x : Plane)
    rw [h, Fin.sum_univ_two] at h2
    simpa [Real.norm_eq_abs, sq_abs] using h2.symm
  have hI0 : inner ℝ (x : Plane) (circleVec 0) = (x : Plane).ofLp 0 := by
    rw [circleVec_zero, EuclideanSpace.inner_single_right]; simp
  have hI1 : inner ℝ (x : Plane) (circleVec 1) = - (x : Plane).ofLp 0 := by
    rw [circleVec_one, inner_neg_right, EuclideanSpace.inner_single_right]; simp
  have hI2 : inner ℝ (x : Plane) (circleVec 2) = (x : Plane).ofLp 1 := by
    rw [circleVec_two, EuclideanSpace.inner_single_right]; simp
  have hI3 : inner ℝ (x : Plane) (circleVec 3) = - (x : Plane).ofLp 1 := by
    rw [circleVec_three, inner_neg_right, EuclideanSpace.inner_single_right]; simp
  rcases lt_trichotomy ((x : Plane).ofLp 0) 0 with h | h | h
  · exact ⟨1, by rw [mem_circlePatch, hI1]; linarith⟩
  · have hb : (x : Plane).ofLp 1 ≠ 0 := by
      intro hb; rw [hb] at hnorm; nlinarith
    rcases lt_trichotomy ((x : Plane).ofLp 1) 0 with h1 | h1 | h1
    · exact ⟨3, by rw [mem_circlePatch, hI3]; linarith⟩
    · exact absurd h1 hb
    · exact ⟨2, by rw [mem_circlePatch, hI2]; linarith⟩
  · exact ⟨0, by rw [mem_circlePatch, hI0]; linarith⟩

/-! ## The target statement -/

theorem circlePatch_isGoodFam :
    Work.ThomBordism.IsGoodFam Work.EMFG.circlePatch ∧
      (⋃ j, Work.EMFG.circlePatch j) = Set.univ := by
  refine ⟨⟨fun j => isOpen_circlePatch j, ?_⟩, circlePatch_cover⟩
  intro β _ f b hne
  haveI : Nonempty β := ⟨b⟩
  have hbridge : (⋂ i : β, circlePatch (f i))
      = {x : Work.Serre.Sph 1 | (x : Plane) ∈ ⋂ i, halfSpace (f i)} := by
    ext x
    simp [Set.mem_iInter, mem_circlePatch, halfSpace]
  rw [hbridge] at hne ⊢
  obtain ⟨x, hx⟩ := hne
  exact contractibleSpace_convexCone_inter_sphere (convex_iInter_halfSpace f)
    (fun y hy t ht => smul_mem_iInter_halfSpace f hy ht)
    (zero_notMem_iInter_halfSpace f) ⟨(x : Plane), hx⟩

end

end Work.EMFG
