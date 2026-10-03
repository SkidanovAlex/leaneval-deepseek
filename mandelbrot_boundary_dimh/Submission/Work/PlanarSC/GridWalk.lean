import Mathlib
import Submission.Work.PlanarSC.JCVocab

/-!
# Grid walks, simple loops and the circle parametrisation

Vocabulary for the proof of `Work.PlanarSC.gridLoop_nullhomotopic_of_simple`:

* `lpt n u` is the lattice point numbered `u = (a,b)` of the level-`n` dyadic grid
  (`gridEdge n (u,v) = segment ℝ (lpt n u) (lpt n v)`);
* `IsGridAdj E u v` says that `u` and `v` are joined by an edge of the finite edge set `E`
  (in either direction);
* `walkPath n u k` is the path following the lattice points `u 0, u 1, …, u k`
  (a concatenation of straight segments);
* `walkPathV` is its lift to a subspace `↥V`;
* `IsSimpleLoop p` says that `p` is injective on the parametrising circle (a Jordan curve);
* `circlePt` is the standard parametrisation of the circle by the unit interval.
-/

open Set
open scoped unitInterval Topology

namespace Work.PlanarSC

noncomputable section

/-! ## Lattice points and grid adjacency -/

/-- The lattice point `(a,b)` of the level-`n` dyadic grid. -/
def lpt (n : ℕ) (u : ℤ × ℤ) : ℂ := Commons.Topology.Plane.gcorner n u.1 u.2

@[simp] theorem lpt_re (n : ℕ) (u : ℤ × ℤ) : (lpt n u).re = (u.1 : ℝ) / 2 ^ n := rfl
@[simp] theorem lpt_im (n : ℕ) (u : ℤ × ℤ) : (lpt n u).im = (u.2 : ℝ) / 2 ^ n := rfl

theorem lpt_injective (n : ℕ) : Function.Injective (lpt n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨h1, h2⟩ := Commons.Topology.Plane.gcorner_inj h
  exact Prod.ext h1 h2

@[simp] theorem lpt_eq_lpt_iff {n : ℕ} {u v : ℤ × ℤ} : lpt n u = lpt n v ↔ u = v :=
  (lpt_injective n).eq_iff

/-- A pair of lattice points spanning a unit step, in either direction. -/
def IsUnitSeg (u v : ℤ × ℤ) : Prop := IsUnitStep (u, v) ∨ IsUnitStep (v, u)

/-- `u` and `v` are joined by an edge of the edge set `E`, in either direction. -/
def IsGridAdj (E : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (u v : ℤ × ℤ) : Prop :=
  (u, v) ∈ E ∨ (v, u) ∈ E

theorem IsGridAdj.flip {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {u v : ℤ × ℤ} (h : IsGridAdj E u v) :
    IsGridAdj E v u := h.elim Or.inr Or.inl

theorem IsGridAdj.isUnitSeg {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {u v : ℤ × ℤ}
    (h : IsGridAdj E u v) (hE : ∀ e ∈ E, IsUnitStep e) : IsUnitSeg u v :=
  h.elim (fun h1 => Or.inl (hE _ h1)) (fun h2 => Or.inr (hE _ h2))

theorem gridEdge_swap (n : ℕ) (u v : ℤ × ℤ) : gridEdge n (v, u) = gridEdge n (u, v) :=
  segment_symm ℝ _ _

theorem gridEdge_subset_gridSkeleton {n : ℕ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    {e : (ℤ × ℤ) × (ℤ × ℤ)} (he : e ∈ E) : gridEdge n e ⊆ gridSkeleton n E :=
  fun _ hz => mem_iUnion₂.mpr ⟨e, he, hz⟩

theorem lpt_mem_gridEdge_left (n : ℕ) (u v : ℤ × ℤ) : lpt n u ∈ gridEdge n (u, v) :=
  left_mem_segment ℝ _ _

theorem lpt_mem_gridEdge_right (n : ℕ) (u v : ℤ × ℤ) : lpt n v ∈ gridEdge n (u, v) :=
  right_mem_segment ℝ _ _

theorem IsGridAdj.left_mem_gridSkeleton {n : ℕ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {u v : ℤ × ℤ}
    (h : IsGridAdj E u v) : lpt n u ∈ gridSkeleton n E := by
  rcases h with h | h
  · exact gridEdge_subset_gridSkeleton h (lpt_mem_gridEdge_left n u v)
  · exact gridEdge_subset_gridSkeleton h (lpt_mem_gridEdge_right n v u)

theorem IsGridAdj.right_mem_gridSkeleton {n : ℕ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {u v : ℤ × ℤ}
    (h : IsGridAdj E u v) : lpt n v ∈ gridSkeleton n E := h.flip.left_mem_gridSkeleton

theorem gridEdge_subset_of_mem {n : ℕ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {V : Set ℂ}
    (hE : ∀ e ∈ E, IsUnitStep e ∧ gridEdge n e ⊆ V) {u v : ℤ × ℤ} (h : IsGridAdj E u v) :
    segment ℝ (lpt n u) (lpt n v) ⊆ V := by
  rcases h with h | h
  · exact (hE _ h).2
  · rw [segment_symm]; exact (hE _ h).2

/-! ## The straight segment as a path -/

/-- The straight-line path from `a` to `b`. -/
def segPath (a b : ℂ) : Path a b where
  toFun t := AffineMap.lineMap a b (t : ℝ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem segPath_apply (a b : ℂ) (t : unitInterval) :
    segPath a b t = AffineMap.lineMap a b (t : ℝ) := rfl

theorem segPath_mem_segment (a b : ℂ) (t : unitInterval) : segPath a b t ∈ segment ℝ a b :=
  segment_eq_image_lineMap ℝ a b ▸ ⟨(t : ℝ), ⟨t.2.1, t.2.2⟩, rfl⟩

theorem segPath_mem_gridEdge {n : ℕ} (u v : ℤ × ℤ) (t : unitInterval) :
    segPath (lpt n u) (lpt n v) t ∈ gridEdge n (u, v) := segPath_mem_segment _ _ _

theorem segPath_mem_gridEdge' {n : ℕ} (u v : ℤ × ℤ) (t : unitInterval) :
    segPath (lpt n u) (lpt n v) t ∈ gridEdge n (v, u) := by
  rw [gridEdge_swap n u v]
  exact segPath_mem_gridEdge u v t

/-- The segment from an endpoint of a grid edge to a point of the edge stays in the edge. -/
theorem segment_subset_gridEdge_left {n : ℕ} {u v : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ gridEdge n (u, v)) : segment ℝ (lpt n u) z ⊆ gridEdge n (u, v) :=
  (convex_segment (𝕜 := ℝ) (lpt n u) (lpt n v)).segment_subset (left_mem_segment ℝ _ _) hz

theorem segment_subset_gridEdge_right {n : ℕ} {u v : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ gridEdge n (u, v)) : segment ℝ z (lpt n v) ⊆ gridEdge n (u, v) :=
  (convex_segment (𝕜 := ℝ) (lpt n u) (lpt n v)).segment_subset hz (right_mem_segment ℝ _ _)

theorem segPath_range_subset {a b : ℂ} {S : Set ℂ} (h : segment ℝ a b ⊆ S) :
    Set.range (segPath a b) ⊆ S := by
  rintro z ⟨t, rfl⟩
  exact h (segPath_mem_segment a b t)

/-- The lift of a path in `ℂ` with values in `V` to a path in the subspace `↥V`. -/
def pathLift {V : Set ℂ} {a b : ℂ} (p : Path a b) (ha : a ∈ V) (hb : b ∈ V)
    (h : ∀ t, p t ∈ V) : Path (⟨a, ha⟩ : ↥V) (⟨b, hb⟩ : ↥V) where
  toFun t := ⟨p t, h t⟩
  continuous_toFun := Continuous.subtype_mk p.continuous h
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem pathLift_apply {V : Set ℂ} {a b : ℂ} (p : Path a b) (ha : a ∈ V)
    (hb : b ∈ V) (h : ∀ t, p t ∈ V) (t : unitInterval) :
    ((pathLift p ha hb h t : ↥V) : ℂ) = p t := rfl

theorem pathLift_map {V : Set ℂ} {a b : ℂ} (p : Path a b) (ha : a ∈ V) (hb : b ∈ V)
    (h : ∀ t, p t ∈ V) : (pathLift p ha hb h).map continuous_subtype_val = p := by
  ext t
  rfl

/-! ## Simple loops -/

/-- A path is a *simple loop* if it is injective on the parametrising circle: two parameters with
the same image are equal, unless they are the two endpoints. -/
def IsSimpleLoop {X : Type*} [TopologicalSpace X] {a b : X} (p : Path a b) : Prop :=
  ∀ s t : unitInterval, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)

theorem IsSimpleLoop.pathLift {V : Set ℂ} {a b : ℂ} {ha : a ∈ V} {hb : b ∈ V} {p : Path a b}
    (hp : IsSimpleLoop p) (h : ∀ t, p t ∈ V) : IsSimpleLoop (pathLift p ha hb h) := by
  intro s t hst
  exact hp s t (congrArg Subtype.val hst)

/-- `IsSimpleLoop` is invariant under endpoint casts. -/
theorem IsSimpleLoop.cast {X : Type*} [TopologicalSpace X] {a b a' b' : X} {p : Path a b}
    (hp : IsSimpleLoop p) (hx : a' = a) (hy : b' = b) : IsSimpleLoop (p.cast hx hy) := by
  subst hx; subst hy
  simpa using hp

/-! ## Elementary homotopy algebra for `Path.trans` -/

theorem path_homotopic_trans_of_left_null {X : Type*} [TopologicalSpace X] {a b : X}
    {P : Path a a} {Q : Path a b} (hP : Path.Homotopic P (Path.refl a)) :
    Path.Homotopic (P.trans Q) Q :=
  (Path.Homotopic.hcomp hP (Path.Homotopic.refl Q)).trans (Path.Homotopic.refl_trans Q)

theorem path_homotopic_trans_of_right_null {X : Type*} [TopologicalSpace X] {a b : X}
    {P : Path a b} {Q : Path b b} (hQ : Path.Homotopic Q (Path.refl b)) :
    Path.Homotopic (P.trans Q) P :=
  (Path.Homotopic.hcomp (Path.Homotopic.refl P) hQ).trans (Path.Homotopic.trans_refl P)

theorem path_homotopic_trans_of_middle_null {X : Type*} [TopologicalSpace X] {a b c : X}
    {P : Path a b} {Q : Path b b} {R : Path b c} (hQ : Path.Homotopic Q (Path.refl b)) :
    Path.Homotopic (P.trans (Q.trans R)) (P.trans R) :=
  (Path.Homotopic.hcomp (Path.Homotopic.refl P)
    (Path.Homotopic.hcomp hQ (Path.Homotopic.refl R))).trans
    (Path.Homotopic.hcomp (Path.Homotopic.refl P) (Path.Homotopic.refl_trans R))

/-! ## Walk paths -/

/-- The path following the lattice points `u 0, u 1, …, u k`: the concatenation of the straight
segments between consecutive lattice points.

For `k = 0` this is the constant path; for `k ≥ 1` the polygonal curve is parametrised
monotonically, in such a way that no sub-interval of the parametrisation is collapsed (this is what
makes the parametrisation injective for a vertex-simple closed walk). -/
def walkPath (n : ℕ) (u : ℕ → ℤ × ℤ) : ∀ k : ℕ, Path (lpt n (u 0)) (lpt n (u k))
  | 0 => Path.refl _
  | 1 => segPath (lpt n (u 0)) (lpt n (u 1))
  | k + 2 => (walkPath n u (k + 1)).trans (segPath (lpt n (u (k + 1))) (lpt n (u (k + 2))))

@[simp] theorem walkPath_zero (n : ℕ) (u : ℕ → ℤ × ℤ) :
    walkPath n u 0 = Path.refl (lpt n (u 0)) := rfl

theorem walkPath_one (n : ℕ) (u : ℕ → ℤ × ℤ) :
    walkPath n u 1 = segPath (lpt n (u 0)) (lpt n (u 1)) := rfl

theorem walkPath_succ_succ (n : ℕ) (u : ℕ → ℤ × ℤ) (k : ℕ) :
    walkPath n u (k + 2) =
      (walkPath n u (k + 1)).trans (segPath (lpt n (u (k + 1))) (lpt n (u (k + 2)))) := rfl

/-- The recursive description of a walk path of at least one step. -/
theorem walkPath_succ {n : ℕ} {u : ℕ → ℤ × ℤ} {k : ℕ} (hk : 1 ≤ k) :
    walkPath n u (k + 1) =
      (walkPath n u k).trans (segPath (lpt n (u k)) (lpt n (u (k + 1)))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact walkPath_succ_succ n u j

/-- Splitting a walk path after its first `k` steps (with `k ≥ 1`). -/
theorem walkPath_add {n : ℕ} {u : ℕ → ℤ × ℤ} (k : ℕ) (hk : 1 ≤ k) :
    ∀ j : ℕ, Path.Homotopic (walkPath n u (k + j))
      ((walkPath n u k).trans (walkPath n (fun i => u (k + i)) j)) := by
  intro j
  induction j with
  | zero => exact (Path.Homotopic.trans_refl (walkPath n u k)).symm
  | succ j ih =>
      rcases j with _ | j'
      · rw [walkPath_one n (fun i => u (k + i)),
          walkPath_succ (u := u) (k := k) hk]
        exact Path.Homotopic.refl _
      · have h1 : walkPath n u (k + (j' + 1 + 1)) =
            walkPath n u ((k + (j' + 1)) + 1) := rfl
        rw [h1, walkPath_succ (u := u) (k := k + (j' + 1)) (by omega),
          walkPath_succ (u := fun i => u (k + i)) (k := j' + 1) (by omega)]
        exact (Path.Homotopic.hcomp ih (Path.Homotopic.refl _)).trans
          (Path.Homotopic.trans_assoc (walkPath n u k) (walkPath n (fun i => u (k + i)) (j' + 1))
            (segPath (lpt n (((fun i => u (k + i)) (j' + 1))))
              (lpt n (((fun i => u (k + i)) (j' + 1 + 1))))))

/-- Every point of a walk path lies in the skeleton of `E`, provided the starting point and the
consecutive adjacencies are there. -/
theorem walkPath_mem_gridSkeleton {n : ℕ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))} {u : ℕ → ℤ × ℤ}
    (h0 : lpt n (u 0) ∈ gridSkeleton n E) :
    ∀ (k : ℕ) (_ : ∀ i < k, IsGridAdj E (u i) (u (i + 1))) (t : unitInterval),
      walkPath n u k t ∈ gridSkeleton n E := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hu t
      rcases k with _ | _ | j
      · simpa using h0
      · rw [walkPath_one]
        rcases hu 0 (by omega) with hadj | hadj
        · exact gridEdge_subset_gridSkeleton hadj (segPath_mem_gridEdge (u 0) (u 1) t)
        · exact gridEdge_subset_gridSkeleton hadj (segPath_mem_gridEdge' (u 0) (u 1) t)
      · rw [walkPath_succ_succ, Path.trans_apply]
        split_ifs with h
        · exact ih (j + 1) (by omega) (fun i hi => hu i (by omega)) _
        · rcases hu (j + 1) (by omega) with hadj | hadj
          · exact gridEdge_subset_gridSkeleton hadj (segPath_mem_gridEdge _ _ _)
          · exact gridEdge_subset_gridSkeleton hadj (segPath_mem_gridEdge' _ _ _)

/-- Every point of a walk path lies in `V`, provided the vertices and the traversed segments do. -/
theorem walkPath_mem_of_subset {n : ℕ} {u : ℕ → ℤ × ℤ} {V : Set ℂ} :
    ∀ (k : ℕ), (∀ i ≤ k, lpt n (u i) ∈ V) →
      (∀ i < k, segment ℝ (lpt n (u i)) (lpt n (u (i + 1))) ⊆ V) →
      ∀ t : unitInterval, walkPath n u k t ∈ V := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hv hseg t
      rcases k with _ | _ | j
      · simpa using hv 0 le_rfl
      · rw [walkPath_one]
        exact hseg 0 (by omega) (segPath_mem_segment _ _ _)
      · rw [walkPath_succ_succ, Path.trans_apply]
        split_ifs with h
        · exact ih (j + 1) (by omega) (fun i hi => hv i (by omega))
            (fun i hi => hseg i (by omega)) _
        · exact hseg (j + 1) (by omega) (segPath_mem_segment _ _ _)

/-- The walk path of the lattice points `u 0, …, u k` in the subspace `↥V`, transported so that
both its endpoints are the point `w` (where the walk starts and ends). -/
def walkPathV {V : Set ℂ} (n : ℕ) (w : ℤ × ℤ) (hw : lpt n w ∈ V) (u : ℕ → ℤ × ℤ) (k : ℕ)
    (h0 : u 0 = w) (hcl : u k = w) (hv : ∀ i ≤ k, lpt n (u i) ∈ V)
    (hseg : ∀ i < k, segment ℝ (lpt n (u i)) (lpt n (u (i + 1))) ⊆ V) :
    Path (⟨lpt n w, hw⟩ : ↥V) (⟨lpt n w, hw⟩ : ↥V) :=
  (pathLift (walkPath n u k) (hv 0 (Nat.zero_le k)) (hv k le_rfl)
      (walkPath_mem_of_subset k hv hseg)).cast
    (Subtype.ext (congrArg (lpt n) h0.symm)) (Subtype.ext (congrArg (lpt n) hcl.symm))

/-- `IsSimpleLoop` of the walk path in `ℂ` transfers to `walkPathV`. -/
theorem walkPathV_isSimple {V : Set ℂ} {n : ℕ} {w : ℤ × ℤ} {hw : lpt n w ∈ V}
    {u : ℕ → ℤ × ℤ} {k : ℕ} {h0 : u 0 = w} {hcl : u k = w}
    {hv : ∀ i ≤ k, lpt n (u i) ∈ V}
    {hseg : ∀ i < k, segment ℝ (lpt n (u i)) (lpt n (u (i + 1))) ⊆ V}
    (h : IsSimpleLoop (walkPath n u k)) :
    IsSimpleLoop (walkPathV n w hw u k h0 hcl hv hseg) :=
  IsSimpleLoop.cast (IsSimpleLoop.pathLift h (walkPath_mem_of_subset k hv hseg))
    (Subtype.ext (congrArg (lpt n) h0.symm)) (Subtype.ext (congrArg (lpt n) hcl.symm))

@[simp] theorem walkPathV_coe {V : Set ℂ} {n : ℕ} {w : ℤ × ℤ} {hw : lpt n w ∈ V}
    {u : ℕ → ℤ × ℤ} {k : ℕ} {h0 : u 0 = w} {hcl : u k = w} {hv : ∀ i ≤ k, lpt n (u i) ∈ V}
    {hseg : ∀ i < k, segment ℝ (lpt n (u i)) (lpt n (u (i + 1))) ⊆ V} (t : unitInterval) :
    ((walkPathV n w hw u k h0 hcl hv hseg t : ↥V) : ℂ) = walkPath n u k t := by
  simp [walkPathV]

/-! ## Homotopies of paths whose range lies in a convex subset -/

/-- **Two paths in `↥V` whose ranges lie in a convex subset `S ⊆ V` are homotopic** (the
straight-line homotopy stays in `S`). -/
theorem path_homotopic_of_convex_subset {V : Set ℂ} {S : Set ℂ} (hS : Convex ℝ S) (hSV : S ⊆ V)
    {a b : ↥V} (p r : Path a b) (hp : ∀ t, (p t : ℂ) ∈ S) (hr : ∀ t, (r t : ℂ) ∈ S) :
    Path.Homotopic p r := by
  have hmem : ∀ x : unitInterval × unitInterval,
      (1 - (x.1 : ℝ)) • (p x.2 : ℂ) + (x.1 : ℝ) • (r x.2 : ℂ) ∈ S := by
    intro x
    have hseg := hS.segment_subset (hp x.2) (hr x.2)
    rw [segment_eq_image_lineMap] at hseg
    exact hseg ⟨(x.1 : ℝ), ⟨x.1.2.1, x.1.2.2⟩, by rw [AffineMap.lineMap_apply_module]⟩
  refine ⟨{ toFun := fun x => (⟨(1 - (x.1 : ℝ)) • (p x.2 : ℂ) + (x.1 : ℝ) • (r x.2 : ℂ),
              hSV (hmem x)⟩ : ↥V)
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · refine Continuous.subtype_mk ?_ (fun x => hSV (hmem x))
    fun_prop
  · intro t
    exact Subtype.ext (by simp)
  · intro t
    exact Subtype.ext (by simp)
  · intro t x hx
    have hx' : x = 0 ∨ x = 1 := by simpa using hx
    rcases hx' with rfl | rfl
    · refine Subtype.ext ?_
      show (1 - (t : ℝ)) • (p 0 : ℂ) + (t : ℝ) • (r 0 : ℂ) = (p 0 : ℂ)
      rw [p.source, r.source, ← add_smul, sub_add_cancel, one_smul]
    · refine Subtype.ext ?_
      show (1 - (t : ℝ)) • (p 1 : ℂ) + (t : ℝ) • (r 1 : ℂ) = (p 1 : ℂ)
      rw [p.target, r.target, ← add_smul, sub_add_cancel, one_smul]

/-- Two paths in `↥V` with ranges in the same grid edge (or its reverse) are homotopic. -/
theorem path_homotopic_of_same_edge {V : Set ℂ} {n : ℕ} {E : Finset ((ℤ × ℤ) × (ℤ × ℤ))}
    (hE : ∀ e ∈ E, IsUnitStep e ∧ gridEdge n e ⊆ V) {u v : ℤ × ℤ} (huv : IsGridAdj E u v)
    {a b : ↥V} (p r : Path a b) (hp : ∀ t, (p t : ℂ) ∈ gridEdge n (u, v))
    (hr : ∀ t, (r t : ℂ) ∈ gridEdge n (u, v)) : Path.Homotopic p r :=
  path_homotopic_of_convex_subset (convex_segment _ _) (gridEdge_subset_of_mem hE huv) p r hp hr

/-! ## The circle parametrisation -/

/-- The standard parametrisation `t ↦ exp (2 π i t)` of the unit circle by the unit interval. -/
def circlePt (t : unitInterval) : Circle := Circle.exp (2 * Real.pi * t)

theorem continuous_circlePt : Continuous circlePt :=
  Circle.exp.continuous.comp (by fun_prop)

@[simp] theorem circlePt_zero : circlePt 0 = 1 := by simp [circlePt]

@[simp] theorem circlePt_one : circlePt 1 = 1 := by
  have h : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [circlePt, h, mul_one, Circle.exp_two_pi]

theorem circlePt_surjective : Function.Surjective circlePt := by
  intro z
  obtain ⟨x, hx⟩ := Circle.exp_surjective z
  have hy : Int.fract (x / (2 * Real.pi)) = x / (2 * Real.pi) - (⌊x / (2 * Real.pi)⌋ : ℝ) :=
    (Int.self_sub_floor _).symm
  have harg : 2 * Real.pi * (Int.fract (x / (2 * Real.pi))) =
      x + (-⌊x / (2 * Real.pi)⌋) * (2 * Real.pi) := by
    rw [hy]
    field_simp
    ring_nf
  refine ⟨⟨Int.fract (x / (2 * Real.pi)), Int.fract_nonneg _,
    le_of_lt (Int.fract_lt_one _)⟩, ?_⟩
  show Circle.exp (2 * Real.pi * Int.fract (x / (2 * Real.pi))) = z
  rw [harg, ← hx, Circle.exp_eq_exp]
  refine ⟨-⌊x / (2 * Real.pi)⌋, ?_⟩
  push_cast
  ring

end

end Work.PlanarSC
