import Submission.Work.Serre.Engine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The subsets of the cube and of the pullback used by the E2(d) argument

`Work.Serre.SerreE2d` computes the relative homology `H_{k+n}(τ^*E, τ^*E|_{∂Iⁿ})` of the pullback
of a Serre fibration along a cube in terms of the homology of the fibre.  The proof (this
directory) is an induction on `n` which reduces the pair `(Iⁿ, ∂Iⁿ)` to the pair of a *slab* and
its boundary part, and then to the *middle slice* of the slab, which is a cube of one dimension
lower.

This file fixes the vocabulary of that argument:

* `Work.Serre.pbPre p τ S` — the preimage of `S ⊆ I^m` in the pullback `τ^*E`;
* `Work.Serre.cubeBdryS m` — the boundary `∂I^m`;
* `Work.Serre.slabU`, `slabV` — the two slabs `{last < 3/4}` and `{last > 1/4}` of `I^{n+1}`;
* `Work.Serre.slabM` — their intersection, the middle slab `{1/4 < last < 3/4}`;
* `Work.Serre.sliceZ` — the middle slice `{last = 1/2}`;
* `Work.Serre.faceTop` — the top face `{last = 1}`.

The elementary (set-theoretic and topological) facts about them are collected at the end.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The boundary `∂Iᵐ` of the cube `Iᵐ = (Fin m → I)`. -/
abbrev cubeBdryS (m : ℕ) : Set (Work.Stems.Cubical.IC m) := Cube.boundary (Fin m)

/-- The preimage in the pullback `τ^*E` of a subset `S` of the cube. -/
def pbPre {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ} (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC m, B)) (S : Set (Work.Stems.Cubical.IC m)) :
    Set (Work.StemsB.Pullback p τ) :=
  {x | Work.StemsB.pullbackSnd p τ x ∈ S}

@[simp]
theorem mem_pbPre {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ} (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC m, B)) (S : Set (Work.Stems.Cubical.IC m))
    (x : Work.StemsB.Pullback p τ) : x ∈ pbPre p τ S ↔ Work.StemsB.pullbackSnd p τ x ∈ S :=
  Iff.rfl

/-- The relative part of the pullback pair over `(S, T)`: the preimage of `T` inside the preimage
of `S`. -/
def pbSub {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ} (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC m, B)) (S T : Set (Work.Stems.Cubical.IC m)) :
    Set (↥(pbPre p τ S)) :=
  {x | (x : Work.StemsB.Pullback p τ) ∈ pbPre p τ T}

@[simp]
theorem mem_pbSub {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ} (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC m, B)) (S T : Set (Work.Stems.Cubical.IC m))
    (x : ↥(pbPre p τ S)) : x ∈ pbSub p τ S T ↔ (x : Work.StemsB.Pullback p τ) ∈ pbPre p τ T :=
  Iff.rfl

/-- The convex combination `(1-t) u + t z` of two points of a cube, as a point of the cube. -/
def lerp (m : ℕ) (u : Work.Stems.Cubical.IC m) (t : unitInterval)
    (z : Work.Stems.Cubical.IC m) : Work.Stems.Cubical.IC m :=
  fun i => ⟨(1 - (t : ℝ)) * (u i : ℝ) + (t : ℝ) * (z i : ℝ), by
    have hu := (u i).2
    have hz := (z i).2
    have ht := t.2
    refine ⟨?_, ?_⟩ <;> nlinarith [hu.1, hu.2, hz.1, hz.2, ht.1, ht.2]⟩

@[simp]
theorem lerp_zero (m : ℕ) (u z : Work.Stems.Cubical.IC m) : lerp m u 0 z = u := by
  funext i
  refine Subtype.ext ?_
  simp [lerp]

@[simp]
theorem lerp_one (m : ℕ) (u z : Work.Stems.Cubical.IC m) : lerp m u 1 z = z := by
  funext i
  refine Subtype.ext ?_
  simp [lerp]

@[simp]
theorem lerp_self (m : ℕ) (u : Work.Stems.Cubical.IC m) (t : unitInterval) :
    lerp m u t u = u := by
  funext i
  refine Subtype.ext ?_
  simp only [lerp, Set.mem_setOf_eq]
  ring_nf

theorem continuous_lerp (m : ℕ) :
    Continuous fun p : Work.Stems.Cubical.IC m × unitInterval × Work.Stems.Cubical.IC m =>
      lerp m p.1 p.2.1 p.2.2 := by
  apply continuous_pi
  intro i
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun p : Work.Stems.Cubical.IC m × unitInterval × Work.Stems.Cubical.IC m =>
      ((p.1 i : unitInterval) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  have h2 : Continuous fun p : Work.Stems.Cubical.IC m × unitInterval × Work.Stems.Cubical.IC m =>
      ((p.2.1 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h3 : Continuous fun p : Work.Stems.Cubical.IC m × unitInterval × Work.Stems.Cubical.IC m =>
      ((p.2.2 i : unitInterval) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  exact ((continuous_const.sub h2).mul h1).add (h2.mul h3)

/-- **The cube is contracted onto any of its points**, by the straight-line homotopy. -/
def cubeContraction (m : ℕ) (z : Work.Stems.Cubical.IC m) :
    C(Work.Stems.Cubical.IC m × unitInterval, Work.Stems.Cubical.IC m) where
  toFun p := lerp m p.1 p.2 z
  continuous_toFun := (continuous_lerp m).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

@[simp]
theorem cubeContraction_zero (m : ℕ) (z : Work.Stems.Cubical.IC m)
    (u : Work.Stems.Cubical.IC m) : cubeContraction m z (u, 0) = u := lerp_zero m u z

@[simp]
theorem cubeContraction_one (m : ℕ) (z : Work.Stems.Cubical.IC m)
    (u : Work.Stems.Cubical.IC m) : cubeContraction m z (u, 1) = z := lerp_one m u z

@[simp]
theorem cubeContraction_self (m : ℕ) (z : Work.Stems.Cubical.IC m) (t : unitInterval) :
    cubeContraction m z (z, t) = z := lerp_self m z t

/-- The midpoint `1/2` of the unit interval. -/
def half : unitInterval := ⟨1/2, by norm_num⟩

theorem coe_half : (half : ℝ) = 1/2 := rfl

/-- The last coordinate of a point of `I^{n+1}`, as a real number. -/
def lastCoord {n : ℕ} (u : Work.Stems.Cubical.IC (n+1)) : ℝ := (u (Fin.last n) : ℝ)

/-- The first slab `{last < 3/4}` of `I^{n+1}`. -/
def slabU (n : ℕ) : Set (Work.Stems.Cubical.IC (n+1)) := {u | lastCoord u < 3/4}

/-- The second slab `{last > 1/4}` of `I^{n+1}`. -/
def slabV (n : ℕ) : Set (Work.Stems.Cubical.IC (n+1)) := {u | 1/4 < lastCoord u}

/-- The middle slab `{1/4 < last < 3/4}` of `I^{n+1}`. -/
def slabM (n : ℕ) : Set (Work.Stems.Cubical.IC (n+1)) :=
  {u | 1/4 < lastCoord u ∧ lastCoord u < 3/4}

/-- The middle slice `{last = 1/2}` of `I^{n+1}`. -/
def sliceZ (n : ℕ) : Set (Work.Stems.Cubical.IC (n+1)) := {u | lastCoord u = 1/2}

/-- The top face `{last = 1}` of `I^{n+1}`. -/
def faceTop (n : ℕ) : Set (Work.Stems.Cubical.IC (n+1)) := {u | lastCoord u = 1}

/-- The middle slice is contained in the middle slab. -/
theorem sliceZ_subset_slabM (n : ℕ) : sliceZ n ⊆ slabM n := fun u hu => by
  refine ⟨?_, ?_⟩ <;> simp only [sliceZ, Set.mem_ofPred_eq] at hu
  · rw [hu]; norm_num
  · rw [hu]; norm_num

/-- The boundary part of the middle slab is contained in the boundary part of the slab. -/
theorem slabM_inter_bdry_subset_slabU_inter_bdry (n : ℕ) :
    slabM n ∩ cubeBdryS (n+1) ⊆ slabU n ∩ cubeBdryS (n+1) :=
  fun _u hu => ⟨(hu.1).2, hu.2⟩

open scoped Topology in
theorem isOpen_slabU (n : ℕ) : IsOpen (slabU n) :=
  isOpen_lt (continuous_apply _ |>.subtype_val) continuous_const

open scoped Topology in
theorem isOpen_slabV (n : ℕ) : IsOpen (slabV n) :=
  isOpen_lt continuous_const (continuous_apply _ |>.subtype_val)

theorem slabU_union_slabV (n : ℕ) : slabU n ∪ slabV n = Set.univ := by
  ext u
  constructor
  · intro _; trivial
  · intro _
    by_cases h : lastCoord u < 3/4
    · exact Or.inl h
    · push_neg at h
      refine Or.inr (lt_of_lt_of_le ?_ h)
      norm_num

/-- The mid point of the middle slab. -/
def midPt (n : ℕ) : Work.Stems.Cubical.IC (n+1) :=
  fun _ => ⟨1/2, by norm_num⟩

theorem lastCoord_midPt (n : ℕ) : lastCoord (midPt n) = 1/2 := rfl

/-- The middle slab is the intersection of the two slabs. -/
theorem slabM_eq_inter (n : ℕ) : slabM n = slabU n ∩ slabV n := by
  ext u
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The middle slab is contained in the first slab. -/
theorem slabM_subset_slabU (n : ℕ) : slabM n ⊆ slabU n := fun _ h => h.2

/-- The middle slice is a subspace of the middle slab. -/
theorem sliceZ_subset_slabM' (n : ℕ) : sliceZ n ⊆ slabM n := sliceZ_subset_slabM n

/-- The middle point lies on the middle slice. -/
theorem mem_sliceZ_midPt (n : ℕ) : midPt n ∈ sliceZ n := rfl

/-- The middle slice is exactly the set of points with last coordinate `1/2`. -/
theorem sliceZ_mem_iff (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    u ∈ sliceZ n ↔ u (Fin.last n) = half := by
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    show lastCoord u = 1/2
    rw [lastCoord, h]
    rfl

/-- The inclusion of the cube `Iⁿ` as the middle slice `{last = 1/2}` of `I^{n+1}`. -/
def sliceIncl (n : ℕ) : C(Work.Stems.Cubical.IC n, Work.Stems.Cubical.IC (n+1)) where
  toFun u := Fin.snoc u half
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [Fin.snoc_last] using continuous_const
    · intro j
      simpa [Fin.snoc_castSucc] using continuous_apply j

@[simp]
theorem sliceIncl_apply_castSucc {n : ℕ} (u : Work.Stems.Cubical.IC n) (j : Fin n) :
    sliceIncl n u (Fin.castSucc j) = u j := by
  simp [sliceIncl, Fin.snoc_castSucc]

@[simp]
theorem sliceIncl_apply_last (n : ℕ) (u : Work.Stems.Cubical.IC n) :
    sliceIncl n u (Fin.last n) = half := by
  simp [sliceIncl, Fin.snoc_last]

theorem lastCoord_sliceIncl (n : ℕ) (u : Work.Stems.Cubical.IC n) :
    lastCoord (sliceIncl n u) = 1/2 := by
  simp [lastCoord, sliceIncl, Fin.snoc_last, half]

end

end Work.Serre
