import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj

set_option synthInstance.maxHeartbeats 400000

/-!
# The range of `attachIncl` carries the topology of `Y`

Area **RATHUREWICZ**.  Given a space `Y`, attaching maps `f : ι → C(S^{n+1}, Y)` and the space
`attachCells n Y ι f` (the pushout of `Y ← ∐ S^{n+1} → ∐ D^{n+2}`), the inclusion
`attachIncl n Y ι f : Y → attachCells n Y ι f` makes `Y` a *subspace* of `attachCells n Y ι f`:
the subspace topology on `range attachIncl` is the topology of `Y`.

Concretely, for every open `W ⊆ Y` there is an open `V ⊆ attachCells n Y ι f` with
`V ∩ range attachIncl = attachIncl '' W`.  The equivalence classes of the gluing relation are the
singletons of the cell *interior* points (which are never identified with anything else, since the
relation only identifies boundary points of the cells with `Y`) together with the sets
`{y} ∪ {boundary points of cells mapped to y}` (`Work.RatHurewicz.AttachRange.Cls`).  So the
*open saturated* set

`S_W = {inl y : y ∈ W} ∪ ⋃_i {inr (i,x) : x ≠ 0, f i (x/‖x‖) ∈ W}`

descends to an open set `V` of `attachCells n Y ι f`, whose trace on `range attachIncl` is exactly
`attachIncl '' W`.  The only non-trivial input is that `x ↦ x/‖x‖` is continuous on the punctured
disc, so that the second piece of `S_W` is open.

The main consequence, `attachIncl_isOpenMap_range`, is that the corestriction of `attachIncl` to its
range is an *open* map, i.e. a homeomorphism onto its range; it is the input of
`Work.RatHurewicz.subsingleton_relPi_of_compressRel_range`.

## Main names

* `cellDir` — the radial retraction `D^{n+2} \ {0} → S^{n+1}`;
* `satSet` — the saturated open set `S_W` above;
* `isInducing_attachIncl` — `attachIncl` is an inducing map;
* `attachIncl_isOpenMap_range` — the target: the corestriction of `attachIncl` to its range is open.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-! ### The radial retraction of the punctured disc onto its boundary sphere -/

/-- The radial projection of a non-zero point of the model cell `D^{n+2}` onto the model sphere
`S^{n+1} = ∂D^{n+2}`: `x ↦ x / ‖x‖`. -/
def cellDirFun (n : ℕ)
    (x : {x : cellDisk n // (x : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0}) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  ‖((x : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))‖⁻¹ •
    ((x : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))

theorem cellDirFun_mem (n : ℕ)
    (x : {x : cellDisk n // (x : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0}) :
    cellDirFun n x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  show ‖‖((x : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))‖⁻¹ •
      (((x : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))))‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2)

theorem continuous_cellDirFun (n : ℕ) : Continuous (cellDirFun n) := by
  unfold cellDirFun
  have hv : Continuous fun x : {x : cellDisk n // (x : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0} =>
      (((x : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2)))) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (hv.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.2)).smul hv

/-- The radial retraction `D^{n+2} \ {0} → S^{n+1}`, as a bundled continuous map. -/
def cellDir (n : ℕ) :
    C({x : cellDisk n // (x : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0}, cellSphere n) where
  toFun x := ⟨cellDirFun n x, cellDirFun_mem n x⟩
  continuous_toFun := Continuous.subtype_mk (continuous_cellDirFun n) (cellDirFun_mem n)

/-- The radial retraction fixes the boundary sphere pointwise. -/
theorem cellDir_cellSphereToDisk (n : ℕ) (z : cellSphere n)
    (h : (((cellSphereToDisk n z : cellDisk n)) : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0) :
    cellDir n ⟨cellSphereToDisk n z, h⟩ = z := by
  refine Subtype.ext ?_
  show cellDirFun n ⟨cellSphereToDisk n z, h⟩ = (z : EuclideanSpace ℝ (Fin (n + 2)))
  unfold cellDirFun
  have hz : ‖((((cellSphereToDisk n z : cellDisk n)) :
      EuclideanSpace ℝ (Fin (n + 2))))‖ = 1 :=
    (by simpa [dist_eq_norm] using (Metric.mem_sphere.mp z.2) :
      ‖(z : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1)
  rw [hz, inv_one, one_smul]
  show (((cellSphereToDisk n z : cellDisk n)) : EuclideanSpace ℝ (Fin (n + 2))) =
    (z : EuclideanSpace ℝ (Fin (n + 2)))
  rfl

/-! ### The saturated open set -/

/-- The saturated open set of `Y ⊕ (Σ i, D^{n+2})` whose image in the quotient is the required
neighbourhood of `attachIncl '' U`: the `U`-part of `Y` together with those *non-zero* points of the
cells whose radial direction is mapped into `U` by the attaching map. -/
def satSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (U : Set Y) : Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
  {a | (∃ y ∈ U, a = Sum.inl y) ∨
    ∃ (i : ι) (x : cellDisk n), a = Sum.inr ⟨i, x⟩ ∧
      ∃ (hx : (x : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0), f i (cellDir n ⟨x, hx⟩) ∈ U}

/-- The class of a point `y ∈ Y` in the gluing relation: `y` itself, together with all boundary
points of cells whose attaching map sends them to `y`. -/
def clsPt (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (a : Y ⊕ (Σ _ : ι, cellDisk n)) (y : Y) : Prop :=
  a = Sum.inl y ∨ ∃ (i : ι) (z : cellSphere n),
    a = Sum.inr ⟨i, cellSphereToDisk n z⟩ ∧ f i z = y

theorem cls_iff (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (a b : Y ⊕ (Σ _ : ι, cellDisk n)) :
    AttachRange.Cls n Y ι f a b ↔ a = b ∨ ∃ y, clsPt n Y ι f a y ∧ clsPt n Y ι f b y :=
  Iff.rfl

theorem mem_satSet_of_clsPt (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {U : Set Y} {b : Y ⊕ (Σ _ : ι, cellDisk n)} {y : Y}
    (hb : clsPt n Y ι f b y) (hy : y ∈ U) : b ∈ satSet n Y ι f U := by
  rcases hb with rfl | ⟨i, z, rfl, hfz⟩
  · exact Or.inl ⟨y, hy, rfl⟩
  · have hz1 : ‖((((cellSphereToDisk n z : cellDisk n)) :
        EuclideanSpace ℝ (Fin (n + 2))))‖ = 1 :=
      (by simpa [dist_eq_norm] using (Metric.mem_sphere.mp z.2) :
        ‖(z : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1)
    refine Or.inr ⟨i, cellSphereToDisk n z, rfl, (fun h0 => ?_), ?_⟩
    · rw [h0, norm_zero] at hz1; exact zero_ne_one hz1
    · rw [cellDir_cellSphereToDisk]
      exact hfz ▸ hy

theorem mem_of_clsPt (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {U : Set Y} {a : Y ⊕ (Σ _ : ι, cellDisk n)} {y : Y}
    (ha : clsPt n Y ι f a y) (h : a ∈ satSet n Y ι f U) : y ∈ U := by
  rcases h with ⟨y', hy', rfl⟩ | ⟨i, x, rfl, hx, hfx⟩
  · rcases ha with h1 | ⟨i, z, h2, -⟩
    · exact (Sum.inl.inj h1) ▸ hy'
    · exact absurd h2 Sum.inl_ne_inr
  · rcases ha with h1 | ⟨i₂, z, h2, h3⟩
    · exact absurd h1 Sum.inr_ne_inl
    · have hh : (⟨i, x⟩ : Σ _ : ι, cellDisk n) = ⟨i₂, cellSphereToDisk n z⟩ :=
        Sum.inr.inj h2
      have h1' : i = i₂ := congrArg Sigma.fst hh
      have h2' : x = cellSphereToDisk n z := congrArg Sigma.snd hh
      subst h1'; subst h2'
      rw [cellDir_cellSphereToDisk] at hfx
      exact h3 ▸ hfx

/-- `satSet` is *saturated* for the gluing relation: it is a union of equivalence classes.  This
holds because a cell interior point is only related to itself, and because for a boundary point
`cellSphereToDisk n z` the radial direction is `z` itself, so the class of `y` is contained in
`satSet` as soon as `y ∈ U`. -/
theorem satSet_saturated (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (U : Set Y) {a b : Y ⊕ (Σ _ : ι, cellDisk n)}
    (hab : Relation.EqvGen (attachRel n Y ι f) a b) (ha : a ∈ satSet n Y ι f U) :
    b ∈ satSet n Y ι f U := by
  rcases (cls_iff n Y ι f a b).mp (AttachRange.eqvGen_le_cls n Y ι f hab) with rfl | ⟨y, h1, h2⟩
  · exact ha
  · exact mem_satSet_of_clsPt n Y ι f h2 (mem_of_clsPt n Y ι f h1 ha)

/-! ### Openness of `satSet` and of its image in the quotient -/

theorem isOpen_satSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {U : Set Y} (hU : IsOpen U) :
    IsOpen (satSet n Y ι f U) := by
  rw [isOpen_sum_iff]
  constructor
  · have h1 : Sum.inl ⁻¹' satSet n Y ι f U = U := by
      ext y
      simp only [Set.mem_preimage, satSet]
      constructor
      · rintro (⟨y', hy', hyy'⟩ | ⟨i, x, hcon, -⟩)
        · exact (Sum.inl.inj hyy') ▸ hy'
        · exact absurd hcon Sum.inl_ne_inr
      · intro hy; exact Or.inl ⟨y, hy, rfl⟩
    rw [h1]; exact hU
  · rw [isOpen_sigma_iff]
    intro i
    have hsub : IsOpen ({x : cellDisk n | (x : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0}) :=
      (isOpen_ne (x := (0 : EuclideanSpace ℝ (Fin (n + 2))))).preimage continuous_subtype_val
    have hcell : IsOpen ((cellDir n) ⁻¹' ((f i) ⁻¹' U)) :=
      (hU.preimage (f i).continuous).preimage (cellDir n).continuous
    have himg := hsub.isOpenMap_subtype_val _ hcell
    convert himg using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro (⟨y, hy, hcon⟩ | ⟨i₂, x₂, hcon, hx₂, hf₂⟩)
      · exact absurd hcon Sum.inr_ne_inl
      · have h1 : i = i₂ := by
          have := Sum.inr.inj hcon
          exact congrArg Sigma.fst this
        have h2 : x = x₂ := by
          have := Sum.inr.inj hcon
          exact congrArg Sigma.snd this
        subst h1; subst h2
        exact ⟨⟨x, hx₂⟩, hf₂, rfl⟩
    · rintro ⟨x', hfx', rfl⟩
      exact Or.inr ⟨i, x', rfl, x'.2, hfx'⟩

/-- The preimage in `Y ⊕ (Σ i, D)` of the image of the saturated set is the saturated set itself. -/
theorem preimage_image_satSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (U : Set Y) :
    Quotient.mk'' ⁻¹' (Quotient.mk'' '' satSet n Y ι f U : Set (attachCells n Y ι f)) =
      satSet n Y ι f U := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := ha
    exact satSet_saturated n Y ι f U (Quotient.exact hba) hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The image of the saturated set is open in `attachCells n Y ι f` (quotient topology). -/
theorem isOpen_quotient_satSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {U : Set Y} (hU : IsOpen U) :
    IsOpen (Quotient.mk'' '' satSet n Y ι f U : Set (attachCells n Y ι f)) := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Y ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Y ι f) :=
    (isQuotientMap_quotient_mk' (X := Y ⊕ (Σ _ : ι, cellDisk n))
      (s := Relation.EqvGen.setoid (attachRel n Y ι f))).isCoinducing
  refine hq.isOpen_preimage.1 ?_
  rw [preimage_image_satSet]
  exact isOpen_satSet n Y ι f hU

/-- The trace of the image of the saturated set on `range attachIncl` is exactly `attachIncl '' U`. -/
theorem attachIncl_preimage_satSet (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (U : Set Y) :
    attachIncl n Y ι f ⁻¹' (Quotient.mk'' '' satSet n Y ι f U :
      Set (attachCells n Y ι f)) = U := by
  ext y
  constructor
  · intro hy
    obtain ⟨b, hb, hby⟩ := hy
    have h1 : Sum.inl y ∈ satSet n Y ι f U :=
      satSet_saturated n Y ι f U (Quotient.exact hby) hb
    rcases h1 with ⟨y', hy', hyy'⟩ | ⟨i, x, hcon, -⟩
    · exact (Sum.inl.inj hyy').symm ▸ hy'
    · exact absurd hcon Sum.inl_ne_inr
  · intro hy
    exact ⟨Sum.inl y, Or.inl ⟨y, hy, rfl⟩, rfl⟩

/-! ### `attachIncl` is an inducing map -/

/-- **The inclusion `Y → attachCells n Y ι f` is an inducing map**: the topology of `Y` is the
topology induced by the inclusion, i.e. the range of `attachIncl` carries the topology of `Y`. -/
theorem isInducing_attachIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) : Topology.IsInducing (attachIncl n Y ι f) := by
  rw [Topology.isInducing_iff]
  refine (TopologicalSpace.ext_iff).2 (fun V => ?_)
  rw [isOpen_induced_iff]
  constructor
  · intro hV
    exact ⟨_, isOpen_quotient_satSet n Y ι f hV, attachIncl_preimage_satSet n Y ι f V⟩
  · rintro ⟨W, hW, hWV⟩
    rw [← hWV]
    exact hW.preimage (attachIncl n Y ι f).continuous

/-- An inducing map's corestriction to its range is an open map (indeed a homeomorphism onto its
range): both the image of an open set and the preimage of an open set of the range are computed by
intersecting with the range. -/
theorem isOpenMap_codRestrict_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsInducing f) :
    IsOpenMap (fun x => (⟨f x, ⟨x, rfl⟩⟩ : ↥(Set.range f))) := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := hf.isOpen_iff.1 hU
  refine (isOpen_induced_iff).2 ⟨V, hV, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx⟩ := p.2
    have hxU : x ∈ U := by
      rw [← hVU]
      simpa [hx] using hp
    exact ⟨x, hxU, Subtype.ext hx⟩
  · rintro ⟨x, hxU, rfl⟩
    have hxV : f x ∈ V := by
      rw [← hVU] at hxU
      simpa using hxU
    exact hxV

/-- **The range of `attachIncl` carries the topology of `Y`.**  The inclusion
`attachIncl n Y ι f` is injective and its image, with the subspace topology from
`attachCells n Y ι f`, is homeomorphic to `Y`.  Concretely: for every open `W ⊆ Y` there is an open
`V ⊆ attachCells n Y ι f` with `V ∩ range attachIncl = attachIncl '' W`.  Proof: a point of a cell
interior is never identified with a point of `Y`, so the equivalence classes of the gluing relation
are the singletons of interior cell points together with the sets
`{y} ∪ {boundary points of cells mapping to y}`; take `V` to be the image in the quotient of the
saturated set `{inl y : y ∈ W} ∪ ⋃_i {inr (i,x) : x ∈ T_i}`, where `T_i ⊆ cellDisk n` is the set of
non-zero points whose radial direction `z` satisfies `f i z ∈ W` (open: the direction map is
continuous on the punctured disc).  This saturated set is open (it is open in both parts of the
disjoint union), so `V` is open in the quotient, and its trace on the range is exactly
`attachIncl '' W`. -/
theorem attachIncl_isOpenMap_range (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    IsOpenMap fun y : Y =>
      (⟨Work.RatHurewicz.attachIncl n Y ι f y, ⟨y, rfl⟩⟩ :
        ↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f))) :=
  isOpenMap_codRestrict_range (isInducing_attachIncl n Y ι f)

end

end Work.RatHurewicz
