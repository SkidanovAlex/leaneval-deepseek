import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.Geometry
import Submission.Work.Thom.DiscSphereTopology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The normal bundle and the tubular neighbourhood of an embedded manifold

This is the definition layer of the **Tubular** chapter (`Work.Tubular`): the tubular neighbourhood
theorem and the Pontryagin–Thom collapse for a compact smooth `8`-manifold `V` embedded in `ℝ^N`
(the model of the Milnor exotic sphere project: `Work.ThomBordism.Man8` and the embedding data
`Work.ThomBordism.PontryaginThom.EmbeddingData`).

* `Work.Tubular.tangentSpace` — the tangent space `T_x` of the image of the embedding, i.e. the
  range of the Fréchet derivative `mfderiv`;
* `Work.Tubular.normalSpace` — the **normal space** `ν_x = T_xᗮ`, the orthogonal complement in the
  ambient inner product space `ℝ^N`;
* `Work.Tubular.NormalTotal` — the **normal total space** `ν = {(x,w) : x ∈ V, w ∈ ν_x}`, a closed
  subspace of `V.pt × ℝ^N`: this is the concrete model of the normal bundle, and the total space of
  the gluing-data bundle `Work.Tubular.NormalBundle` (with which it is identified);
* `Work.Tubular.normalNorm`, `tubeMap` — the fibrewise norm and the **tubular map**
  `(x,w) ↦ e x + w`;
* `Work.Tubular.normalDiscSet` / `normalClosedDiscSet` / `normalSphereSet` and the disc/sphere
  bundles `NormalDiscSub` / `NormalSphSub`, the quotient `NormalThomSpace` (the Thom space of `ν`)
  with `normalThomMk` and the basepoint;
* `Work.Tubular.TubeChart` — **the tubular neighbourhood theorem**, in the closed-disc form in which
  it is used: a radius `ε > 0`, a closed neighbourhood `U ⊇ e(V)` whose points are exactly the
  images of the closed `ε`-disc bundle under `tubeMap`, with a continuous inverse `inv`, together
  with the two facts that make the open part well behaved (its openness) and smooth (the inverse is
  `C^∞` on `U`);
* `Work.Tubular.HasTubularNeighbourhood` — the existence statement.
-/

open scoped Manifold ContDiff Topology
open Function Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

/-- `ℝⁿ`: the ambient Euclidean space. -/
abbrev Euc (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-! ## The tangent and normal spaces -/

/-- The **tangent space** at `x` of the image of the embedding `E`: the range of the Fréchet
derivative of `E.e` at `x`.  (For a manifold, `mfderiv` is the derivative read in the charts of
`V.pt`; the range is a subspace of the ambient `ℝ^N` because the target model is a vector space.) -/
def tangentSpace (E : EmbeddingData V N) (x : V.pt) : Submodule ℝ (Euc N) :=
  (mfderiv (𝓡 8) 𝓘(ℝ, Euc N) E.e x).toLinearMap.range

/-- The **normal space** at `x` of the image of the embedding `E`: the orthogonal complement of the
tangent space `T_x` in the ambient `ℝ^N`.  This is the fibre over `x` of the normal bundle. -/
def normalSpace (E : EmbeddingData V N) (x : V.pt) : Submodule ℝ (Euc N) :=
  (tangentSpace E x)ᗮ

@[simp] theorem mem_normalSpace_iff {E : EmbeddingData V N} {x : V.pt} {w : Euc N} :
    w ∈ normalSpace E x ↔ ∀ u ∈ tangentSpace E x, inner ℝ u w = 0 :=
  Submodule.mem_orthogonal (tangentSpace E x) w

/-- A vector of the normal space is orthogonal to every vector of the tangent space. -/
theorem inner_eq_zero_of_mem_normalSpace {E : EmbeddingData V N} {x : V.pt} {w : Euc N}
    (hw : w ∈ normalSpace E x) {u : Euc N} (hu : u ∈ tangentSpace E x) : inner ℝ u w = 0 :=
  (mem_normalSpace_iff.1 hw) u hu

/-- A vector of the tangent space is orthogonal to every vector of the normal space. -/
theorem inner_eq_zero_of_mem_tangentSpace {E : EmbeddingData V N} {x : V.pt} {u : Euc N}
    (hu : u ∈ tangentSpace E x) {w : Euc N} (hw : w ∈ normalSpace E x) : inner ℝ w u = 0 := by
  rw [real_inner_comm]
  exact inner_eq_zero_of_mem_normalSpace hw hu

/-- The tangent and the normal space are complementary: the ambient space is their direct sum. -/
theorem tangentSpace_sup_normalSpace (E : EmbeddingData V N) (x : V.pt) :
    tangentSpace E x ⊔ normalSpace E x = ⊤ := by
  rw [normalSpace]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- The tangent and the normal space have trivial intersection. -/
theorem tangentSpace_inf_normalSpace (E : EmbeddingData V N) (x : V.pt) :
    tangentSpace E x ⊓ normalSpace E x = ⊥ := by
  rw [normalSpace]
  exact Submodule.inf_orthogonal_eq_bot (tangentSpace E x)

/-! ## The normal total space -/

/-- The **normal total space** of the embedding `E`: the points `(x,w)` with `x ∈ V.pt` and `w` in
the normal space at `x`.  This is a closed subspace of `V.pt × ℝ^N`, and is the concrete model of
the normal bundle `ν` of `E` (the gluing-data bundle `Work.Tubular.NormalBundleData` is identified
with it by `Work.Tubular.normalTotalIso`). -/
abbrev NormalTotal (E : EmbeddingData V N) : Type _ :=
  { p : V.pt × Euc N // p.2 ∈ normalSpace E p.1 }

namespace NormalTotal

variable {E : EmbeddingData V N}

@[ext] theorem ext {p q : NormalTotal E} (h : p.1 = q.1) : p = q := Subtype.ext h

/-- The base point of a point of the normal total space. -/
def proj (p : NormalTotal E) : V.pt := p.1.1

/-- The normal vector of a point of the normal total space. -/
def vec (p : NormalTotal E) : Euc N := p.1.2

@[simp] theorem proj_mk (x : V.pt) (w : Euc N) (hw : w ∈ normalSpace E x) :
    proj (⟨(x, w), hw⟩ : NormalTotal E) = x := rfl

@[simp] theorem vec_mk (x : V.pt) (w : Euc N) (hw : w ∈ normalSpace E x) :
    vec (⟨(x, w), hw⟩ : NormalTotal E) = w := rfl

@[simp] theorem eta (p : NormalTotal E) : (⟨(p.proj, p.vec), p.2⟩ : NormalTotal E) = p := rfl

/-- The normal vector of a point of the normal total space is normal. -/
theorem vec_mem (p : NormalTotal E) : p.vec ∈ normalSpace E p.proj := p.2

/-- The projection to the base is continuous. -/
theorem continuous_proj (E : EmbeddingData V N) : Continuous (proj (E := E)) :=
  continuous_subtype_val.fst

/-- The normal vector is continuous. -/
theorem continuous_vec (E : EmbeddingData V N) : Continuous (vec (E := E)) :=
  continuous_subtype_val.snd

end NormalTotal

/-- The **fibrewise norm** of the normal bundle: the Euclidean norm of the normal vector. -/
def normalNorm (E : EmbeddingData V N) (p : NormalTotal E) : ℝ := ‖p.1.2‖

@[simp] theorem normalNorm_mk (E : EmbeddingData V N) (x : V.pt) (w : Euc N)
    (hw : w ∈ normalSpace E x) : normalNorm E (⟨(x, w), hw⟩ : NormalTotal E) = ‖w‖ := rfl

theorem continuous_normalNorm (E : EmbeddingData V N) : Continuous (normalNorm E) :=
  NormalTotal.continuous_vec E |>.norm

theorem normalNorm_nonneg (E : EmbeddingData V N) (p : NormalTotal E) : 0 ≤ normalNorm E p :=
  norm_nonneg _

/-- **The tubular map** `(x,w) ↦ e x + w`: a point of the normal bundle is sent to the corresponding
point of the ambient space. -/
def tubeMap (E : EmbeddingData V N) (p : NormalTotal E) : Euc N := E.e p.1.1 + p.1.2

@[simp] theorem tubeMap_mk (E : EmbeddingData V N) (x : V.pt) (w : Euc N)
    (hw : w ∈ normalSpace E x) : tubeMap E (⟨(x, w), hw⟩ : NormalTotal E) = E.e x + w := rfl

/-- The tubular map sends the zero section to the embedding. -/
theorem tubeMap_zeroSection (E : EmbeddingData V N) (x : V.pt) :
    tubeMap E (⟨(x, 0), by simp⟩ : NormalTotal E) = E.e x := by
  simp

/-- The tubular map is continuous. -/
theorem continuous_tubeMap (E : EmbeddingData V N) : Continuous (tubeMap E) :=
  ((E.smooth.continuous.comp (NormalTotal.continuous_proj E)).add
    (NormalTotal.continuous_vec E))

/-! ## The disc bundle, the sphere bundle and the Thom space of the normal bundle -/

/-- The open `ε`-**disc bundle** of the normal bundle, as a subset of the normal total space. -/
def normalDiscSet (E : EmbeddingData V N) (ε : ℝ) : Set (NormalTotal E) :=
  {p | normalNorm E p < ε}

/-- The closed `ε`-**disc bundle** of the normal bundle. -/
def normalClosedDiscSet (E : EmbeddingData V N) (ε : ℝ) : Set (NormalTotal E) :=
  {p | normalNorm E p ≤ ε}

/-- The `ε`-**sphere bundle** of the normal bundle. -/
def normalSphereSet (E : EmbeddingData V N) (ε : ℝ) : Set (NormalTotal E) :=
  {p | normalNorm E p = ε}

@[simp] theorem mem_normalDiscSet {E : EmbeddingData V N} {ε : ℝ} {p : NormalTotal E} :
    p ∈ normalDiscSet E ε ↔ normalNorm E p < ε := Iff.rfl

@[simp] theorem mem_normalClosedDiscSet {E : EmbeddingData V N} {ε : ℝ} {p : NormalTotal E} :
    p ∈ normalClosedDiscSet E ε ↔ normalNorm E p ≤ ε := Iff.rfl

@[simp] theorem mem_normalSphereSet {E : EmbeddingData V N} {ε : ℝ} {p : NormalTotal E} :
    p ∈ normalSphereSet E ε ↔ normalNorm E p = ε := Iff.rfl

theorem normalSphereSet_subset_closedDiscSet {E : EmbeddingData V N} {ε : ℝ} :
    normalSphereSet E ε ⊆ normalClosedDiscSet E ε :=
  fun _ h => le_of_eq (mem_normalSphereSet.1 h)

theorem normalDiscSet_subset_closedDiscSet {E : EmbeddingData V N} {ε : ℝ} :
    normalDiscSet E ε ⊆ normalClosedDiscSet E ε :=
  fun _ h => le_of_lt (mem_normalDiscSet.1 h)

/-- The **closed `ε`-disc bundle** `D_ε(ν)`, as a topological subspace of the normal total space. -/
abbrev NormalDiscSub (E : EmbeddingData V N) (ε : ℝ) : Type _ :=
  {p : NormalTotal E // p ∈ normalClosedDiscSet E ε}

/-- The **`ε`-sphere bundle** `S_ε(ν)`, as a topological subspace of the normal total space. -/
abbrev NormalSphSub (E : EmbeddingData V N) (ε : ℝ) : Type _ :=
  {p : NormalTotal E // p ∈ normalSphereSet E ε}

/-- Membership in the sphere bundle, read in the closed disc bundle. -/
def normalSphereInDisc (E : EmbeddingData V N) (ε : ℝ) : Set (NormalDiscSub E ε) :=
  {q | (q : NormalTotal E) ∈ normalSphereSet E ε}

@[simp] theorem mem_normalSphereInDisc {E : EmbeddingData V N} {ε : ℝ} (q : NormalDiscSub E ε) :
    q ∈ normalSphereInDisc E ε ↔ ((q : NormalTotal E) ∈ normalSphereSet E ε) := Iff.rfl

/-- The setoid collapsing the sphere bundle inside the disc bundle: the Thom space of the normal
bundle is `D_ε(ν) / S_ε(ν)`. -/
def normalThomSetoid (E : EmbeddingData V N) (ε : ℝ) : Setoid (NormalDiscSub E ε) where
  r q q' := q = q' ∨ (q ∈ normalSphereInDisc E ε ∧ q' ∈ normalSphereInDisc E ε)
  iseqv :=
    { refl := fun q => Or.inl rfl
      symm := fun {q q'} h => by
        rcases h with h | ⟨h1, h2⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨h2, h1⟩
      trans := fun {q q' q''} h h' => by
        rcases h with h | ⟨h1, h2⟩
        · exact h ▸ h'
        · rcases h' with h' | ⟨h1', h2'⟩
          · exact Or.inr ⟨h1, h'.symm ▸ h2⟩
          · exact Or.inr ⟨h1, h2'⟩ }

/-- **The Thom space of the normal bundle**: `Th(ν) = D_ε(ν)/S_ε(ν)`. -/
def NormalThomSpace (E : EmbeddingData V N) (ε : ℝ) : Type _ :=
  Quotient (normalThomSetoid E ε)

instance (E : EmbeddingData V N) (ε : ℝ) : TopologicalSpace (NormalThomSpace E ε) :=
  inferInstanceAs (TopologicalSpace (Quotient (normalThomSetoid E ε)))

/-- The quotient map `D_ε(ν) → Th(ν)`. -/
def normalThomMk (E : EmbeddingData V N) (ε : ℝ) (q : NormalDiscSub E ε) : NormalThomSpace E ε :=
  Quotient.mk'' q

theorem continuous_normalThomMk (E : EmbeddingData V N) (ε : ℝ) :
    Continuous (normalThomMk E ε) := by
  unfold normalThomMk
  exact continuous_quot_mk

/-- Two points of the disc bundle have the same image in the Thom space exactly when they are equal
or both lie on the sphere bundle. -/
theorem normalThomMk_eq_iff {E : EmbeddingData V N} {ε : ℝ} (q q' : NormalDiscSub E ε) :
    normalThomMk E ε q = normalThomMk E ε q' ↔
      q = q' ∨ (q ∈ normalSphereInDisc E ε ∧ q' ∈ normalSphereInDisc E ε) :=
  Quotient.eq''

/-- The image in the Thom space of a point of the sphere bundle. -/
def normalThomBasepoint (E : EmbeddingData V N) (ε : ℝ) (q : NormalSphSub E ε) :
    NormalThomSpace E ε :=
  normalThomMk E ε ⟨q.1, le_of_eq q.2⟩

/-- All points of the sphere bundle have the same image in the Thom space. -/
theorem normalThomBasepoint_eq {E : EmbeddingData V N} {ε : ℝ} (q q' : NormalSphSub E ε) :
    normalThomBasepoint E ε q = normalThomBasepoint E ε q' := by
  refine (normalThomMk_eq_iff _ _).2 (Or.inr ⟨?_, ?_⟩)
  · change normalNorm E (q : NormalTotal E) = ε
    exact q.2
  · change normalNorm E (q' : NormalTotal E) = ε
    exact q'.2

/-- The basepoint of the Thom space, given any point of the sphere bundle. -/
def normalBasepoint (E : EmbeddingData V N) (ε : ℝ) (q : NormalSphSub E ε) : NormalThomSpace E ε :=
  normalThomBasepoint E ε q

/-- A point of the disc bundle not on the sphere does not map to the basepoint. -/
theorem normalThomMk_ne_basepoint {E : EmbeddingData V N} {ε : ℝ} {q : NormalDiscSub E ε}
    (hq : q ∉ normalSphereInDisc E ε) (q' : NormalSphSub E ε) :
    normalThomMk E ε q ≠ normalThomBasepoint E ε q' := by
  intro h
  rcases (normalThomMk_eq_iff q ⟨q'.1, le_of_eq q'.2⟩).1 h with h' | ⟨h1, -⟩
  · exact hq (by rw [h']; exact q'.2)
  · exact hq h1

/-! ## The tubular neighbourhood theorem -/

/-- **The open tube of radius `ε`**: the image of the open `ε`-disc bundle of the normal bundle under
the tubular map.  This is the set on which the tubular map is a *diffeomorphism*; it is an open
neighbourhood of the image of `E` (both facts are fields of `TubeChart`). -/
def openTubeSet (E : EmbeddingData V N) (ε : ℝ) : Set (Euc N) :=
  tubeMap E '' {p : NormalTotal E | normalNorm E p < ε}

theorem openTubeSet_eq (E : EmbeddingData V N) (ε : ℝ) :
    openTubeSet E ε = tubeMap E '' {p : NormalTotal E | normalNorm E p < ε} := rfl

/-- **The tubular neighbourhood theorem for `E : V ↪ ℝ^N`**, in the closed-disc form in which the
chapter uses it.

There are a radius `ε > 0` and a closed set `U ⊆ ℝ^N` such that the tubular map
`(x,w) ↦ e x + w` maps the closed `ε`-disc bundle of the normal bundle *bijectively* onto `U`, with
continuous inverse `inv`; equivalently `inv` is the "normal foot" of a point of `U`.

The extra fields record the two facts about the **open** part `tubeMap '' {‖w‖ < ε}` that the
applications need: it is open in `ℝ^N` (so it is a genuine neighbourhood of `e(V)`, and the tube map
is a homeomorphism of the open disc bundle onto it), and the inverse is `C^∞` there (so the tube map
is a diffeomorphism). -/
structure TubeChart (E : EmbeddingData V N) (ε : ℝ) where
  /-- the radius is positive -/
  eps_pos : 0 < ε
  /-- the closed tube: the image of the closed `ε`-disc bundle -/
  U : Set (Euc N)
  /-- the tube is closed -/
  isClosed_U : IsClosed U
  /-- the inverse of the tubular map on the tube: the normal foot of a point -/
  inv : Euc N → NormalTotal E
  /-- the normal foot of a point of the tube has norm at most `ε` -/
  inv_mem : ∀ y ∈ U, normalNorm E (inv y) ≤ ε
  /-- `inv` is a right inverse of the tubular map on the tube -/
  tubeMap_inv : ∀ y ∈ U, tubeMap E (inv y) = y
  /-- the closed disc bundle lands in the tube -/
  mem_U : ∀ p : NormalTotal E, normalNorm E p ≤ ε → tubeMap E p ∈ U
  /-- `inv` is a left inverse of the tubular map on the closed disc bundle -/
  inv_tubeMap : ∀ p : NormalTotal E, normalNorm E p ≤ ε → inv (tubeMap E p) = p
  /-- `inv` is continuous -/
  continuousOn_inv : ContinuousOn inv U
  /-- the image of the **open** disc bundle is open in the ambient space -/
  isOpen_openTube : IsOpen (openTubeSet E ε)
  /-- the inverse is smooth, so the tubular map is a diffeomorphism of the open disc bundle onto the
  open tube -/
  contMDiffOn_inv : ContMDiffOn 𝓘(ℝ, Euc N) ((𝓡 8).prod 𝓘(ℝ, Euc N)) ∞
    (fun y => ((inv y).1.1, (inv y).1.2)) (openTubeSet E ε)

namespace TubeChart

variable {E : EmbeddingData V N} {ε : ℝ}

/-- The open tube of a `TubeChart`: the image of the open `ε`-disc bundle, a neighbourhood of `e(V)`
in the ambient space. -/
def openTube (_C : TubeChart E ε) : Set (Euc N) :=
  tubeMap E '' {p : NormalTotal E | normalNorm E p < ε}

theorem openTube_isOpen (C : TubeChart E ε) : IsOpen C.openTube := C.isOpen_openTube

theorem openTube_eq (C : TubeChart E ε) :
    C.openTube = {y ∈ C.U | normalNorm E (C.inv y) < ε} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨C.mem_U p (le_of_lt hp), by rw [C.inv_tubeMap p (le_of_lt hp)]; exact hp⟩
  · rintro ⟨hyU, hy⟩
    exact ⟨C.inv y, hy, C.tubeMap_inv y hyU⟩

/-- The closed disc bundle maps onto the tube. -/
theorem image_closedDiscSet (C : TubeChart E ε) :
    tubeMap E '' {p : NormalTotal E | normalNorm E p ≤ ε} = C.U := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact C.mem_U p hp
  · intro y hy
    exact ⟨C.inv y, C.inv_mem y hy, C.tubeMap_inv y hy⟩

/-- The open tube is contained in the (closed) tube. -/
theorem openTube_subset_U (C : TubeChart E ε) : C.openTube ⊆ C.U :=
  fun _ ⟨p, hp, hpy⟩ => hpy ▸ C.mem_U p (le_of_lt hp)

/-- The embedding lands in the open tube. -/
theorem mem_openTube (C : TubeChart E ε) (x : V.pt) : E.e x ∈ C.openTube :=
  ⟨⟨(x, 0), by simp⟩, by simpa using C.eps_pos, by simp⟩

/-- The embedding lands in the tube. -/
theorem zero_mem_U (C : TubeChart E ε) (x : V.pt) : E.e x ∈ C.U := by
  simpa [← image_closedDiscSet C] using
    (show E.e x ∈ tubeMap E '' {p : NormalTotal E | normalNorm E p ≤ ε} from
      ⟨⟨(x, 0), by simp⟩, by simp [C.eps_pos.le], by simp⟩)

end TubeChart

/-- **The tubular neighbourhood theorem** for `E : V ↪ ℝ^N`. -/
def HasTubularNeighbourhood (E : EmbeddingData V N) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ Nonempty (TubeChart E ε)

end

end Work.Tubular
