import Mathlib
import Submission.Work.TangentClasses.Bundle
import Submission.Work.TangentClasses.Tangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The disc bundle, the sphere bundle and the Thom space of a real vector bundle

This is the geometric layer of the Thom chapter.  It builds on the gluing-data model of real
vector bundles of `Submission/Work/TangentClasses/Bundle.lean`
(`Work.TangentClasses.RealBundle B F ι = VectorBundleCore ℝ B F ι`) and adds

* `Work.Thom.IsEuclidean Z` — the structure that makes the unit disc and unit sphere well defined:
  every transition function preserves the fibre norm (a "Euclidean" bundle; equivalently, the
  fibrewise norm is independent of the trivialisation used to compute it,
  `Work.Thom.fibreNorm_localTriv`);
* `Work.Thom.discSet Z`, `Work.Thom.sphereSet Z`, `Work.Thom.closedDiscSet Z` — the open unit disc,
  the unit sphere, and the closed unit disc of `E` (subsets of the total space `Z.TotalSpace`);
* `Work.Thom.DiscSub Z` — the **closed disc bundle** `D(E)`, as a subspace of the total space, and
  `Work.Thom.sphereInDisc Z ⊆ DiscSub Z` — the **sphere bundle** `S(E)` as its boundary;
* `Work.Thom.zeroComplement Z = {p | p.2 ≠ 0}` — the complement of the zero section, the other
  standard model of the pair whose cohomology carries the Thom class (`H^n(E,E∖0) ≅ H^n(D E,S E)`);
* `Work.Thom.ThomSpace Z` — the **Thom space** `Th(E) = D(E)/S(E)`, with its quotient map
  `thomMk` and its basepoint;
* `Work.Thom.zeroSection Z : C(B, Z.TotalSpace)` and `Work.Thom.zeroSectionDisc Z : C(B, D(E))` —
  the zero section, whose pullback of the Thom class is the Euler class.

The two topological facts about these sets (that `discSet` is open, that `closedDiscSet` is closed —
so that `S(E)` is closed in `D(E)` and the Thom space is a genuine quotient of a good pair) are in
`Submission/Work/Thom/DiscSphereTopology.lean`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle

noncomputable section

variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}

/-! ## Euclidean bundles -/

/-- **A Euclidean real bundle**: a real bundle whose transition functions preserve the fibre
norm.  This is the structure that makes the fibrewise norm — and hence the disc and sphere
bundles — well defined without choosing trivialisations: on the overlap `baseSet i ∩ baseSet j`
the two trivialisations give the same norm, `Work.Thom.fibreNorm_localTriv`. -/
def IsEuclidean (Z : RealBundle B F ι) : Prop :=
  ∀ i j (x : B), x ∈ Z.baseSet i ∩ Z.baseSet j → ∀ v : F, ‖Z.coordChange i j x v‖ = ‖v‖

/-- The norm of a vector of the bundle, in the fibre over its base point.  (Written out with an
explicit type ascription because the fibre `Z.Fiber x` is only reducibly equal to the model fibre
`F`, which type class search does not unfold.) -/
def fibreNorm (Z : RealBundle B F ι) (p : Z.TotalSpace) : ℝ :=
  ‖(show F from (p.2 : Z.Fiber p.1))‖

@[simp] theorem fibreNorm_mk (Z : RealBundle B F ι) (x : B) (v : F) :
    fibreNorm Z (⟨x, v⟩ : Z.TotalSpace) = ‖v‖ := rfl

/-- The fibrewise norm is homogeneous: `fibreNorm` of a scaled vector is `|c|` times the norm. -/
theorem fibreNorm_smul {Z : RealBundle B F ι} (x : B) (c : ℝ) (v : F) :
    fibreNorm Z (⟨x, c • v⟩ : Z.TotalSpace) = |c| * fibreNorm Z (⟨x, v⟩ : Z.TotalSpace) := by
  simp only [fibreNorm_mk, norm_smul, Real.norm_eq_abs]

/-- **The fibrewise norm is independent of the trivialisation**: in a Euclidean bundle, reading a
vector in the chart `i` does not change its norm. -/
theorem fibreNorm_localTriv {Z : RealBundle B F ι} (hZ : IsEuclidean Z) (i : ι) (p : Z.TotalSpace)
    (hp : p.1 ∈ Z.baseSet i) : fibreNorm Z p = ‖(Z.localTriv i p).2‖ := by
  have h := hZ (Z.indexAt p.1) i p.1 ⟨Z.mem_baseSet_at p.1, hp⟩
    (show F from (p.2 : Z.Fiber p.1))
  rw [fibreNorm, VectorBundleCore.localTriv_apply]
  exact h.symm

/-- The fibrewise norm is unchanged when read in the *preferred* chart of the base point. -/
theorem fibreNorm_localTrivAt {Z : RealBundle B F ι} (hZ : IsEuclidean Z) (p : Z.TotalSpace) :
    fibreNorm Z p = ‖(Z.localTrivAt p.1 p).2‖ :=
  fibreNorm_localTriv hZ (Z.indexAt p.1) p (Z.mem_baseSet_at p.1)

/-- The trivial bundle is Euclidean. -/
theorem isEuclidean_trivial (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : Type*) [Inhabited ι] : IsEuclidean (RealBundle.trivial B F ι) := by
  intro i j x hx v
  simp

/-- The pullback of a Euclidean bundle is Euclidean. -/
theorem IsEuclidean.pullback {Z : RealBundle B F ι} (hZ : IsEuclidean Z) {B' : Type*}
    [TopologicalSpace B'] (f : C(B', B)) : IsEuclidean (Z.pullback f) := by
  intro i j x hx v
  exact hZ i j (f x) hx v

/-- The Whitney sum of two Euclidean bundles is Euclidean (the product norm behaves). -/
private theorem norm_prodMap_eq {a b : Type*} [NormedAddCommGroup a] [NormedAddCommGroup b]
    (f : a → a) (g : b → b) (hf : ∀ w, ‖f w‖ = ‖w‖) (hg : ∀ w, ‖g w‖ = ‖w‖) (v : a × b) :
    ‖(f v.1, g v.2)‖ = ‖v‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  simp [hf, hg]

theorem IsEuclidean.sum {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {ι₁ ι₂ : Type*}
    {Z₁ : RealBundle B F₁ ι₁} {Z₂ : RealBundle B F₂ ι₂}
    (h₁ : IsEuclidean Z₁) (h₂ : IsEuclidean Z₂) : IsEuclidean (Z₁.sum Z₂) := by
  intro i j x hx v
  have h := hx
  rw [RealBundle.sum_baseSet] at h
  rw [RealBundle.sum_coordChange, ContinuousLinearMap.coe_prodMap', Prod.map_apply]
  exact norm_prodMap_eq (fun w => Z₁.coordChange i.1 j.1 x w) (fun w => Z₂.coordChange i.2 j.2 x w)
    (fun w => h₁ i.1 j.1 x ⟨h.1.1, h.2.1⟩ w) (fun w => h₂ i.2 j.2 x ⟨h.1.2, h.2.2⟩ w) v

/-! ## The disc, the sphere and the complement of the zero section -/

/-- The **open unit disc bundle** `D°(E) ⊆ E`. -/
def discSet (Z : RealBundle B F ι) : Set Z.TotalSpace := {p | fibreNorm Z p < 1}

/-- The **unit sphere bundle** `S(E) ⊆ E`. -/
def sphereSet (Z : RealBundle B F ι) : Set Z.TotalSpace := {p | fibreNorm Z p = 1}

/-- The **closed unit disc bundle** `D(E) ⊆ E`. -/
def closedDiscSet (Z : RealBundle B F ι) : Set Z.TotalSpace := {p | fibreNorm Z p ≤ 1}

/-- The complement of the zero section, `E ∖ 0·B`: the pair `(E,E∖0)` is the other standard model
of the pair whose cohomology carries the Thom class. -/
def zeroComplement (Z : RealBundle B F ι) : Set Z.TotalSpace := {p | (show F from p.2) ≠ 0}

@[simp] theorem mem_discSet {Z : RealBundle B F ι} (p : Z.TotalSpace) :
    p ∈ discSet Z ↔ fibreNorm Z p < 1 := Iff.rfl

@[simp] theorem mem_sphereSet {Z : RealBundle B F ι} (p : Z.TotalSpace) :
    p ∈ sphereSet Z ↔ fibreNorm Z p = 1 := Iff.rfl

@[simp] theorem mem_closedDiscSet {Z : RealBundle B F ι} (p : Z.TotalSpace) :
    p ∈ closedDiscSet Z ↔ fibreNorm Z p ≤ 1 := Iff.rfl

@[simp] theorem mem_zeroComplement {Z : RealBundle B F ι} (p : Z.TotalSpace) :
    p ∈ zeroComplement Z ↔ (show F from p.2) ≠ 0 := Iff.rfl

/-- Membership in the disc bundle is read in any chart of a Euclidean bundle. -/
theorem mem_discSet_iff {Z : RealBundle B F ι} (hZ : IsEuclidean Z) (i : ι) (p : Z.TotalSpace)
    (hp : p.1 ∈ Z.baseSet i) : p ∈ discSet Z ↔ ‖(Z.localTriv i p).2‖ < 1 := by
  rw [mem_discSet, fibreNorm_localTriv hZ i p hp]

/-- Membership in the sphere bundle is read in any chart of a Euclidean bundle. -/
theorem mem_sphereSet_iff {Z : RealBundle B F ι} (hZ : IsEuclidean Z) (i : ι) (p : Z.TotalSpace)
    (hp : p.1 ∈ Z.baseSet i) : p ∈ sphereSet Z ↔ ‖(Z.localTriv i p).2‖ = 1 := by
  rw [mem_sphereSet, fibreNorm_localTriv hZ i p hp]

/-- Membership in the closed disc bundle is read in any chart of a Euclidean bundle. -/
theorem mem_closedDiscSet_iff {Z : RealBundle B F ι} (hZ : IsEuclidean Z) (i : ι) (p : Z.TotalSpace)
    (hp : p.1 ∈ Z.baseSet i) : p ∈ closedDiscSet Z ↔ ‖(Z.localTriv i p).2‖ ≤ 1 := by
  rw [mem_closedDiscSet, fibreNorm_localTriv hZ i p hp]

theorem sphereSet_subset_closedDiscSet (Z : RealBundle B F ι) :
    sphereSet Z ⊆ closedDiscSet Z := by
  intro p hp
  rw [mem_sphereSet] at hp
  rw [mem_closedDiscSet]
  rw [hp]

theorem discSet_subset_closedDiscSet (Z : RealBundle B F ι) :
    discSet Z ⊆ closedDiscSet Z := by
  intro p hp
  rw [mem_discSet] at hp
  rw [mem_closedDiscSet]
  exact le_of_lt hp

@[simp] theorem mem_sphereSet_mk {Z : RealBundle B F ι} (x : B) (v : F) :
    (⟨x, v⟩ : Z.TotalSpace) ∈ sphereSet Z ↔ ‖v‖ = 1 := by
  rw [mem_sphereSet, fibreNorm_mk]

@[simp] theorem mem_discSet_mk {Z : RealBundle B F ι} (x : B) (v : F) :
    (⟨x, v⟩ : Z.TotalSpace) ∈ discSet Z ↔ ‖v‖ < 1 := by
  rw [mem_discSet, fibreNorm_mk]

@[simp] theorem mem_closedDiscSet_mk {Z : RealBundle B F ι} (x : B) (v : F) :
    (⟨x, v⟩ : Z.TotalSpace) ∈ closedDiscSet Z ↔ ‖v‖ ≤ 1 := by
  rw [mem_closedDiscSet, fibreNorm_mk]

@[simp] theorem mem_zeroComplement_mk {Z : RealBundle B F ι} (x : B) (v : F) :
    (⟨x, v⟩ : Z.TotalSpace) ∈ zeroComplement Z ↔ v ≠ 0 := by
  rw [mem_zeroComplement]

/-! ## The closed disc bundle, the sphere bundle inside it, and the zero section -/

/-- The **closed disc bundle** `D(E)`, as a topological subspace of the total space. -/
abbrev DiscSub (Z : RealBundle B F ι) : Type _ := {p : Z.TotalSpace // p ∈ closedDiscSet Z}

/-- The **sphere bundle** `S(E)`, as a topological subspace of the total space. -/
abbrev SphSub (Z : RealBundle B F ι) : Type _ := {p : Z.TotalSpace // p ∈ sphereSet Z}

/-- The sphere bundle, as a subset of the closed disc bundle. -/
def sphereInDisc (Z : RealBundle B F ι) : Set (DiscSub Z) :=
  {q | (q : Z.TotalSpace) ∈ sphereSet Z}

@[simp] theorem mem_sphereInDisc {Z : RealBundle B F ι} (q : DiscSub Z) :
    q ∈ sphereInDisc Z ↔ ((q : Z.TotalSpace) ∈ sphereSet Z) := Iff.rfl

/-- The **zero section** `B → E`, as a continuous map (Mathlib's
`Bundle.Trivialization.continuous_zeroSection`). -/
def zeroSection (Z : RealBundle B F ι) : C(B, Z.TotalSpace) :=
  ⟨Bundle.zeroSection F Z.Fiber, Bundle.Trivialization.continuous_zeroSection ℝ⟩

@[simp] theorem zeroSection_apply (Z : RealBundle B F ι) (x : B) :
    (zeroSection Z x : Z.TotalSpace) = ⟨x, 0⟩ := rfl

@[simp] theorem zeroSection_snd (Z : RealBundle B F ι) (x : B) :
    (show F from (zeroSection Z x).2) = 0 := rfl

@[simp] theorem zeroSection_fst (Z : RealBundle B F ι) (x : B) : (zeroSection Z x).1 = x := rfl

theorem zeroSection_mem_closedDiscSet (Z : RealBundle B F ι) (x : B) :
    zeroSection Z x ∈ closedDiscSet Z := by
  rw [zeroSection_apply, mem_closedDiscSet_mk]
  simp

theorem zeroSection_mem_zeroComplement_iff (Z : RealBundle B F ι) (x : B) :
    zeroSection Z x ∈ zeroComplement Z ↔ (0 : F) ≠ 0 := by
  rw [zeroSection_apply, mem_zeroComplement_mk]

/-- The zero section is never in the sphere bundle. -/
theorem zeroSection_notMem_sphereSet (Z : RealBundle B F ι) (x : B) :
    zeroSection Z x ∉ sphereSet Z := by
  rw [zeroSection_apply, mem_sphereSet_mk]
  norm_num

/-- The zero section is never in the complement of the zero section. -/
theorem zeroSection_notMem_zeroComplement (Z : RealBundle B F ι) (x : B) :
    zeroSection Z x ∉ zeroComplement Z := by
  rw [zeroSection_apply, mem_zeroComplement_mk]
  simp

/-- The zero section, as a continuous map into the closed disc bundle. -/
def zeroSectionDisc (Z : RealBundle B F ι) : C(B, DiscSub Z) :=
  ⟨fun x => ⟨zeroSection Z x, zeroSection_mem_closedDiscSet Z x⟩,
    (zeroSection Z).continuous.subtype_mk fun x => zeroSection_mem_closedDiscSet Z x⟩

@[simp] theorem zeroSectionDisc_apply (Z : RealBundle B F ι) (x : B) :
    (zeroSectionDisc Z x : Z.TotalSpace) = zeroSection Z x := rfl

theorem zeroSectionDisc_notMem_sphereInDisc (Z : RealBundle B F ι) (x : B) :
    zeroSectionDisc Z x ∉ sphereInDisc Z :=
  zeroSection_notMem_sphereSet Z x

/-! ## The Thom space -/

/-- The setoid collapsing the sphere bundle to a point inside the closed disc bundle: the Thom
space is `D(E)/S(E)`. -/
def thomSetoid (Z : RealBundle B F ι) : Setoid (DiscSub Z) where
  r q q' := q = q' ∨ ((q : Z.TotalSpace) ∈ sphereSet Z ∧ (q' : Z.TotalSpace) ∈ sphereSet Z)
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

/-- **The Thom space** `Th(E) = D(E)/S(E)` of a real vector bundle. -/
def ThomSpace (Z : RealBundle B F ι) : Type _ := Quotient (thomSetoid Z)

instance (Z : RealBundle B F ι) : TopologicalSpace (ThomSpace Z) :=
  inferInstanceAs (TopologicalSpace (Quotient (thomSetoid Z)))

/-- The quotient map `D(E) → Th(E)`. -/
def thomMk (Z : RealBundle B F ι) (q : DiscSub Z) : ThomSpace Z := Quotient.mk'' q

theorem continuous_thomMk (Z : RealBundle B F ι) : Continuous (thomMk Z) := by
  unfold thomMk
  exact continuous_quot_mk

/-- Two points of the disc bundle have the same image in the Thom space exactly when they are equal
or both lie in the sphere bundle. -/
theorem thomMk_eq_thomMk_iff {Z : RealBundle B F ι} (q q' : DiscSub Z) :
    thomMk Z q = thomMk Z q' ↔
      q = q' ∨ (q ∈ sphereInDisc Z ∧ q' ∈ sphereInDisc Z) :=
  Quotient.eq''

/-- The basepoint of the Thom space: the image of any point of the sphere bundle. -/
def IsThomBasepoint (Z : RealBundle B F ι) (y : ThomSpace Z) : Prop :=
  ∃ q : DiscSub Z, q ∈ sphereInDisc Z ∧ thomMk Z q = y

/-- All points of the sphere bundle have the same image in the Thom space. -/
theorem thomMk_eq_of_mem_sphereInDisc {Z : RealBundle B F ι} {q q' : DiscSub Z}
    (hq : q ∈ sphereInDisc Z) (hq' : q' ∈ sphereInDisc Z) : thomMk Z q = thomMk Z q' :=
  (thomMk_eq_thomMk_iff q q').2 (Or.inr ⟨hq, hq'⟩)

/-- A point of the disc bundle not on the sphere is not a basepoint. -/
theorem thomMk_notMem_sphere_ne_basepoint {Z : RealBundle B F ι} {q : DiscSub Z}
    (hq : q ∉ sphereInDisc Z) {y : ThomSpace Z} (hy : IsThomBasepoint Z y) :
    thomMk Z q ≠ y := by
  obtain ⟨q', hq', rfl⟩ := hy
  intro h
  rcases (thomMk_eq_thomMk_iff q q').1 h with he | ⟨h1, -⟩
  · exact hq (he ▸ hq')
  · exact hq h1

end

end Work.Thom
