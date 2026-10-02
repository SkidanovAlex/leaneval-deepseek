import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Transversality to the zero section of a Thom-like target

This is the opening file of the **Transversality** chapter (`Work.ThomBordism.Transversality`), the
part of area THOM that turns a null-homotopy of the Pontryagin–Thom class of a manifold (family)
into a null-bordism of a multiple of it.

The geometry of the Pontryagin–Thom construction happens in the *manifold part* of a Thom space: on
`Th(γ_k) ∖ {∞}` there is a "vertical coordinate" `Φ`, the trivialisation of the normal bundle of
the zero section `G ≅ G̃r_k(ℝ^{k+m})`, which is a submersion along its zero set `Φ ⁻¹' {0} = G`
(the tubular neighbourhood theorem for the zero section).  Everything in this chapter is stated
against that model, `CoreTarget n k`:

* `CoreTarget n k` — a smooth `n`-manifold `E` (in the application the total space of the universal
  oriented `k`-plane bundle) with a smooth map `Φ : E → ℝ^k` which is a submersion along its zero
  set.  The **core** `X.core = Φ ⁻¹' {0}` is the zero section, a closed submanifold of codimension
  `k`;
* `IsTransverseAt X I F x` — `F : M → E` is **transverse to the core at `x`**: either `F x` is off
  the core, or the composite `Φ ∘ F` is a submersion at `x`.

The second is the form of transversality in which *everything is provable from Mathlib's
submersion API*: `Φ` being a submersion along the core means `ker dΦ = T core`, so the standard
condition `im (dF_x) + T_{F x} core = T_{F x} E` is equivalent, after applying `dΦ_{F x}`, to the
surjectivity of `d(Φ ∘ F)_x` — i.e. exactly to `IsSubmersionAt (Φ ∘ F) x`.

## Main definitions

* `Work.ThomBordism.Transversality.CoreTarget`, `.core`
* `Work.ThomBordism.Transversality.IsTransverseAt`, `.IsTransverseOn`, `.IsTransverse`

## Main results

* `isOpen_setOf_isTransverseAt` — transversality is an open condition in the source;
* `IsTransverseOn.exists_isOpen_superset` — transversality on a set extends to a neighbourhood of
  it (so "transverse near the boundary" can be tested on the boundary);
* `isTransverseOn_of_avoid`, `isTransverseAt_of_isSubmersionAt` — the two sufficient conditions
  that make the definition usable (and show it is not vacuous);
* `isTransverseAt_of_eventuallyEq` — transversality is a local property of the map.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality

noncomputable section

/-- **The manifold part of a Thom-like target, with its core.**

`E` is a smooth manifold of dimension `n`; in the application `E = Th(γ_k) ∖ {∞}`, the total space
of the universal oriented `k`-plane bundle over the Grassmannian `G̃r_k(ℝ^{k+m})`.  `Φ : E → ℝ^k`
is the *vertical coordinate* (the trivialisation of the normal bundle of the zero section along
itself), required to be a submersion along its zero set: this is the tubular neighbourhood theorem
for the zero section, and it makes the **core** `X.core = Φ ⁻¹' {0}` — the zero section
`G ≅ G̃r_k(ℝ^{k+m})` — a closed submanifold of `E` of codimension `k`.

(We do not require `Φ` to be a submersion everywhere, only along the core, which is what the
tubular neighbourhood theorem gives.) -/
structure CoreTarget (n k : ℕ) where
  /-- the manifold part of the target -/
  E : Type
  [topologicalSpace : TopologicalSpace E]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) E]
  [isManifold : IsManifold (𝓡 n) ∞ E]
  /-- the vertical coordinate (the trivialisation of the normal bundle of the core) -/
  Φ : E → EuclideanSpace ℝ (Fin k)
  /-- `Φ` is smooth -/
  contMDiff_Φ : ContMDiff (𝓡 n) (𝓡 k) ∞ Φ
  /-- `Φ` is a submersion along its zero set, so the core is a closed submanifold of codimension
  `k` (`ker dΦ = T core`) -/
  isSubmersionAt_Φ : ∀ x : E, Φ x = 0 → IsSubmersionAt (𝓡 n) (𝓡 k) ∞ Φ x

attribute [instance] CoreTarget.topologicalSpace CoreTarget.chartedSpace CoreTarget.isManifold

variable {n k : ℕ}

/-- The **core** of a `CoreTarget`: the zero set of the vertical coordinate, i.e. the zero section
of the universal bundle.  In the application this is `G̃r_k(ℝ^{k+m}) ⊂ Th(γ_k)`. -/
def CoreTarget.core (X : CoreTarget n k) : Set X.E := {x | X.Φ x = 0}

@[simp] theorem CoreTarget.mem_core {X : CoreTarget n k} {x : X.E} :
    x ∈ X.core ↔ X.Φ x = 0 := Iff.rfl

@[simp] theorem CoreTarget.core_eq_preimage (X : CoreTarget n k) :
    X.core = X.Φ ⁻¹' {0} := rfl

/-- **`F` is transverse to the core at `x`.**

Either `F x` is off the core (no condition), or the composite `Φ ∘ F` is a submersion at `x`.  With
`Φ` a submersion along the core (`CoreTarget.isSubmersionAt_Φ`), this is equivalent to the standard
condition that the derivative of `F` at `x` meets the tangent space of the core transversally:
`ker dΦ_{F x} = T_{F x} core`, so applying `dΦ_{F x}` turns
`im (dF_x) + T_{F x} core = T_{F x} E` into the surjectivity of `d(Φ ∘ F)_x`. -/
def IsTransverseAt (X : CoreTarget n k) {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (F : M → X.E) (x : M) : Prop :=
  X.Φ (F x) = 0 → IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Φ (F y)) x

/-! ### What the definition says at a boundary point

`Manifold.IsSubmersionAt` is Mathlib's chart-based normal form: in appropriate charts, the map reads
as the projection `(y, z) ↦ y` on the target of the extended source chart, which is a **relative**
neighbourhood of the image point inside `range I`.  Consequently:

* at an **interior** point of `M` the condition is equivalent to the surjectivity of
  `d(Φ ∘ F)_x`, hence — `Φ` being a submersion along the core — to the classical condition
  `im (dF_x) + T (core) = T E`;
* at a **boundary** point of `M` it is the corresponding "half-space projection" form: `Φ ∘ F`
  reads as `(y, z) ↦ y` on a relative neighbourhood of the boundary point.  This is exactly the
  condition under which the preimage of the core is a manifold *with boundary* at `x`, with
  boundary `∂M ∩ F ⁻¹' core` (the prototype is `M = ` a half-space, `Φ ∘ F = ` the projection onto
  the first `k` coordinates, whose zero set is a half-space inside `M`).

The two forms are *not* interchangeable at boundary points, and `IsSubmersionAt` is *not* closed
under composition there: `Submission/Work/ThomBordism/Transversality/counterexample_comp.lean`
(refutation in `isSubmersionAt_comp_refuted.lean`) exhibits a submersion at a boundary point whose
composite with another submersion fails to be one.  This chapter never composes two submersions: it
applies `IsSubmersionAt` directly to `Φ ∘ F` for the geometric maps `F` of the
Pontryagin–Thom construction. -/

/-- **`F` is transverse to the core on the set `A`.** -/
def IsTransverseOn (X : CoreTarget n k) {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (F : M → X.E) (A : Set M) : Prop :=
  ∀ x ∈ A, IsTransverseAt X I F x

/-- **`F` is transverse to the core.** -/
def IsTransverse (X : CoreTarget n k) {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (F : M → X.E) : Prop :=
  IsTransverseOn X I F univ

/-! ## The API of the definition

The two lemmas `isOpen_setOf_isTransverseAt` and `IsTransverseOn.exists_isOpen_superset` are the
ones the homotopy theorem in `Homotopy.lean` uses: they show that "transverse to the core on `A`"
is the same as "transverse to the core on a neighbourhood of `A`". -/

variable {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem isTransverseAt_def {X : CoreTarget n k} {F : M → X.E} {x : M} :
    IsTransverseAt X I F x ↔ (X.Φ (F x) = 0 → IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Φ (F y)) x) :=
  Iff.rfl

theorem isTransverseOn_def {X : CoreTarget n k} {F : M → X.E} {A : Set M} :
    IsTransverseOn X I F A ↔ ∀ x ∈ A, IsTransverseAt X I F x := Iff.rfl

theorem isTransverse_def {X : CoreTarget n k} {F : M → X.E} :
    IsTransverse X I F ↔ ∀ x : M, IsTransverseAt X I F x :=
  ⟨fun h x => h x trivial, fun h x _ => h x⟩

theorem IsTransverseOn.mono {X : CoreTarget n k} {F : M → X.E} {A B : Set M}
    (h : IsTransverseOn X I F A) (hBA : B ⊆ A) : IsTransverseOn X I F B :=
  fun x hx => h x (hBA hx)

theorem IsTransverseOn.isTransverseAt {X : CoreTarget n k} {F : M → X.E} {A : Set M}
    (h : IsTransverseOn X I F A) {x : M} (hx : x ∈ A) : IsTransverseAt X I F x := h x hx

theorem isTransverse_iff_isTransverseOn_univ {X : CoreTarget n k} {F : M → X.E} :
    IsTransverse X I F ↔ IsTransverseOn X I F univ := Iff.rfl

/-- A map which is a submersion at `x` after composing with the vertical coordinate is transverse
to the core at `x`. -/
theorem isTransverseAt_of_isSubmersionAt {X : CoreTarget n k} {F : M → X.E} {x : M}
    (h : IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Φ (F y)) x) : IsTransverseAt X I F x :=
  fun _ => h

/-- A map which avoids the core is transverse to it: this is the case of a map landing in the
complement of the zero section. -/
theorem isTransverseAt_of_Φ_ne_zero {X : CoreTarget n k} {F : M → X.E} {x : M}
    (h : X.Φ (F x) ≠ 0) : IsTransverseAt X I F x :=
  fun h0 => absurd h0 h

/-- A map which avoids the core is transverse to it on every set. -/
theorem isTransverseOn_of_avoid {X : CoreTarget n k} {F : M → X.E} {A : Set M}
    (h : ∀ x ∈ A, X.Φ (F x) ≠ 0) : IsTransverseOn X I F A :=
  fun x hx => isTransverseAt_of_Φ_ne_zero I (h x hx)

/-- On the preimage of the core, transversality is exactly submersivity of `Φ ∘ F`. -/
theorem isTransverseAt_iff_of_mem_core {X : CoreTarget n k} {F : M → X.E} {x : M}
    (h : X.Φ (F x) = 0) :
    IsTransverseAt X I F x ↔ IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Φ (F y)) x :=
  ⟨fun h' => h' h, fun h' _ => h'⟩

/-- **Transversality is an open condition in the source**: the set of points at which `F` is
transverse to the core is open, as soon as `Φ ∘ F` is continuous. -/
theorem isOpen_setOf_isTransverseAt {X : CoreTarget n k} {F : M → X.E}
    (hF : Continuous fun y => X.Φ (F y)) : IsOpen {x : M | IsTransverseAt X I F x} := by
  have h1 : IsOpen {x : M | X.Φ (F x) ≠ 0} := isOpen_compl_iff.mpr (isClosed_eq hF continuous_const)
  have h2 : IsOpen {x : M | IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Φ (F y)) x} :=
    isOpen_isSubmersionAt
  have h_eq : {x : M | IsTransverseAt X I F x}
      = {x : M | X.Φ (F x) ≠ 0} ∪ {x : M | IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Φ (F y)) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [isTransverseAt_def]
    constructor
    · intro h
      by_cases hx : X.Φ (F x) = 0
      · exact Or.inr (h hx)
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact fun h0 => absurd h0 hx
      · exact fun _ => hx
  rw [h_eq]
  exact h1.union h2

/-- **Transversality on `A` extends to a neighbourhood of `A`.**  (Any open set containing `A`
contains an open neighbourhood of `A`, and the set of transverse points is open.) -/
theorem IsTransverseOn.exists_isOpen_superset {X : CoreTarget n k} {F : M → X.E} {A : Set M}
    (hF : Continuous fun y => X.Φ (F y)) (h : IsTransverseOn X I F A) :
    ∃ U : Set M, A ⊆ U ∧ IsOpen U ∧ IsTransverseOn X I F U := by
  refine ⟨{x : M | IsTransverseAt X I F x}, fun x hx => h x hx,
    isOpen_setOf_isTransverseAt I hF, fun x hx => hx⟩

/-- **Transversality is a local property of the map.** -/
theorem isTransverseAt_of_eventuallyEq {X : CoreTarget n k} {F G : M → X.E} {x : M}
    (h : F =ᶠ[𝓝 x] G) : IsTransverseAt X I F x ↔ IsTransverseAt X I G x := by
  have hΦ : (fun y => X.Φ (F y)) =ᶠ[𝓝 x] (fun y => X.Φ (G y)) := h.fun_comp X.Φ
  rw [isTransverseAt_def, isTransverseAt_def, h.self_of_nhds]
  exact imp_congr_right fun _ => IsSubmersionAt.congr_iff hΦ

theorem isTransverseAt_congr {X : CoreTarget n k} {F G : M → X.E} (h : F = G) {x : M} :
    IsTransverseAt X I F x ↔ IsTransverseAt X I G x := by
  subst h; rfl

/-- The preimage of the core is closed (as soon as `Φ ∘ F` is continuous). -/
theorem isClosed_preimage_core {X : CoreTarget n k} {F : M → X.E}
    (hF : Continuous fun y => X.Φ (F y)) : IsClosed {x : M | X.Φ (F x) = 0} :=
  isClosed_eq hF continuous_const


/-- **The identity map is transverse to the core** (at every point).  This is the consistency check
of the definition: the core `X.core` is a submanifold of codimension `k`, so the map that includes
it (here: the identity of `E`) is transverse to it, and indeed `Φ` is a submersion along the core by
hypothesis. -/
theorem isTransverseAt_id_core (X : CoreTarget n k) (x : X.E) :
    IsTransverseAt X (𝓡 n) (id : X.E → X.E) x :=
  fun h => X.isSubmersionAt_Φ x h

/-- **Transversality on a union of sets**: if `F` is transverse to the core on each `U i`, then it is
transverse on the union (a pointwise statement, no openness needed). -/
theorem isTransverseOn_iUnion {X : CoreTarget n k} {F : M → X.E} {ι : Type} (U : ι → Set M)
    (h : ∀ i, IsTransverseOn X I F (U i)) : IsTransverseOn X I F (⋃ i, U i) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact h i x hi


/-- **The preimage of the core is compact** (when the source is compact): the topological half of the
statement that the transverse preimage is a compact manifold. -/
theorem isCompact_preimage_core {X : CoreTarget n k} {F : M → X.E}
    (hF : Continuous fun y => X.Φ (F y)) [CompactSpace M] :
    IsCompact {x : M | X.Φ (F x) = 0} :=
  (isClosed_eq hF continuous_const).isCompact

end

end Work.ThomBordism.Transversality
