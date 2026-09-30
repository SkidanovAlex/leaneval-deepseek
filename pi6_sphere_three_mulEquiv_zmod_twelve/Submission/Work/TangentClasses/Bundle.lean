import Mathlib

set_option autoImplicit false

/-!
# Real vector bundles over a topological space: the gluing (chart/transition) model

This is the first module of the *tangent-classes* chapter.  It fixes the chapter's notion of a
**real vector bundle**, namely *gluing data*: an open cover of the base, transition functions
between the trivialisations, the cocycle condition — i.e. exactly "charts with transition
functions".  Concretely we use Mathlib's `VectorBundleCore ℝ B F ι`, which is that data:

* `baseSet : ι → Set B`, open, with `indexAt x` a chosen index with `x ∈ baseSet (indexAt x)`;
* `coordChange i j : B → F →L[ℝ] F`, continuous on `baseSet i ∩ baseSet j`, with
  `coordChange i i = 1` and the cocycle `coordChange j k ∘ coordChange i j = coordChange i k`.

A core gives (`VectorBundleCore.vectorBundle`) a `VectorBundle ℝ F Z.Fiber` instance on
`Z.Fiber = fun _ => F`, hence a `FiberBundle`, a topology on the total space `Z.TotalSpace`, a
continuous projection `Z.proj`, and local trivialisations `Z.localTriv i`; all of the Mathlib
bundle API is therefore available.  What this module adds is the chapter's operations on bundles
*at the level of the gluing data*:

* `RealBundle.trivial` — the trivial bundle (all transitions `1`);
* `RealBundle.sum` — the **Whitney sum**: the fibre is `F₁ × F₂` and the transition function over
  `baseSet i ∩ baseSet j` is the block-diagonal `(coordChange i j) × (coordChange i j)`; this is a
  new gluing datum, with the cocycle inherited componentwise;
* `RealBundle.pullback` — the pullback of a bundle along a continuous map `f : C(B', B)`:
  the cover is the preimage cover and the transitions are the transitions composed with `f`
  (functoriality `pullback_id`, `pullback_comp` hold *definitionally*);
* `RealBundle.Iso` — an isomorphism of bundles (a fibrewise continuous linear equivalence), with
  `refl`/`symm`/`trans`/`pullback`, so that a caller can *state* identifications such as
  "`TX` restricted to the disc bundle is `π^*(TS⁴ ⊕ ξ)`".

The tangent bundle `TM` of a smooth manifold is `Submission/Work/TangentClasses/Tangent.lean`;
the Pontryagin classes of a bundle (over `S⁴`, pulled back to any base) are in
`Submission/Work/TangentClasses/Pontryagin.lean`.
-/

namespace Work.TangentClasses

open Bundle

noncomputable section

variable {B : Type*} [TopologicalSpace B]

/-- A **real vector bundle** over a topological space `B`, presented by gluing data (an open cover
and transition functions satisfying the cocycle condition): this is Mathlib's `VectorBundleCore`.
The model fibre is `F` and the index type of the cover is `ι`. -/
abbrev RealBundle (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : Type*) : Type _ := VectorBundleCore ℝ B F ι

namespace RealBundle

variable {F F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {ι ι₁ ι₂ ι₃ : Type*}

/-- The **rank** of a real bundle: the dimension of its fibre. -/
def rank (_Z : RealBundle B F ι) : ℕ := Module.finrank ℝ F

/-- Two gluing data with the same cover, index map and transition functions are equal. -/
@[ext]
theorem ext {Z Z' : RealBundle B F ι} (hbase : Z.baseSet = Z'.baseSet)
    (hindex : Z.indexAt = Z'.indexAt)
    (hcoord : ∀ i j x, Z.coordChange i j x = Z'.coordChange i j x) : Z = Z' := by
  obtain ⟨b, hb, i, hi, c, hc, hcc⟩ := Z
  obtain ⟨b', hb', i', hi', c', hc', hcc'⟩ := Z'
  simp only at hbase hindex hcoord
  subst hbase
  subst hindex
  have hcc : c = c' := by funext p q x; exact hcoord p q x
  subst hcc
  rfl

/-- The fiber of a bundle at `x` (definitionally the model fibre). -/
theorem fiber_eq (Z : RealBundle B F ι) (x : B) : Z.Fiber x = F := rfl

/-- The rank of each fiber is the rank of the bundle. -/
theorem finrank_fiber (Z : RealBundle B F ι) (x : B) : Module.finrank ℝ (Z.Fiber x) = Z.rank :=
  rfl

/-- The projection of the total space of a bundle is continuous. -/
theorem continuous_proj (Z : RealBundle B F ι) : Continuous Z.proj :=
  FiberBundle.continuous_proj F Z.Fiber

/-! ## The trivial bundle -/

/-- The **trivial** real bundle: the whole base is one chart and the transition functions are the
identity. -/
def trivial (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : Type*) [Inhabited ι] : RealBundle B F ι :=
  trivialVectorBundleCore ℝ B F ι

variable {ι₀ : Type*} [Inhabited ι₀]

@[simp] theorem trivial_baseSet (i : ι₀) : (trivial B F ι₀).baseSet i = Set.univ := rfl

@[simp] theorem trivial_indexAt (x : B) : (trivial B F ι₀).indexAt x = default := rfl

@[simp] theorem trivial_coordChange (i j : ι₀) (x : B) :
    (trivial B F ι₀).coordChange i j x = ContinuousLinearMap.id ℝ F := rfl

@[simp] theorem trivial_rank : (trivial B F ι₀).rank = Module.finrank ℝ F := rfl

/-! ## The Whitney sum -/

/-- **Whitney sum (direct sum) of two real bundles.**  Over a common refinement of the two covers
(indexed by `ι₁ × ι₂`) the transition function of the sum is the block-diagonal transition
`(coordChange₁ i i') × (coordChange₂ j j')` on the product fibre `F₁ × F₂`. -/
def sum (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂) :
    RealBundle B (F₁ × F₂) (ι₁ × ι₂) where
  baseSet p := Z₁.baseSet p.1 ∩ Z₂.baseSet p.2
  isOpen_baseSet p := (Z₁.isOpen_baseSet p.1).inter (Z₂.isOpen_baseSet p.2)
  indexAt x := (Z₁.indexAt x, Z₂.indexAt x)
  mem_baseSet_at x := ⟨Z₁.mem_baseSet_at x, Z₂.mem_baseSet_at x⟩
  coordChange p q x := (Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x)
  coordChange_self p x hx v := by
    rw [ContinuousLinearMap.coe_prodMap']
    exact Prod.ext (Z₁.coordChange_self p.1 x hx.1 v.1) (Z₂.coordChange_self p.2 x hx.2 v.2)
  continuousOn_coordChange p q :=
    ((Z₁.continuousOn_coordChange p.1 q.1).mono fun _ hx => ⟨hx.1.1, hx.2.1⟩).prod_mapL ℝ
      ((Z₂.continuousOn_coordChange p.2 q.2).mono fun _ hx => ⟨hx.1.2, hx.2.2⟩)
  coordChange_comp p q r x hx v := by
    rw [ContinuousLinearMap.coe_prodMap', ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.coe_prodMap']
    exact Prod.ext
      (Z₁.coordChange_comp p.1 q.1 r.1 x ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩ v.1)
      (Z₂.coordChange_comp p.2 q.2 r.2 x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩ v.2)

@[simp] theorem sum_baseSet (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂)
    (p : ι₁ × ι₂) : (Z₁.sum Z₂).baseSet p = Z₁.baseSet p.1 ∩ Z₂.baseSet p.2 := rfl

@[simp] theorem sum_indexAt (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂) (x : B) :
    (Z₁.sum Z₂).indexAt x = (Z₁.indexAt x, Z₂.indexAt x) := rfl

@[simp] theorem sum_coordChange (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂)
    (p q : ι₁ × ι₂) (x : B) :
    (Z₁.sum Z₂).coordChange p q x =
      (Z₁.coordChange p.1 q.1 x).prodMap (Z₂.coordChange p.2 q.2 x) := rfl

theorem sum_rank [Module.Finite ℝ F₁] [Module.Finite ℝ F₂]
    (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂) :
    (Z₁.sum Z₂).rank = Z₁.rank + Z₂.rank := by
  rw [rank, rank, rank, Module.finrank_prod]

/-- The sum with the trivial bundle is the "stabilisation" of a bundle. -/
def stabilize (Z : RealBundle B F ι) (k : ℕ) : RealBundle B (F × (Fin k → ℝ)) (ι × ι₀) :=
  Z.sum (trivial B (Fin k → ℝ) ι₀)

theorem stabilize_rank [Module.Finite ℝ F] (Z : RealBundle B F ι) (k : ℕ) :
    (Z.stabilize (ι₀ := ι₀) k).rank = Z.rank + k := by
  rw [stabilize, sum_rank, trivial_rank, rank, Module.finrank_fin_fun]

/-! ## Pullback along a continuous map -/

/-- **Pullback** of a real bundle along a continuous map `f : C(B', B)`: the cover is the
preimage of the cover of `B` and the transition functions are those of `B` composed with `f`. -/
def pullback (Z : RealBundle B F ι) {B' : Type*} [TopologicalSpace B'] (f : C(B', B)) :
    RealBundle B' F ι where
  baseSet i := f ⁻¹' Z.baseSet i
  isOpen_baseSet i := (Z.isOpen_baseSet i).preimage f.continuous
  indexAt x := Z.indexAt (f x)
  mem_baseSet_at x := Z.mem_baseSet_at (f x)
  coordChange i j x := Z.coordChange i j (f x)
  coordChange_self i x hx v := Z.coordChange_self i (f x) hx v
  continuousOn_coordChange i j :=
    (Z.continuousOn_coordChange i j).comp f.continuous.continuousOn fun _ hx => hx
  coordChange_comp i j k x hx v := Z.coordChange_comp i j k (f x) hx v

@[simp] theorem pullback_baseSet (Z : RealBundle B F ι) {B' : Type*} [TopologicalSpace B']
    (f : C(B', B)) (i : ι) : (Z.pullback f).baseSet i = f ⁻¹' Z.baseSet i := rfl

@[simp] theorem pullback_indexAt (Z : RealBundle B F ι) {B' : Type*} [TopologicalSpace B']
    (f : C(B', B)) (x : B') : (Z.pullback f).indexAt x = Z.indexAt (f x) := rfl

@[simp] theorem pullback_coordChange (Z : RealBundle B F ι) {B' : Type*} [TopologicalSpace B']
    (f : C(B', B)) (i j : ι) (x : B') :
    (Z.pullback f).coordChange i j x = Z.coordChange i j (f x) := rfl

theorem pullback_rank (Z : RealBundle B F ι) {B' : Type*} [TopologicalSpace B'] (f : C(B', B)) :
    (Z.pullback f).rank = Z.rank := rfl

@[simp] theorem pullback_id (Z : RealBundle B F ι) :
    Z.pullback (ContinuousMap.id B) = Z := rfl

theorem pullback_comp (Z : RealBundle B F ι) {B' B'' : Type*} [TopologicalSpace B']
    [TopologicalSpace B''] (g : C(B', B)) (f : C(B'', B')) :
    (Z.pullback g).pullback f = Z.pullback (g.comp f) := rfl

@[simp] theorem pullback_trivial {B' : Type*} [TopologicalSpace B'] (f : C(B', B)) :
    (trivial B F ι₀).pullback f = trivial B' F ι₀ := rfl

theorem pullback_sum (Z₁ : RealBundle B F₁ ι₁) (Z₂ : RealBundle B F₂ ι₂)
    {B' : Type*} [TopologicalSpace B'] (f : C(B', B)) :
    (Z₁.sum Z₂).pullback f = (Z₁.pullback f).sum (Z₂.pullback f) := rfl

end RealBundle

end

end Work.TangentClasses
