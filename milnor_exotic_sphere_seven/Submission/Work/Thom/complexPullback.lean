import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexification

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The pullback of gluing data (over `ℝ` or `ℂ`), and its interaction with the complexification

`Submission/Work/TangentClasses/Bundle.lean` defines the pullback `RealBundle.pullback` of a *real*
gluing datum along a continuous map.  The Chern/Pontryagin layer of this chapter needs the same
operation over `ℂ` (for the naturality of the Chern classes under pullback — the splitting
principle), so this module defines it once, for an arbitrary `NontriviallyNormedField`, as
`Work.Thom.bundleComap`, together with:

* the definitional API `bundleComap_baseSet`, `bundleComap_indexAt`, `bundleComap_coordChange`;
* `Work.Thom.bundleComap_id`, `bundleComap_comp` (functoriality, definitional);
* `Work.Thom.realification_bundleComap` — **the realification commutes with the pullback**;
* `Work.Thom.complexificationCore_bundleComap` — **the complexification commutes with the
  pullback**: `(f^*E) ⊗_ℝ ℂ = f^*(E ⊗_ℝ ℂ)`, so the Pontryagin classes of `f^*E` are the pullbacks
  of those of `E` as soon as the Chern classes are natural (`README.md` ADDENDUM 20).
-/

namespace Work.Thom

noncomputable section

/-- Two gluing data with the same cover, index map and transition functions are equal (the
`VectorBundleCore` version of `Work.TangentClasses.RealBundle.ext`, for an arbitrary field of
scalars). -/
theorem bundleCore_ext {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*}
    {Z Z' : VectorBundleCore 𝕜 B F ι} (hbase : Z.baseSet = Z'.baseSet)
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

/-- **Pullback of gluing data along a continuous map.**  The cover is the preimage cover and the
transition functions are those of the original bundle composed with `f`.  This is
`Work.TangentClasses.RealBundle.pullback` for an arbitrary field of scalars; it is a *definition*
(not a `choose`), so its defining equations hold by `rfl`. -/
def bundleComap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B B' : Type*} [TopologicalSpace B]
    [TopologicalSpace B'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*}
    (Z : VectorBundleCore 𝕜 B F ι) (f : C(B', B)) : VectorBundleCore 𝕜 B' F ι where
  baseSet i := f ⁻¹' Z.baseSet i
  isOpen_baseSet i := (Z.isOpen_baseSet i).preimage f.continuous
  indexAt x := Z.indexAt (f x)
  mem_baseSet_at x := Z.mem_baseSet_at (f x)
  coordChange i j x := Z.coordChange i j (f x)
  coordChange_self i x hx v := Z.coordChange_self i (f x) hx v
  continuousOn_coordChange i j :=
    (Z.continuousOn_coordChange i j).comp f.continuous.continuousOn fun _ hx => hx
  coordChange_comp i j k x hx v := Z.coordChange_comp i j k (f x) hx v

@[simp] theorem bundleComap_baseSet {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B B' : Type*}
    [TopologicalSpace B] [TopologicalSpace B'] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) (f : C(B', B)) (i : ι) :
    (bundleComap Z f).baseSet i = f ⁻¹' Z.baseSet i := rfl

@[simp] theorem bundleComap_indexAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B B' : Type*}
    [TopologicalSpace B] [TopologicalSpace B'] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) (f : C(B', B)) (x : B') :
    (bundleComap Z f).indexAt x = Z.indexAt (f x) := rfl

@[simp] theorem bundleComap_coordChange {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B B' : Type*}
    [TopologicalSpace B] [TopologicalSpace B'] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) (f : C(B', B)) (i j : ι)
    (x : B') : (bundleComap Z f).coordChange i j x = Z.coordChange i j (f x) := rfl

@[simp] theorem bundleComap_id {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*}
    [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*}
    (Z : VectorBundleCore 𝕜 B F ι) : bundleComap Z (ContinuousMap.id B) = Z := by
  refine bundleCore_ext (funext fun i => ?_) rfl (fun i j x => rfl)
  exact Set.preimage_id

theorem bundleComap_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B B' B'' : Type*}
    [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B''] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι)
    (g : C(B', B)) (f : C(B'', B')) :
    bundleComap (bundleComap Z g) f = bundleComap Z (g.comp f) := by
  refine bundleCore_ext (funext fun i => ?_) rfl (fun i j x => rfl)
  exact Set.preimage_comp.symm

/-! ## Interaction with the realification and the complexification -/

/-- **The realification commutes with the pullback.** -/
theorem realification_bundleComap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {ι : Type}
    (Z : VectorBundleCore ℂ B F ι) (f : C(B', B)) :
    realification (bundleComap Z f) = bundleComap (realification Z) f := by
  have hbase : (realification (bundleComap Z f)).baseSet
      = (bundleComap (realification Z) f).baseSet := by
    funext i
    simp only [realification_baseSet, bundleComap_baseSet]
  have hindex : (realification (bundleComap Z f)).indexAt
      = (bundleComap (realification Z) f).indexAt := by
    funext x
    simp only [realification_indexAt, bundleComap_indexAt]
  refine bundleCore_ext hbase hindex (fun i j x => ?_)
  apply ContinuousLinearMap.ext
  intro v
  rw [realification_coordChange (bundleComap Z f), bundleComap_coordChange,
    bundleComap_coordChange, realification_coordChange Z]

/-- **The complexification commutes with the pullback**: `(f^*E) ⊗_ℝ ℂ = f^*(E ⊗_ℝ ℂ)`. -/
theorem complexificationCore_bundleComap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {k : ℕ} {ι : Type} (E : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι)
    (f : C(B', B)) :
    complexificationCore (bundleComap E f) = bundleComap (complexificationCore E) f := by
  refine bundleCore_ext rfl rfl (fun i j x => ?_)
  rfl

end

end Work.Thom
