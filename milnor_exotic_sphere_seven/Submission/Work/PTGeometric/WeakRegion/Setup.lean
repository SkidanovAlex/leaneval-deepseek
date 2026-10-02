import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Basic
import Submission.Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf
import Submission.Work.PTGeometric.WeakRegion.modelData_boundaryZero_cinf
import Submission.Work.PTGeometric.regionManifoldTheorem
import Submission.Work.PTGeometric.exists_chart_at_interior_zero
import Submission.Work.PTGeometric.isSubmersionAt_of_surjective_mfderiv_real
import Submission.Work.ThomBordism.Transversality.Preimage.BoundaryCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the weak region-charting theorem — the per-point chart data

This file sets up the chart data for the region `{Φ ≤ 0}` of a smooth function `Φ` on a smooth
manifold with boundary `A` under the *weak* hypotheses of
`Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak`: `Φ` has nonvanishing derivative at each of
its zeros, is nonnegative on `∂A` near its boundary zeros and is tangent to `∂A` at the boundary
zeros with a *negative* multiple of the boundary coordinate.

At each point `m` of the region an *ambient chart* `dom m` of the maximal atlas at `m.1` and a
*model chart* `T m` (an open partial homeomorphism of the model space) are produced, such that the
sign of `Φ` is read off from the *first coordinate* of `T m (dom m.extend ·)`.  The three cases are

* `Φ m.1 < 0`: the region contains a neighbourhood, `T m` is the identity;
* `Φ m.1 = 0` with `m.1` an interior point of `A`: `T m` is the affine straightening of
  `Work.PTGeometric.exists_chart_at_interior_zero`;
* `Φ m.1 = 0` with `m.1 ∈ ∂A`: `T m` is the *graph straightening*
  `z ↦ z - h (tail z) • e 0` given by the half-space graph result
  `Work.PTGeometric.WeakRegion.exists_graph_halfSpace` (used here as
  `exists_graph_halfSpace_local`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners

namespace Work.PTGeometric.WeakRegion

noncomputable section

/-- **The data of the weak region-charting theorem.** -/
structure RegionSetupWeak (k : ℕ) where
  /-- the ambient manifold -/
  A : Type
  [topologicalSpace : TopologicalSpace A]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace (8 + k + 1)) A]
  [isManifold : IsManifold (𝓡∂ (8 + k + 1)) ∞ A]
  [t2Space : T2Space A]
  /-- the defining function -/
  Φ : A → ℝ
  hΦ : ContMDiff (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) ∞ Φ
  /-- **the weak regularity hypothesis** -/
  hweak : ∀ x : A, Φ x = 0 → mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) Φ x ≠ 0
  /-- **the sign condition at the boundary zeros** -/
  hsign : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary A, Φ x = 0 →
    ∀ᶠ y in 𝓝 x, y ∈ (𝓡∂ (8 + k + 1)).boundary A → 0 ≤ Φ y
  /-- **the tangency condition at the boundary zeros** -/
  hone : ∀ x ∈ (𝓡∂ (8 + k + 1)).boundary A, Φ x = 0 →
    ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace (8 + k + 1))) (c : ℝ),
      e ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
      (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ (8 + k + 1)).boundary A) ∧
      mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) Φ x
        = c • mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x
  /-- **the region is compact** -/
  hK : IsCompact {x : A | Φ x ≤ 0}

attribute [instance] RegionSetupWeak.topologicalSpace RegionSetupWeak.chartedSpace
  RegionSetupWeak.isManifold RegionSetupWeak.t2Space

namespace RegionSetupWeak

variable {k : ℕ} (S : RegionSetupWeak k)

/-- The region `{x | Φ x ≤ 0}`, as a subtype of the ambient manifold. -/
abbrev Region : Type := {x : S.A // S.Φ x ≤ 0}

/-! ## The two delegated components, stated here as hypotheses of the development

These two statements are proved in
`Submission/Work/PTGeometric/WeakRegion/exists_graph_halfSpace_cinf.lean` and
`Submission/Work/PTGeometric/WeakRegion/modelData_boundaryZero_cinf.lean` (the `C^∞` versions; the
earlier `exists_graph_halfSpace.lean` / `exists_modelData_at_boundaryZero.lean` prove the analogous
statements for the *analytic* order `ω`, which the development cannot use because `Φ` is only `C^∞`);
they are repeated here (with the same statements) so that the assembly below can be developed and
type-checked independently. -/

/-- **The half-space graph result** (the crux). -/
theorem exists_graph_halfSpace_local {n : ℕ} [NeZero n]
    (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp0 : p.ofLp 0 = 0)
    (hC : ∃ U ∈ 𝓝 p, ContDiffOn ℝ ∞ Ψ (U ∩ Set.range (𝓡∂ n)))
    (h0 : Ψ p = 0) (c : ℝ) (hc : c < 0)
    (hd : fderivWithin ℝ Ψ (Set.range (𝓡∂ n)) p
      = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0))
    (hsign : ∀ᶠ z in 𝓝[Set.range (𝓡∂ n)] p, z.ofLp 0 = 0 → 0 ≤ Ψ z) :
    ∃ (h : EuclideanSpace ℝ (Fin n) → ℝ) (W : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ tailVec p ∈ W ∧ ContDiffOn ℝ ∞ h W ∧ (∀ u ∈ W, 0 ≤ h u) ∧
      h (tailVec p) = 0 ∧
      (∀ᶠ z in 𝓝[Set.range (𝓡∂ n)] p, (Ψ z ≤ 0 ↔ h (tailVec z) ≤ z.ofLp 0)) :=
  exists_graph_halfSpace_cinf Ψ p hp0 hC h0 c hc hd hsign

/-- **Reading the weak hypotheses in the preferred chart at a boundary zero.** -/
theorem exists_modelData_local {n : ℕ} [NeZero n]
    {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace n) A]
    [IsManifold (𝓡∂ n) ∞ A]
    {Φ : A → ℝ} (hΦ : ContMDiff (𝓡∂ n) (𝓘(ℝ, ℝ)) ∞ Φ) {x : A}
    (hxb : x ∈ (𝓡∂ n).boundary A) (hx0 : Φ x = 0)
    (hsign : ∀ᶠ y in 𝓝 x, y ∈ (𝓡∂ n).boundary A → 0 ≤ Φ y)
    (hone : ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace n)) (c : ℝ),
      e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
      (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ n).boundary A) ∧
      mfderiv (𝓡∂ n) (𝓘(ℝ, ℝ)) Φ x
        = c • mfderiv (𝓡∂ n) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x) :
    ∃ (c : ℝ) (Ψ : EuclideanSpace ℝ (Fin n) → ℝ),
      c < 0 ∧
      (∀ y ∈ (extChartAt (𝓡∂ n) x).source, Ψ (extChartAt (𝓡∂ n) x y) = Φ y) ∧
      (extChartAt (𝓡∂ n) x x).ofLp 0 = 0 ∧
      (∃ U ∈ 𝓝 (extChartAt (𝓡∂ n) x x), ContDiffOn ℝ ∞ Ψ (U ∩ Set.range (𝓡∂ n))) ∧
      Ψ (extChartAt (𝓡∂ n) x x) = 0 ∧
      fderivWithin ℝ Ψ (Set.range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x)
        = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0) ∧
      (∀ᶠ z in 𝓝[Set.range (𝓡∂ n)] (extChartAt (𝓡∂ n) x x), z.ofLp 0 = 0 → 0 ≤ Ψ z) :=
  modelData_boundaryZero_cinf hΦ hxb hx0 hsign hone

/-! ## Three model partial homeomorphisms -/

/-- The identity partial homeomorphism of a topological space. -/
def idPH (E : Type*) [TopologicalSpace E] : OpenPartialHomeomorph E E where
  toFun := id
  invFun := id
  source := univ
  target := univ
  map_source' := fun x _ => mem_univ x
  map_target' := fun x _ => mem_univ x
  left_inv' := fun x _ => rfl
  right_inv' := fun x _ => rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp] theorem idPH_apply {E : Type*} [TopologicalSpace E] (z : E) : idPH E z = z := rfl

@[simp] theorem idPH_symm {E : Type*} [TopologicalSpace E] (z : E) : (idPH E).symm z = z := rfl

@[simp] theorem idPH_source {E : Type*} [TopologicalSpace E] : (idPH E).source = univ := rfl

@[simp] theorem idPH_target {E : Type*} [TopologicalSpace E] : (idPH E).target = univ := rfl

/-- The affine partial homeomorphism `z ↦ L (z - o)` (a global homeomorphism, so source and target
are everything). -/
def affinePH {n : ℕ} [NeZero n] (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (o : EuclideanSpace ℝ (Fin n)) : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) where
  toFun := fun z => L (z - o)
  invFun := fun z => L.symm z + o
  source := univ
  target := univ
  map_source' := fun z _ => mem_univ _
  map_target' := fun z _ => mem_univ _
  left_inv' := fun z _ => by simp [ContinuousLinearEquiv.symm_apply_apply]
  right_inv' := fun z _ => by simp [ContinuousLinearEquiv.apply_symm_apply]
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := (L.continuous.comp (continuous_id.sub continuous_const)).continuousOn
  continuousOn_invFun := ((L.symm.continuous.comp continuous_id).add
    continuous_const).continuousOn

@[simp] theorem affinePH_apply {n : ℕ} [NeZero n]
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (o z : EuclideanSpace ℝ (Fin n)) : affinePH L o z = L (z - o) := rfl

@[simp] theorem affinePH_symm {n : ℕ} [NeZero n]
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (o z : EuclideanSpace ℝ (Fin n)) : (affinePH L o).symm z = L.symm z + o := rfl

/-- **The graph straightening** `z ↦ z - h (tail z) • e 0` of a function `h` of the tangential
coordinates, with inverse `z ↦ z + h (tail z) • e 0`; it is a homeomorphism of `{z | tail z ∈ W}`
onto itself. -/
def graphPH {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun := fun z => z - h (tailVec z) • eZero
  invFun := fun z => z + h (tailVec z) • eZero
  source := {z | tailVec z ∈ W}
  target := {z | tailVec z ∈ W}
  map_source' := fun z hz => by
    simpa only [Set.mem_setOf_eq, tailVec_sub_smul_eZero] using hz
  map_target' := fun z hz => by
    have hz' : tailVec (z - (-(h (tailVec z))) • eZero) ∈ W := by
      simpa only [Set.mem_setOf_eq, tailVec_sub_smul_eZero] using hz
    have heq : z + h (tailVec z) • eZero = z - (-(h (tailVec z))) • eZero := by module
    rwa [heq]
  left_inv' := fun z _ => by
    show (z - h (tailVec z) • eZero) + h (tailVec (z - h (tailVec z) • eZero)) • eZero = z
    rw [tailVec_sub_smul_eZero]
    module
  right_inv' := fun z _ => by
    show (z + h (tailVec z) • eZero) - h (tailVec (z + h (tailVec z) • eZero)) • eZero = z
    rw [show tailVec (z + h (tailVec z) • eZero) = tailVec z from by
      rw [show z + h (tailVec z) • eZero = z - (-(h (tailVec z))) • eZero from by module]
      exact tailVec_sub_smul_eZero z (-(h (tailVec z)))]
    module
  open_source := hW.preimage continuous_tailVec
  open_target := hW.preimage continuous_tailVec
  continuousOn_toFun := by
    have h1 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => h (tailVec z))
        {z | tailVec z ∈ W} :=
      hsm.continuousOn.comp continuous_tailVec.continuousOn (fun z hz => hz)
    exact ContinuousOn.sub continuousOn_id
      (h1.smul (continuousOn_const : ContinuousOn (fun _ : EuclideanSpace ℝ (Fin n) => eZero) _))
  continuousOn_invFun := by
    have h1 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => h (tailVec z))
        {z | tailVec z ∈ W} :=
      hsm.continuousOn.comp continuous_tailVec.continuousOn (fun z hz => hz)
    exact ContinuousOn.add continuousOn_id
      (h1.smul (continuousOn_const : ContinuousOn (fun _ : EuclideanSpace ℝ (Fin n) => eZero) _))

@[simp] theorem graphPH_apply {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W)
    (z : EuclideanSpace ℝ (Fin n)) :
    graphPH h W hW hsm z = z - h (tailVec z) • eZero := rfl

@[simp] theorem graphPH_symm {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W)
    (z : EuclideanSpace ℝ (Fin n)) :
    (graphPH h W hW hsm).symm z = z + h (tailVec z) • eZero := rfl

@[simp] theorem graphPH_source {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W) :
    (graphPH h W hW hsm).source = {z | tailVec z ∈ W} := rfl

@[simp] theorem graphPH_target {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W) :
    (graphPH h W hW hsm).target = {z | tailVec z ∈ W} := rfl

/-- **The image of the source of a chart of the maximal atlas is open in the model** when the
source lies in the interior of the manifold. -/
theorem isOpen_extend_image_source {n : ℕ} [NeZero n] {A : Type*} [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A]
    {e : OpenPartialHomeomorph A (EuclideanHalfSpace n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A)
    (hint : e.source ⊆ (𝓡∂ n).interior A) :
    IsOpen ((e.extend (𝓡∂ n)) '' e.source) := by
  obtain ⟨W, hWopen, hW⟩ :=
    Work.ThomBordism.Transversality.Preimage.exists_isOpen_extend_target e
  have him : (e.extend (𝓡∂ n)) '' e.source = W ∩ range (𝓡∂ n) := by
    rw [← OpenPartialHomeomorph.extend_target_eq_image_source (f := e) (I := 𝓡∂ n)]
    exact hW
  have hsub : (e.extend (𝓡∂ n)) '' e.source ⊆ interior (range (𝓡∂ n)) := by
    rintro z ⟨y, hy, rfl⟩
    have h1 : (e.extend (𝓡∂ n)) y ∈ interior ((e.extend (𝓡∂ n)).target) :=
      (Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas
        (n := (∞ : WithTop ℕ∞)) (by simp) he hy).mp (hint hy)
    have h2 : (e.extend (𝓡∂ n)).target ⊆ range (𝓡∂ n) := by
      rw [hW]
      exact inter_subset_right
    exact interior_mono h2 h1
  have heq : W ∩ range (𝓡∂ n) = W ∩ interior (range (𝓡∂ n)) := by
    refine Subset.antisymm (fun z hz => ⟨hz.1, ?_⟩)
      (fun z hz => ⟨hz.1, interior_subset hz.2⟩)
    have hz' : z ∈ (e.extend (𝓡∂ n)) '' e.source := by rw [him]; exact hz
    exact hsub hz'
  rw [him, heq]
  exact hWopen.inter isOpen_interior


/-- The graph straightening of a function which is `C^∞` on `W` is `C^∞` on its source. -/
theorem graphPH_contDiff {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W) :
    ContDiffOn ℝ ∞ (graphPH h W hW hsm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (graphPH h W hW hsm).source := by
  have h1 : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => h (tailVec z))
      {z | tailVec z ∈ W} :=
    hsm.comp contDiff_tailVec.contDiffOn (fun z hz => hz)
  have h2 : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => h (tailVec z) • eZero)
      {z | tailVec z ∈ W} :=
    h1.smul (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : EuclideanSpace ℝ (Fin n) => (eZero : EuclideanSpace ℝ (Fin n)))
      {z : EuclideanSpace ℝ (Fin n) | tailVec z ∈ W})
  exact ContDiffOn.sub contDiffOn_id h2

/-- The inverse graph straightening is `C^∞` on its target as well. -/
theorem graphPH_contDiff_symm {n : ℕ} [NeZero n] (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (W : Set (EuclideanSpace ℝ (Fin n))) (hW : IsOpen W) (hsm : ContDiffOn ℝ ∞ h W) :
    ContDiffOn ℝ ∞ ((graphPH h W hW hsm).symm : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) (graphPH h W hW hsm).target := by
  have h1 : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => h (tailVec z))
      {z | tailVec z ∈ W} :=
    hsm.comp contDiff_tailVec.contDiffOn (fun z hz => hz)
  have h2 : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => h (tailVec z) • eZero)
      {z | tailVec z ∈ W} :=
    h1.smul (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : EuclideanSpace ℝ (Fin n) => (eZero : EuclideanSpace ℝ (Fin n)))
      {z : EuclideanSpace ℝ (Fin n) | tailVec z ∈ W})
  exact ContDiffOn.add contDiffOn_id h2

/-- **Case C of the chart data**: a boundary zero.  The chart is the preferred chart at `m.1`
(restricted to a neighbourhood on which the epigraph description holds) and the model chart is the
graph straightening of the tangential graph function. -/
theorem exists_chartData_caseC (m : S.Region) (h0 : S.Φ m.1 = 0)
    (hb : (𝓡∂ (8 + k + 1)).IsBoundaryPoint m.1) :
    ∃ (dom : OpenPartialHomeomorph S.A (Half k)) (T : OpenPartialHomeomorph (Mod k) (Mod k)),
      dom ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A ∧ m.1 ∈ dom.source ∧
      (dom.extend (𝓡∂ (8 + k + 1))) m.1 ∈ T.source ∧ T.source = T.target ∧
      ContDiffOn ℝ ∞ (T : Mod k → Mod k) T.source ∧
      ContDiffOn ℝ ∞ (T.symm : Mod k → Mod k) T.target ∧
      IsOpen {u : Half k | (T.symm : Mod k → Mod k) u.1
        ∈ (dom.extend (𝓡∂ (8 + k + 1))).target ∧ u.1 ∈ T.target} ∧
      (∀ y ∈ dom.source, (dom.extend (𝓡∂ (8 + k + 1))) y ∈ T.source →
        (S.Φ y ≤ 0 ↔ 0 ≤ ((T ((dom.extend (𝓡∂ (8 + k + 1))) y)).ofLp 0))) ∧
      (((T ((dom.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0 = 0) ↔
        (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0)) := by
  classical
  have hbdy : m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A := hb
  obtain ⟨c, Ψ, hc, hPsi, hp0c, hCdiff, hPsi0, hderiv, hsignP⟩ :=
    exists_modelData_local (n := 8 + k + 1) S.hΦ hbdy h0
      (S.hsign m.1 hbdy h0) (S.hone m.1 hbdy h0)
  obtain ⟨h, W, hWopen, htailp, hsm, hnonneg, hzero, hepi⟩ :=
    exists_graph_halfSpace_local Ψ (extChartAt (𝓡∂ (8 + k + 1)) m.1 m.1) hp0c hCdiff
      hPsi0 c hc hderiv hsignP
  -- an open neighbourhood `V` of the chart image on which the epigraph description holds
  have hEv : ∀ᶠ z in 𝓝 (extChartAt (𝓡∂ (8 + k + 1)) m.1 m.1),
      z ∈ Set.range (𝓡∂ (8 + k + 1)) → (Ψ z ≤ 0 ↔ h (tailVec z) ≤ z.ofLp 0) :=
    (mem_nhdsWithin_iff_eventually).mp hepi
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp (Filter.eventually_iff.mp hEv)
  have hVprop : ∀ z ∈ V, z ∈ Set.range (𝓡∂ (8 + k + 1)) →
      (Ψ z ≤ 0 ↔ h (tailVec z) ≤ z.ofLp 0) := fun z hz => hVsub hz
  -- the preferred ambient chart, restricted to the good set
  set chi : OpenPartialHomeomorph S.A (Half k) := chartAt (Half k) m.1 with hchidef
  have hchimem : chi ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m.1
  have hchi_ext : chi.extend (𝓡∂ (8 + k + 1)) m.1 = extChartAt (𝓡∂ (8 + k + 1)) m.1 m.1 := rfl
  set U : Set S.A := chi.source ∩ (chi.extend (𝓡∂ (8 + k + 1))) ⁻¹' V with hUdef
  have hUopen : IsOpen U := by
    have h : IsOpen ((chi.extend (𝓡∂ (8 + k + 1))).source
        ∩ (chi.extend (𝓡∂ (8 + k + 1))) ⁻¹' V) :=
      chi.continuousOn_extend.isOpen_inter_preimage
        (by rw [OpenPartialHomeomorph.extend_source]; exact chi.open_source) hVopen
    simpa only [OpenPartialHomeomorph.extend_source] using h
  have hUm : m.1 ∈ U := by
    refine ⟨mem_chart_source (Half k) m.1, ?_⟩
    rw [Set.mem_preimage, hchi_ext]
    exact hpV
  set dom : OpenPartialHomeomorph S.A (Half k) := chi.restr U with hdomdef
  have hdommem : dom ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ (8 + k + 1))) hchimem hUopen
  have hdomsrc : dom.source = chi.source ∩ U :=
    OpenPartialHomeomorph.restr_source' chi U hUopen
  have hdomext : ∀ y, dom.extend (𝓡∂ (8 + k + 1)) y = chi.extend (𝓡∂ (8 + k + 1)) y :=
    fun y => rfl
  refine ⟨dom, graphPH h W hWopen hsm, hdommem, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdomsrc]
    exact ⟨mem_chart_source (Half k) m.1, hUm⟩
  · rw [hdomext]
    show tailVec (chi.extend (𝓡∂ (8 + k + 1)) m.1) ∈ W
    rw [hchi_ext]
    exact htailp
  · exact graphPH_contDiff h W hWopen hsm
  · exact graphPH_contDiff_symm h W hWopen hsm
  · -- ## openness of the target
    obtain ⟨W', hW'open, hW'⟩ :=
      Work.ThomBordism.Transversality.Preimage.exists_isOpen_extend_target chi
    have himg : (dom.extend (𝓡∂ (8 + k + 1))).target
        = (W' ∩ V) ∩ Set.range (𝓡∂ (8 + k + 1)) := by
      rw [OpenPartialHomeomorph.extend_target_eq_image_source, hdomsrc]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨y, ⟨hysrc, hyU⟩, rfl⟩
        have hyV : chi.extend (𝓡∂ (8 + k + 1)) y ∈ V := hyU.2
        have hytgt : chi.extend (𝓡∂ (8 + k + 1)) y
            ∈ (chi.extend (𝓡∂ (8 + k + 1))).target :=
          PartialEquiv.map_source _ (by simpa using hysrc)
        have h3 : chi.extend (𝓡∂ (8 + k + 1)) y
            ∈ W' ∩ Set.range (𝓡∂ (8 + k + 1)) := by
          rw [← hW']; exact hytgt
        exact ⟨⟨h3.1, hyV⟩, h3.2⟩
      · rintro z ⟨⟨hzW', hzV⟩, hzR⟩
        have hztgt : z ∈ (chi.extend (𝓡∂ (8 + k + 1))).target := by
          rw [hW']; exact ⟨hzW', hzR⟩
        have hztgt' : z ∈ (chi.extend (𝓡∂ (8 + k + 1))) '' chi.source := by
          rw [← OpenPartialHomeomorph.extend_target_eq_image_source chi]
          exact hztgt
        obtain ⟨y, hysrc, hyz⟩ := hztgt'
        refine ⟨y, ⟨hysrc, ?_⟩, hyz⟩
        rw [hUdef]
        exact ⟨hysrc, by rw [Set.mem_preimage, hyz]; exact hzV⟩
    set Z : Half k → Mod k := fun u => (graphPH h W hWopen hsm).symm u.1 with hZdef
    have hZval : ∀ u : Half k, Z u = (u.1 : Mod k) + h (tailVec u.1) • eZero :=
      fun u => rfl
    have hzsrcW : ∀ u : Half k, u.1 ∈ (graphPH h W hWopen hsm).target ↔ tailVec u.1 ∈ W :=
      fun u => Iff.rfl
    have hmeq : {u : Half k | Z u ∈ (dom.extend (𝓡∂ (8 + k + 1))).target
          ∧ u.1 ∈ (graphPH h W hWopen hsm).target}
        = {u : Half k | tailVec u.1 ∈ W ∧ (Z u ∈ W' ∧ Z u ∈ V)} := by
      ext u
      rw [himg]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨h4, h1, h2⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨⟨h2, h3⟩, ?_⟩, h1⟩
        have hZU : 0 ≤ (Z u).ofLp 0 := by
          rw [hZval, ofLp_add_smul_eZero]
          have hnn : 0 ≤ h (tailVec u.1) := hnonneg _ h1
          have hu0 : 0 ≤ u.1.ofLp 0 := u.2
          linarith
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact hZU
    rw [hmeq]
    have hcont : ContinuousOn Z {u : Half k | tailVec u.1 ∈ W} := by
      have h1 : ContinuousOn (fun u : Half k => h (tailVec u.1))
          {u : Half k | tailVec u.1 ∈ W} :=
        hsm.continuousOn.comp (continuous_tailVec.comp continuous_subtype_val).continuousOn
          (fun u hu => hu)
      have h2 : ContinuousOn (fun u : Half k => h (tailVec u.1) • eZero)
          {u : Half k | tailVec u.1 ∈ W} :=
        h1.smul (continuousOn_const :
          ContinuousOn (fun _ : Half k => (eZero : EuclideanSpace ℝ (Fin (8 + k + 1))))
            {u : Half k | tailVec u.1 ∈ W})
      have h3 : ContinuousOn (fun u : Half k => (u.1 : Mod k) + h (tailVec u.1) • eZero)
          {u : Half k | tailVec u.1 ∈ W} :=
        continuous_subtype_val.continuousOn.add h2
      exact h3.congr (fun u _ => (hZval u).symm)
    have hopen1 : IsOpen {u : Half k | tailVec u.1 ∈ W} :=
      hWopen.preimage (continuous_tailVec.comp continuous_subtype_val)
    have hset2 : {u : Half k | tailVec u.1 ∈ W ∧ (Z u ∈ W' ∧ Z u ∈ V)}
        = ({u : Half k | tailVec u.1 ∈ W} ∩ Z ⁻¹' W')
          ∩ ({u : Half k | tailVec u.1 ∈ W} ∩ Z ⁻¹' V) := by
      ext u
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h1, h3⟩
      · rintro ⟨⟨h1, h2⟩, -, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [hset2]
    exact (hcont.isOpen_inter_preimage hopen1 hW'open).inter
      (hcont.isOpen_inter_preimage hopen1 hVopen)
  · -- ## the sign of `Φ` is the sign of the zeroth coordinate
    intro y hy hyT
    have hyU : y ∈ U := by
      have h1 : y ∈ chi.source ∩ U := by rw [← hdomsrc]; exact hy
      exact h1.2
    have hyV : chi.extend (𝓡∂ (8 + k + 1)) y ∈ V := hyU.2
    have hyR : chi.extend (𝓡∂ (8 + k + 1)) y ∈ Set.range (𝓡∂ (8 + k + 1)) := by
      rw [OpenPartialHomeomorph.extend_coe]
      exact ⟨_, rfl⟩
    have hep := hVprop _ hyV hyR
    have hchiextfun : chi.extend (𝓡∂ (8 + k + 1)) = extChartAt (𝓡∂ (8 + k + 1)) m.1 := rfl
    have hPsiy : Ψ (chi.extend (𝓡∂ (8 + k + 1)) y) = S.Φ y := by
      have h2 : (chi.extend (𝓡∂ (8 + k + 1))) y = extChartAt (𝓡∂ (8 + k + 1)) m.1 y := rfl
      rw [h2]
      exact hPsi y (by
        rw [← hchiextfun, OpenPartialHomeomorph.extend_source]
        exact (hdomsrc ▸ hy).1)
    have hval : ((graphPH h W hWopen hsm) ((dom.extend (𝓡∂ (8 + k + 1))) y)).ofLp 0
        = ((dom.extend (𝓡∂ (8 + k + 1))) y).ofLp 0
          - h (tailVec ((dom.extend (𝓡∂ (8 + k + 1))) y)) := by
      show (((dom.extend (𝓡∂ (8 + k + 1))) y
        - h (tailVec ((dom.extend (𝓡∂ (8 + k + 1))) y)) • eZero).ofLp 0 = _)
      rw [ofLp_sub_smul_eZero]
    rw [hval, hdomext, ← hPsiy]
    constructor
    · intro hle
      have h1 := hep.mp hle
      linarith
    · intro hle
      have h1 : h (tailVec (chi.extend (𝓡∂ (8 + k + 1)) y))
          ≤ (chi.extend (𝓡∂ (8 + k + 1)) y).ofLp 0 := by linarith
      exact hep.mpr h1
  · -- ## the zeroth coordinate of the base point
    have hval : ((graphPH h W hWopen hsm) ((dom.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0
        = ((dom.extend (𝓡∂ (8 + k + 1))) m.1).ofLp 0
          - h (tailVec ((dom.extend (𝓡∂ (8 + k + 1))) m.1)) := by
      show (((dom.extend (𝓡∂ (8 + k + 1))) m.1
        - h (tailVec ((dom.extend (𝓡∂ (8 + k + 1))) m.1)) • eZero).ofLp 0 = _)
      rw [ofLp_sub_smul_eZero]
    have h1 : ((graphPH h W hWopen hsm) ((dom.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0
        = ((dom.extend (𝓡∂ (8 + k + 1))) m.1).ofLp 0
          - h (tailVec ((dom.extend (𝓡∂ (8 + k + 1))) m.1)) := hval
    have h2 : ((dom.extend (𝓡∂ (8 + k + 1))) m.1).ofLp 0 = 0 := by
      rw [hdomext, hchi_ext, hp0c]
    have h3 : h (tailVec ((dom.extend (𝓡∂ (8 + k + 1))) m.1)) = 0 := by
      rw [hdomext, hchi_ext]
      exact hzero
    rw [h1, h2, h3, sub_zero]
    exact ⟨fun _ => Or.inl hbdy, fun _ => rfl⟩

/-- **The chart data at a point `m` of the region.**

Each point of the region carries an ambient chart `dom` of the maximal atlas and a *model chart*
`T` (a partial homeomorphism of the model space, i.e. of the coordinates of `dom`) with the
properties that `T.source = T.target`, that both `T` and `T.symm` are smooth, that the *sign* of `Φ`
is read off from the zeroth coordinate of `T (dom.extend ·)`, that `T.symm` maps the half-space of
the model into the target of `dom.extend`, and that the zeroth coordinate of `T (dom.extend m.1)`
vanishes exactly when either `m.1 ∈ ∂A` or `Φ m.1 = 0`. -/
theorem exists_chartData (m : S.Region) :
    ∃ (dom : OpenPartialHomeomorph S.A (Half k)) (T : OpenPartialHomeomorph (Mod k) (Mod k)),
      dom ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A ∧ m.1 ∈ dom.source ∧
      (dom.extend (𝓡∂ (8 + k + 1))) m.1 ∈ T.source ∧ T.source = T.target ∧
      ContDiffOn ℝ ∞ (T : Mod k → Mod k) T.source ∧
      ContDiffOn ℝ ∞ (T.symm : Mod k → Mod k) T.target ∧
      IsOpen {u : Half k | (T.symm : Mod k → Mod k) u.1
        ∈ (dom.extend (𝓡∂ (8 + k + 1))).target ∧ u.1 ∈ T.target} ∧
      (∀ y ∈ dom.source, (dom.extend (𝓡∂ (8 + k + 1))) y ∈ T.source →
        (S.Φ y ≤ 0 ↔ 0 ≤ ((T ((dom.extend (𝓡∂ (8 + k + 1))) y)).ofLp 0))) ∧
      (((T ((dom.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0 = 0) ↔
        (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0)) := by
  classical
  by_cases hA : S.Φ m.1 < 0
  · -- ## Case A: the region contains a neighbourhood of `m.1`
    have hreg : {y : S.A | S.Φ y ≤ 0} ∈ 𝓝 m.1 := by
      have h1 : S.Φ ⁻¹' Iio 0 ∈ 𝓝 m.1 :=
        (S.hΦ.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds hA
      exact Filter.mem_of_superset h1 (fun y (hy : S.Φ y < 0) => le_of_lt hy)
    obtain ⟨U, hUsub, hUopen, hUm⟩ := mem_nhds_iff.mp hreg
    obtain ⟨dom, hdom, hmdom, hdomsub⟩ :=
      exists_chart_source_subset (n := 8 + k + 1) S.A hUopen hUm
    refine ⟨dom, idPH (Mod k), hdom, hmdom, mem_univ _, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · show ContDiffOn ℝ ∞ (fun z : Mod k => z) univ
      exact contDiff_id.contDiffOn
    · show ContDiffOn ℝ ∞ (fun z : Mod k => z) univ
      exact contDiff_id.contDiffOn
    · -- openness of the target
      obtain ⟨W, hWopen, hW⟩ :=
        Work.ThomBordism.Transversality.Preimage.exists_isOpen_extend_target dom
      have hset : {u : Half k | (idPH (Mod k)).symm u.1
            ∈ (dom.extend (𝓡∂ (8 + k + 1))).target ∧ u.1 ∈ (idPH (Mod k)).target}
          = Subtype.val ⁻¹' W := by
        ext u
        constructor
        · rintro ⟨hu, -⟩
          have h2 : u.1 ∈ W ∩ Set.range (𝓡∂ (8 + k + 1)) := hW ▸ hu
          exact h2.1
        · intro hu
          refine ⟨?_, mem_univ _⟩
          rw [hW]
          exact ⟨hu, by rw [range_modelWithCornersEuclideanHalfSpace]; exact u.2⟩
      rw [hset]
      exact hWopen.preimage continuous_subtype_val
    · -- the sign of `Φ` is the sign of the zeroth coordinate
      intro y hy _
      have hΦy : S.Φ y ≤ 0 := hUsub (hdomsub hy)
      have hcoord : 0 ≤ ((idPH (Mod k)) ((dom.extend (𝓡∂ (8 + k + 1))) y)).ofLp 0 := by
        simpa only [idPH_apply] using
          Work.ThomBordism.Transversality.Preimage.zero_le_extend_apply_coord dom hy
      exact ⟨fun _ => hcoord, fun _ => hΦy⟩
    · -- the zeroth coordinate of the base point
      have hcoord : ((idPH (Mod k)) ((dom.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0
          = ((dom.extend (𝓡∂ (8 + k + 1))) m.1).ofLp 0 := rfl
      rw [hcoord]
      have hb := Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := 8 + k + 1) hdom hmdom
      rw [hb]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · exact absurd h (ne_of_lt hA)
  · -- the region point is a zero of `Φ`
    have h0 : S.Φ m.1 = 0 := le_antisymm m.2 (not_lt.mp hA)
    rcases (𝓡∂ (8 + k + 1)).isInteriorPoint_or_isBoundaryPoint m.1 with hint | hbnd
    · -- ## Case B: an interior zero: the affine straightening
      have hsurj : Function.Surjective (mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ,ℝ)) S.Φ m.1) := by
        intro y
        have hne : mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ,ℝ)) S.Φ m.1 ≠ 0 := S.hweak m.1 h0
        obtain ⟨v, hv⟩ : ∃ v, mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ,ℝ)) S.Φ m.1 v ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hne (ContinuousLinearMap.ext hc)
        set yv : ℝ := show ℝ from y with hyv
        set Lv : ℝ := show ℝ from mfderiv (𝓡∂ (8 + k + 1)) (𝓘(ℝ,ℝ)) S.Φ m.1 v with hLv
        refine ⟨(yv / Lv) • v, ?_⟩
        rw [map_smul]
        show (yv / Lv) * Lv = y
        rw [div_mul_cancel₀ yv (by rw [hLv]; exact hv)]
      have hsub : IsSubmersionAt (𝓡∂ (8 + k + 1)) (𝓘(ℝ,ℝ)) ∞ S.Φ m.1 :=
        isSubmersionAt_of_surjective_mfderiv_real (𝓡∂ (8 + k + 1)) S.hΦ hint h0 hsurj
      obtain ⟨e, L, he, hme, hesubint, hiff, hiff0⟩ :=
        exists_chart_at_interior_zero (n := 8 + k + 1) S.A S.Φ hint h0 hsub
      refine ⟨e, affinePH L ((e.extend (𝓡∂ (8 + k + 1))) m.1), he, hme, mem_univ _, rfl,
        ?_, ?_, ?_, ?_, ?_⟩
      · show ContDiffOn ℝ ∞ (fun z : Mod k => L (z - (e.extend (𝓡∂ (8 + k + 1))) m.1)) univ
        exact (L.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
      · show ContDiffOn ℝ ∞ (fun z : Mod k => L.symm z + (e.extend (𝓡∂ (8 + k + 1))) m.1) univ
        exact ((L.symm.contDiff.comp contDiff_id).add contDiff_const).contDiffOn
      · -- openness of the target
        have himopen : IsOpen ((e.extend (𝓡∂ (8 + k + 1))) '' e.source) :=
          isOpen_extend_image_source he hesubint
        have htarget : (e.extend (𝓡∂ (8 + k + 1))).target
            = (e.extend (𝓡∂ (8 + k + 1))) '' e.source :=
          OpenPartialHomeomorph.extend_target_eq_image_source e
        have hset : {u : Half k | (affinePH L ((e.extend (𝓡∂ (8 + k + 1))) m.1)).symm u.1
              ∈ (e.extend (𝓡∂ (8 + k + 1))).target
              ∧ u.1 ∈ (affinePH L ((e.extend (𝓡∂ (8 + k + 1))) m.1)).target}
            = (fun u : Half k => L.symm u.1 + (e.extend (𝓡∂ (8 + k + 1))) m.1)
              ⁻¹' ((e.extend (𝓡∂ (8 + k + 1))) '' e.source) := by
          ext u
          rw [htarget]
          constructor
          · rintro ⟨h1, -⟩
            exact h1
          · intro h1
            exact ⟨h1, mem_univ _⟩
        rw [hset]
        have hcont : Continuous (fun u : Half k =>
            L.symm u.1 + (e.extend (𝓡∂ (8 + k + 1))) m.1) :=
          (L.symm.continuous.comp continuous_subtype_val).add continuous_const
        exact himopen.preimage hcont
      · -- the sign of `Φ` is the sign of the zeroth coordinate
        intro y hy _
        have h1 : S.Φ y ≤ 0 ↔ 0 ≤ (L ((e.extend (𝓡∂ (8 + k + 1))) y
            - (e.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0 := hiff y hy
        have h2 : ((affinePH L ((e.extend (𝓡∂ (8 + k + 1))) m.1))
            ((e.extend (𝓡∂ (8 + k + 1))) y)).ofLp 0
            = (L ((e.extend (𝓡∂ (8 + k + 1))) y
                - (e.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0 := rfl
        rw [h2]
        exact h1
      · -- the zeroth coordinate of the base point
        have hz : ((affinePH L ((e.extend (𝓡∂ (8 + k + 1))) m.1))
            ((e.extend (𝓡∂ (8 + k + 1))) m.1)).ofLp 0 = 0 := by
          show (L (((e.extend (𝓡∂ (8 + k + 1))) m.1
            - (e.extend (𝓡∂ (8 + k + 1))) m.1))).ofLp 0 = 0
          rw [sub_self, map_zero]
          rfl
        rw [hz]
        exact ⟨fun _ => Or.inr h0, fun _ => rfl⟩
    · -- ## Case C: a boundary zero: the graph straightening
      exact exists_chartData_caseC S m h0 hbnd

end RegionSetupWeak

end

end Work.PTGeometric.WeakRegion
