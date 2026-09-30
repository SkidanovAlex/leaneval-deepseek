import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexification
import Submission.Work.TangentClasses.Tangent

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Pontryagin classes of a general real vector bundle, and `p₁(TM)` of a smooth manifold

This module turns the Chern classes of `Submission/Work/Thom/chernClass.lean` into the
**Pontryagin classes of a real vector bundle** by the classical formula

  `p_i(E) := (-1)^i c_{2i}(E ⊗_ℝ ℂ)`,

and then applies it to the **tangent bundle of a smooth manifold**, giving the *defined* class
`Work.Thom.p1Tangent' M ∈ H⁴(M;ℤ)` of item (4) of the chapter's deliverable.

The construction of `p1Tangent' M` proceeds in four steps, all of them definitions (no theorem about
characteristic classes is needed for the *definition*, only for its properties):

1. `Work.TangentClasses.tangentBundle I M` presents `TM` over the (usually infinite) atlas of `M`,
   with the model space `E` as fibre;
2. `Work.Thom.RealBundle.mapFibre` replaces the fibre `E` by `EuclideanSpace ℝ (Fin (finrank ℝ E))`
   along a continuous linear equivalence (this is needed because the Chern classes are stated for
   the standard fibre `EuclideanSpace ℂ (Fin k)`);
3. `Work.Thom.RealBundle.reindex` restricts the cover to a **finite** subcover — supplied by
   `Work.Thom.exists_finite_chart_cover` from compactness of `M`, since the recursion
   `Work.Thom.chernClass` is stated for a finite index type;
4. `Work.Thom.complexificationCore` complexifies, and `Work.Thom.chernClass k 2` gives `c₂` of the
   complexification; the class is `p1Tangent' M := - c₂(TM ⊗_ℝ ℂ)`.

The class `p1Tangent' M` is a *function of `M`*: no free data enters.  Its properties (naturality,
the agreement with `Work.TangentClasses.p1Tangent` for the capped `8`-manifold, the Whitney formula,
stability) are *not* proved here; they are the splitting principle and are stated in `README.md`
ADDENDUM 20.

## The main definitions

* `Work.Thom.RealBundle.reindex`, `Work.Thom.RealBundle.mapFibre`;
* `Work.Thom.exists_finite_chart_cover`;
* `Work.Thom.pontryaginClass`, `Work.Thom.pontryagin1` (for a real bundle over a finite cover);
* `Work.Thom.p1Tangent'` (for a smooth manifold).
-/

namespace Work.TangentClasses

open Bundle

namespace RealBundle

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F F' : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {ι ι' : Type*}

/-- **Reindexing a bundle along a refining cover.**  Given gluing data `Z` over the cover `ι` and a
family `σ : ι' → ι` which still covers the base (`∀ x, ∃ i, x ∈ Z.baseSet (σ i)`), this is the same
bundle presented over the cover `ι'`. -/
def reindex (Z : RealBundle B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) : RealBundle B F ι' where
  baseSet i := Z.baseSet (σ i)
  isOpen_baseSet i := Z.isOpen_baseSet (σ i)
  indexAt x := Classical.choose (hσ x)
  mem_baseSet_at x := Classical.choose_spec (hσ x)
  coordChange i j x := Z.coordChange (σ i) (σ j) x
  coordChange_self i x hx v := Z.coordChange_self (σ i) x hx v
  continuousOn_coordChange i j := Z.continuousOn_coordChange (σ i) (σ j)
  coordChange_comp i j l x hx v := Z.coordChange_comp (σ i) (σ j) (σ l) x hx v

@[simp] theorem reindex_baseSet (Z : RealBundle B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) (i : ι') :
    (Z.reindex σ hσ).baseSet i = Z.baseSet (σ i) := rfl

@[simp] theorem reindex_coordChange (Z : RealBundle B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) (i j : ι') (x : B) :
    (Z.reindex σ hσ).coordChange i j x = Z.coordChange (σ i) (σ j) x := rfl

@[simp] theorem reindex_rank (Z : RealBundle B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) : (Z.reindex σ hσ).rank = Z.rank := rfl

/-- **Changing the fibre of a bundle along a continuous linear equivalence.**  The transition
functions become `e ∘ g ∘ e⁻¹`. -/
def mapFibre (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) : RealBundle B F' ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := ContinuousLinearMap.compL ℝ F' F F' (e : F →L[ℝ] F')
    ((ContinuousLinearMap.compL ℝ F' F F (Z.coordChange i j x)) (e.symm : F' →L[ℝ] F))
  coordChange_self i x hx v := by
    show e (Z.coordChange i i x (e.symm v)) = v
    rw [Z.coordChange_self i x hx (e.symm v)]
    exact ContinuousLinearEquiv.apply_symm_apply e v
  continuousOn_coordChange i j :=
    ((ContinuousLinearMap.compL ℝ F' F F' (e : F →L[ℝ] F')).continuous.comp_continuousOn
      (((ContinuousLinearMap.compL ℝ F' F F).flip (e.symm : F' →L[ℝ] F)).continuous.comp_continuousOn
        (Z.continuousOn_coordChange i j)))
  coordChange_comp i j l x hx v := by
    show e (Z.coordChange j l x (e.symm (e (Z.coordChange i j x (e.symm v))))) =
      e (Z.coordChange i l x (e.symm v))
    have hs : e.symm (e (Z.coordChange i j x (e.symm v)))
        = Z.coordChange i j x (e.symm v) :=
      ContinuousLinearEquiv.symm_apply_apply e (Z.coordChange i j x (e.symm v))
    rw [hs]
    exact congrArg e (Z.coordChange_comp i j l x hx (e.symm v))

@[simp] theorem mapFibre_baseSet (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) (i : ι) :
    (Z.mapFibre e).baseSet i = Z.baseSet i := rfl

@[simp] theorem mapFibre_indexAt (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) (x : B) :
    (Z.mapFibre e).indexAt x = Z.indexAt x := rfl

theorem mapFibre_coordChange (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) (i j : ι) (x : B) :
    (Z.mapFibre e).coordChange i j x =
      (e : F →L[ℝ] F').comp ((Z.coordChange i j x).comp (e.symm : F' →L[ℝ] F)) := rfl

@[simp] theorem mapFibre_rank (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) :
    (Z.mapFibre e).rank = Z.rank := by
  simp only [rank]
  exact e.toLinearEquiv.finrank_eq.symm

end

end RealBundle

end Work.TangentClasses

/-! ## The finite chart cover of a compact manifold -/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **Every compact charted space has a finite chart cover**, in the form of a finite family
`σ : Fin N → atlas H M` of charts whose sources cover `M`.  This is what allows the tangent bundle
of a compact manifold (presented over the possibly infinite atlas) to be reindexed to a finite cover,
which the Chern class recursion `Work.Thom.chernClass` requires. -/
theorem exists_finite_chart_cover {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] :
    ∃ (N : ℕ) (σ : Fin N → atlas H M), ∀ x : M, ∃ i, x ∈ (σ i).1.source := by
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, (chartAt H x).source := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : M => (chartAt H x).source) (fun x => (chartAt H x).open_source) hcover
  refine ⟨t.card, fun i => achart H (t.equivFin.symm i), fun x => ?_⟩
  have hx : x ∈ ⋃ y ∈ t, (chartAt H y).source := ht (Set.mem_univ x)
  obtain ⟨y, hyt, hyx⟩ := Set.mem_iUnion₂.mp hx
  exact ⟨t.equivFin ⟨y, hyt⟩, by simpa using hyx⟩

end

end Work.Thom

/-! ## The Pontryagin classes of a real bundle over a finite cover -/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The first Pontryagin class of a real vector bundle** of rank `k` over a finite gluing-data
cover, in the classical normalisation `p₁(E) = - c₂(E ⊗_ℝ ℂ)` (Milnor–Stasheff,
`p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)`). -/
noncomputable def pontryagin1 [Fintype ι] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) : Coh ℤ 4 B :=
  - chernClass k 2 (complexificationCore Z)

/-- **The `i`-th Pontryagin class of a real vector bundle**, `p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)`. -/
noncomputable def pontryaginClass [Fintype ι] (i : ℕ) {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) : Coh ℤ (4 * i) B :=
  cohTransport (by ring : 2 * (2 * i) = 4 * i)
    (((-1 : ℤ) ^ i) • chernClass k (2 * i) (complexificationCore Z))

/-- The defining equation of `pontryagin1`. -/
theorem pontryagin1_def [Fintype ι] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    pontryagin1 Z = - chernClass k 2 (complexificationCore Z) := rfl

/-! ## The tangent bundle of a smooth manifold over a finite cover -/

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- **The model space of a smooth manifold, identified with `ℝ ^ finrank ℝ E`** by a continuous
linear equivalence (`ContinuousLinearEquiv.ofFinrankEq`; no isometry is needed). -/
noncomputable def modelLinearEquiv [FiniteDimensional ℝ E] :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin])

/-- The base sets of the finite-cover presentation of `TM` are the sources of the charts. -/
theorem mapFibre_tangentBundle_baseSet (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [FiniteDimensional ℝ E]
    (i : atlas H M) :
    ((tangentBundle I M).mapFibre (modelLinearEquiv (E := E))).baseSet i = i.1.source :=
  Work.TangentClasses.tangentBundle_baseSet (I := I) (M := M) i

/-- The size of the finite chart cover chosen for a compact charted space. -/
noncomputable def chartCoverSize {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] : ℕ :=
  Classical.choose (exists_finite_chart_cover (H := H) (M := M))

/-- The finite chart cover chosen for a compact charted space: a family of charts indexed by
`Fin (chartCoverSize H M)` whose sources cover `M`. -/
noncomputable def chartCover {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] :
    Fin (chartCoverSize (H := H) (M := M)) → atlas H M :=
  Classical.choose (Classical.choose_spec (exists_finite_chart_cover (H := H) (M := M)))

/-- The defining property of `chartCover`: the sources of its charts cover the manifold. -/
theorem chartCover_spec {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] :
    ∀ x : M, ∃ i, x ∈ (chartCover (H := H) (M := M) i).1.source :=
  Classical.choose_spec (Classical.choose_spec (exists_finite_chart_cover (H := H) (M := M)))

/-- The witness that `chartCover` still covers the base in the form `Work.Thom.RealBundle.reindex`
expects. -/
theorem chartCover_reindex_cover (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
    [FiniteDimensional ℝ E] :
    ∀ x : M, ∃ i, x ∈ ((tangentBundle I M).mapFibre (modelLinearEquiv (E := E))).baseSet
      (chartCover (H := H) (M := M) i) := by
  intro x
  obtain ⟨i, hi⟩ := chartCover_spec (H := H) (M := M) x
  exact ⟨i, by rw [mapFibre_tangentBundle_baseSet I M]; exact hi⟩

/-- **The complexified tangent bundle of a compact smooth manifold, presented over a finite cover**:
the four-step construction of the module docstring, as a single named gluing datum.  Its rank is
`finrank ℝ E` and it is indexed by a finite type, so the Chern classes
`Work.Thom.chernClass` apply to it. -/
noncomputable def complexifiedTangentBundleFinite (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
    [FiniteDimensional ℝ E] :
    VectorBundleCore ℂ M (EuclideanSpace ℂ (Fin (Module.finrank ℝ E)))
      (Fin (chartCoverSize (H := H) (M := M))) :=
  complexificationCore
    ((((tangentBundle I M).mapFibre (modelLinearEquiv (E := E))).reindex
      (chartCover (H := H) (M := M)) (chartCover_reindex_cover I M)))

/-- **The first Pontryagin class of the tangent bundle of a compact smooth manifold**,
`p₁(TM) = - c₂(TM ⊗_ℝ ℂ) ∈ H⁴(M;ℤ)`: item (4) of the chapter's deliverable.  It is a *defined*
class, a function of `M` alone — no free data. -/
noncomputable def p1Tangent' (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
    [FiniteDimensional ℝ E] : Coh ℤ 4 M :=
  - chernClass (Module.finrank ℝ E) 2 (complexifiedTangentBundleFinite I M)

/-- The defining equation of `p1Tangent'`. -/
theorem p1Tangent'_def (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M] [FiniteDimensional ℝ E] :
    p1Tangent' I M = - chernClass (Module.finrank ℝ E) 2 (complexifiedTangentBundleFinite I M) :=
  rfl

/-- **The second Pontryagin class of the tangent bundle of a compact smooth manifold**,
`p₂(TM) = c₄(TM ⊗_ℝ ℂ) ∈ H⁸(M;ℤ)`.  Like `p1Tangent'` it is a *defined* class, a function of `M`
alone; this is what repairs the defect recorded in `Submission/NOTES.md` §15.10, where `p₂` was free
data (and *not* determined by the restriction to a disc bundle). -/
noncomputable def p2Tangent' (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
    [FiniteDimensional ℝ E] : Coh ℤ 8 M :=
  chernClass (Module.finrank ℝ E) 4 (complexifiedTangentBundleFinite I M)

/-- The defining equation of `p2Tangent'`. -/
theorem p2Tangent'_def (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M] [FiniteDimensional ℝ E] :
    p2Tangent' I M = chernClass (Module.finrank ℝ E) 4 (complexifiedTangentBundleFinite I M) :=
  rfl

end

end Work.Thom
