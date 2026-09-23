import Mathlib
import Submission.Work.OddBound.PiExtChart
import Submission.Work.OddBound.design.PiExtManifold
import Submission.Work.piManifold.isManifold_pi

/-!
# The polygon space `Fin (N-1) → M` is a `C^n` manifold on `𝓘(ℝ, Fin (N-1) → E)`

`PiExtChart.lean` builds the charted space `piChartedSpaceExt` on `P = Fin (N-1) → M` out of the
`E`-valued extended charts `extChartHomeo x = I ∘ chartAt H x`, i.e. as the `piChartedSpace` of the
family `fun _ ↦ chartedSpaceExtChart`.

Here we prove that this charted space is a `C^n` manifold (for every `n ≤ ∞`) with respect to the
*self* model `𝓘(ℝ, Fin (N-1) → E)` on the model vector space `Fin (N-1) → E`.

The proof has two ingredients:

* the transition `(extChartHomeo x).symm ≫ extChartHomeo y` of two extended charts is `C^n` on its
  source (`extChartHomeo_trans_contDiffOn`), because its underlying partial equivalence is Mathlib's
  `I.extendCoordChange (chartAt H x) (chartAt H y)`, whose smoothness is
  `ModelWithCorners.contDiffOn_extendCoordChange`;
* a finite `pi`-product of maps that are `C^n` for the self model on `E` is `C^n` for the self model
  on the product (`contDiffGroupoid_pi_self`, the `𝓘(ℝ, ·)`-analogue of `contDiffGroupoid_prod`).

Both are combined in the `compatible` field of the `HasGroupoid` structure underlying `IsManifold`,
using `Work.piManifold.pi_symm_trans_pi` to write the transition of the product charts as the product
of the transitions.
-/

namespace Work.OddBound

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField

noncomputable section

section Groupoid

/-- For the *self* model `𝓘(ℝ, F)` on a normed space, membership in the `C^n` groupoid is simply
`C^n`-ness of the map on its source together with `C^n`-ness of its inverse on its target. -/
lemma mem_contDiffGroupoid_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {e : OpenPartialHomeomorph F F} :
    e ∈ contDiffGroupoid n (𝓘(ℝ, F)) ↔
      ContDiffOn ℝ n ⇑e e.source ∧ ContDiffOn ℝ n ⇑e.symm e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.preimage_id, Set.range_id, Set.inter_univ, Function.comp_id, Function.id_comp]

end Groupoid

section ExtChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- The `E`-valued extended chart `extChartHomeo x` has the same underlying partial equivalence as
Mathlib's `extChartAt I x`. -/
lemma extChartHomeo_toPartialEquiv (x : M) :
    (extChartHomeo (I := I) x).toPartialEquiv = extChartAt I x := by
  apply PartialEquiv.ext
  · intro m
    show (extChartHomeo (I := I) x) m = (extChartAt I x) m
    rw [extChartHomeo_coe, extChartAt_coe]
    rfl
  · intro z
    show (extChartHomeo (I := I) x).symm z = (extChartAt I x).symm z
    rw [show (extChartHomeo (I := I) x).symm z = (chartAt H x).symm (I.symm z) from by
      rw [extChartHomeo, OpenPartialHomeomorph.transHomeomorph_symm_apply]
      simp [ModelWithCorners.toHomeomorph_symm_apply]]
    rw [extChartAt_coe_symm]
    rfl
  · rw [show (extChartHomeo (I := I) x).toPartialEquiv.source
          = (extChartHomeo (I := I) x).source from rfl,
      extChartHomeo_source, extChartAt_source]

/-- The transition of two extended charts `(extChartHomeo x).symm ≫ extChartHomeo y` is the partial
equivalence `I.extendCoordChange (chartAt H x) (chartAt H y)`. -/
lemma extChartHomeo_trans_toPartialEquiv (x y : M) :
    ((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y)).toPartialEquiv
      = ModelWithCorners.extendCoordChange (I := I) (chartAt H x) (chartAt H y) := by
  rw [OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.symm_toPartialEquiv,
    extChartHomeo_toPartialEquiv, extChartHomeo_toPartialEquiv]
  rfl

/-- The transition of two extended charts is `C^n` on its source. -/
lemma extChartHomeo_trans_contDiffOn (n : ℕ∞ω) (hn : n ≤ (∞ : ℕ∞ω)) (x y : M) :
    ContDiffOn ℝ n ⇑((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y))
      ((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y)).source := by
  haveI : IsManifold I n M := IsManifold.of_le hn
  have h := ModelWithCorners.contDiffOn_extendCoordChange (I := I) (n := n)
    (e := chartAt H x) (e' := chartAt H y) (IsManifold.chart_mem_maximalAtlas (I := I) x)
    (IsManifold.chart_mem_maximalAtlas (I := I) y)
  show ContDiffOn ℝ n ⇑(((extChartHomeo (I := I) x).symm.trans
      (extChartHomeo (I := I) y)).toPartialEquiv)
    (((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y)).toPartialEquiv).source
  rw [extChartHomeo_trans_toPartialEquiv]
  exact h

/-- The transition of two extended charts belongs to the `C^n` groupoid for the self model on `E`. -/
lemma extChartHomeo_trans_mem (n : ℕ∞ω) (hn : n ≤ (∞ : ℕ∞ω)) (x y : M) :
    ((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y))
      ∈ contDiffGroupoid n (𝓘(ℝ, E)) := by
  rw [mem_contDiffGroupoid_self]
  refine ⟨extChartHomeo_trans_contDiffOn n hn x y, ?_⟩
  have hsymm : ((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y)).symm
      = (extChartHomeo (I := I) y).symm.trans (extChartHomeo (I := I) x) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  have htar : ((extChartHomeo (I := I) x).symm.trans (extChartHomeo (I := I) y)).target
      = ((extChartHomeo (I := I) y).symm.trans (extChartHomeo (I := I) x)).source := by
    rw [← OpenPartialHomeomorph.symm_source, hsymm]
  rw [hsymm, htar]
  exact extChartHomeo_trans_contDiffOn n hn y x

end ExtChart

section PiSelf

/-- A finite `pi`-product of `C^n` open partial homeomorphisms of `F` is `C^n` for the *self* model
on the product `ι → F`. This is the `𝓘(ℝ, ·)`-analogue of `contDiffGroupoid_prod`. -/
lemma contDiffGroupoid_pi_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] {n : ℕ∞ω} {g : ι → OpenPartialHomeomorph F F}
    (hg : ∀ i, g i ∈ contDiffGroupoid n (𝓘(ℝ, F))) :
    OpenPartialHomeomorph.pi g ∈ contDiffGroupoid n (𝓘(ℝ, ι → F)) := by
  rw [mem_contDiffGroupoid_self]
  constructor
  · have hgi : ∀ i, ContDiffOn ℝ n ⇑(g i) (g i).source :=
      fun i => (mem_contDiffGroupoid_self.mp (hg i)).1
    rw [contDiffOn_pi]
    intro i
    refine (hgi i).comp
      ((ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).contDiff.contDiffOn) ?_
    intro x hx
    exact (Set.mem_univ_pi.mp hx) i
  · have hgi : ∀ i, ContDiffOn ℝ n ⇑((g i).symm) ((g i).target) :=
      fun i => (mem_contDiffGroupoid_self.mp (hg i)).2
    rw [contDiffOn_pi]
    intro i
    refine (hgi i).comp
      ((ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).contDiff.contDiffOn) ?_
    intro x hx
    exact (Set.mem_univ_pi.mp hx) i

end PiSelf

end

theorem isManifold_piChartedSpaceExt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    (N : ℕ) (n : WithTop ℕ∞) (hn : n ≤ (∞ : ℕ∞ω)) :
    @IsManifold ℝ _ ((Fin (N - 1)) → E) _ _ ((Fin (N - 1)) → E) _
      (𝓘(ℝ, (Fin (N - 1)) → E)) n ((Fin (N - 1)) → M) _ (Work.OddBound.piChartedSpaceExt (I := I) N) := by
  classical
  refine @IsManifold.mk ℝ _ _ _ _ _ _ _ _ ((Fin (N - 1)) → M) _
    (piChartedSpaceExt (I := I) N) ?_
  refine @HasGroupoid.mk ((Fin (N - 1)) → E) _ ((Fin (N - 1)) → M) _
    (piChartedSpaceExt (I := I) N) (contDiffGroupoid n (𝓘(ℝ, (Fin (N - 1)) → E))) ?_
  rintro f g ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  have hci : ∀ i : Fin (N - 1), ∃ x : M, extChartHomeo (I := I) x = c i := fun i => by
    have h := (Set.mem_univ_pi.mp hc) i
    change c i ∈ Set.range (extChartHomeo (I := I)) at h
    exact Set.mem_range.mp h
  choose x hx using hci
  have hci' : ∀ i : Fin (N - 1), ∃ y : M, extChartHomeo (I := I) y = c' i := fun i => by
    have h := (Set.mem_univ_pi.mp hc') i
    change c' i ∈ Set.range (extChartHomeo (I := I)) at h
    exact Set.mem_range.mp h
  choose y hy using hci'
  rw [Work.piManifold.pi_symm_trans_pi]
  refine contDiffGroupoid_pi_self (fun i => ?_)
  rw [← hx i, ← hy i]
  exact extChartHomeo_trans_mem n hn (x i) (y i)

end Work.OddBound
