import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Finite products of smooth manifolds

This file proves that the finite product `ι → M` of a smooth manifold `M`, modelled on a
model-with-corners `I`, is again a smooth manifold, modelled on `ModelWithCorners.pi (fun _ => I)`.

The two ingredients supplied by Mathlib are

* `ChartedSpace (ModelPi H) (∀ i, M i)` (`piChartedSpace`), whose charts are the `pi`-products of
  the charts of the factors, and
* `ModelWithCorners.pi` on `(∀ i, E i, ModelPi H)`.

What is missing (and is supplied here) is the fact that the resulting atlas is `C^n`: the transition
maps of the product are the `pi`-products of the transition maps of the factors, and a finite
`pi`-product of `C^n` maps (read through the models) is `C^n`.  This is the analogue for `pi`-types
of `contDiffGroupoid_prod` and `IsManifold.prod` from the library.
-/

namespace Work.piManifold

open scoped ContDiff Manifold Bundle Topology
open Bundle

section PiManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {H : ι → Type*} [∀ i, TopologicalSpace (H i)]
variable {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}

/-! ### Unfolding lemmas for `ModelWithCorners.pi` -/

@[simp] lemma modelPi_apply (x : (i : ι) → H i) (i : ι) :
    ModelWithCorners.pi I x i = I i (x i) := rfl

@[simp] lemma modelPi_symm_apply (x : (i : ι) → E i) (i : ι) :
    (ModelWithCorners.pi I).symm x i = (I i).symm (x i) := by
  show (PartialEquiv.pi fun i => (I i).toPartialEquiv).symm x i = (I i).symm (x i)
  rw [PartialEquiv.pi_symm]
  rfl

lemma range_modelPi :
    Set.range (ModelWithCorners.pi I) = Set.univ.pi (fun i => Set.range (I i)) := by
  ext z
  simp only [Set.mem_range, Set.mem_univ_pi]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro hz
    exact ⟨fun i => (hz i).choose, funext fun i => by simpa using (hz i).choose_spec⟩

lemma mem_univ_pi_symm_modelPi (s : ∀ i, Set (H i)) (z : (i : ι) → E i) :
    (ModelWithCorners.pi I).symm z ∈ Set.univ.pi s ↔ ∀ i, (I i).symm (z i) ∈ s i := by
  rw [Set.mem_univ_pi]
  exact forall_congr' fun i => by simp

/-- The domain of the `pi`-model read through the models of the factors. -/
lemma preimage_pi_range_modelPi (s : ∀ i, Set (H i)) :
    (ModelWithCorners.pi I).symm ⁻¹' (Set.univ.pi s) ∩ Set.range (ModelWithCorners.pi I) =
      Set.univ.pi (fun i => (I i).symm ⁻¹' s i ∩ Set.range (I i)) := by
  ext z
  rw [Set.mem_inter_iff, Set.mem_preimage, mem_univ_pi_symm_modelPi, range_modelPi]
  simp only [Set.mem_univ_pi]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- A finite `pi`-product of maps which are `C^n` when read through the models is `C^n` when read
through the `pi`-model. -/
theorem contDiffOn_modelPi_comp {n : ℕ∞ω} {f : ∀ i, H i → H i} {u : ∀ i, Set (H i)}
    (hf : ∀ i, ContDiffOn 𝕜 n ((I i) ∘ f i ∘ (I i).symm)
      ((I i).symm ⁻¹' u i ∩ Set.range (I i))) :
    ContDiffOn 𝕜 n (fun (x : (i : ι) → E i) (i : ι) => I i (f i ((I i).symm (x i))))
      (Set.univ.pi (fun i => (I i).symm ⁻¹' u i ∩ Set.range (I i))) := by
  rw [contDiffOn_pi]
  intro i
  refine (hf i).comp
    ((ContinuousLinearMap.proj i : ((j : ι) → E j) →L[𝕜] E i).contDiff.contDiffOn) ?_
  intro x hx
  simpa only [ContinuousLinearMap.proj_apply] using Set.mem_univ_pi.mp hx i

/-- The `pi`-product of the inverses composed with the `pi`-product is the `pi`-product of the
composed transition maps. -/
lemma pi_symm_trans_pi {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)]
    (e e' : ∀ i, OpenPartialHomeomorph (Y i) (X i)) :
    (OpenPartialHomeomorph.pi e).symm.trans (OpenPartialHomeomorph.pi e') =
      OpenPartialHomeomorph.pi (fun i => (e i).symm.trans (e' i)) := by
  apply OpenPartialHomeomorph.toPartialEquiv_injective
  simp only [OpenPartialHomeomorph.pi_toPartialHomeomorph,
    OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.symm_toPartialEquiv,
    PartialEquiv.pi_symm, PartialEquiv.pi_trans]

/-- The `pi`-product of `C^n` open partial homeomorphisms (read through models with corners) is
`C^n` for the `pi`-model. This is the `pi`-analogue of `contDiffGroupoid_prod`. -/
theorem contDiffGroupoid_pi {n : ℕ∞ω} {e : ∀ i, OpenPartialHomeomorph (H i) (H i)}
    (he : ∀ i, e i ∈ contDiffGroupoid n (I i)) :
    OpenPartialHomeomorph.pi e ∈ contDiffGroupoid n (ModelWithCorners.pi I) := by
  have he1 : ∀ i, ContDiffOn 𝕜 n ((I i) ∘ ⇑(e i) ∘ (I i).symm)
      ((I i).symm ⁻¹' (e i).source ∩ Set.range (I i)) := by
    intro i
    have h := he i
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at h
    exact h.1
  have he2 : ∀ i, ContDiffOn 𝕜 n ((I i) ∘ ⇑((e i).symm) ∘ (I i).symm)
      ((I i).symm ⁻¹' (e i).target ∩ Set.range (I i)) := by
    intro i
    have h := he i
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at h
    exact h.2
  rw [contDiffGroupoid]
  refine mem_groupoid_of_pregroupoid.mpr ⟨?_, ?_⟩
  · show ContDiffOn 𝕜 n ((ModelWithCorners.pi I) ∘ ⇑(OpenPartialHomeomorph.pi e) ∘
        (ModelWithCorners.pi I).symm)
        ((ModelWithCorners.pi I).symm ⁻¹' (OpenPartialHomeomorph.pi e).source ∩
          Set.range (ModelWithCorners.pi I))
    have h := contDiffOn_modelPi_comp (I := I) (f := fun i => ⇑(e i))
      (u := fun i => (e i).source) he1
    rw [show (OpenPartialHomeomorph.pi e).source = Set.univ.pi (fun i => (e i).source) from rfl]
    rw [preimage_pi_range_modelPi]
    exact h
  · show ContDiffOn 𝕜 n ((ModelWithCorners.pi I) ∘ ⇑((OpenPartialHomeomorph.pi e).symm) ∘
        (ModelWithCorners.pi I).symm)
        ((ModelWithCorners.pi I).symm ⁻¹' (OpenPartialHomeomorph.pi e).target ∩
          Set.range (ModelWithCorners.pi I))
    have h := contDiffOn_modelPi_comp (I := I) (f := fun i => ⇑((e i).symm))
      (u := fun i => (e i).target) he2
    rw [show (OpenPartialHomeomorph.pi e).target = Set.univ.pi (fun i => (e i).target) from rfl]
    rw [preimage_pi_range_modelPi]
    exact h

/-- A finite product of `C^n` manifolds is a `C^n` manifold. This is the `pi`-analogue of
`IsManifold.prod`. -/
theorem isManifoldPi {n : ℕ∞ω} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) n (M i)] :
    IsManifold (ModelWithCorners.pi I) n ((i : ι) → M i) where
  compatible := by
    rintro f g ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have hei : ∀ i, e i ∈ atlas (H i) (M i) := fun i => (Set.mem_univ_pi.mp he) i
    have hei' : ∀ i, e' i ∈ atlas (H i) (M i) := fun i => (Set.mem_univ_pi.mp he') i
    rw [pi_symm_trans_pi]
    exact contDiffGroupoid_pi fun i => (contDiffGroupoid n (I i)).compatible (hei i) (hei' i)

end PiManifold

/-! ### The constant-family case -/

theorem isManifold_pi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι] :
    IsManifold (ModelWithCorners.pi (fun _ : ι => I)) ∞ (ι → M) :=
  isManifoldPi (I := fun _ : ι => I) (M := fun _ : ι => M)

end Work.piManifold
