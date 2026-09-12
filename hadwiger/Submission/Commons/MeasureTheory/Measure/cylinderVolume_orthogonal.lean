import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Commons.MeasureTheory.Measure

/-- The linear map `(x, y) ↦ e₁ x + e₂ y` on the orthogonal sum of the two Euclidean
factors. -/
private def cylMap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V) :
    WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) →ₗ[ℝ] V where
  toFun := fun w => e1 w.fst + e2 w.snd
  map_add' := by
    intro x y
    rw [WithLp.add_fst, WithLp.add_snd, map_add, map_add]
    abel
  map_smul' := by
    intro c x
    rw [WithLp.smul_fst, WithLp.smul_snd]
    change e1 (c • x.fst) + e2 (c • x.snd) = c • (e1 x.fst + e2 x.snd)
    rw [e1.map_smul, e2.map_smul]
    rw [← smul_add]

private lemma cylMap_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0)
    (w : WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) :
    ‖cylMap e1 e2 w‖ ^ 2 = ‖w‖ ^ 2 := by
  change ‖e1 w.fst + e2 w.snd‖ ^ 2 = ‖w‖ ^ 2
  rw [norm_add_sq_real]
  rw [horth w.fst w.snd]
  ring_nf
  rw [e1.norm_map w.fst, e2.norm_map w.snd]
  rw [WithLp.prod_norm_sq_eq_of_L2 w]

private lemma cylMap_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0)
    (w : WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) :
    ‖cylMap e1 e2 w‖ = ‖w‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (cylMap_norm_sq e1 e2 horth w)

/-- The linear isometry `(x, y) ↦ e₁ x + e₂ y` from the orthogonal sum. -/
private def cylIsom {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0) :
    WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) →ₗᵢ[ℝ] V where
  toLinearMap := cylMap e1 e2
  norm_map' := cylMap_norm e1 e2 horth

private lemma mem_range_cylMap_of_left {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V) (x : EuclideanSpace ℝ (Fin k)) :
    e1 x ∈ LinearMap.range (cylMap e1 e2) := by
  refine ⟨WithLp.toLp 2 (x, 0), ?_⟩
  simp [cylMap]

private lemma mem_range_cylMap_of_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V) (y : EuclideanSpace ℝ (Fin l)) :
    e2 y ∈ LinearMap.range (cylMap e1 e2) := by
  refine ⟨WithLp.toLp 2 (0, y), ?_⟩
  simp [cylMap]

private lemma cylMap_range_eq_top {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (hspan : Submodule.span ℝ (Set.range e1 ∪ Set.range e2) = ⊤) :
    LinearMap.range (cylMap e1 e2) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro v hv
    rcases hv with hv | hv
    · rcases hv with ⟨x, rfl⟩
      exact mem_range_cylMap_of_left e1 e2 x
    · rcases hv with ⟨y, rfl⟩
      exact mem_range_cylMap_of_right e1 e2 y

/-- The isometric linear equivalence between the orthogonal sum and `V`. -/
private noncomputable def cylEquiv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (hspan : Submodule.span ℝ (Set.range e1 ∪ Set.range e2) = ⊤)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0) :
    WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) ≃ₗᵢ[ℝ] V := by
  refine LinearIsometryEquiv.ofSurjective (cylIsom e1 e2 horth) ?_
  change Function.Surjective (cylMap e1 e2)
  rw [← LinearMap.range_eq_top]
  exact cylMap_range_eq_top e1 e2 hspan

private lemma cylEquiv_apply_toLp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (hspan : Submodule.span ℝ (Set.range e1 ∪ Set.range e2) = ⊤)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0)
    (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :
    cylEquiv e1 e2 hspan horth (WithLp.toLp 2 p) = e1 p.1 + e2 p.2 := by
  rcases p with ⟨x, y⟩
  simp [cylEquiv, cylIsom, cylMap]

/-- Pushforward measure of an injective measure-preserving map. -/
private lemma measure_image_eq_of_measurePreserving_emb {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) (hfe : MeasurableEmbedding f) (s : Set α) :
    ν (f '' s) = μ s := by
  calc
    ν (f '' s) = μ (f ⁻¹' (f '' s)) := (hf.measure_preimage_emb hfe (f '' s)).symm
    _ = μ s := by rw [Set.preimage_image_eq _ hfe.injective]

/-- The cylinder set is the translate of the image of the orthogonal sum. -/
private lemma cylinder_set_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (hspan : Submodule.span ℝ (Set.range e1 ∪ Set.range e2) = ⊤)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0)
    (a : V) (A : Set (EuclideanSpace ℝ (Fin k))) (Z : Set (EuclideanSpace ℝ (Fin l))) :
    Set.image2 (fun (x y : V) => x + y)
        ((fun x : EuclideanSpace ℝ (Fin k) => a + e1 x) '' A) (e2 '' Z) =
      (fun v : V => a + v) ''
        ((cylEquiv e1 e2 hspan horth :
          WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → V) ''
          (WithLp.toLp 2 '' (A ×ˢ Z))) := by
  -- LHS as an image2 over A and Z with the fully associated addition
  have hL : Set.image2 (fun (x y : V) => x + y)
        ((fun x : EuclideanSpace ℝ (Fin k) => a + e1 x) '' A) (e2 '' Z)
      = Set.image2 (fun (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin l)) =>
          a + (e1 x + e2 y)) A Z := by
    rw [Set.image2_image_left, Set.image2_image_right]
    apply Set.image2_congr'
    intro x y
    exact add_assoc a (e1 x) (e2 y)
  -- inner part of the right hand side
  have hInner : (cylEquiv e1 e2 hspan horth :
        WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → V) ''
          (WithLp.toLp 2 '' (A ×ˢ Z))
      = Set.image2 (fun (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin l)) =>
          e1 x + e2 y) A Z := by
    rw [← Set.image_comp]
    apply le_antisymm <;> intro v <;> simp only [Set.mem_image, Set.mem_prod]
    · rintro ⟨p, hp, h⟩
      rcases hp with ⟨hpA, hpZ⟩
      refine ⟨p.1, hpA, p.2, hpZ, ?_⟩
      simpa [cylEquiv_apply_toLp] using h
    · rintro ⟨x, hxA, y, hyZ, h⟩
      refine ⟨(x, y), ⟨hxA, hyZ⟩, ?_⟩
      simpa [cylEquiv_apply_toLp] using h
  calc
    Set.image2 (fun (x y : V) => x + y)
        ((fun x : EuclideanSpace ℝ (Fin k) => a + e1 x) '' A) (e2 '' Z)
        = Set.image2 (fun (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin l)) =>
            a + (e1 x + e2 y)) A Z := hL
    _ = (fun v : V => a + v) ''
          (Set.image2 (fun (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin l)) =>
            e1 x + e2 y) A Z) := by
          rw [Set.image_image2]
    _ = (fun v : V => a + v) '' ((cylEquiv e1 e2 hspan horth :
          WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → V) ''
          (WithLp.toLp 2 '' (A ×ˢ Z))) := by rw [hInner]


/-- The requested cylinder volume identity: the volume of an orthogonal cylinder
`(a + e₁ A) + e₂ Z` in `V` is the product of the volumes of `A` and `Z`. -/
theorem cylinderVolume_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {k l : ℕ}
    (e1 : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] V)
    (e2 : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] V)
    (hspan : Submodule.span ℝ (Set.range e1 ∪ Set.range e2) = ⊤)
    (horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0)
    (a : V) (A : Set (EuclideanSpace ℝ (Fin k))) (Z : Set (EuclideanSpace ℝ (Fin l)))
    (hA : MeasurableSet A) (hZ : MeasurableSet Z) :
    MeasureTheory.volume
      (Set.image2 (fun (x y : V) => x + y)
        ((fun x : EuclideanSpace ℝ (Fin k) => a + e1 x) '' A) (e2 '' Z)) =
      MeasureTheory.volume A * MeasureTheory.volume Z := by
  let W := WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))
  let S : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) := A ×ˢ Z
  have _hSmeas : MeasurableSet S := by
    simpa [S] using hA.prod hZ
  have hfeτ : MeasurableEmbedding (fun v : V => a + v) := by
    simpa using (Homeomorph.addLeft a).measurableEmbedding
  have hfeι : MeasurableEmbedding (cylEquiv e1 e2 hspan horth : W → V) := by
    simpa [LinearIsometryEquiv.coe_toHomeomorph] using
      (cylEquiv e1 e2 hspan horth).toHomeomorph.measurableEmbedding
  have hfeToLp : MeasurableEmbedding (WithLp.toLp 2 :
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l) → W) := by
    simpa [MeasurableEquiv.coe_toLp] using
      (MeasurableEquiv.toLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))).measurableEmbedding
  rw [cylinder_set_eq e1 e2 hspan horth a A Z]
  calc
    MeasureTheory.volume ((fun v : V => a + v) ''
        ((cylEquiv e1 e2 hspan horth : W → V) '' (WithLp.toLp 2 '' S)))
        = MeasureTheory.volume ((cylEquiv e1 e2 hspan horth : W → V) ''
            (WithLp.toLp 2 '' S)) := by
          exact measure_image_eq_of_measurePreserving_emb
            (measurePreserving_add_left (volume : Measure V) a) hfeτ
            ((cylEquiv e1 e2 hspan horth : W → V) '' (WithLp.toLp 2 '' S))
    _ = MeasureTheory.volume (WithLp.toLp 2 '' S) := by
          exact measure_image_eq_of_measurePreserving_emb
            (LinearIsometryEquiv.measurePreserving (cylEquiv e1 e2 hspan horth)) hfeι
            (WithLp.toLp 2 '' S)
    _ = MeasureTheory.volume S := by
          exact measure_image_eq_of_measurePreserving_emb
            (WithLp.volume_preserving_toLp (EuclideanSpace ℝ (Fin k))
              (EuclideanSpace ℝ (Fin l))) hfeToLp S
    _ = MeasureTheory.volume A * MeasureTheory.volume Z := by
          rw [MeasureTheory.Measure.volume_eq_prod (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin l))]
          simp [S]

end Commons.MeasureTheory.Measure