import Mathlib
import Submission.Work.WilE2.range_eq_top_of_linearIndependent_comp

set_option autoImplicit false

namespace Work.WilE2.RegVals

/-- The (injective) linear map forgetting that a linear map between topological vector
spaces is continuous. -/
noncomputable def clmToLinearMap (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] :
    (E →L[ℝ] ℝ) →ₗ[ℝ] (E →ₗ[ℝ] ℝ) where
  toFun f := f.toLinearMap
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

lemma clmToLinearMap_ker (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] :
    (clmToLinearMap E).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  ext x
  have h := congrArg (fun g : E →ₗ[ℝ] ℝ => g x) hf
  simpa [clmToLinearMap] using h

/-- A continuous linear map `T : E → ℝ^m` is surjective exactly when its `m` coordinate
functionals `x ↦ (T x) a` are linearly independent in the dual of `E`. -/
theorem surjective_iff_linearIndependent_coord {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (T : E →L[ℝ] (Fin m → ℝ)) :
    Function.Surjective T ↔ LinearIndependent ℝ (fun a => (ContinuousLinearMap.proj a).comp T) := by
  classical
  constructor
  · -- Surjectivity forces the coordinates to be independent: a linear relation between
    -- them gives a relation between the coordinate functionals of `ℝ^m`, which vanishes
    -- because every vector of `ℝ^m` is a value of `T`.
    intro hsurj
    rw [Fintype.linearIndependent_iff]
    intro g hg b
    obtain ⟨x, hx⟩ := hsurj (Pi.single b (1 : ℝ))
    have h3 : (∑ i, g i * (Pi.single b (1:ℝ) : Fin m → ℝ) i) = g b := by
      rw [Fintype.sum_eq_single b]
      · simp
      · intro i hi
        have h0 : (Pi.single b (1:ℝ) : Fin m → ℝ) i = 0 := Pi.single_eq_of_ne hi 1
        rw [h0, mul_zero]
    have key : (∑ i, g i * (T x) i) = 0 := by
      have h1 : (∑ i, g i * (T x) i)
          = (∑ i, g i • ((ContinuousLinearMap.proj i).comp T)) x := by simp
      rw [h1, hg]
      simp
    rw [hx] at key
    rw [h3] at key
    exact key
  · -- Conversely, independence of the coordinate functionals gives surjectivity: they are
    -- the pullbacks of the coordinate projections along `T`, and the latter form a basis of
    -- the dual of `ℝ^m`, so the dual map of `T` is injective.
    intro hind
    have hind' : LinearIndependent ℝ
        (fun a => clmToLinearMap E ((ContinuousLinearMap.proj a).comp T)) :=
      hind.map' (clmToLinearMap E) (clmToLinearMap_ker E)
    have hind'' : LinearIndependent ℝ
        (fun a => (ContinuousLinearMap.proj a).toLinearMap.comp T.toLinearMap) := by
      simpa [clmToLinearMap] using hind'
    obtain ⟨htop, _⟩ := Work.WilE2.range_eq_top_of_linearIndependent_comp T.toLinearMap
        (fun a : Fin m => (ContinuousLinearMap.proj a).toLinearMap) hind''
        (by simp [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
    have hsurj' : Function.Surjective T.toLinearMap := LinearMap.range_eq_top.mp htop
    intro y
    obtain ⟨x, hx⟩ := hsurj' y
    exact ⟨x, hx⟩

end Work.WilE2.RegVals
