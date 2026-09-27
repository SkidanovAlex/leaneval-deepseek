import Mathlib
import Submission.Work.Projection.GeneralDefs
import Submission.Work.Projection.Basic
import Submission.Work.Projection.compact_embedding
import Submission.Work.Projection.exists_good_direction_general
import Submission.Work.Projection.exists_countable_chart_cover_general

/-!
# The weak Whitney embedding theorem for compact manifolds, general model with corners

Every compact smooth manifold modelled on a finite dimensional real vector space `E` and a
boundaryless model with corners `I : ModelWithCorners ℝ E H` embeds smoothly and immersively
into `ℝ^{2n+1}`, where `n = finrank ℝ E`.

The proof follows the Euclidean case (`Work.Projection.exists_embedding_euclidean_of_compact`):

1. Mathlib's partition-of-unity argument (`exists_embedding_euclidean_of_compact`, already stated
   for an arbitrary model with corners) produces a smooth *closed* embedding `e₀ : M → ℝ^K` with
   injective derivative, for some `K`.
2. Inflate it to `ℝ^{2n+1+K}` by adding zeros (`pad`).
3. Apply the general projection lemma `exists_good_direction_general` repeatedly, lowering the
   ambient dimension one at a time, until it reaches `2n+1`.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

/-- Composition of a smooth map with a continuous linear map, for an arbitrary model with
corners. -/
lemma contMDiff_comp_clm_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N k : ℕ} (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (e : M → EuclideanSpace ℝ (Fin N))
    (hsm : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ e) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ (⇑L ∘ e) :=
  L.contMDiff.comp hsm

/-- The derivative of `L ∘ e` for a continuous linear map `L`, for an arbitrary model with
corners. -/
lemma mfderiv_comp_clm_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N k : ℕ} (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (e : M → EuclideanSpace ℝ (Fin N))
    (hsm : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ e) (x : M) :
    mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (⇑L ∘ e) x =
      L ∘L mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e x := by
  rw [mfderiv_comp x (f := e) (g := ⇑L) (L.differentiableAt.mdifferentiableAt)
    (hsm.mdifferentiableAt (by simp))]
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- **Reduction to the base dimension.**  An injective immersion of a nonempty manifold modelled
on the finite dimensional `E` into `ℝ^{2n+1+m}`, `n = finrank ℝ E`, can be lowered to one into
`ℝ^{2n+1}`. -/
theorem reduce_steps_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M] (m : ℕ)
    (e : M → EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1 + m)))
    (hsm : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1 + m))) ∞ e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1 + m))) e x)) :
    ∃ e' : M → EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1))) ∞ e' ∧
      Function.Injective e' ∧
      ∀ x, Function.Injective
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1))) e' x) := by
  induction m with
  | zero => exact ⟨e, hsm, hinj, himm⟩
  | succ m ih =>
      obtain ⟨p, hcov⟩ := exists_countable_chart_cover_general (I := I) (M := M)
      obtain ⟨u, hu1, hu2⟩ :=
        exists_good_direction_general (I := I) (M := M)
          (k := 2 * Module.finrank ℝ E + 1 + m) (by omega) e hsm hinj himm p hcov
      refine ih (⇑(projVec u) ∘ e) (contMDiff_comp_clm_general (projVec u) e hsm) hu1 ?_
      intro x
      rw [mfderiv_comp_clm_general (projVec u) e hsm x]
      exact hu2 x

/-- **Weak Whitney embedding theorem** for compact smooth manifolds modelled on a finite
dimensional real vector space `E` and a boundaryless model with corners `I`: such a manifold embeds
smoothly and immersively in `ℝ^{2n+1}`, where `n = finrank ℝ E`. -/
theorem exists_embedding_euclidean_of_compact_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1))) ∞ e ∧
      IsEmbedding e ∧
      ∀ x, Function.Injective
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E + 1))) e x) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x,
      ⟨⟨Subsingleton.elim _ _⟩, fun x => isEmptyElim x⟩, fun x => isEmptyElim x⟩
  · haveI := hM
    obtain ⟨K, e₀, hsm₀, hemb₀, himm₀⟩ :
        ∃ (K : ℕ) (e : M → EuclideanSpace ℝ (Fin K)),
          ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ e ∧
          IsClosedEmbedding e ∧
          ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) e x) :=
      _root_.exists_embedding_euclidean_of_compact (I := I) (M := M)
    have hle : K ≤ 2 * Module.finrank ℝ E + 1 + K := by omega
    obtain ⟨e', hsm', hinj', himm'⟩ :=
      reduce_steps_general (I := I) (M := M) K (⇑(pad hle) ∘ e₀)
        (contMDiff_comp_clm_general (pad hle) e₀ hsm₀)
        (Function.Injective.comp (pad_injective hle) hemb₀.injective) (fun x => by
          rw [mfderiv_comp_clm_general (pad hle) e₀ hsm₀ x]
          exact (pad_injective hle).comp (himm₀ x))
    exact ⟨e', hsm', (Continuous.isClosedEmbedding hsm'.continuous hinj').toIsEmbedding, himm'⟩

end Work.Projection
