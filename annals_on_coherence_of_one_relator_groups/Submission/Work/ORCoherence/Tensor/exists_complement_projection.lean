import Mathlib
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Map

namespace Work.ORCoherence.Tensor

open scoped BigOperators

/-- The projection of `X →₀ R` onto the coefficients outside `X₀`: it keeps the
coefficient at `i` when `i ∉ X₀` and sends it to `0` when `i ∈ X₀`. -/
noncomputable def complementProjection {R : Type*} [Ring R] {X : Type*} [DecidableEq X]
    (X₀ : Finset X) : (X →₀ R) →ₗ[R] (X →₀ R) where
  toFun f := Finsupp.filter (fun i => i ∉ X₀) f
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

lemma complementProjection_apply {R : Type*} [Ring R] {X : Type*} [DecidableEq X]
    (X₀ : Finset X) (f : X →₀ R) :
    complementProjection X₀ f = Finsupp.filter (fun i => i ∉ X₀) f := rfl

lemma complementProjection_apply_apply {R : Type*} [Ring R] {X : Type*} [DecidableEq X]
    (X₀ : Finset X) (f : X →₀ R) (i : X) :
    complementProjection X₀ f i = if i ∈ X₀ then 0 else f i := by
  rw [complementProjection_apply, Finsupp.filter_apply]
  by_cases hi : i ∈ X₀ <;> simp [hi]

/-- The kernel of `complementProjection X₀` is the submodule of finitely supported
functions whose support is contained in `X₀`. -/
lemma ker_complementProjection {R : Type*} [Ring R] {X : Type*} [DecidableEq X]
    (X₀ : Finset X) :
    LinearMap.ker (complementProjection (R := R) (X := X) X₀)
      = Finsupp.supported R R (↑X₀ : Set X) := by
  ext f
  rw [LinearMap.mem_ker, Finsupp.mem_supported]
  constructor
  · intro h i hi
    by_contra hnot
    have h2 : complementProjection X₀ f i = 0 := by rw [h]; simp
    rw [complementProjection_apply_apply] at h2
    have hnot' : ¬ (i ∈ X₀) := hnot
    rw [if_neg hnot'] at h2
    exact (Finsupp.mem_support_iff.mp (by simpa using hi)) h2
  · intro hsub
    ext i
    rw [complementProjection_apply_apply]
    by_cases hi : i ∈ X₀
    · simp [hi]
    · simp only [if_neg hi]
      by_contra hne
      have hmem : i ∈ f.support := Finsupp.mem_support_iff.mpr hne
      exact hi (by simpa using hsub hmem)

theorem exists_complement_projection {R : Type*} [Ring R] (X : Type*) [DecidableEq X]
    (X₀ : Finset X) :
    ∃ ρ : (X →₀ R) →ₗ[R] (X →₀ R),
      LinearMap.ker ρ = Submodule.span R {x | ∃ i ∈ X₀, x = Finsupp.single i (1 : R)} := by
  refine ⟨complementProjection X₀, ?_⟩
  have hset : (fun i => Finsupp.single i (1 : R)) '' (↑X₀ : Set X)
      = {x | ∃ i ∈ X₀, x = Finsupp.single i (1 : R)} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [ker_complementProjection, Finsupp.supported_eq_span_single, hset]

end Work.ORCoherence.Tensor
