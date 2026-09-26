import Mathlib
import Submission.Work.Core.Basic

/-!
# Sums of Schwartz functions

Given a family `u : ι → 𝓢(E, ℂ)` of complex-valued Schwartz functions whose
Schwartz seminorms are all summable, the series `∑ i, u i` converges in the
Schwartz space.  The sum is the Schwartz function whose value at `x` is the
pointwise series `∑' i, u i x`.

This is the "polynomial bounds on all Schwartz seminorms imply convergence of
the reconstruction series" step in the proof of the CKMRV Fourier-interpolation
theorem: it lets one build a radial Schwartz function out of four rapidly
decreasing coefficient sequences.

The proof is the standard `M`-test for a family of seminorms generating the
topology (`WithSeminorms`): the seminorm of the difference between the partial
sum over `s` and the full sum is bounded by the sum of the seminorms over the
complement of `s`, which tends to `0`.

## Main results

* `Work.Summability.schwartzSum`: the Schwartz function `x ↦ ∑' i, u i x`.
* `Work.Summability.hasSum_schwartzSum`: the series converges to it in `𝓢(E, ℂ)`.
* `Work.Summability.exists_schwartz_tsum`: the statement requested by the
  CKMRV development.
-/

open Filter
open scoped SchwartzMap Topology ContDiff

namespace Work.Summability

section General

variable {κ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The seminorms of a complex-valued Schwartz function do not depend on whether
they are viewed over `ℂ` or over `ℝ`. -/
lemma schwartz_seminorm_complex_eq {k l : ℕ} (f : 𝓢(E, ℂ)) :
    (SchwartzMap.seminorm ℂ k l) f = (SchwartzMap.seminorm ℝ k l) f := by
  rw [SchwartzMap.seminorm_apply, SchwartzMap.seminorm_apply]

/-- The family of `ℝ`-valued Schwartz seminorms of `u` is summable when the
family of `ℂ`-valued ones is. -/
lemma schwartz_summable_seminorm_real (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (k l : ℕ) :
    Summable fun i => (SchwartzMap.seminorm ℝ k l) (v i) :=
  (h k l).congr fun i => schwartz_seminorm_complex_eq (v i)

/-- If all Schwartz seminorms of `u` are summable then `u` is pointwise
summable. -/
lemma schwartz_summable_apply (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (x : E) :
    Summable fun i => v i x :=
  Summable.of_norm_bounded (h 0 0) fun i => SchwartzMap.norm_le_seminorm ℂ (v i) x

/-- If all Schwartz seminorms of `u` are summable then the norms of the `l`-th
iterated derivatives at a fixed point form a summable family. -/
lemma schwartz_summable_iteratedFDeriv_norm (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (l : ℕ) (x : E) :
    Summable fun i => ‖iteratedFDeriv ℝ l (v i) x‖ :=
  (h 0 l).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun i => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (v i) l x

/-- The pointwise series of a seminorm-summable family of Schwartz functions is
smooth. -/
lemma contDiff_tsum_schwartz (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) :
    ContDiff ℝ ∞ fun x => ∑' i, v i x := by
  refine contDiff_tsum (𝕜 := ℝ) (N := ⊤) (f := fun i => (v i : E → ℂ))
    (v := fun k i => (SchwartzMap.seminorm ℝ 0 k) (v i)) (fun i => (v i).smooth ⊤) ?_ ?_
  · intro k _
    exact schwartz_summable_seminorm_real v h 0 k
  · intro k i x _
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (v i) k x

/-- The iterated derivative of the pointwise series is the pointwise series of
the iterated derivatives. -/
lemma iteratedFDeriv_tsum_schwartz (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (l : ℕ) :
    iteratedFDeriv ℝ l (fun x => ∑' i, v i x) = fun x => ∑' i, iteratedFDeriv ℝ l (v i) x := by
  refine iteratedFDeriv_tsum (𝕜 := ℝ) (N := ⊤) (f := fun i => (v i : E → ℂ))
    (v := fun k i => (SchwartzMap.seminorm ℝ 0 k) (v i)) (fun i => (v i).smooth ⊤) ?_ ?_ le_top
  · intro k _
    exact schwartz_summable_seminorm_real v h 0 k
  · intro k i x _
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (v i) k x

/-- The Schwartz decay estimate for the pointwise series of a seminorm-summable
family, with the sum of the seminorms as the bound. -/
lemma norm_pow_mul_iteratedFDeriv_tsum_le (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (k l : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x => ∑' i, v i x) x‖ ≤
      ∑' i, (SchwartzMap.seminorm ℂ k l) (v i) := by
  rw [iteratedFDeriv_tsum_schwartz v h l]
  calc ‖x‖ ^ k * ‖∑' i, iteratedFDeriv ℝ l (v i) x‖
      ≤ ‖x‖ ^ k * ∑' i, ‖iteratedFDeriv ℝ l (v i) x‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm (schwartz_summable_iteratedFDeriv_norm v h l x)
    _ = ∑' i, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (v i) x‖ := by rw [tsum_mul_left]
    _ ≤ ∑' i, (SchwartzMap.seminorm ℂ k l) (v i) := by
        refine Summable.tsum_le_tsum (fun i => SchwartzMap.le_seminorm ℂ k l (v i) x) ?_ (h k l)
        exact (h k l).of_nonneg_of_le (fun _ => by positivity)
          fun i => SchwartzMap.le_seminorm ℂ k l (v i) x

/-- The sum of a seminorm-summable family of complex-valued Schwartz functions,
as a Schwartz function: the function `x ↦ ∑' i, v i x`. -/
noncomputable def schwartzSum (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) : 𝓢(E, ℂ) where
  toFun := fun x => ∑' i, v i x
  smooth' := contDiff_tsum_schwartz v h
  decay' := fun k n => ⟨_, norm_pow_mul_iteratedFDeriv_tsum_le v h k n⟩

lemma schwartzSum_apply (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (x : E) :
    schwartzSum v h x = ∑' i, v i x := rfl

/-- Every seminorm of the sum is bounded by the sum of the seminorms. -/
lemma seminorm_schwartzSum_le (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (k l : ℕ) :
    (SchwartzMap.seminorm ℂ k l) (schwartzSum v h) ≤
      ∑' i, (SchwartzMap.seminorm ℂ k l) (v i) :=
  SchwartzMap.seminorm_le_bound ℂ k l _
    (tsum_nonneg fun i => apply_nonneg (SchwartzMap.seminorm ℂ k l) (v i))
    fun x => norm_pow_mul_iteratedFDeriv_tsum_le v h k l x

/-- The sum splits as the partial sum over a finite set plus the sum over the
complement. -/
lemma schwartzSum_split (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) (T : Finset κ) :
    schwartzSum v h = (∑ i ∈ T, v i) + schwartzSum (fun i : {j // j ∉ T} => v i)
      (fun k l => (h k l).subtype fun j => j ∉ T) := by
  ext x
  show (∑' i, v i x) = _
  rw [show ((∑ i ∈ T, v i) + schwartzSum (fun i : {j // j ∉ T} => v i)
        (fun k l => (h k l).subtype fun j => j ∉ T)) x
      = ∑ i ∈ T, v i x + ∑' i : {j // j ∉ T}, v i x from by simp [schwartzSum_apply]]
  exact (Summable.sum_add_tsum_compl (s := T) (schwartz_summable_apply v h x)).symm

/-- The sum of the seminorms over the complement of a finite set tends to `0`. -/
lemma tendsto_tsum_compl_seminorm (v : κ → 𝓢(E, ℂ)) (k l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : Finset κ in atTop, (∑' i : {j // j ∉ s}, (SchwartzMap.seminorm ℂ k l) (v i)) < ε :=
  (tendsto_order.1 (tendsto_tsum_compl_atTop_zero
    (fun i => (SchwartzMap.seminorm ℂ k l) (v i)))).2 ε hε

/-- `M`-test for the Schwartz space: if all Schwartz seminorms of a family are
summable then the family is summable in the Schwartz space, with sum `schwartzSum`. -/
theorem hasSum_schwartzSum (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) :
    HasSum v (schwartzSum v h) := by
  show Tendsto (fun s : Finset κ => ∑ i ∈ s, v i) atTop (𝓝 (schwartzSum v h))
  refine ((schwartz_withSeminorms ℝ E ℂ).tendsto_nhds _ _).2 ?_
  intro m ε hε
  obtain ⟨k, l⟩ := m
  filter_upwards [tendsto_tsum_compl_seminorm v k l hε] with s hs
  have hdiff : (∑ i ∈ s, v i) - schwartzSum v h =
      -schwartzSum (fun i : {j // j ∉ s} => v i) (fun k l => (h k l).subtype fun j => j ∉ s) := by
    rw [schwartzSum_split v h s]
    abel
  rw [hdiff]
  refine lt_of_le_of_lt ?_ hs
  calc (schwartzSeminormFamily ℝ E ℂ (k, l))
        (-schwartzSum (fun i : {j // j ∉ s} => v i) (fun k l => (h k l).subtype fun j => j ∉ s))
      = (SchwartzMap.seminorm ℝ k l)
          (schwartzSum (fun i : {j // j ∉ s} => v i) (fun k l => (h k l).subtype fun j => j ∉ s)) :=
        map_neg_eq_map _ _
    _ = (SchwartzMap.seminorm ℂ k l) (schwartzSum (fun i : {j // j ∉ s} => v i)
          (fun k l => (h k l).subtype fun j => j ∉ s)) :=
        (schwartz_seminorm_complex_eq _).symm
    _ ≤ ∑' i : {j // j ∉ s}, (SchwartzMap.seminorm ℂ k l) (v i) :=
        seminorm_schwartzSum_le _ _ k l

/-- Variant of `hasSum_schwartzSum` phrased with `Summable`. -/
theorem summable_schwartz_of_summable_seminorm (v : κ → 𝓢(E, ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (v i)) : Summable v :=
  ⟨schwartzSum v h, hasSum_schwartzSum v h⟩

end General

open LeanEval.Analysis.CKMRVInterpolation

theorem exists_schwartz_tsum {ι : Type*} (n : ℕ)
    (u : ι → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (u i)) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), HasSum u g ∧ ∀ x, g x = ∑' i, u i x :=
  ⟨schwartzSum u h, hasSum_schwartzSum u h, fun x => schwartzSum_apply u h x⟩

end Work.Summability
