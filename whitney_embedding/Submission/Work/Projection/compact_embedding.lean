import Mathlib
import Submission.Work.Projection.Basic
import Submission.Work.Projection.Defs
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.exists_countable_chart_cover

/-!
# The weak Whitney embedding theorem for compact manifolds

Every compact smooth `n`-manifold embeds smoothly into `ℝ^{2n+1}`, with injective derivative.

Starting from the embedding into some `ℝ^K` produced by Mathlib's partition-of-unity argument
(`exists_embedding_euclidean_of_compact`), we inflate it to dimension `2n+1+K` (adding zeros) and
then repeatedly apply the projection lemma `exists_good_direction` to lower the dimension one at a
time, until the ambient dimension is `2n+1`.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Projection

variable {n : ℕ}

/-- The coordinate projection `(Fin j → ℝ) → (Fin K → ℝ)` given by inserting zeros. -/
noncomputable def padFun {j K : ℕ} (_h : j ≤ K) : (Fin j → ℝ) →L[ℝ] (Fin K → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin K =>
    if hi : (i : ℕ) < j then (ContinuousLinearMap.proj (⟨i, hi⟩ : Fin j)) else 0

lemma padFun_apply {j K : ℕ} (h : j ≤ K) (v : Fin j → ℝ) (i : Fin K) :
    padFun h v i = if hi : (i : ℕ) < j then v ⟨i, hi⟩ else 0 := by
  simp only [padFun, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

/-- The coordinate inclusion `ℝ^j → ℝ^K` for `j ≤ K`, given by extending a vector by zeros. -/
noncomputable def pad {j K : ℕ} (h : j ≤ K) :
    EuclideanSpace ℝ (Fin j) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin K => ℝ)).symm :
      (Fin K → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin K)) ∘L
    (padFun h) ∘L
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin j => ℝ)) :
      EuclideanSpace ℝ (Fin j) →L[ℝ] (Fin j → ℝ))

lemma pad_apply {j K : ℕ} (h : j ≤ K) (z : EuclideanSpace ℝ (Fin j)) (i : Fin K) :
    pad h z i = if hi : (i : ℕ) < j then z ⟨i, hi⟩ else 0 := by
  have h1 : pad h z =
      WithLp.toLp 2 (padFun h ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin j => ℝ)) z)) := rfl
  rw [h1, PiLp.toLp_apply, padFun_apply]
  split_ifs with hi
  · simpa using PiLp.continuousLinearEquiv_apply 2 ℝ (fun _ : Fin j => ℝ) z (⟨i, hi⟩ : Fin j)
  · rfl

lemma pad_injective {j K : ℕ} (h : j ≤ K) : Function.Injective (pad h) := by
  intro z z' hz
  ext i
  have key := congrArg (fun w : EuclideanSpace ℝ (Fin K) => w (Fin.castLE h i)) hz
  rw [pad_apply, pad_apply] at key
  simpa using key

/-- Composing a smooth map with a continuous linear map. -/
lemma contMDiff_comp_clm {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {N k : ℕ} (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (e : M → EuclideanSpace ℝ (Fin N)) (hsm : ContMDiff (𝓡 n) (𝓡 N) ∞ e) :
    ContMDiff (𝓡 n) (𝓡 k) ∞ (⇑L ∘ e) :=
  L.contMDiff.comp hsm

/-- The derivative of `L ∘ e` for a continuous linear map `L`. -/
lemma mfderiv_comp_clm {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {N k : ℕ} (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (e : M → EuclideanSpace ℝ (Fin N)) (hsm : ContMDiff (𝓡 n) (𝓡 N) ∞ e) (x : M) :
    mfderiv (𝓡 n) (𝓡 k) (⇑L ∘ e) x = L ∘L mfderiv (𝓡 n) (𝓡 N) e x := by
  rw [mfderiv_comp x (f := e) (g := ⇑L) (L.differentiableAt.mdifferentiableAt)
    (hsm.mdifferentiableAt (by simp))]
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- **Reduction to the base dimension.**  An injective immersion of a second-countable
`n`-manifold into `ℝ^{2n+1+m}` can be lowered to one into `ℝ^{2n+1}`. -/
theorem reduce_steps {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M] (m : ℕ)
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1 + m)))
    (hsm : ContMDiff (𝓡 n) (𝓡 (2 * n + 1 + m)) ∞ e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1 + m)) e x)) :
    ∃ e' : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e' ∧ Function.Injective e' ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e' x) := by
  induction m with
  | zero => exact ⟨e, hsm, hinj, himm⟩
  | succ m ih =>
      obtain ⟨p, hcov⟩ := exists_countable_chart_cover n M
      obtain ⟨u, hu1, hu2⟩ :=
        exists_good_direction (n := n) (k := 2 * n + 1 + m) (by omega) e hsm hinj himm p hcov
      refine ih (⇑(projVec u) ∘ e) (contMDiff_comp_clm (projVec u) e hsm) hu1 ?_
      intro x
      rw [mfderiv_comp_clm (projVec u) e hsm x]
      exact hu2 x

/-- **Weak Whitney embedding theorem** for compact manifolds: a compact smooth `n`-manifold
embeds smoothly and immersively into `ℝ^{2n+1}`. -/
theorem exists_embedding_euclidean_of_compact (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e ∧ IsEmbedding e ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x,
      ⟨⟨Subsingleton.elim _ _⟩, fun x => isEmptyElim x⟩, fun x => isEmptyElim x⟩
  · haveI := hM
    obtain ⟨K, e₀, hsm₀, hemb₀, himm₀⟩ :
        ∃ (K : ℕ) (e : M → EuclideanSpace ℝ (Fin K)), ContMDiff (𝓡 n) (𝓡 K) ∞ e ∧
          IsClosedEmbedding e ∧ ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 K) e x) :=
      _root_.exists_embedding_euclidean_of_compact
    have hle : K ≤ 2 * n + 1 + K := by omega
    obtain ⟨e', hsm', hinj', himm'⟩ :=
      reduce_steps (n := n) K (⇑(pad hle) ∘ e₀) (contMDiff_comp_clm (pad hle) e₀ hsm₀)
        (Function.Injective.comp (pad_injective hle) hemb₀.injective) (fun x => by
          rw [mfderiv_comp_clm (pad hle) e₀ hsm₀ x]
          exact (pad_injective hle).comp (himm₀ x))
    exact ⟨e', hsm', (Continuous.isClosedEmbedding hsm'.continuous hinj').toIsEmbedding, himm'⟩

end Work.Projection
