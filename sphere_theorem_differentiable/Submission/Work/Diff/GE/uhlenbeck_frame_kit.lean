import Mathlib
import Submission.Work.Diff.GE.uhlenbeck_defs
import Submission.Work.Diff.GE.inner_sum_smul_sum_smul
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.matrix_sqrt_family_kit
import Submission.Work.Diff.GE.ricAt_symm_kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Uhlenbeck frame at a point along a Ricci flow

Given a Ricci flow `G` on `[0,T)` and a point `x`, there is a family of frames at `x` which is
`G s`-orthonormal for every `s ∈ [0,T)` and moves by the Uhlenbeck/Ricci rule
`∂ₛ eᵢ = Ric(eᵢ)^♯`, i.e. `⟨∂ₛ eᵢ, eⱼ⟩ = Ric(eᵢ,eⱼ)` (the frame has no "rotation" part).

The proof is pointwise linear algebra: fixing the frame `u := onFrame (G t) x` at time `t`, the
metric at `x` is encoded in the symmetric matrix `metricMat G x u s` of its inner products; a family
of matrices `Φ` with `Φᵀ (metricMat G x u s) Φ = 1` produces `G s`-orthonormal frames, and the
family is chosen so that `Φ` is the inverse square root of `metricMat G x u s` normalised so that
`Φ'(t) = ricMat (G t) x u` (the matrix of the Ricci tensor).  The existence of such a `Φ` is the
matrix lemma `Work.Diff.GE.matrix_sqrt_family`; the symmetry of the Ricci matrix is
`Work.Diff.GE.ricAt_symm`; the passage from matrix products to inner products is
`Work.Diff.GE.inner_sum_smul_sum_smul`.

The frame `e` is only required to be orthonormal on `[0,T)` and to be differentiated at the single
time `t`, so away from a neighbourhood of `t` (within `[0,T)`) it is patched with the
`Classical.epsilon`-chosen orthonormal frame `onFrame (G s) x`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Matrices as sums of elementary matrices -/

/-- The `(i,j)`-entry of a sum of elementary matrices. -/
lemma sum_singles_apply {n : ℕ} (c : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ i', ∑ j', c i' j' • Matrix.single i' j' (1 : ℝ)) i j = c i j := by
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · intro hj
      simp at hj
  · intro i' _ hi'
    simp [hi']
  · intro hi
    simp at hi

/-- Every matrix is the sum of its entries times the elementary matrices. -/
lemma matrix_eq_sum_singles {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A = ∑ i, ∑ j, A i j • Matrix.single i j (1 : ℝ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · intro hj
      simp at hj
  · intro i' _ hi'
    simp [hi']
  · intro hi
    simp at hi

/-- The metric matrix as a sum of elementary matrices. -/
lemma metricMat_eq_sum_singles (G : ℝ → SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (s : ℝ) :
    metricMat G x u s
      = ∑ i, ∑ j, (G s).inner x (u i) (u j) • Matrix.single i j (1 : ℝ) :=
  matrix_eq_sum_singles _

/-- The Ricci matrix as a sum of elementary matrices. -/
lemma ricMat_eq_sum_singles (g : SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    ricMat g x u
      = ∑ i, ∑ j, ricAt (lcOf g) x (u i) (u j) • Matrix.single i j (1 : ℝ) :=
  matrix_eq_sum_singles _

/-- The norm of an entry of a matrix is bounded by the matrix norm. -/
lemma norm_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h1 : ‖A i j‖₊ ≤ ∑ j', ‖A i j'‖₊ := by
    apply Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (a := j) (fun j' _ => by positivity)
    exact Finset.mem_univ j
  have h2 : (∑ j', ‖A i j'‖₊) ≤ Finset.univ.sup (fun i' => ∑ j', ‖A i' j'‖₊) :=
    Finset.le_sup (f := fun i' => ∑ j', ‖A i' j'‖₊) (Finset.mem_univ i)
  have h3 : ‖A‖₊ = Finset.univ.sup (fun i' => ∑ j', ‖A i' j'‖₊) := Matrix.linfty_opNNNorm_def A
  have key : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [h3]
    exact le_trans h1 h2
  have key' : (‖A i j‖₊ : ℝ) ≤ (‖A‖₊ : ℝ) := by exact_mod_cast key
  simpa using key'

/-- The `(i,j)`-entry of a matrix, as a linear functional. -/
noncomputable def matEntryLM {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun := fun A => A i j
  map_add' := by intro A B; simp
  map_smul' := by intro c A; simp

/-- The `(i,j)`-entry of a matrix, as a continuous linear functional. -/
noncomputable def matEntryCLM {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous (matEntryLM i j) 1 (by
    intro A
    change ‖A i j‖ ≤ 1 * ‖A‖
    simpa using norm_entry_le A i j)

/-- Entrywise differentiability from differentiability of a matrix-valued function. -/
lemma hasDerivWithinAt_entry {n : ℕ} {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Φdot : Matrix (Fin n) (Fin n) ℝ} {S : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt Φ Φdot S t) (i j : Fin n) :
    HasDerivWithinAt (fun s => Φ s i j) (Φdot i j) S t :=
  (matEntryCLM i j).hasFDerivAt.comp_hasDerivWithinAt t h

/-- **The manifold specialisation** of `inner_sum_smul_sum_smul`: the pairing of two linear
combinations of a frame with the metric `G s` is the corresponding matrix product.  The statement is
phrased for `E`, which is definitionally the tangent space. -/
lemma inner_pairing_metricMat (G : ℝ → SMet I M) (x : M) (s : ℝ)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A C : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) (i j) :
    (G s).inner x (∑ k, A k i • u k) (∑ l, C l j • u l)
      = (A.transpose * metricMat G x u s * C) i j :=
  inner_sum_smul_sum_smul (V := E)
    (B := (show E →L[ℝ] E →L[ℝ] ℝ from (G s).inner x))
    (u := (show Fin (Module.finrank ℝ E) → E from u))
    (Mm := metricMat G x u s) (A := A) (C := C) (fun k l => rfl) i j

/-! ## The metric matrix is differentiable along the flow -/

/-- The matrix of inner products at `x` is differentiable at `t` within `[0,T)` along a Ricci flow,
with derivative `-2` times the Ricci matrix. -/
lemma metricMat_hasDerivWithinAt (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    HasDerivWithinAt (metricMat G x u) ((-2 : ℝ) • ricMat (G t) x u) (Set.Ico 0 T) t := by
  have hkey : HasDerivWithinAt
      (fun s => ∑ i, ∑ j, (G s).inner x (u i) (u j) • Matrix.single i j (1 : ℝ))
      (∑ i, ∑ j, (-2 * ricAt (lcOf (G t)) x (u i) (u j)) • Matrix.single i j (1 : ℝ))
      (Set.Ico 0 T) t := by
    have h1 := HasDerivWithinAt.sum (u := Finset.univ)
      (fun (i : Fin (Module.finrank ℝ E)) _ => HasDerivWithinAt.sum (u := Finset.univ)
        (fun (j : Fin (Module.finrank ℝ E)) _ =>
          (hflow.2 t ht x (u i) (u j)).smul_const (Matrix.single i j (1 : ℝ))))
    rw [show (∑ i, ∑ j, fun s => (G s).inner x (u i) (u j) • Matrix.single i j (1 : ℝ))
        = fun s => ∑ i, ∑ j, (G s).inner x (u i) (u j) • Matrix.single i j (1 : ℝ) from by
      funext s
      simp only [Finset.sum_apply]] at h1
    exact h1
  have hval : (∑ i, ∑ j, (-2 * ricAt (lcOf (G t)) x (u i) (u j)) • Matrix.single i j (1 : ℝ))
      = (-2 : ℝ) • ricMat (G t) x u := by
    conv_rhs => rw [ricMat_eq_sum_singles (G t) x u]
    ext i j
    rw [sum_singles_apply (c := fun i j => -2 * ricAt (lcOf (G t)) x (u i) (u j)) i j,
      Matrix.smul_apply, smul_eq_mul,
      sum_singles_apply (c := fun i j => ricAt (lcOf (G t)) x (u i) (u j)) i j]
  have hfun : metricMat G x u
      = fun s => ∑ i, ∑ j, (G s).inner x (u i) (u j) • Matrix.single i j (1 : ℝ) := by
    funext s
    exact metricMat_eq_sum_singles G x u s
  rw [hfun, ← hval]
  exact hkey

/-! ## The frame attached to a family of matrices -/

/-- The frame at `x` whose `i`-th vector is the `i`-th column of `Φ` read in the frame `u`.
Declared as an `abbrev` so that it unfolds during rewriting. -/
noncomputable abbrev frameFromMatrix (x : M) (u : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Φ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
    Fin (Module.finrank ℝ E) → TangentSpace I x :=
  fun i => ∑ j, Φ j i • u j

@[simp] lemma frameFromMatrix_apply (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (Φ : Matrix _ _ ℝ) (i) :
    frameFromMatrix x u Φ i = ∑ j, Φ j i • u j := rfl

/-- The frame built from the identity matrix is the original frame. -/
lemma frameFromMatrix_one (x : M) (u : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    frameFromMatrix x u
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) = u := by
  funext i
  rw [frameFromMatrix_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply, hj]
  · intro hi
    simp at hi

/-- A matrix `Φ` with `Φᵀ (metricMat) Φ = 1` produces a `G s`-orthonormal frame. -/
lemma isONFrame_frameFromMatrix (G : ℝ → SMet I M) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Φ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) (s : ℝ)
    (h : Φ.transpose * metricMat G x u s * Φ = 1) :
    IsONFrame (G s) x (frameFromMatrix x u Φ) := by
  intro i j
  rw [show (G s).inner x (frameFromMatrix x u Φ i) (frameFromMatrix x u Φ j)
      = (Φ.transpose * metricMat G x u s * Φ) i j from
    inner_pairing_metricMat G x s u Φ Φ i j,
    h, Matrix.one_apply]

/-- Differentiation of a finite linear combination of a fixed family of vectors, with coefficients
depending differentiably on the parameter.  Stated for `E`-valued vectors, which is what Mathlib's
`HasDerivWithinAt.sum` is set up for; `hasDerivWithinAt_frameFromMatrix` transfers it back to the
tangent space. -/
lemma hasDerivWithinAt_sum_smul (T t : ℝ) (u : Fin (Module.finrank ℝ E) → E)
    {Φ : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    {Φdot : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun s => Φ s i j) (Φdot i j) (Set.Ico 0 T) t) (i) :
    HasDerivWithinAt (fun s => (∑ j, Φ s j i • u j : E)) (∑ j, Φdot j i • u j)
      (Set.Ico 0 T) t := by
  have h' := HasDerivWithinAt.sum (u := Finset.univ) (fun j _ => (h j i).smul_const (u j))
  rw [show (∑ j, fun s => Φ s j i • u j) = fun s => ∑ j, Φ s j i • u j from by
    funext s
    simp only [Finset.sum_apply]] at h'
  exact h'

/-- Differentiation of the frame built from a differentiable matrix family. -/
lemma hasDerivWithinAt_frameFromMatrix (T t : ℝ) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x)
    {Φ : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    {Φdot : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun s => Φ s i j) (Φdot i j) (Set.Ico 0 T) t) (i) :
    HasDerivWithinAt (fun s => frameFromMatrix x u (Φ s) i)
      (∑ j, Φdot j i • u j) (Set.Ico 0 T) t :=
  hasDerivWithinAt_sum_smul T t (show Fin (Module.finrank ℝ E) → E from u) h i

/-! ## The Uhlenbeck frame from a matrix square root -/

/-- **The Uhlenbeck frame**, given the coefficient matrix family `Φ`.  If `Φ` is the (symmetric)
inverse square root of the metric matrix, normalised so that `Φ t = 1` and
`Φ'(t) = ricMat (G t) x u`, then the columns of `Φ` build the required moving frame. -/
lemma exists_uhlenbeck_frame_of_matrix
    (G : ℝ → SMet I M) (T t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (hu : IsONFrame (G t) x u)
    (hRic : ∀ i j, ricMat (G t) x u i j = ricMat (G t) x u j i)
    (Φ : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΦt : Φ t = 1)
    (hconstr : ∀ᶠ s in nhdsWithin t (Set.Ico 0 T),
      (Φ s).transpose * metricMat G x u s * Φ s = 1)
    (hΦderiv : HasDerivWithinAt Φ (ricMat (G t) x u) (Set.Ico 0 T) t) :
    ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
      (v : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∀ s ∈ Set.Ico 0 T, IsONFrame (G s) x (e s)) ∧
      (∀ i, HasDerivWithinAt (fun s ↦ e s i) (v i) (Set.Ico 0 T) t) ∧
      (∀ i j, (G t).inner x (v i) (e t j)
        = ricAt (lcOf (G t)) x (e t i) (e t j)) := by
  classical
  let S : Set ℝ := {s | (Φ s).transpose * metricMat G x u s * Φ s = 1}
  have hS : S ∈ nhdsWithin t (Set.Ico 0 T) := hconstr
  have hSt : t ∈ S := hconstr.self_of_nhdsWithin ht
  refine ⟨fun s i => if s ∈ S then frameFromMatrix x u (Φ s) i else onFrame (G s) x i,
    fun i => ∑ j, ricMat (G t) x u j i • u j, ?_, ?_, ?_⟩
  · intro s hs
    by_cases h : s ∈ S
    · simpa only [h, ite_true] using isONFrame_frameFromMatrix G x u (Φ s) s h
    · simpa only [h, ite_false] using isONFrame_onFrame (G s) x
  · intro i
    -- the derivative is proved for the `E`-valued function, along the defeq `TangentSpace I x = E`
    let uE : Fin (Module.finrank ℝ E) → E := show Fin (Module.finrank ℝ E) → E from u
    let eE : ℝ → E := fun s => if s ∈ S
      then (∑ j, Φ s j i • uE j) else (show E from onFrame (G s) x i)
    have hsum : HasDerivWithinAt (fun s => (∑ j, Φ s j i • uE j : E))
        (∑ j, (ricMat (G t) x u) j i • uE j) (Set.Ico 0 T) t :=
      hasDerivWithinAt_sum_smul T t uE
        (fun a b => hasDerivWithinAt_entry hΦderiv a b) i
    have hev : eE =ᶠ[nhdsWithin t (Set.Ico 0 T)] (fun s => (∑ j, Φ s j i • uE j : E)) := by
      filter_upwards [hS] with s hs
      dsimp only [eE]
      exact if_pos hs
    have hder : HasDerivWithinAt eE (∑ j, (ricMat (G t) x u) j i • uE j) (Set.Ico 0 T) t := by
      rw [hev.hasDerivWithinAt_iff (by dsimp only [eE]; exact if_pos hSt)]
      exact hsum
    exact hder
  · intro i j
    have hframe : frameFromMatrix x u (Φ t) = u := by
      rw [hΦt, frameFromMatrix_one]
    have hMt : metricMat G x u t = 1 := metricMat_eq_one G x u t hu
    have hL : (G t).inner x (∑ k, ricMat (G t) x u k i • u k) (∑ l, Φ t l j • u l)
        = ricMat (G t) x u j i := by
      rw [inner_pairing_metricMat G x t u (ricMat (G t) x u) (Φ t) i j, hMt, hΦt]
      simp only [Matrix.mul_one, Matrix.transpose_apply]
    have hR : ricAt (lcOf (G t)) x (frameFromMatrix x u (Φ t) i)
        (frameFromMatrix x u (Φ t) j) = ricMat (G t) x u i j := by
      rw [hframe]
      simp [ricMat_apply]
    simp only [hSt, ite_true]
    rw [hL, hR]
    exact (hRic i j).symm

/-! ## The Uhlenbeck frame along a Ricci flow -/

theorem uhlenbeck_frame_exists_kit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M) :
    ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
      (v : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∀ s ∈ Set.Ico 0 T, Submission.Diff.IsONFrame (G s) x (e s)) ∧
      (∀ i, HasDerivWithinAt (fun s : ℝ ↦ e s i) (v i) (Set.Ico 0 T) t) ∧
      (∀ i j, (G t).inner x (v i) (e t j)
        = Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (e t i) (e t j)) := by
  classical
  obtain ⟨u, hu⟩ := exists_isONFrame (I := I) (M := M) (G t) x
  have hM : metricMat G x u t = 1 := metricMat_eq_one G x u t hu
  have hsym : ∀ s, (metricMat G x u s).transpose = metricMat G x u s :=
    fun s => metricMat_symm G x u s
  have hdiff : HasDerivWithinAt (metricMat G x u) ((-2 : ℝ) • ricMat (G t) x u)
      (Set.Ico 0 T) t :=
    metricMat_hasDerivWithinAt G T hflow t ht x u
  obtain ⟨Φ, hΦt, hconstr, hΦderiv⟩ :=
    matrix_sqrt_family_kit (Module.finrank ℝ E) (metricMat G x u) ((-2 : ℝ) • ricMat (G t) x u)
      t T hM hsym hdiff
  have hΦderiv' : HasDerivWithinAt Φ (ricMat (G t) x u) (Set.Ico 0 T) t := by
    convert hΦderiv using 1
    rw [smul_smul]
    norm_num
  have hRic : ∀ i j, ricMat (G t) x u i j = ricMat (G t) x u j i := by
    intro i j
    simpa [ricMat_apply] using ricAt_symm_kit hLC (G t) x (u i) (u j)
  exact exists_uhlenbeck_frame_of_matrix G T t ht x u hu hRic Φ hΦt hconstr hΦderiv'

/-- **The Uhlenbeck frame in the derivative form used by `CurvEvolution`**: the pairing condition
`⟪v i, e t j⟫ = Ric(e t i, e t j)` upgrades to `∂ₛ eᵢ = ∑ⱼ Ric(eᵢ,eⱼ) • eⱼ`. -/
theorem uhlenbeck_frame_kit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M) :
    ∃ e : ℝ → Fin (Module.finrank ℝ E) → E,
      (∀ s ∈ Set.Ico 0 T, Submission.Diff.IsONFrame (G s) x (e s)) ∧
      ∀ i, HasDerivWithinAt (fun s : ℝ ↦ e s i)
        ((∑ j, Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (e t i) (e t j) • e t j
          : TangentSpace I x) : E) (Set.Ico 0 T) t := by
  classical
  obtain ⟨e, v, hON, hv, hpair⟩ := uhlenbeck_frame_exists_kit hLC G T hflow t ht x
  refine ⟨fun s i ↦ (e s i : E), ?_, ?_⟩
  · intro s hs
    exact hON s hs
  · intro i
    by_cases hn : 0 < Module.finrank ℝ E
    · -- expand `v i` in the `G t`-orthonormal frame `e t`
      have hv' : v i = ∑ j, Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (e t i)
          (e t j) • e t j := by
        rw [← Work.Diff.GE.sum_smul_inner_eq_self (I := I) (M := M) (G t) x hn (e t) (hON t ht) (v i)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpair i j]
      have hmain : HasDerivWithinAt (fun s : ℝ ↦ (e s i : E))
          ((∑ j, Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (e t i)
            (e t j) • e t j : TangentSpace I x) : E) (Set.Ico 0 T) t := by
        have h' : HasDerivWithinAt (fun s : ℝ ↦ e s i)
            (∑ j, Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (e t i)
              (e t j) • e t j) (Set.Ico 0 T) t := by
          rw [← hv']
          exact hv i
        exact h'
      exact hmain
    · -- degenerate case: the index type is empty
      have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
      exact Fin.elim0 (h0 ▸ i)

end Work.Diff.GE
