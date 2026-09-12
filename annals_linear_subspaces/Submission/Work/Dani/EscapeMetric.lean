import Mathlib
import ChallengeDeps
import Submission.Work.Dani.EscapeGlueEps
import Submission.Work.Dani.OrthoRep
import Submission.GeometryOfNumbers.WedgeBlocks
import Submission.GeometryOfNumbers.DiagonalFlow
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry

/-!
# The graph chart for the escape direction of conjunct 2

After `Submission.EscapeGlueEps`, conjunct 2 (`∃ x, β_k(x) = d/(k(d−ℓ))`) is reduced to the
existence of a plane `x` of dimension `ℓ` with **zero escape rate**
`∀ ε > 0, ∃ T, ∀ t ≥ T, e^{−εt} ≤ λ₁(a_t s_x ℤᵈ)` (plus rational-point-freeness).

This file sets up the *graph chart* `x = graphPlane c = span(e_i + c_i)` (an `ℓ`-plane
transverse to `x₀ᗮ`, `x₀ = modelX ℓ` the first `ℓ` coordinate directions) in which

* the head/tail decomposition w.r.t. `x₀ ⊕ x₀ᗮ` is explicit (Parseval in the standard basis),
* the exponential two-scale flow acts as `e^{−t/ℓ}` on the head and `e^{t/(d−ℓ)}` on the tail,

so that the escape condition becomes a statement about the `ℓ×m` matrix `c` attackable by
**Borel–Cantelli** (metric Diophantine approximation — the *convergent* half of Khintchine).

Module `Submission.Work.Dani.EscapeMetric`, namespace `Submission.EscapeMetric`.
-/

noncomputable section

open LinearSubspaces Module Real
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Submission.EscapeMetric

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "𝔹" => Submission.ExteriorCoordinates.B

/-- The head-basis index of `i : Fin ℓ` inside `Fin d`. -/
def headIdx (l : ℕ) (hld : l < d) (i : Fin l) : Fin d :=
  ⟨i.val, lt_of_lt_of_le i.isLt (le_of_lt hld)⟩

/-- The tail-basis index of `j : Fin (d−ℓ)` inside `Fin d`. -/
def tailIdx (l : ℕ) (hld : l < d) (j : Fin (d - l)) : Fin d :=
  ⟨l + j.val, by have := j.isLt; omega⟩

@[simp] lemma headIdx_val (l : ℕ) (hld : l < d) (i : Fin l) : (headIdx l hld i).val = i.val := rfl

@[simp] lemma tailIdx_val (l : ℕ) (hld : l < d) (j : Fin (d - l)) :
    (tailIdx l hld j).val = l + j.val := rfl

lemma headIdx_lt (l : ℕ) (hld : l < d) (i : Fin l) : (headIdx l hld i).val < l := i.isLt

lemma le_tailIdx (l : ℕ) (hld : l < d) (j : Fin (d - l)) : l ≤ (tailIdx l hld j).val := by
  simp

lemma headIdx_injective (l : ℕ) (hld : l < d) : Function.Injective (headIdx l hld) := by
  intro i j h
  exact Fin.ext (by simpa using congrArg Fin.val h)

lemma tailIdx_injective (l : ℕ) (hld : l < d) : Function.Injective (tailIdx l hld) := by
  intro i j h
  have h1 : l + i.val = l + j.val := by simpa using congrArg Fin.val h
  exact Fin.ext (by omega)

lemma headIdx_ne_tailIdx (l : ℕ) (hld : l < d) (i : Fin l) (j : Fin (d - l)) :
    headIdx l hld i ≠ tailIdx l hld j := by
  intro h
  have h1 : (headIdx l hld i).val = (tailIdx l hld j).val := congrArg Fin.val h
  simp only [headIdx_val, tailIdx_val] at h1
  have := i.isLt
  omega

/-- The head part `∑ i, a i • (B d) i` (`i < ℓ`): a vector of `x₀ = modelX ℓ`. -/
def headVec (l : ℕ) (hld : l < d) (a : Fin l → ℝ) : ℝᵈ :=
  ∑ i, a i • (𝔹 d) (headIdx l hld i)

/-- The tail part `∑ j, y j • (B d) (ℓ+j)`: a vector of `x₀ᗮ`. -/
def tailVec (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) : ℝᵈ :=
  ∑ j, y j • (𝔹 d) (tailIdx l hld j)

/-- The graph vector `∑ i, a i • (e_i + c_i)` of a coefficient vector `a`. -/
def graphVec (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) : ℝᵈ :=
  ∑ i, a i • ((𝔹 d) (headIdx l hld i) + tailVec l hld (c i))

/-- The graph linear map `a ↦ ∑ i, a i • (e_i + c_i)`; its range is the graph plane. -/
def graphLinearMap (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) :
    (Fin l → ℝ) →ₗ[ℝ] ℝᵈ where
  toFun := graphVec l hld c
  map_add' := by
    intro a b
    simp only [graphVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp only [graphVec, Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

/-- The graph plane `span(e_i + c_i)`. -/
def graphPlane (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) : Submodule ℝ ℝᵈ :=
  LinearMap.range (graphLinearMap l hld c)

lemma graphVec_mem_graphPlane (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ)
    (a : Fin l → ℝ) : graphVec l hld c a ∈ graphPlane l hld c :=
  ⟨a, rfl⟩

/-! ### Inner products with the standard basis -/

lemma inner_std_eq_coord (k : Fin d) (v : ℝᵈ) : inner ℝ ((𝔹 d) k) v = v k := by
  simp [Submission.ExteriorCoordinates.B, EuclideanSpace.basisFun_apply, PiLp.inner_apply]

lemma inner_coord_eq_std (k : Fin d) (v : ℝᵈ) : inner ℝ v ((𝔹 d) k) = v k := by
  rw [real_inner_comm, inner_std_eq_coord]

lemma inner_std_headVec (l : ℕ) (hld : l < d) (a : Fin l → ℝ) (i : Fin l) :
    inner ℝ ((𝔹 d) (headIdx l hld i)) (headVec l hld a) = a i := by
  classical
  rw [headVec, inner_sum]
  have hterm : ∀ j : Fin l,
      inner ℝ ((𝔹 d) (headIdx l hld i)) (a j • (𝔹 d) (headIdx l hld j)) =
        if j = i then a i else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [inner_smul_right, if_pos rfl, inner_self_eq_norm_sq_to_K, (𝔹 d).norm_eq_one]
      norm_num
    · rw [inner_smul_right,
        Orthonormal.inner_eq_zero (𝔹 d).orthonormal
          (fun h => hj (headIdx_injective l hld h).symm), mul_zero, if_neg hj]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp

lemma inner_std_tailVec (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) (j : Fin (d - l)) :
    inner ℝ ((𝔹 d) (tailIdx l hld j)) (tailVec l hld y) = y j := by
  classical
  rw [tailVec, inner_sum]
  have hterm : ∀ j' : Fin (d - l),
      inner ℝ ((𝔹 d) (tailIdx l hld j)) (y j' • (𝔹 d) (tailIdx l hld j')) =
        if j' = j then y j else 0 := by
    intro j'
    by_cases hj : j' = j
    · subst hj
      rw [inner_smul_right, if_pos rfl, inner_self_eq_norm_sq_to_K, (𝔹 d).norm_eq_one]
      norm_num
    · rw [inner_smul_right,
        Orthonormal.inner_eq_zero (𝔹 d).orthonormal
          (fun h => hj (tailIdx_injective l hld h).symm), mul_zero, if_neg hj]
  rw [Finset.sum_congr rfl fun j' _ => hterm j']
  simp

lemma inner_std_orth_headVec (l : ℕ) (hld : l < d) (a : Fin l → ℝ) (j : Fin (d - l)) :
    inner ℝ ((𝔹 d) (tailIdx l hld j)) (headVec l hld a) = 0 := by
  classical
  rw [headVec, inner_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_right,
    Orthonormal.inner_eq_zero (𝔹 d).orthonormal (fun h => headIdx_ne_tailIdx l hld i j h.symm),
    mul_zero]

lemma inner_std_orth_tailVec (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) (i : Fin l) :
    inner ℝ ((𝔹 d) (headIdx l hld i)) (tailVec l hld y) = 0 := by
  classical
  rw [tailVec, inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [inner_smul_right,
    Orthonormal.inner_eq_zero (𝔹 d).orthonormal (fun h => headIdx_ne_tailIdx l hld i j h),
    mul_zero]

/-! ### Norms (Parseval) -/

lemma norm_sq_headVec (l : ℕ) (hld : l < d) (a : Fin l → ℝ) :
    ‖headVec l hld a‖ ^ 2 = ∑ i, (a i) ^ 2 := by
  rw [headVec]
  exact Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul _
    ((𝔹 d).orthonormal.comp _ (headIdx_injective l hld)) a

lemma norm_sq_tailVec (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) :
    ‖tailVec l hld y‖ ^ 2 = ∑ j, (y j) ^ 2 := by
  rw [tailVec]
  exact Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul _
    ((𝔹 d).orthonormal.comp _ (tailIdx_injective l hld)) y

/-- Coordinates as inner products with the standard basis. -/
lemma coord_eq_inner (k : Fin d) (v : ℝᵈ) : v k = inner ℝ ((𝔹 d) k) v :=
  (inner_std_eq_coord k v).symm

lemma headVec_coord_head (l : ℕ) (hld : l < d) (a : Fin l → ℝ) (i : Fin l) :
    headVec l hld a (headIdx l hld i) = a i := by
  rw [coord_eq_inner, inner_std_headVec]

lemma headVec_coord_tail (l : ℕ) (hld : l < d) (a : Fin l → ℝ) (j : Fin (d - l)) :
    headVec l hld a (tailIdx l hld j) = 0 := by
  rw [coord_eq_inner, inner_std_orth_headVec]

lemma tailVec_coord_tail (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) (j : Fin (d - l)) :
    tailVec l hld y (tailIdx l hld j) = y j := by
  rw [coord_eq_inner, inner_std_tailVec]

lemma tailVec_coord_head (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) (i : Fin l) :
    tailVec l hld y (headIdx l hld i) = 0 := by
  rw [coord_eq_inner, inner_std_orth_tailVec]

/-- Every index of `Fin d` is a head or a tail index. -/
lemma eq_headIdx_or_tailIdx (l : ℕ) (hld : l < d) (k : Fin d) :
    (∃ i : Fin l, k = headIdx l hld i) ∨ (∃ j : Fin (d - l), k = tailIdx l hld j) := by
  by_cases hk : k.val < l
  · exact Or.inl ⟨⟨k.val, hk⟩, (Fin.ext rfl).symm⟩
  · refine Or.inr ⟨⟨k.val - l, by omega⟩, ?_⟩
    refine (Fin.ext ?_).symm
    simp only [tailIdx_val]
    omega

/-- Two vectors with the same coordinates in the standard basis are equal. -/
lemma eq_of_forall_inner_std_eq {u v : ℝᵈ}
    (h : ∀ k : Fin d, inner ℝ ((𝔹 d) k) u = inner ℝ ((𝔹 d) k) v) : u = v := by
  have h1 : (∑ k : Fin d, inner ℝ ((𝔹 d) k) u • (𝔹 d) k) = u := (𝔹 d).sum_repr' u
  have h2 : (∑ k : Fin d, inner ℝ ((𝔹 d) k) v • (𝔹 d) k) = v := (𝔹 d).sum_repr' v
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl fun k _ => by rw [h k]

/-- **Reconstruction**: the head and tail parts of `v` sum to `v`. -/
lemma reconstruct (l : ℕ) (hld : l < d) (v : ℝᵈ) :
    headVec l hld (fun i => v (headIdx l hld i)) +
      tailVec l hld (fun j => v (tailIdx l hld j)) = v := by
  refine eq_of_forall_inner_std_eq fun k => ?_
  rcases eq_headIdx_or_tailIdx l hld k with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp only [inner_add_right, inner_std_eq_coord, headVec_coord_head, tailVec_coord_head,
      add_zero]
  · simp only [inner_add_right, inner_std_eq_coord, headVec_coord_tail, tailVec_coord_tail,
      zero_add]

/-- `v` minus its head part is its tail part. -/
lemma sub_headVec_eq_tailVec (l : ℕ) (hld : l < d) (v : ℝᵈ) :
    v - headVec l hld (fun i => v (headIdx l hld i)) =
      tailVec l hld (fun j => v (tailIdx l hld j)) := by
  refine eq_of_forall_inner_std_eq fun k => ?_
  rcases eq_headIdx_or_tailIdx l hld k with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp only [inner_sub_right, inner_std_eq_coord, headVec_coord_head, tailVec_coord_head,
      sub_self]
  · simp only [inner_sub_right, inner_std_eq_coord, headVec_coord_tail, tailVec_coord_tail,
      sub_zero]

/-- `v` minus its tail part is its head part. -/
lemma sub_tailVec_eq_headVec (l : ℕ) (hld : l < d) (v : ℝᵈ) :
    v - tailVec l hld (fun j => v (tailIdx l hld j)) =
      headVec l hld (fun i => v (headIdx l hld i)) := by
  refine eq_of_forall_inner_std_eq fun k => ?_
  rcases eq_headIdx_or_tailIdx l hld k with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp only [inner_sub_right, inner_std_eq_coord, headVec_coord_head, tailVec_coord_head,
      sub_zero]
  · simp only [inner_sub_right, inner_std_eq_coord, headVec_coord_tail, tailVec_coord_tail,
      sub_self]

lemma headVec_mem_modelX (l : ℕ) (hld : l < d) (a : Fin l → ℝ) :
    headVec l hld a ∈ Submission.WedgeBlocks.modelX (d := d) l := by
  classical
  rw [headVec]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submission.WedgeBlocks.std_mem_modelX l _ i.isLt

lemma tailVec_mem_orth (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) :
    tailVec l hld y ∈ (Submission.WedgeBlocks.modelX (d := d) l)ᗮ := by
  classical
  rw [tailVec]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact Submission.WedgeBlocks.std_mem_modelX_orth l _ (by simp)

/-! ### Span identities -/

lemma headVec_mem_span (l : ℕ) (hld : l < d) (a : Fin l → ℝ) :
    headVec l hld a ∈ Submodule.span ℝ
      (Set.range (fun i : Fin l => (𝔹 d) (headIdx l hld i))) := by
  classical
  rw [headVec]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma tailVec_mem_span (l : ℕ) (hld : l < d) (y : Fin (d - l) → ℝ) :
    tailVec l hld y ∈ Submodule.span ℝ
      (Set.range (fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j))) := by
  classical
  rw [tailVec]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- `x₀ = modelX ℓ` is the span of the head standard vectors. -/
lemma modelX_eq_span_headIdx (l : ℕ) (hld : l < d) :
    Submission.WedgeBlocks.modelX (d := d) l =
      Submodule.span ℝ (Set.range (fun i : Fin l => (𝔹 d) (headIdx l hld i))) := by
  unfold Submission.WedgeBlocks.modelX
  congr 1
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, by simp [headIdx]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨headIdx l hld i, i.isLt, rfl⟩

/-- `x₀ᗮ` is the span of the tail standard vectors. -/
lemma orth_eq_span_tailIdx (l : ℕ) (hld : l < d) :
    (Submission.WedgeBlocks.modelX (d := d) l)ᗮ =
      Submodule.span ℝ (Set.range (fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j))) := by
  classical
  have hle : Submodule.span ℝ
      (Set.range (fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j))) ≤
      (Submission.WedgeBlocks.modelX (d := d) l)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact Submission.WedgeBlocks.std_mem_modelX_orth l _ (le_tailIdx l hld j)
  have hdim1 : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j)))) = d - l := by
    have hli : LinearIndependent ℝ (fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j)) :=
      ((𝔹 d).orthonormal.comp _ (tailIdx_injective l hld)).linearIndependent
    simpa using finrank_span_eq_card (b := fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j)) hli
  have hdim2 : Module.finrank ℝ ((Submission.WedgeBlocks.modelX (d := d) l)ᗮ) = d - l := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ)
      (Submission.WedgeBlocks.modelX (d := d) l)
    rw [Submission.PlaneFinrank.finrank_modelX l (le_of_lt hld)] at h
    have hE : Module.finrank ℝ ℝᵈ = d := by simp
    rw [hE] at h
    omega
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hdim2, hdim1])).symm

/-- **The head projection**: the orthogonal projection of `v` onto `x₀ = modelX ℓ` is its
coordinate head part. -/
lemma starProjection_modelX_eq_headVec (l : ℕ) (hld : l < d) (v : ℝᵈ) :
    ((Submission.WedgeBlocks.modelX (d := d) l).starProjection v : ℝᵈ) =
      headVec l hld (fun i => v (headIdx l hld i)) := by
  classical
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (K := Submission.WedgeBlocks.modelX (d := d) l) (u := v)
    (v := headVec l hld (fun i => v (headIdx l hld i)))
    (headVec_mem_modelX l hld (fun i => v (headIdx l hld i))) ?_
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [modelX_eq_span_headIdx l hld] at hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hu
  simp only [inner_sub_right, sum_inner]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [real_inner_smul_left, inner_std_eq_coord, headVec_coord_head, sub_self]

/-- **The tail projection**: the orthogonal projection of `v` onto `x₀ᗮ` is its coordinate tail
part. -/
lemma starProjection_orth_eq_tailVec (l : ℕ) (hld : l < d) (v : ℝᵈ) :
    (((Submission.WedgeBlocks.modelX (d := d) l)ᗮ).starProjection v : ℝᵈ) =
      tailVec l hld (fun j => v (tailIdx l hld j)) := by
  classical
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (K := (Submission.WedgeBlocks.modelX (d := d) l)ᗮ) (u := v)
    (v := tailVec l hld (fun j => v (tailIdx l hld j)))
    (tailVec_mem_orth l hld (fun j => v (tailIdx l hld j))) ?_
  rw [Submodule.orthogonal_orthogonal, sub_tailVec_eq_headVec l hld v]
  exact headVec_mem_modelX l hld _

/-! ### The two-scale flow preserves `x₀` and `x₀ᗮ`, acting by `a` resp. `b` -/

lemma scaleMap_twoScale_std_low {l : ℕ} (hld : l < d) (a b : ℝ) (i : Fin l) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l)
      ((𝔹 d) (headIdx l hld i)) = a • (𝔹 d) (headIdx l hld i) := by
  rw [Submission.DiagonalFlow.scaleMap_basis, Submission.DiagonalFlow.twoScale_apply,
    if_pos (show (headIdx l hld i).val < l from i.isLt)]

lemma scaleMap_twoScale_std_high {l : ℕ} (hld : l < d) (a b : ℝ) (j : Fin (d - l)) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l)
      ((𝔹 d) (tailIdx l hld j)) = b • (𝔹 d) (tailIdx l hld j) := by
  rw [Submission.DiagonalFlow.scaleMap_basis, Submission.DiagonalFlow.twoScale_apply,
    if_neg (show ¬ (tailIdx l hld j).val < l by simp)]

/-- The two-scale flow preserves `x₀`. -/
lemma scaleMap_twoScale_mem_modelX {l : ℕ} (hld : l < d) (a b : ℝ) {v : ℝᵈ}
    (hv : v ∈ Submission.WedgeBlocks.modelX (d := d) l) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v ∈
      Submission.WedgeBlocks.modelX (d := d) l := by
  rw [modelX_eq_span_headIdx l hld] at hv ⊢
  exact Submodule.span_induction
    (p := fun x _ => Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) x ∈
      Submodule.span ℝ (Set.range (fun i : Fin l => (𝔹 d) (headIdx l hld i))))
    (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      rw [scaleMap_twoScale_std_low (l := l) hld a b i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (by simp) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun r x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) hv

/-- The two-scale flow preserves `x₀ᗮ`. -/
lemma scaleMap_twoScale_mem_orth {l : ℕ} (hld : l < d) (a b : ℝ) {v : ℝᵈ}
    (hv : v ∈ (Submission.WedgeBlocks.modelX (d := d) l)ᗮ) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v ∈
      (Submission.WedgeBlocks.modelX (d := d) l)ᗮ := by
  rw [orth_eq_span_tailIdx l hld] at hv ⊢
  exact Submodule.span_induction
    (p := fun x _ => Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) x ∈
      Submodule.span ℝ (Set.range (fun j : Fin (d - l) => (𝔹 d) (tailIdx l hld j))))
    (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      rw [scaleMap_twoScale_std_high (l := l) hld a b j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    (by simp) (fun x y _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun r x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) hv

/-- On `x₀` the two-scale flow is the scalar `a`. -/
lemma scaleMap_twoScale_eq_smul_of_mem_modelX {l : ℕ} (hld : l < d) (a b : ℝ) {v : ℝᵈ}
    (hv : v ∈ Submission.WedgeBlocks.modelX (d := d) l) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v = a • v := by
  rw [modelX_eq_span_headIdx l hld] at hv
  exact Submodule.span_induction
    (p := fun x _ => Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) x =
      a • x)
    (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact scaleMap_twoScale_std_low (l := l) hld a b i)
    (by simp) (fun x y _ _ hx hy => by rw [map_add, hx, hy, smul_add])
    (fun r x _ hx => by rw [map_smul, hx, smul_comm]) hv

/-- On `x₀ᗮ` the two-scale flow is the scalar `b`. -/
lemma scaleMap_twoScale_eq_smul_of_mem_orth {l : ℕ} (hld : l < d) (a b : ℝ) {v : ℝᵈ}
    (hv : v ∈ (Submission.WedgeBlocks.modelX (d := d) l)ᗮ) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v = b • v := by
  rw [orth_eq_span_tailIdx l hld] at hv
  exact Submodule.span_induction
    (p := fun x _ => Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) x =
      b • x)
    (fun x hx => by obtain ⟨j, rfl⟩ := hx; exact scaleMap_twoScale_std_high (l := l) hld a b j)
    (by simp) (fun x y _ _ hx hy => by rw [map_add, hx, hy, smul_add])
    (fun r x _ hx => by rw [map_smul, hx, smul_comm]) hv

/-- **The flow decomposition**: `a_t v = a • π_{x₀}v + b • π_{x₀ᗮ}v`. -/
lemma scaleMap_twoScale_eq_add {l : ℕ} (hld : l < d) (a b : ℝ) (v : ℝᵈ) :
    Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v =
      a • ((Submission.WedgeBlocks.modelX (d := d) l).starProjection v : ℝᵈ) +
      b • ((((Submission.WedgeBlocks.modelX (d := d) l)ᗮ).starProjection v : ℝᵈ)) := by
  set K : Submodule ℝ ℝᵈ := Submission.WedgeBlocks.modelX (d := d) l with hK
  have horth : v - K.starProjection v = Kᗮ.starProjection v := by
    have h := congrFun (congrArg DFunLike.coe (Submodule.starProjection_orthogonal (𝕜 := ℝ) K)) v
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    rw [h]
  have hmem : K.starProjection v ∈ K := by
    rw [Submodule.starProjection_apply]
    exact (K.orthogonalProjectionOnto v).2
  have hmem' : Kᗮ.starProjection v ∈ Kᗮ := by
    rw [Submodule.starProjection_apply]
    exact (Kᗮ.orthogonalProjectionOnto v).2
  have hdecomp : v = K.starProjection v + Kᗮ.starProjection v := by
    rw [← horth]; abel
  have hmain : Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l)
        (K.starProjection v + Kᗮ.starProjection v) =
      a • (K.starProjection v) + b • (Kᗮ.starProjection v) := by
    rw [map_add, scaleMap_twoScale_eq_smul_of_mem_modelX (l := l) hld a b hmem,
      scaleMap_twoScale_eq_smul_of_mem_orth (l := l) hld a b hmem']
  conv_lhs => rw [hdecomp]
  exact hmain

/-- Orthogonality Pythagoras, one-sided form. -/
lemma norm_sq_le_norm_add_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x y : E}
    (h : inner ℝ x y = 0) : ‖x‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
  have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y h
  nlinarith [sq_nonneg (‖y‖)]

/-- **The flow lower bound**: the two-scale flow shrinks no vector below
`max(a‖π_{x₀}v‖, b‖π_{x₀ᗮ}v‖)` (for `a, b ≥ 0`). -/
lemma max_le_norm_scaleMap_twoScale {l : ℕ} (hld : l < d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (v : ℝᵈ) :
    max (a * ‖((Submission.WedgeBlocks.modelX (d := d) l).starProjection v : ℝᵈ)‖)
        (b * ‖(((Submission.WedgeBlocks.modelX (d := d) l)ᗮ).starProjection v : ℝᵈ)‖)
      ≤ ‖Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v‖ := by
  set K : Submodule ℝ ℝᵈ := Submission.WedgeBlocks.modelX (d := d) l with hK
  have hmem : K.starProjection v ∈ K := by
    rw [Submodule.starProjection_apply]
    exact (K.orthogonalProjectionOnto v).2
  have hmem' : Kᗮ.starProjection v ∈ Kᗮ := by
    rw [Submodule.starProjection_apply]
    exact (Kᗮ.orthogonalProjectionOnto v).2
  have hxy : inner ℝ (K.starProjection v) (Kᗮ.starProjection v) = 0 :=
    (Submodule.mem_orthogonal K _).mp hmem' _ hmem
  have horth : inner ℝ (a • (K.starProjection v)) (b • (Kᗮ.starProjection v)) = 0 := by
    rw [inner_smul_left, inner_smul_right, hxy, mul_zero, mul_zero]
  have hflow := scaleMap_twoScale_eq_add (l := l) hld a b v
  have h1 : a * ‖(K.starProjection v : ℝᵈ)‖ ≤
      ‖Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v‖ := by
    have hsq := norm_sq_le_norm_add_sq horth
    rw [norm_smul, Real.norm_of_nonneg ha] at hsq
    rw [← hflow] at hsq
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have h2 : b * ‖(Kᗮ.starProjection v : ℝᵈ)‖ ≤
      ‖Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v‖ := by
    have horth' : inner ℝ (b • (Kᗮ.starProjection v)) (a • (K.starProjection v)) = 0 := by
      rw [inner_smul_left, inner_smul_right, inner_eq_zero_symm.mpr hxy, mul_zero, mul_zero]
    have hsq := norm_sq_le_norm_add_sq horth'
    have hadd : b • (Kᗮ.starProjection v) + a • (K.starProjection v) =
        Submission.DiagonalFlow.scaleMap (Submission.DiagonalFlow.twoScale a b l) v := by
      rw [hflow]; abel
    rw [norm_smul, Real.norm_of_nonneg hb] at hsq
    rw [hadd] at hsq
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  exact max_le h1 h2


/-! ### From "no short integer vector" to the escape hypothesis

This is the bridge between the metric-Diophantine statement (about integer vectors `n` and
their head/tail projections) and the glue hypothesis `c ≤ λ₁(a_t s_x ℤᵈ)`. -/

lemma inner_std_apply_of_mem_intPoints {n : ℝᵈ} (hn : n ∈ intPoints (d := d)) (k : Fin d) :
    ∃ z : ℤ, inner ℝ ((𝔹 d) k) n = z := by
  obtain ⟨z, hz⟩ := Submission.EscapeGlue.intPoints_coord_int n hn k
  exact ⟨z, by rw [inner_std_eq_coord]; exact hz⟩

/-- The orthogonal projection onto `x₀` commutes with an isometry carrying `x` onto `x₀`. -/
lemma starProjection_map_eq {l : ℕ} {x : Submodule ℝ ℝᵈ} {s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ}
    (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x = Submission.WedgeBlocks.modelX (d := d) l) (n : ℝᵈ) :
    ((Submission.WedgeBlocks.modelX (d := d) l).starProjection (s n) : ℝᵈ) =
      s ((x.starProjection n : ℝᵈ)) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (K := Submission.WedgeBlocks.modelX (d := d) l) (u := s n)
    (v := s (x.starProjection n : ℝᵈ)) ?_ ?_
  · rw [← hs]
    exact ⟨(x.starProjection n : ℝᵈ), Submodule.starProjection_apply_mem x n, rfl⟩
  · rw [← map_sub]
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [← hs] at hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    have hgoal : inner ℝ (n - x.starProjection n) u = 0 :=
      Submodule.starProjection_inner_eq_zero (K := x) n u hu
    have hgoal' : inner ℝ u (n - x.starProjection n) = 0 := by
      rwa [real_inner_comm] at hgoal
    show inner ℝ ((s : ℝᵈ → ℝᵈ) u) ((s : ℝᵈ → ℝᵈ) (n - x.starProjection n)) = 0
    rw [LinearIsometryEquiv.inner_map_map s u (n - x.starProjection n)]
    exact hgoal'

/-- The orthogonal projection onto `x₀ᗮ` commutes with an isometry carrying `x` onto `x₀`. -/
lemma starProjection_orth_map_eq {l : ℕ} {x : Submodule ℝ ℝᵈ} {s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ}
    (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x = Submission.WedgeBlocks.modelX (d := d) l) (n : ℝᵈ) :
    (((Submission.WedgeBlocks.modelX (d := d) l)ᗮ).starProjection (s n) : ℝᵈ) =
      s ((xᗮ).starProjection n : ℝᵈ) := by
  have h3 : (((Submission.WedgeBlocks.modelX (d := d) l)ᗮ).starProjection (s n) : ℝᵈ) =
      s n - ((Submission.WedgeBlocks.modelX (d := d) l).starProjection (s n) : ℝᵈ) := by
    have h := congrFun (congrArg DFunLike.coe
      (Submodule.starProjection_orthogonal (𝕜 := ℝ)
        (Submission.WedgeBlocks.modelX (d := d) l))) (s n)
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    exact h
  have h2 : ((xᗮ).starProjection n : ℝᵈ) = n - (x.starProjection n : ℝᵈ) := by
    have h := congrFun (congrArg DFunLike.coe (Submodule.starProjection_orthogonal (𝕜 := ℝ) x)) n
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    exact h
  rw [h3, starProjection_map_eq hs n, h2, map_sub]

/-- **Escape from "no bad integer vector"**: if no nonzero integer vector `n` satisfies
`max(e^{−t/ℓ}‖π_x n‖, e^{t/(d−ℓ)}‖π_xᗮ n‖) < e^{−εt}`, then the first minimum of the flowed
lattice `a_t s_x ℤᵈ` is at least `e^{−εt}`. -/
theorem successiveMinimum_ge_of_no_bad {l : ℕ} (hld : l < d) (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (x : Submodule ℝ ℝᵈ)
    (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x = Submission.WedgeBlocks.modelX (d := d) l)
    {t ε : ℝ}
    (hno : ∀ n : ℝᵈ, n ∈ intPoints (d := d) → n ≠ 0 →
      Real.exp (-(ε * t)) ≤ max (Real.exp (-t / (l : ℝ)) * ‖(x.starProjection n : ℝᵈ)‖)
        (Real.exp (t / ((d : ℝ) - (l : ℝ))) * ‖(xᗮ).starProjection n‖)) :
    Real.exp (-(ε * t)) ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
      (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1 := by
  classical
  set L : Submodule ℤ ℝᵈ :=
    Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t) with hL
  have hd0 : 0 < d := Nat.zero_lt_of_lt hld
  let T : ℝᵈ ≃ₗ[ℝ] ℝᵈ := Submission.EscapeGlue.flowMap (d := d) l s t
  -- nonemptiness of the successive-minimum set
  have hLI := Submission.ImageLattice.linearIndependent_imageBasis (d := d) T
  let idx0 : Fin d := ⟨0, hd0⟩
  have hmem : (Submission.ImageLattice.imageBasis (d := d) T idx0 : ℝᵈ) ∈ L := by
    rw [hL]
    exact Submission.ImageLattice.imageBasis_mem_imageSpan (d := d) T idx0
  let w0 : L := ⟨(Submission.ImageLattice.imageBasis (d := d) T idx0 : ℝᵈ), hmem⟩
  have hlin : LinearIndependent ℤ (fun _ : Fin 1 => (w0 : ℝᵈ)) := by
    have hc := LinearIndependent.comp hLI (fun _ : Fin 1 => idx0)
      (by intro a b _; exact Subsingleton.elim a b)
    have hfam : (fun i : Fin d => ((Submission.ImageLattice.imageBasis (d := d) T i) : ℝᵈ)) ∘
          (fun _ : Fin 1 => idx0) =
        (fun _ : Fin 1 => ((Submission.ImageLattice.imageBasis (d := d) T idx0) : ℝᵈ)) := by
      funext j; rfl
    rwa [hfam] at hc
  have hS : (Commons.Lattice.SuccessiveMinima.successiveMinimumSet L 1).Nonempty :=
    Commons.Lattice.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
      L 1 (f := fun _ : Fin 1 => w0) hlin ‖(w0 : ℝᵈ)‖ (fun j => le_rfl) (norm_nonneg _)
  -- the norm floor
  refine Commons.Lattice.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge L _ le_rfl
    hS ?_
  intro v hv0
  have hvT : (v : ℝᵈ) ∈ Submission.ImageLattice.imageSpan (d := d) T := by
    rw [← hL]; exact v.2
  rw [Submission.ImageLattice.imageSpan_eq_map (d := d) T] at hvT
  obtain ⟨n, hn_int, hnv⟩ := (Submodule.mem_map).mp hvT
  have hnv' : T n = (v : ℝᵈ) := hnv
  have hn0 : n ≠ 0 := by
    intro h0
    apply hv0
    have : (v : ℝᵈ) = 0 := by rw [← hnv', h0]; simp
    exact Subtype.ext this
  -- the flow lower bound at `s n`
  have hfloor := max_le_norm_scaleMap_twoScale (l := l) hld
    (a := Real.exp (-t / (l : ℝ))) (b := Real.exp (t / ((d : ℝ) - (l : ℝ))))
    (Real.exp_nonneg _) (Real.exp_nonneg _) (s n)
  rw [starProjection_map_eq hs n, starProjection_orth_map_eq hs n,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hfloor
  · have hT : T n = Submission.DiagonalFlow.scaleMap
        (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
          (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l) (s n) :=
      Submission.EscapeGlue.flowMap_apply (d := d) l s t n
    have hbad := hno n hn_int hn0
    calc Real.exp (-(ε * t)) ≤ max (Real.exp (-t / (l : ℝ)) * ‖(x.starProjection n : ℝᵈ)‖)
          (Real.exp (t / ((d : ℝ) - (l : ℝ))) * ‖(xᗮ).starProjection n‖) := hbad
      _ ≤ ‖Submission.DiagonalFlow.scaleMap
            (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
              (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l) (s n)‖ := hfloor
      _ = ‖(v : ℝᵈ)‖ := by rw [← hT, hnv']


/-! ### The graph vector, its coefficient family, and first conversion facts -/

/-- The tail-coordinate family `j ↦ Σ i, a i * c i j` of the combination `Σ i, a i • c i`. -/
def cComb (l : ℕ) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) : Fin (d - l) → ℝ :=
  fun j => ∑ i, a i * c i j

lemma tailVec_add (l : ℕ) (hld : l < d) (y y' : Fin (d - l) → ℝ) :
    tailVec l hld (y + y') = tailVec l hld y + tailVec l hld y' := by
  simp only [tailVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma tailVec_smul (l : ℕ) (hld : l < d) (r : ℝ) (y : Fin (d - l) → ℝ) :
    tailVec l hld (r • y) = r • tailVec l hld y := by
  simp only [tailVec, Pi.smul_apply, smul_assoc, Finset.smul_sum]

lemma tailVec_sum (l : ℕ) (hld : l < d) {ι : Type*} (s : Finset ι)
    (y : ι → Fin (d - l) → ℝ) :
    tailVec l hld (∑ i ∈ s, y i) = ∑ i ∈ s, tailVec l hld (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [tailVec]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tailVec_add, ih]

lemma tailVec_cComb (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) (a : Fin l → ℝ) :
    tailVec l hld (cComb l c a) = ∑ i, a i • tailVec l hld (c i) := by
  classical
  have h1 : cComb l c a = ∑ i, a i • c i := by
    funext j
    simp [cComb, Finset.sum_apply, Pi.smul_apply]
  rw [h1, tailVec_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [tailVec_smul]

/-- **The graph vector in head/tail form**: `graphVec c a = headVec a + tailVec (cComb c a)`. -/
lemma graphVec_eq_headVec_add (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ)
    (a : Fin l → ℝ) :
    graphVec l hld c a = headVec l hld a + tailVec l hld (cComb l c a) := by
  classical
  rw [graphVec, headVec, tailVec_cComb]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_add]

/-- The head part of a vector is controlled by its `x`-projections (both projections have
norm at most one). -/
lemma norm_headComp_le (l : ℕ) (hld : l < d) (x : Submodule ℝ ℝᵈ) (n : ℝᵈ) :
    ‖headVec l hld (fun i => n (headIdx l hld i))‖ ≤
      ‖(x.starProjection n : ℝᵈ)‖ + ‖(xᗮ).starProjection n‖ := by
  have h1 : headVec l hld (fun i => n (headIdx l hld i)) =
      ((Submission.WedgeBlocks.modelX (d := d) l).starProjection n : ℝᵈ) :=
    (starProjection_modelX_eq_headVec l hld n).symm
  set P : ℝᵈ := (x.starProjection n : ℝᵈ) with hP
  set Q : ℝᵈ := (xᗮ).starProjection n with hQ
  have hdecomp : n = P + Q := by
    have h := congrFun (congrArg DFunLike.coe (Submodule.starProjection_orthogonal (𝕜 := ℝ) x)) n
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    rw [hP, hQ, h]; abel
  rw [h1, hdecomp, map_add]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact Submodule.norm_starProjection_apply_le _ _
  · exact Submodule.norm_starProjection_apply_le _ _

end Submission.EscapeMetric

end
