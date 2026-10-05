import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp

/-!
# RPA3, D2: vocabulary for `theta_columns_independent`

`θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)` is the tubular parametrisation of the
neighbourhood of the Lagrangian family.  Node D2 needs the statement that the four columns
`∂_xθ, ∂_tθ, ∂_{ξ₁}θ, ∂_{ξ₂}θ` of the derivative of `Z ↦ θ(τ,Z)` are linearly independent,
uniformly for `ξ` in a small ball and `(τ,x,t)` in a compact parameter region.

This file collects the vocabulary in which that statement is proved:

* `thTheta`, the tubular map as a function on `ℝ × PS` (`w = (τ,((x,t),ξ))`);
* `thCol`, the four columns, as functions of `w`;
* `thCoord`, the four coordinate functionals of `PS`, and `thColMat`, the `4 × 4` matrix of the
  four columns in those coordinates;
* the elementary dictionary between `ColumnsIndependent`, the sum `∑ j, a j • thCol L j w`, and
  invertibility of `thColMat`.

Everything here is proved from `TubularDefs` and `Symp` only.
-/

open scoped ContDiff Matrix

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-! ## Coordinates of `PS` -/

/-- `q₁` as a linear functional on `PS`. -/
def thCq1 : PS →ₗ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `q₂` as a linear functional on `PS`. -/
def thCq2 : PS →ₗ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `p₁` as a linear functional on `PS`. -/
def thCp1 : PS →ₗ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `p₂` as a linear functional on `PS`. -/
def thCp2 : PS →ₗ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- The four coordinate functionals of `PS`, indexed by `Fin 4`. -/
def thCoord : Fin 4 → (PS →ₗ[ℝ] ℝ) := ![thCq1, thCq2, thCp1, thCp2]

@[simp] theorem thCoord_zero_apply (v : PS) : thCoord 0 v = v.1.1 := rfl
@[simp] theorem thCoord_one_apply (v : PS) : thCoord 1 v = v.1.2 := rfl
@[simp] theorem thCoord_two_apply (v : PS) : thCoord 2 v = v.2.1 := rfl
@[simp] theorem thCoord_three_apply (v : PS) : thCoord 3 v = v.2.2 := rfl

theorem thCoord_continuous (i : Fin 4) : Continuous (thCoord i) := by
  fin_cases i <;>
    (first | exact continuous_fst.fst | exact continuous_fst.snd |
      exact continuous_snd.fst | exact continuous_snd.snd)

/-- A point of `PS` all of whose coordinates vanish is zero. -/
theorem thCoord_eq_zero {v : PS} (h : ∀ i, thCoord i v = 0) : v = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [thCoord_zero_apply, thCoord_one_apply, thCoord_two_apply,
    thCoord_three_apply] at h0 h1 h2 h3
  exact Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3)

/-! ## The tubular map and its four columns, on `ℝ × PS` -/

/-- The tubular map as a function of `w = (τ, ((x,t),ξ)) : ℝ × PS`. -/
def thTheta (L : LagFamilyAll) (w : ℝ × PS) : PS :=
  theta L w.1 w.2.1.1 w.2.1.2 w.2.2

@[simp] theorem thTheta_apply (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    thTheta L (τ, ((x, t), ξ)) = theta L τ x t ξ := rfl

/-- The four columns `∂_xθ, ∂_tθ, ∂_{ξ₁}θ, ∂_{ξ₂}θ` of the derivative of `Z ↦ θ(τ,Z)`, as
functions of `w = (τ, ((x,t),ξ)) : ℝ × PS`. -/
def thCol (L : LagFamilyAll) (j : Fin 4) (w : ℝ × PS) : PS :=
  ![deriv (fun y => theta L w.1 y w.2.1.2 w.2.2) w.2.1.1,
    deriv (fun s => theta L w.1 w.2.1.1 s w.2.2) w.2.1.2,
    deriv (fun u => theta L w.1 w.2.1.1 w.2.1.2 (u, w.2.2.2)) w.2.2.1,
    deriv (fun u => theta L w.1 w.2.1.1 w.2.1.2 (w.2.2.1, u)) w.2.2.2] j

@[simp] theorem thCol_zero (L : LagFamilyAll) (w : ℝ × PS) :
    thCol L 0 w = deriv (fun y => theta L w.1 y w.2.1.2 w.2.2) w.2.1.1 := rfl

@[simp] theorem thCol_one (L : LagFamilyAll) (w : ℝ × PS) :
    thCol L 1 w = deriv (fun s => theta L w.1 w.2.1.1 s w.2.2) w.2.1.2 := rfl

@[simp] theorem thCol_two (L : LagFamilyAll) (w : ℝ × PS) :
    thCol L 2 w = deriv (fun u => theta L w.1 w.2.1.1 w.2.1.2 (u, w.2.2.2)) w.2.2.1 := rfl

@[simp] theorem thCol_three (L : LagFamilyAll) (w : ℝ × PS) :
    thCol L 3 w = deriv (fun u => theta L w.1 w.2.1.1 w.2.1.2 (w.2.2.1, u)) w.2.2.2 := rfl

/-- The `4 × 4` matrix of the four columns of `Z ↦ θ(τ,Z)`, in the coordinates of `PS`. -/
def thColMat (L : LagFamilyAll) (w : ℝ × PS) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => thCoord i (thCol L j w)

@[simp] theorem thColMat_apply (L : LagFamilyAll) (w : ℝ × PS) (i j : Fin 4) :
    thColMat L w i j = thCoord i (thCol L j w) := rfl

theorem continuous_thColMat (L : LagFamilyAll) (h : ∀ j, Continuous (thCol L j)) :
    Continuous (thColMat L) := by
  refine continuous_matrix fun i j => ?_
  exact (thCoord_continuous i).comp (h j)

/-! ## The dictionary with `ColumnsIndependent` -/

/-- `ColumnsIndependent` is the injectivity of the map `a ↦ ∑ j, a j • thCol L j w` on `ℝ⁴`. -/
theorem columnsIndependent_iff_sum (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    ColumnsIndependent L τ x t ξ ↔
      ∀ a : Fin 4 → ℝ, (∑ j, a j • thCol L j (τ, ((x, t), ξ))) = 0 → a = 0 := by
  constructor
  · intro h a ha
    rw [Fin.sum_univ_four] at ha
    simp only [thCol_zero, thCol_one, thCol_two, thCol_three] at ha
    obtain ⟨h0, h1, h2, h3⟩ := h (a 0) (a 1) (a 2) (a 3) ha
    funext i
    fin_cases i <;> assumption
  · intro h a b c d habcd
    have hsum : (∑ j, (![a, b, c, d] : Fin 4 → ℝ) j • thCol L j (τ, ((x, t), ξ))) = 0 := by
      rw [Fin.sum_univ_four]
      simpa using habcd
    have h0 := congrFun (h _ hsum) 0
    have h1 := congrFun (h _ hsum) 1
    have h2 := congrFun (h _ hsum) 2
    have h3 := congrFun (h _ hsum) 3
    exact ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- A nonzero determinant of `thColMat` gives linear independence of the four columns. -/
theorem columnsIndependent_of_det_ne_zero (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ)
    (h : (thColMat L (τ, ((x, t), ξ))).det ≠ 0) : ColumnsIndependent L τ x t ξ := by
  rw [columnsIndependent_iff_sum]
  intro a ha
  refine Matrix.eq_zero_of_mulVec_eq_zero h ?_
  funext i
  show (thColMat L (τ, ((x, t), ξ)) *ᵥ a) i = (0 : ℝ)
  rw [Matrix.mulVec_apply_eq_sum]
  have key : ∀ j : Fin 4, thColMat L (τ, ((x, t), ξ)) i j * a j
      = thCoord i (a j • thCol L j (τ, ((x, t), ξ))) := by
    intro j
    rw [thColMat_apply, map_smul, smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun j _ => key j), ← map_sum, ha, map_zero]

/-- Linear independence of the four columns gives a nonzero determinant of `thColMat`. -/
theorem det_ne_zero_of_columnsIndependent (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ)
    (h : ColumnsIndependent L τ x t ξ) : (thColMat L (τ, ((x, t), ξ))).det ≠ 0 := by
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨v, hvne, hv⟩ := hdet
  rw [columnsIndependent_iff_sum] at h
  refine hvne (h v ?_)
  refine thCoord_eq_zero fun i => ?_
  have h2 : Matrix.mulVec (thColMat L (τ, ((x, t), ξ))) v i = 0 := by rw [hv]; rfl
  rw [Matrix.mulVec_apply_eq_sum] at h2
  rw [← h2, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [thColMat_apply, map_smul, smul_eq_mul, mul_comm]

end Work.RPA3
