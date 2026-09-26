import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SellingDefs

/-! Auxiliary lemmas for the assembly of `exists_conj_into_sellingStab` (owned by the node;
not part of the shared `SellingDefs` interface). -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- `IsUnit B.det` gives the right cancellation law. -/
theorem mul_inv_of_isUnit {B : IMat} (h : IsUnit B.det) : B * B⁻¹ = 1 :=
  haveI := Matrix.invertibleOfIsUnitDet B h
  Matrix.mul_inv_of_invertible B

/-- `IsUnit B.det` gives the left cancellation law. -/
theorem inv_mul_of_isUnit {B : IMat} (h : IsUnit B.det) : B⁻¹ * B = 1 :=
  haveI := Matrix.invertibleOfIsUnitDet B h
  Matrix.inv_mul_of_invertible B

/-- An integer matrix (applied to `y, y'`) preserves congruence mod `2`. -/
theorem modEq_mulVec {B : IMat} {y y' : IVec} (h : modEq y y') :
    modEq (B.mulVec y) (B.mulVec y') := by
  intro i
  choose c hcc using fun j : Fin 3 => h j
  refine ⟨∑ j, B i j * c j, ?_⟩
  have hsub : (B.mulVec y') i - (B.mulVec y) i = ∑ j, B i j * (y' j - y j) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  rw [hsub]
  have : ∑ j : Fin 3, B i j * (y' j - y j) = 2 * ∑ j : Fin 3, B i j * c j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcc j]; ring
  rw [this]

/-- A unimodular integer matrix is injective on `ℤ³`. -/
theorem mulVec_eq_zero {B : IMat} (hB : B⁻¹ * B = 1) {y : IVec} (h : B.mulVec y = 0) : y = 0 := by
  have : y = B⁻¹.mulVec (B.mulVec y) := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at this
  exact this

/-- A unimodular integer matrix induces a bijection on the classes mod `2`. -/
theorem modEq_mulVec_iff {B : IMat} (hB : B * B⁻¹ = 1) (hB' : B⁻¹ * B = 1) {y y' : IVec} :
    modEq (B.mulVec y) (B.mulVec y') ↔ modEq y y' := by
  constructor
  · intro h
    have h1 := modEq_mulVec (B := B⁻¹) h
    have hy : B⁻¹.mulVec (B.mulVec y) = y := by rw [Matrix.mulVec_mulVec, hB', Matrix.one_mulVec]
    have hy' : B⁻¹.mulVec (B.mulVec y') = y' := by rw [Matrix.mulVec_mulVec, hB', Matrix.one_mulVec]
    rwa [hy, hy'] at h1
  · exact modEq_mulVec

/-- Conjugating the form and the class structure: `y` is minimal for `Q₂ = BᵀQ₁B` iff `B y` is
minimal for `Q₁`. -/
theorem minVecs_map_iff {B Q₁ Q₂ : IMat} (hBu : IsUnit B.det) (h : Bᵀ * Q₁ * B = Q₂)
    (y : IVec) : y ∈ minVecs Q₂ ↔ B.mulVec y ∈ minVecs Q₁ := by
  have hB : B * B⁻¹ = 1 := mul_inv_of_isUnit hBu
  have hB' : B⁻¹ * B = 1 := inv_mul_of_isUnit hBu
  have hBB' : ∀ z : IVec, B.mulVec (B⁻¹.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  have hB'B : ∀ z : IVec, B⁻¹.mulVec (B.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hB', Matrix.one_mulVec]
  have hqe : ∀ w, qf Q₂ w = qf Q₁ (B.mulVec w) := by
    intro w; rw [← h, qf_conj]
  have hmod : ∀ w w' : IVec, modEq (B.mulVec w) (B.mulVec w') ↔ modEq w w' :=
    fun w w' => modEq_mulVec_iff hB hB'
  constructor
  · rintro ⟨hy0, hy⟩
    refine ⟨fun h0 => hy0 (by rw [← hB'B y, h0, Matrix.mulVec_zero]), fun z hz => ?_⟩
    have hz' : modEq y (B⁻¹.mulVec z) := by
      have h1 : modEq (B.mulVec y) (B.mulVec (B⁻¹.mulVec z)) := by rw [hBB' z]; exact hz
      exact (hmod y (B⁻¹.mulVec z)).mp h1
    have hy' := hy _ hz'
    have h1 : qf Q₁ (B.mulVec y) = qf Q₂ y := (hqe y).symm
    have h2 : qf Q₁ z = qf Q₂ (B⁻¹.mulVec z) := by
      calc qf Q₁ z = qf Q₁ (B.mulVec (B⁻¹.mulVec z)) := by rw [hBB' z]
        _ = qf Q₂ (B⁻¹.mulVec z) := (hqe (B⁻¹.mulVec z)).symm
    rw [h1, h2]
    exact hy'
  · rintro ⟨hy0, hy⟩
    refine ⟨fun h0 => hy0 (by rw [h0, Matrix.mulVec_zero]), fun y' hy' => ?_⟩
    have hthis := hy (B.mulVec y') ((hmod y y').mpr hy')
    have h1 : qf Q₂ y = qf Q₁ (B.mulVec y) := hqe y
    have h2 : qf Q₂ y' = qf Q₁ (B.mulVec y') := hqe y'
    rw [h1, h2]
    exact hthis

/-- `sellingVecs` is closed under negation. -/
theorem sellingVecs_neg (E : List (Fin 4 × Fin 4)) (y : IVec) :
    y ∈ sellingVecs E ↔ -y ∈ sellingVecs E := by
  have hx : (Fin.cons (0 : ℤ) (-y) : Fin 4 → ℤ) = -(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) := by
    funext a
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩ <;> simp
  have hval : ∀ a b : Fin 4,
      |(Fin.cons (0 : ℤ) (-y) : Fin 4 → ℤ) a - (Fin.cons (0 : ℤ) (-y) : Fin 4 → ℤ) b| =
      |(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) a - (Fin.cons (0 : ℤ) y : Fin 4 → ℤ) b| := by
    intro a b
    rw [hx, Pi.neg_apply, Pi.neg_apply]
    have h : -(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) a - -(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) b =
        -((Fin.cons (0 : ℤ) y : Fin 4 → ℤ) a - (Fin.cons (0 : ℤ) y : Fin 4 → ℤ) b) := by ring
    rw [h, abs_neg]
  constructor
  · rintro ⟨hy0, hy⟩
    exact ⟨neg_ne_zero.mpr hy0, fun e he => by rw [hval e.1 e.2]; exact hy e he⟩
  · rintro ⟨hy0, hy⟩
    exact ⟨neg_ne_zero.mp hy0, fun e he => by rw [← hval e.1 e.2]; exact hy e he⟩

/-- `sellingVecs` only depends on the underlying set of edges. -/
theorem sellingVecs_congr_finset {E E' : List (Fin 4 × Fin 4)} (h : E.toFinset = E'.toFinset) :
    sellingVecs E = sellingVecs E' := by
  have hmem : ∀ e : Fin 4 × Fin 4, e ∈ E ↔ e ∈ E' := by
    intro e
    rw [← List.mem_toFinset, h, List.mem_toFinset]
  ext y
  constructor
  · rintro ⟨hy0, hy⟩
    exact ⟨hy0, fun e he => hy e ((hmem e).mpr he)⟩
  · rintro ⟨hy0, hy⟩
    exact ⟨hy0, fun e he => hy e ((hmem e).mp he)⟩

/-- A unit determinant is `1` or `-1`. -/
theorem det_eq_one_or_neg_one {B : IMat} (h : IsUnit B.det) : B.det = 1 ∨ B.det = -1 :=
  Int.isUnit_iff.mp h

/-- The conjugate of a unimodular matrix preserves an invariant form. -/
theorem conjugate_invariant {Q W A : IMat} (hW : W * W⁻¹ = 1) (hW' : W⁻¹ * W = 1)
    (hA : Aᵀ * Q * A = Q) :
    (W⁻¹ * A * W)ᵀ * (Wᵀ * Q * W) * (W⁻¹ * A * W) = Wᵀ * Q * W := by
  have ht : (W⁻¹ * A * W)ᵀ = Wᵀ * Aᵀ * (W⁻¹)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hc1 : (W⁻¹)ᵀ * Wᵀ = 1 := by
    rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
  rw [ht]
  calc (Wᵀ * Aᵀ * (W⁻¹)ᵀ) * (Wᵀ * Q * W) * (W⁻¹ * A * W)
      = Wᵀ * (Aᵀ * ((W⁻¹)ᵀ * Wᵀ) * (Q * (W * W⁻¹)) * A) * W := by noncomm_ring
    _ = Wᵀ * (Aᵀ * 1 * (Q * 1) * A) * W := by rw [hc1, hW]
    _ = Wᵀ * Q * W := by
        rw [show Aᵀ * 1 * (Q * 1) * A = Aᵀ * Q * A from by noncomm_ring, hA]

/-- Inverse of a product of unimodular matrices. -/
theorem inv_mul_eq {C W : IMat} (_hC : C * C⁻¹ = 1) (hC' : C⁻¹ * C = 1)
    (hW : W * W⁻¹ = 1) (hW' : W⁻¹ * W = 1) : (C * W⁻¹)⁻¹ = W * C⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  calc W * C⁻¹ * (C * W⁻¹) = W * (C⁻¹ * C) * W⁻¹ := by noncomm_ring
    _ = W * 1 * W⁻¹ := by rw [hC']
    _ = 1 := by rw [Matrix.mul_one, hW]

end Work.SG
