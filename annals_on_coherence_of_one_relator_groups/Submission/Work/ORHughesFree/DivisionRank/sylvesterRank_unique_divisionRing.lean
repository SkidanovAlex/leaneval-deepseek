import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.ORHughesFree.DivisionRank

open Work.ORHughesFree

/-- The identity `p × p` matrix has Sylvester rank `p`.  This is the normalization that pins
down the value of a Sylvester rank function on matrices over a division ring. -/
theorem rk_one_identity {R : Type*} [Ring R] (rk : SylvesterRank R) (p : ℕ) :
    rk.rk p p (1 : Matrix (Fin p) (Fin p) R) = p := by
  induction p with
  | zero =>
      rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) R) 0, rk.rk_zero]
      norm_num
  | succ p ih =>
      have hstep : blockDiagFin (1 : Matrix (Fin p) (Fin p) R)
          (1 : Matrix (Fin 1) (Fin 1) R) = (1 : Matrix (Fin (p+1)) (Fin (p+1)) R) := by
        simp [blockDiagFin]
      rw [← hstep, rk.rk_blockDiag, ih, rk.rk_one]
      push_cast
      ring

/-- **Rank factorization over a division ring.**  Every `n × m` matrix `A` over a division ring
admits a factorization `A = B * C` through a `p`-dimensional space, where `B` has a left inverse
`B'` and `C` has a right inverse `C'`.  Concretely `p` is the dimension of the row space of `A`.

This is the "Gaussian elimination"/Smith normal form input for the uniqueness of Sylvester rank
functions: the factorization is independent of any rank function. -/
theorem exists_rank_factorization {D : Type*} [DivisionRing D] (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) D) :
    ∃ (p : ℕ) (B : Matrix (Fin n) (Fin p) D) (C : Matrix (Fin p) (Fin m) D)
      (B' : Matrix (Fin p) (Fin n) D) (C' : Matrix (Fin m) (Fin p) D),
      A = B * C ∧ B' * B = 1 ∧ C * C' = 1 := by
  classical
  -- The left-linear map `x ↦ x * A` has the rows of `A` as its image.
  let f : (Fin n → D) →ₗ[D] (Fin m → D) := A.toLinearMapRight'
  let W : Submodule D (Fin m → D) := LinearMap.range f
  let p : ℕ := Module.finrank D W
  let b : Module.Basis (Fin p) D W := Module.finBasis D W
  let e : W ≃ₗ[D] (Fin p → D) := b.equivFun
  let fW : (Fin n → D) →ₗ[D] W := f.codRestrict W (fun x => LinearMap.mem_range.mpr ⟨x, rfl⟩)
  -- The inclusion of the image, and the projection onto coordinates in the chosen basis.
  let g : (Fin p → D) →ₗ[D] (Fin m → D) := W.subtype.comp e.symm.toLinearMap
  let h : (Fin n → D) →ₗ[D] (Fin p → D) := e.toLinearMap.comp fW
  have h1 : W.subtype ∘ₗ fW = f := LinearMap.subtype_comp_codRestrict f W _
  have hgh : g ∘ₗ h = f := by
    rw [← h1]
    ext x
    simp only [LinearMap.comp_apply, g, h, LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]
    rw [LinearEquiv.symm_apply_apply]
  have hginj : Function.Injective g := by
    intro x y hxy
    exact e.symm.injective (Subtype.coe_injective hxy)
  have hfWsurj : Function.Surjective fW := by
    intro w
    obtain ⟨x, hx⟩ := w.2
    exact ⟨x, Subtype.ext hx⟩
  have hsurj : Function.Surjective h := by
    intro y
    obtain ⟨x, hx⟩ := hfWsurj (e.symm y)
    refine ⟨x, ?_⟩
    simp only [h, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [hx, LinearEquiv.apply_symm_apply]
  -- Right inverse of `h` (it is surjective), left inverse of `g` (it is injective).
  obtain ⟨h', hh'⟩ := h.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let B : Matrix (Fin n) (Fin p) D := h.toMatrixRight'
  let B' : Matrix (Fin p) (Fin n) D := h'.toMatrixRight'
  obtain ⟨g', hg'⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hginj)
  let C : Matrix (Fin p) (Fin m) D := g.toMatrixRight'
  let C' : Matrix (Fin m) (Fin p) D := g'.toMatrixRight'
  have hCg : C.toLinearMapRight' = g := LinearEquiv.symm_apply_apply _ _
  have hBh : B.toLinearMapRight' = h := LinearEquiv.symm_apply_apply _ _
  have hBC : B * C = A := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, hCg, hBh]
    show g ∘ₗ h = A.toLinearMapRight'
    rw [hgh]
  refine ⟨p, B, C, B', C', hBC.symm, ?_, ?_⟩
  · have hh : (h ∘ₗ h').toMatrixRight' = (1 : Matrix (Fin p) (Fin p) D) := by
      rw [hh']; exact LinearMap.toMatrixRight'_id
    rw [LinearMap.toMatrixRight'_comp] at hh
    simpa only [B, B'] using hh
  · have hg : (g' ∘ₗ g).toMatrixRight' = (1 : Matrix (Fin p) (Fin p) D) := by
      rw [hg']; exact LinearMap.toMatrixRight'_id
    rw [LinearMap.toMatrixRight'_comp] at hg
    simpa only [C, C'] using hg

/-- Any Sylvester rank function assigns to `A` the dimension `p` of any rank factorization
`A = B * C` with `B` left-invertible and `C` right-invertible. -/
theorem sylvesterRank_eq_of_rank_factorization {D : Type*} [DivisionRing D] (rk : SylvesterRank D)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) D) (B : Matrix (Fin n) (Fin p) D)
    (C : Matrix (Fin p) (Fin m) D) (B' : Matrix (Fin p) (Fin n) D)
    (C' : Matrix (Fin m) (Fin p) D) (hBC : A = B * C) (hB : B' * B = 1) (hC : C * C' = 1) :
    rk.rk n m A = p := by
  have hId : rk.rk p p (1 : Matrix (Fin p) (Fin p) D) = p := rk_one_identity rk p
  have hle : rk.rk n m A ≤ (p : ℝ) := by
    have h1 : rk.rk n m A ≤ rk.rk p m C := by
      rw [hBC]; exact rk.rk_mul_le_right B C
    have h2 : rk.rk p m C ≤ (p : ℝ) := by
      have h := rk.rk_mul_le_left (1 : Matrix (Fin p) (Fin p) D) C
      rw [Matrix.one_mul, hId] at h
      exact h
    exact le_trans h1 h2
  have hge : (p : ℝ) ≤ rk.rk n m A := by
    have h1 : B' * A * C' = (1 : Matrix (Fin p) (Fin p) D) := by
      rw [hBC, ← Matrix.mul_assoc B' B C, Matrix.mul_assoc (B' * B) C C', hB, hC, Matrix.one_mul]
    have h2 : rk.rk p p (B' * A * C') ≤ rk.rk n p (A * C') := by
      rw [Matrix.mul_assoc]
      exact rk.rk_mul_le_right B' (A * C')
    have h3 : rk.rk n p (A * C') ≤ rk.rk n m A := rk.rk_mul_le_left A C'
    have h4 : (p : ℝ) = rk.rk p p (B' * A * C') := by rw [h1]; exact hId.symm
    rw [h4]
    exact le_trans h2 h3
  exact le_antisymm hle hge

theorem sylvesterRank_unique_divisionRing {D : Type*} [DivisionRing D] (rk₁ rk₂ : SylvesterRank D)
    (n m : ℕ) (A : Matrix (Fin n) (Fin m) D) : rk₁.rk n m A = rk₂.rk n m A := by
  obtain ⟨p, B, C, B', C', hA, hB, hC⟩ := exists_rank_factorization n m A
  rw [sylvesterRank_eq_of_rank_factorization rk₁ A B C B' C' hA hB hC,
      sylvesterRank_eq_of_rank_factorization rk₂ A B C B' C' hA hB hC]

end Work.ORHughesFree.DivisionRank
