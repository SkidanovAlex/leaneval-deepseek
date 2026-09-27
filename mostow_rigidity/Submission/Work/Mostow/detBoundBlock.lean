import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.absDetTwoBlockLe
import Submission.Work.Mostow.detFin2BlockDiag
import Submission.Work.Mostow.chordCoeSq
import Submission.Work.Mostow.prodLePowOfSumLe

namespace Work.Mostow

open scoped RealInnerProductSpace

theorem detBoundBlock (r : ℕ) (hr : 0 < r)
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (Submission.Mostow.E (2 * r)))
    (φ : Fin r → AddCircle (2 * Real.pi)) (ρ : Fin r → ℝ) (hρ : ∀ i, 0 < ρ i) (δ : ℝ) (hδ : 0 < δ)
    (R : Submission.Mostow.E (2 * r) ≃ₗᵢ[ℝ] Submission.Mostow.E (2 * r))
    (hblock : ∀ (i : Fin r) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      R (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (hle : ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 ≤ δ ^ 2) :
    |LinearMap.det ((R.toLinearEquiv : Submission.Mostow.E (2 * r) →ₗ[ℝ] Submission.Mostow.E (2 * r)) -
        LinearMap.id)| ≤ δ ^ (2 * r) / ∏ i, (ρ i) ^ 2 := by
  classical
  -- The rotation angle of the `i`-th block, read off on the first basis vector.
  let t0 : Fin r → ℝ := fun i => Classical.choose (hblock i 1 0)
  have ht0spec : ∀ i, (t0 i : AddCircle (2*Real.pi)) = φ i ∧
      R (e (i, 0)) = Real.cos (t0 i) • e (i, 0) + Real.sin (t0 i) • e (i, 1) := by
    intro i; simp only [t0]; simpa using Classical.choose_spec (hblock i 1 0)
  have ht0R : ∀ i, R (e (i, 0)) = Real.cos (t0 i) • e (i, 0) + Real.sin (t0 i) • e (i, 1) :=
    fun i => (ht0spec i).2
  have ht0φ : ∀ i, (t0 i : AddCircle (2*Real.pi)) = φ i := fun i => (ht0spec i).1
  let t1 : Fin r → ℝ := fun i => Classical.choose (hblock i 0 1)
  have ht1spec : ∀ i, (t1 i : AddCircle (2*Real.pi)) = φ i ∧
      R (e (i, 1)) = (-Real.sin (t1 i)) • e (i, 0) + Real.cos (t1 i) • e (i, 1) := by
    intro i; simp only [t1]; simpa using Classical.choose_spec (hblock i 0 1)
  have ht1R : ∀ i, R (e (i, 1)) = (-Real.sin (t1 i)) • e (i, 0) + Real.cos (t1 i) • e (i, 1) :=
    fun i => (ht1spec i).2
  -- `F = R - 1` and its matrix in the orthonormal basis `e`.
  let F : Submission.Mostow.E (2*r) →ₗ[ℝ] Submission.Mostow.E (2*r) :=
    (R.toLinearEquiv : Submission.Mostow.E (2*r) →ₗ[ℝ] Submission.Mostow.E (2*r)) - LinearMap.id
  let B : Fin r → Matrix (Fin 2) (Fin 2) ℝ := fun i =>
    !![Real.cos (t0 i) - 1, -Real.sin (t1 i); Real.sin (t0 i), Real.cos (t1 i) - 1]
  -- `F` respects the direct sum of the 2-dimensional blocks, so its matrix is block diagonal.
  have htoMat : LinearMap.toMatrix e.toBasis e.toBasis F =
      Matrix.of (fun (x y : Fin r × Fin 2) => if x.1 = y.1 then B x.1 x.2 y.2 else 0) := by
    ext x y
    rw [Matrix.of_apply]
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    obtain ⟨i,a⟩ := x
    obtain ⟨j,b⟩ := y
    by_cases hij : i = j
    · subst hij
      fin_cases a <;> fin_cases b <;>
        simp [F, B, ht0R, ht1R, LinearMap.sub_apply, inner_sub_right, inner_add_right,
          inner_smul_right]
    · rw [ite_eq_right hij]
      fin_cases b <;>
        simp [F, ht0R, ht1R, LinearMap.sub_apply, inner_sub_right, inner_add_right,
          inner_smul_right, hij]
  -- determinant = product of the block determinants
  have hdet : LinearMap.det F = ∏ i, (B i).det := by
    rw [(LinearMap.det_toMatrix e.toBasis F).symm, htoMat, detFin2BlockDiag B]
  have habs : |LinearMap.det F| = ∏ i, |(B i).det| := by
    rw [hdet, Finset.abs_prod]
  -- each block is bounded by the chord of its rotation angle
  have hBle : ∀ i, |(B i).det| ≤ 2 - 2 * Real.cos (t0 i) := by
    intro i
    have h := absDetTwoBlockLe (a := t0 i) (b := t1 i) (by rw [ht0φ i, (ht1spec i).1])
    simpa [B] using h
  have hprod : ∏ i, |(B i).det| ≤ ∏ i, (Submission.Mostow.chord (φ i))^2 := by
    have h1 : ∏ i, |(B i).det| ≤ ∏ i, (2 - 2 * Real.cos (t0 i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hBle i)
    have h2 : ∏ i, (2 - 2 * Real.cos (t0 i)) = ∏ i, (Submission.Mostow.chord (φ i))^2 := by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [← chordCoeSq (t0 i), ← ht0φ i]
      rfl
    rw [h2] at h1; exact h1
  have hmain : |LinearMap.det F| ≤ ∏ i, (Submission.Mostow.chord (φ i))^2 := by
    rw [habs]; exact hprod
  -- arithmetic: AM-GM plus the hypothesis `∑ ρᵢ² chordᵢ² ≤ δ²`
  have hx : ∀ i, 0 ≤ (ρ i)^2 * (Submission.Mostow.chord (φ i))^2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h4 := prodLePowOfSumLe (r := r) (x := fun i => (ρ i)^2 * (Submission.Mostow.chord (φ i))^2)
      hr hx hδ hle
  have hsplit : ∏ i, ((ρ i)^2 * (Submission.Mostow.chord (φ i))^2)
      = (∏ i, (ρ i)^2) * (∏ i, (Submission.Mostow.chord (φ i))^2) := Finset.prod_mul_distrib
  have hpos : 0 < ∏ i, (ρ i)^2 := Finset.prod_pos (fun i _ => pow_pos (hρ i) 2)
  have hlast : ∏ i, (Submission.Mostow.chord (φ i))^2 ≤ δ^(2*r) / ∏ i, (ρ i)^2 := by
    rw [le_div_iff₀ hpos, mul_comm, ← hsplit]
    exact h4
  exact le_trans hmain hlast

end Work.Mostow
