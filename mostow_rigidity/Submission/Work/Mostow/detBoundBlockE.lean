import Mathlib
import Submission.Work.Mostow.detBoundBlock

namespace Work.Mostow

open scoped RealInnerProductSpace

/-- If `x : Fin r → ℝ` is nonnegative and its sum is at most `δ ^ 2` with `δ > 0`, then the
product of the entries is at most `δ ^ (2 * r)`.  Unlike `prodLePowOfSumLe` this needs no
positivity assumption on `r` (the case `r = 0` is the trivial `1 ≤ 1`). -/
theorem prodLePowOfSumLeZero {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) {δ : ℝ}
    (_hδ : 0 < δ) (h : ∑ i, x i ≤ δ ^ 2) : ∏ i, x i ≤ δ ^ (2 * r) := by
  have hle : ∀ i, x i ≤ δ ^ 2 := fun i =>
    (Finset.single_le_sum (f := x) (fun j _ => hx j) (Finset.mem_univ i)).trans h
  calc ∏ i, x i ≤ ∏ _i : Fin r, δ ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ => hx i) (fun i _ => hle i)
    _ = (δ ^ 2) ^ r := by simp
    _ = δ ^ (2 * r) := (pow_mul δ 2 r).symm

theorem detBoundBlockE (m : ℕ) (hm : Even m)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (φ : Fin (m / 2) → AddCircle (2 * Real.pi)) (ρ : Fin (m / 2) → ℝ) (hρ : ∀ i, 0 < ρ i)
    (δ : ℝ) (hδ : 0 < δ) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      R (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (hle : ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 ≤ δ ^ 2) :
    |LinearMap.det ((R.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m) - LinearMap.id)|
      ≤ δ ^ m / ∏ i, (ρ i) ^ 2 := by
  classical
  -- `m` is even, so `m = 2 * (m / 2)`.
  obtain ⟨b, hb⟩ := even_iff_exists_two_mul.mp hm
  have hdvd : 2 ∣ m := ⟨b, hb⟩
  have hm2 : 2 * (m / 2) = m := Nat.mul_div_cancel' hdvd
  -- The rotation angle of the `i`-th block, read off on the first basis vector.
  let t0 : Fin (m / 2) → ℝ := fun i => Classical.choose (hblock i 1 0)
  have ht0spec : ∀ i, (t0 i : AddCircle (2 * Real.pi)) = φ i ∧
      R (e (i, 0)) = Real.cos (t0 i) • e (i, 0) + Real.sin (t0 i) • e (i, 1) := by
    intro i; simp only [t0]; simpa using Classical.choose_spec (hblock i 1 0)
  have ht0R : ∀ i, R (e (i, 0)) = Real.cos (t0 i) • e (i, 0) + Real.sin (t0 i) • e (i, 1) :=
    fun i => (ht0spec i).2
  have ht0φ : ∀ i, (t0 i : AddCircle (2 * Real.pi)) = φ i := fun i => (ht0spec i).1
  let t1 : Fin (m / 2) → ℝ := fun i => Classical.choose (hblock i 0 1)
  have ht1spec : ∀ i, (t1 i : AddCircle (2 * Real.pi)) = φ i ∧
      R (e (i, 1)) = (-Real.sin (t1 i)) • e (i, 0) + Real.cos (t1 i) • e (i, 1) := by
    intro i; simp only [t1]; simpa using Classical.choose_spec (hblock i 0 1)
  have ht1R : ∀ i, R (e (i, 1)) = (-Real.sin (t1 i)) • e (i, 0) + Real.cos (t1 i) • e (i, 1) :=
    fun i => (ht1spec i).2
  -- `F = R - 1` and its matrix in the orthonormal basis `e`.
  let F : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m :=
    (R.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m) - LinearMap.id
  let B : Fin (m / 2) → Matrix (Fin 2) (Fin 2) ℝ := fun i =>
    !![Real.cos (t0 i) - 1, -Real.sin (t1 i); Real.sin (t0 i), Real.cos (t1 i) - 1]
  -- `F` respects the direct sum of the 2-dimensional blocks, so its matrix is block diagonal.
  have htoMat : LinearMap.toMatrix e.toBasis e.toBasis F =
      Matrix.of (fun (x y : Fin (m / 2) × Fin 2) => if x.1 = y.1 then B x.1 x.2 y.2 else 0) := by
    ext x y
    rw [Matrix.of_apply]
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    obtain ⟨i, a⟩ := x
    obtain ⟨j, bb⟩ := y
    by_cases hij : i = j
    · subst hij
      fin_cases a <;> fin_cases bb <;>
        simp [F, B, ht0R, ht1R, LinearMap.sub_apply, inner_sub_right, inner_add_right,
          inner_smul_right]
    · rw [ite_eq_right hij]
      fin_cases bb <;>
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
  have hprod : ∏ i, |(B i).det| ≤ ∏ i, (Submission.Mostow.chord (φ i)) ^ 2 := by
    have h1 : ∏ i, |(B i).det| ≤ ∏ i, (2 - 2 * Real.cos (t0 i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hBle i)
    have h2 : ∏ i, (2 - 2 * Real.cos (t0 i)) = ∏ i, (Submission.Mostow.chord (φ i)) ^ 2 := by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [← chordCoeSq (t0 i), ← ht0φ i]
      rfl
    rw [h2] at h1; exact h1
  have hmain : |LinearMap.det F| ≤ ∏ i, (Submission.Mostow.chord (φ i)) ^ 2 := by
    rw [habs]; exact hprod
  -- arithmetic: AM-GM plus the hypothesis `∑ ρᵢ² chordᵢ² ≤ δ²`
  have hx : ∀ i, 0 ≤ (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h4 := prodLePowOfSumLeZero (x := fun i => (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2)
      hx hδ hle
  have hsplit : ∏ i, ((ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2)
      = (∏ i, (ρ i) ^ 2) * (∏ i, (Submission.Mostow.chord (φ i)) ^ 2) := Finset.prod_mul_distrib
  have hpos : 0 < ∏ i, (ρ i) ^ 2 := Finset.prod_pos (fun i _ => pow_pos (hρ i) 2)
  have hδm : δ ^ m = δ ^ (2 * (m / 2)) := congrArg (fun n => δ ^ n) hm2.symm
  have hlast : ∏ i, (Submission.Mostow.chord (φ i)) ^ 2 ≤ δ ^ m / ∏ i, (ρ i) ^ 2 := by
    rw [hδm, le_div_iff₀ hpos, mul_comm, ← hsplit]
    exact h4
  exact le_trans hmain hlast

end Work.Mostow
