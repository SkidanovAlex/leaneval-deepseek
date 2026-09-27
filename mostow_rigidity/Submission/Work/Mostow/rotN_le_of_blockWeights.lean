import Mathlib
import Submission.Work.Mostow.screwAtZ
import Submission.Work.Mostow.displacementBlocks

namespace Work.Mostow

open scoped RealInnerProductSpace
open Submission.Mostow

/-!
# `Work.Mostow.rotN_le_of_blockWeights`

The *operator-norm* form of the block-displacement estimate: if an isometry `R` of
`E m = ℝ^m` acts on each two-dimensional block `span {e (i,0), e (i,1)}` of an orthonormal
basis `e : Fin (m/2) × Fin 2 → E m` as a rotation of angle `φ i` (mod `2π`), then the operator
norm of `R - 1` is bounded by the *weighted* chord length of `φ`:

  `rotN R ≤ δ / ρ_`  whenever  `∑ i, (ρ i)^2 · chord (φ i)^2 ≤ δ^2`  and  `ρ_ ≤ ρ i`.

Indeed `‖R v - v‖² = ∑ i, chord (φ i)^2 · ‖Pᵢ v‖²` for every `v` (`screw_blkRotNormSq`), where
`Pᵢ` is the orthogonal projection onto the `i`-th block; since the blocks are orthogonal, the
`‖Pᵢ v‖²` sum to `‖v‖²`, so `‖R v - v‖ ≤ (maxᵢ chord (φ i)) · ‖v‖`.  The weight hypothesis gives
`chord (φ i)² ≤ δ²/ρ_²` for every `i`, hence `rotN R ≤ δ/ρ_` by the pointwise criterion
`nib_rotN_le_of_unit`.
-/

noncomputable section

/-- Squared norm of a block vector, expanded in an orthonormal basis. -/
private lemma rnlb_blk_norm_sq {r : ℕ} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ X) (i : Fin r) (v : X) :
    ‖(inner ℝ (e (i, (0 : Fin 2))) v) • e (i, (0 : Fin 2)) +
      (inner ℝ (e (i, 1)) v) • e (i, 1)‖ ^ 2
    = (inner ℝ (e (i, (0 : Fin 2))) v) ^ 2 + (inner ℝ (e (i, 1)) v) ^ 2 := by
  have hu : ‖e (i, (0 : Fin 2))‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, e.inner_eq_ite (i, (0 : Fin 2)) (i, (0 : Fin 2))]; simp
  have hv : ‖e (i, (1 : Fin 2))‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, e.inner_eq_ite (i, (1 : Fin 2)) (i, (1 : Fin 2))]; simp
  have hinner : inner ℝ (e (i, (0 : Fin 2))) (e (i, (1 : Fin 2))) = 0 := by
    rw [e.inner_eq_ite (i, (0 : Fin 2)) (i, (1 : Fin 2))]; simp
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hinner, norm_smul, norm_smul,
      mul_pow, mul_pow, hu, hv, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

/-- The squared norms of the block projections of `v` sum to `‖v‖²` (the blocks are orthogonal
and span). -/
private lemma rnlb_sum_blkProj (m : ℕ)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (E m)) (v : E m) :
    ∑ i, ‖screwBlkProj e i v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hnorm : ‖v‖ ^ 2 = ∑ j : Fin (m / 2) × Fin 2, (inner ℝ (e j) v) ^ 2 := by
    rw [← e.repr.norm_map v, EuclideanSpace.real_norm_sq_eq]
    simp [OrthonormalBasis.repr_apply_apply]
  rw [hnorm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [screwBlkProj]
  rw [rnlb_blk_norm_sq]

/-- **Operator-norm block-displacement bound.** -/
theorem rotN_le_of_blockWeights (m : ℕ)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (φ : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      R (x • e (i, Fin.castSucc (0 : Fin 1)) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc (0 : Fin 1)) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (ρ : Fin (m / 2) → ℝ) (ρ_ δ : ℝ) (hρ_ : 0 < ρ_) (hρle : ∀ i, ρ_ ≤ ρ i) (hδ : 0 < δ)
    (hle : ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 ≤ δ ^ 2) :
    Submission.Mostow.rotN R ≤ δ / ρ_ := by
  have hK : 0 ≤ δ / ρ_ := by positivity
  refine nib_rotN_le_of_unit hK ?_
  intro v hv
  -- choose real lifts of the block angles
  have ht0 : ∀ i : Fin (m / 2), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      R (e (i, Fin.castSucc 0)) = Real.cos t • e (i, Fin.castSucc 0) + Real.sin t • e (i, 1) := by
    intro i
    obtain ⟨t, ht, hform⟩ := hblock i 1 0
    exact ⟨t, ht, by simpa using hform⟩
  choose θ hθ using ht0
  have h1θ : ∀ i : Fin (m / 2), R (e (i, 1)) =
      -Real.sin (θ i) • e (i, Fin.castSucc 0) + Real.cos (θ i) • e (i, 1) := by
    intro i
    obtain ⟨t', ht', hform'⟩ := hblock i 0 1
    have key : (t' : Real.Angle) = (θ i : Real.Angle) := ht'.trans (hθ i).1.symm
    have hcos : Real.cos t' = Real.cos (θ i) := by
      rw [← Real.Angle.cos_coe t', key, Real.Angle.cos_coe]
    have hsin : Real.sin t' = Real.sin (θ i) := by
      rw [← Real.Angle.sin_coe t', key, Real.Angle.sin_coe]
    simpa [hcos, hsin] using hform'
  have hid := screw_blkRotNormSq e R θ (fun i => (hθ i).2) h1θ v
  -- each block contribution is at most `(δ/ρ_)²`
  have h2cos_le : ∀ i : Fin (m / 2), (2 - 2 * Real.cos (θ i)) ≤ (δ / ρ_) ^ 2 := by
    intro i
    have hc := screw_chord_sq_eq_cos (φ i)
    have hcos_eq : Real.Angle.cos (φ i) = Real.cos (θ i) := by
      rw [← Real.Angle.cos_coe (θ i)]
      exact (congrArg Real.Angle.cos (hθ i).1).symm
    rw [hcos_eq] at hc
    rw [← hc, div_pow]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ρ_ ^ 2)]
    have hterm : (ρ i) ^ 2 * (chord (φ i)) ^ 2 ≤ δ ^ 2 :=
      le_trans (Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg (ρ j))
        (sq_nonneg (chord (φ j)))) (Finset.mem_univ i)) hle
    have hρsq : ρ_ ^ 2 ≤ (ρ i) ^ 2 := pow_le_pow_left₀ hρ_.le (hρle i) 2
    calc (chord (φ i)) ^ 2 * ρ_ ^ 2
        = ρ_ ^ 2 * (chord (φ i)) ^ 2 := by ring
      _ ≤ (ρ i) ^ 2 * (chord (φ i)) ^ 2 :=
          mul_le_mul_of_nonneg_right hρsq (sq_nonneg _)
      _ ≤ δ ^ 2 := hterm
  have hsum : ∑ i, (2 - 2 * Real.cos (θ i)) * ‖screwBlkProj e i v‖ ^ 2
      ≤ (δ / ρ_) ^ 2 * ‖v‖ ^ 2 := by
    calc ∑ i, (2 - 2 * Real.cos (θ i)) * ‖screwBlkProj e i v‖ ^ 2
        ≤ ∑ i, (δ / ρ_) ^ 2 * ‖screwBlkProj e i v‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h2cos_le i) (sq_nonneg _))
      _ = (δ / ρ_) ^ 2 * ∑ i, ‖screwBlkProj e i v‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (δ / ρ_) ^ 2 * ‖v‖ ^ 2 := by rw [rnlb_sum_blkProj]
  have hsq : ‖R v - v‖ ^ 2 ≤ (δ / ρ_) ^ 2 := by
    rw [hid]
    exact hsum.trans (by rw [hv]; norm_num)
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hK] at h

end

end Work.Mostow
