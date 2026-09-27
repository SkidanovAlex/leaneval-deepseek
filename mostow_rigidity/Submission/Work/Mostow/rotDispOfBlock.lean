import Mathlib
import Submission.Work.Mostow.screwAtZ

namespace Work.Mostow

/-- **Block-diagonal displacement bound.**  If `c` acts on every two-dimensional block
`span {e (i,0), e (i,1)}` of the orthonormal basis `e` as the rotation whose circle angle is
`φ i`, if every block projection of `Wz` is dominated by `ρ i`, and if the `ρ`-weighted sum of
squared chords of the angles `φ i` is at most `δ²`, then `c` displaces `Wz` by at most `δ`. -/
theorem rotDispOfBlock (m : ℕ) (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (c : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (φ : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      c (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (Wz : Submission.Mostow.E m) (ρ : Fin (m / 2) → ℝ) (hρ : ∀ i, 0 < ρ i) (δ : ℝ) (hδ : 0 < δ)
    (hdom : ∀ i : Fin (m / 2),
      ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖ ≤ ρ i)
    (hdisp : ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 ≤ δ ^ 2) :
    ‖c Wz - Wz‖ ≤ δ := by
  -- a real lift `θ i` of the block angle `φ i`, with the two images of the block basis vectors
  have ht0 : ∀ i : Fin (m / 2), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = φ i ∧
        c (e (i, Fin.castSucc 0)) =
          Real.cos t • e (i, Fin.castSucc 0) + Real.sin t • e (i, 1) := by
    intro i
    obtain ⟨t, ht, hform⟩ := hblock i 1 0
    exact ⟨t, ht, by simpa using hform⟩
  choose θ hθ hθ0 using ht0
  have hθ1 : ∀ i : Fin (m / 2), c (e (i, 1)) =
      - Real.sin (θ i) • e (i, Fin.castSucc 0) + Real.cos (θ i) • e (i, 1) := by
    intro i
    obtain ⟨t', ht', hform'⟩ := hblock i 0 1
    have key : (t' : Real.Angle) = (θ i : Real.Angle) := ht'.trans (hθ i).symm
    have hcos : Real.cos t' = Real.cos (θ i) := by
      rw [← Real.Angle.cos_coe t', key, Real.Angle.cos_coe]
    have hsin : Real.sin t' = Real.sin (θ i) := by
      rw [← Real.Angle.sin_coe t', key, Real.Angle.sin_coe]
    simpa [hcos, hsin] using hform'
  -- block norm bound coming from `hdom`
  have hdom' : ∀ i : Fin (m / 2), ‖screwBlkProj e i Wz‖ ≤ ρ i := by
    intro i
    have h := hdom i
    simpa only [screwBlkProj, Fin.castSucc_zero] using h
  -- `2 - 2 cos θ i` is the squared chord of the circle angle `φ i`
  have hchord : ∀ i : Fin (m / 2),
      2 - 2 * Real.cos (θ i) = (Submission.Mostow.chord (φ i)) ^ 2 := by
    intro i
    have hc := screw_chord_sq_eq_cos (φ i)
    have hcx : Real.Angle.cos (φ i) = Real.cos (θ i) := by
      rw [← Real.Angle.cos_coe (θ i)]
      exact (congrArg Real.Angle.cos (hθ i)).symm
    rw [hcx] at hc
    exact hc.symm
  have hfs : ∀ i : Fin (m / 2), 0 ≤ 2 - 2 * Real.cos (θ i) :=
    fun i => by linarith [Real.cos_le_one (θ i)]
  have hsq : ∀ i : Fin (m / 2), ‖screwBlkProj e i Wz‖ ^ 2 ≤ (ρ i) ^ 2 :=
    fun i => pow_le_pow_left₀ (norm_nonneg _) (hdom' i) 2
  -- the block-rotation norm formula and the final estimate
  have hmain := screw_blkRotNormSq e c θ hθ0 hθ1 Wz
  have hle : ‖c Wz - Wz‖ ^ 2 ≤ δ ^ 2 := by
    calc ‖c Wz - Wz‖ ^ 2
        = ∑ i : Fin (m / 2),
            (2 - 2 * Real.cos (θ i)) * ‖screwBlkProj e i Wz‖ ^ 2 := hmain
      _ ≤ ∑ i : Fin (m / 2), (2 - 2 * Real.cos (θ i)) * (ρ i) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_left (hsq i) (hfs i)
      _ = ∑ i : Fin (m / 2), (ρ i) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hchord i]; ring
      _ ≤ δ ^ 2 := hdisp
  nlinarith [norm_nonneg (c Wz - Wz), hδ, hle]

end Work.Mostow
