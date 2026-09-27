import Mathlib
import Submission.Work.KT.HopfK.Disk

namespace Work.KT.HopfK

/-- For `0 ≤ x ≤ √3/2` one has `√(1 - x²) ≥ 1/2`. -/
private lemma one_half_le_sqrt_one_sub_sq {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.sqrt 3 / 2) : 1 / 2 ≤ Real.sqrt (1 - x ^ 2) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs3le : Real.sqrt 3 / 2 ≤ 1 := by nlinarith
  have hx1 : x ≤ 1 := le_trans hx hs3le
  have hx2 : x ^ 2 ≤ 3 / 4 := by nlinarith
  rw [Real.le_sqrt (by norm_num) (by nlinarith)]
  nlinarith

/-- `Real.sqrt 3 / 2 ≤ 1`. -/
private lemma sqrt_three_div_two_le_one : Real.sqrt 3 / 2 ≤ (1 : ℝ) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith

theorem hk_diskW_bdry_cases (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (n r : ℕ) (δ : ℝ) (χ : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) :
    ∀ z : Ball (Eu m × Eu m), z ∈ bdry (Eu m × Eu m) →
    ((P.map (evalC z) = diagIdemMat r n) ∧ diskCos χ z = 0 ∧ diskSin χ z = 1) ∨
    ((P.map (evalC z) = diagIdemMat r n) ∧ (Q.map (evalC z) = diagIdemMat r n)) ∨
    ((Q.map (evalC z) = diagIdemMat r n) ∧ diskCos χ z = 1 ∧ diskSin χ z = 0) := by
  intro z hz
  have hδ' : 1 - δ ≤ Real.sqrt 3 / 2 := by linarith
  have hs3le : Real.sqrt 3 / 2 ≤ (1 : ℝ) := sqrt_three_div_two_le_one
  -- the boundary condition, in coordinates
  have hnorm : max ‖(z : Eu m × Eu m).1‖ ‖(z : Eu m × Eu m).2‖ = 1 := by
    have h : ‖(z : Eu m × Eu m)‖ = 1 := hz
    rwa [Prod.norm_def] at h
  -- the sphere point and the height identity
  have hχz : χ z = chiB m (hopfKMap m μ
      ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := hχ z hz
  have hcos : diskCos χ z = hkCos m (hopfKMap m μ
      ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := by
    show (Real.cos (Real.pi / 2 * χ z) : ℂ) =
      (Real.cos (Real.pi / 2 * chiB m (hopfKMap m μ
        ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) : ℂ)
    rw [hχz]
  have hsin : diskSin χ z = hkSin m (hopfKMap m μ
      ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := by
    show (Real.sin (Real.pi / 2 * χ z) : ℂ) =
      (Real.sin (Real.pi / 2 * chiB m (hopfKMap m μ
        ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩)) : ℂ)
    rw [hχz]
  have htc : tgtHeight m (hopfKMap m μ
      ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) =
      hopfSnd m (z : Eu m × Eu m) := tgtHeight_hopfKMap m μ _
  rcases le_total ‖(z : Eu m × Eu m).1‖ ‖(z : Eu m × Eu m).2‖ with hle | hle
  · -- `‖y‖ = 1`
    have hy1 : ‖(z : Eu m × Eu m).2‖ = 1 := by
      rw [max_eq_right hle] at hnorm
      exact hnorm
    have hPdiag : P.map (evalC z) = diagIdemMat r n := hPc z (by rw [hy1]; linarith)
    have hsnd : hopfSnd m (z : Eu m × Eu m) =
        Real.sqrt (1 - ‖(z : Eu m × Eu m).1‖ ^ 2) := by
      rw [hopfSnd_of_le m hle, hy1, one_pow]
    by_cases hx : ‖(z : Eu m × Eu m).1‖ ≤ Real.sqrt 3 / 2
    · left
      have hh : 1 / 2 ≤ tgtHeight m (hopfKMap m μ
          ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := by
        rw [htc, hsnd]
        exact one_half_le_sqrt_one_sub_sq (norm_nonneg _) hx
      exact ⟨hPdiag, by rw [hcos, hkCos_eq_zero_of m hh],
        by rw [hsin, hkSin_eq_one_of m hh]⟩
    · push Not at hx
      right; left
      exact ⟨hPdiag, hQc z (by linarith)⟩
  · -- `‖x‖ = 1`
    have ha1 : ‖(z : Eu m × Eu m).1‖ = 1 := by
      rw [max_eq_left hle] at hnorm
      exact hnorm
    have hQdiag : Q.map (evalC z) = diagIdemMat r n := hQc z (by rw [ha1]; linarith)
    have hsnd : hopfSnd m (z : Eu m × Eu m) =
        -Real.sqrt (1 - ‖(z : Eu m × Eu m).2‖ ^ 2) := by
      rw [hopfSnd_of_ge m hle, ha1, one_pow]
    by_cases hy : ‖(z : Eu m × Eu m).2‖ ≤ Real.sqrt 3 / 2
    · right; right
      have hh : tgtHeight m (hopfKMap m μ
          ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) ≤ -(1 / 2) := by
        rw [htc, hsnd]
        have := one_half_le_sqrt_one_sub_sq (norm_nonneg _) hy
        linarith
      exact ⟨hQdiag, by rw [hcos, hkCos_eq_one_of m hh],
        by rw [hsin, hkSin_eq_zero_of m hh]⟩
    · push Not at hy
      right; left
      exact ⟨hPc z (by linarith), hQdiag⟩

end Work.KT.HopfK
