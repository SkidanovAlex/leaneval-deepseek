import Mathlib
import Submission.Work.Modular.GroupAlgebra

noncomputable section

open scoped MonoidAlgebra

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

/-- The group-ring element `T⁻¹`, the inverse of `tR` inside `ℂ[Γ]` (as an inverse of the
group element `genT`).  We use it because `ℂ[Γ]` carries no `Inv` instance, and the ideal
`I` happens to absorb the difference between `T⁻¹` and the quadratic expression
`2 - T + (T - 1)² T⁻¹`. -/
def uRinv : GroupRing := MonoidAlgebra.of ℂ Gamma genT⁻¹

theorem tR_mul_uRinv : tR * uRinv = 1 := by
  show MonoidAlgebra.of ℂ Gamma genT * MonoidAlgebra.of ℂ Gamma genT⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem uRinv_mul_tR : uRinv * tR = 1 := by
  show MonoidAlgebra.of ℂ Gamma genT⁻¹ * MonoidAlgebra.of ℂ Gamma genT = 1
  rw [← map_mul, inv_mul_cancel, map_one]

/-- The quadratic identity `(T - 1)² T⁻¹ = T - 2 + T⁻¹`; equivalently `T⁻¹ = 2 - T + (T - 1)² T⁻¹`,
i.e. the inverse of `T` agrees with a *polynomial* in `T` modulo the ideal `I`. -/
theorem sq_sub_one_mul_uRinv : (tR - 1) ^ 2 * uRinv = tR - 2 + uRinv := by
  have hu : tR * uRinv = 1 := tR_mul_uRinv
  calc (tR - 1) ^ 2 * uRinv = tR * (tR * uRinv) - 2 * (tR * uRinv) + uRinv := by noncomm_ring
    _ = tR * 1 - 2 * 1 + uRinv := by rw [hu]
    _ = tR - 2 + uRinv := by simp

theorem uRinv_eq : uRinv = 2 - tR + (tR - 1) ^ 2 * uRinv := by
  rw [sq_sub_one_mul_uRinv]
  abel

/-- The basic quadratic identity `T² = 2 T - 1 + (T - 1)²` in the group algebra. -/
theorem tR_mul_tR_eq : tR * tR = 2 * tR - 1 + (tR - 1) ^ 2 := by noncomm_ring

theorem sR_mul_tR_mul_tR_eq :
    sR * (tR * tR) = -sR + 2 * (sR * tR) + sR * (tR - 1) ^ 2 := by
  rw [tR_mul_tR_eq]
  have e : sR * (2 * tR) = 2 * (sR * tR) := by rw [two_mul, mul_add, two_mul]
  rw [mul_add, mul_sub, mul_one, e]
  abel

/-- The key relation `T S T = S T⁻¹ S`, a consequence of `(S T)³ = 1`: from `(genS * genT)³ = 1`
in the presented group we get `(genS * genT)² = genT⁻¹ * genS`, and applying `ℂ[Γ] ↪`-style
transport through `MonoidAlgebra.of` (a monoid homomorphism) yields the identity in the ring. -/
theorem tR_mul_sR_mul_tR_eq : tR * sR * tR = sR * uRinv * sR := by
  have hgkey : genT * genS * genT = genS * genT⁻¹ * genS := by
    have hg2 : (genS * genT) ^ 2 = genT⁻¹ * genS := by
      have hcube : (genS * genT) ^ 3 = 1 := genS_mul_genT_cube
      have ha : (genS * genT) * (genS * genT) ^ 2 = 1 := by
        rw [← pow_succ']; exact hcube
      have h1 : (genS * genT)⁻¹ = (genS * genT) ^ 2 := inv_eq_of_mul_eq_one_right ha
      have hSin : genS⁻¹ = genS := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_two, genS_sq]
      rw [mul_inv_rev, hSin] at h1
      exact h1.symm
    have hs : genS * genS = 1 := by rw [← pow_two, genS_sq]
    have h := congrArg (fun x => genS * x) hg2
    have e1 : genS * (genS * genT) ^ 2 = genT * genS * genT := by
      rw [pow_two]
      calc genS * (genS * genT * (genS * genT)) = (genS * genS) * genT * genS * genT := by group
        _ = genT * genS * genT := by rw [hs, one_mul]
    have e2 : genS * (genT⁻¹ * genS) = genS * genT⁻¹ * genS := by group
    rw [e1, e2] at h
    exact h
  have h2 : MonoidAlgebra.of ℂ Gamma (genT * genS * genT)
      = MonoidAlgebra.of ℂ Gamma (genS * genT⁻¹ * genS) := by rw [hgkey]
  simpa [sR, tR, uRinv, ← map_mul] using h2

/-- Consequence of `T S T = S T⁻¹ S` and of `T⁻¹ = 2 - T + (T - 1)² T⁻¹`, in the form needed
for the second row of the matrix `sigmaT`. -/
theorem sR_mul_uRinv_mul_sR_eq :
    sR * uRinv * sR = 2 - sR * tR * sR + sR * (tR - 1) ^ 2 * (uRinv * sR) := by
  have hSS : sR * sR = 1 := by rw [← pow_two, sR_sq]
  have h1 : sR * uRinv * sR = sR * (2 - tR + (tR - 1) ^ 2 * uRinv) * sR := by
    conv_lhs => rw [uRinv_eq]
  rw [h1]
  rw [show sR * (2 - tR + (tR - 1) ^ 2 * uRinv) * sR
        = 2 * (sR * sR) - sR * tR * sR + sR * (tR - 1) ^ 2 * uRinv * sR from by noncomm_ring]
  rw [hSS, mul_one]
  noncomm_ring

/-- Consequence of `T⁻¹ = 2 - T + (T - 1)² T⁻¹`, in the form needed for the last row of the
matrix `sigmaT`. -/
theorem uRinv_mul_sR_eq :
    uRinv * sR = -(tR * sR) + 2 * sR + (tR - 1) ^ 2 * (uRinv * sR) := by
  have h1 : uRinv * sR = (2 - tR + (tR - 1) ^ 2 * uRinv) * sR := by
    conv_lhs => rw [uRinv_eq]
  conv_lhs => rw [h1]
  rw [show (2 - tR + (tR - 1) ^ 2 * uRinv) * sR
        = -(tR * sR) + 2 * sR + (tR - 1) ^ 2 * (uRinv * sR) from by
        rw [add_mul, sub_mul, mul_assoc, sub_eq_add_neg, add_comm (2 * sR) (-(tR * sR))]]

theorem sR_mul_sR_mul_uRinv_mul_sR : sR * (sR * uRinv * sR) = uRinv * sR := by
  have hSS : sR * sR = 1 := by rw [← pow_two, sR_sq]
  rw [show sR * (sR * uRinv * sR) = (sR * sR) * uRinv * sR from by noncomm_ring]
  rw [hSS, one_mul]

/-- Right multiplication by `T` on the six basis elements agrees with the matrix `sigmaT` modulo
the right ideal `I`: this is the computation `M i * T = ∑ j, σ(T) i j • M j + I` of the paper,
which uses `T² = 2T - 1 + (T - 1)²` and `(S T)³ = 1`. -/
theorem basisElem_mul_tR (i : Fin 6) : ∃ n : GroupRing × GroupRing,
    basisElem i * tR = ∑ j, sigmaT i j • basisElem j +
      (tR - 1) ^ 2 * n.1 + sR * (tR - 1) ^ 2 * n.2 := by
  fin_cases i
  · exact ⟨(0, 0), by rw [Fin.sum_univ_six]; simp [sigmaT, basisElem]⟩
  · refine ⟨(1, 0), ?_⟩
    rw [Fin.sum_univ_six]
    simp [sigmaT, basisElem]
    simp only [Algebra.smul_def, map_ofNat]
    rw [tR_mul_tR_eq]
    abel
  · refine ⟨(0, uRinv * sR), ?_⟩
    rw [Fin.sum_univ_six]
    simp [sigmaT, basisElem]
    simp only [Algebra.smul_def, map_ofNat, mul_one]
    rw [tR_mul_sR_mul_tR_eq]
    simpa [sub_eq_add_neg] using sR_mul_uRinv_mul_sR_eq
  · exact ⟨(0, 0), by rw [Fin.sum_univ_six]; simp [sigmaT, basisElem]⟩
  · refine ⟨(0, 1), ?_⟩
    rw [Fin.sum_univ_six]
    simp [sigmaT, basisElem]
    simp only [Algebra.smul_def, map_ofNat]
    rw [show sR * tR * tR = sR * (tR * tR) from by noncomm_ring]
    exact sR_mul_tR_mul_tR_eq
  · refine ⟨(uRinv * sR, 0), ?_⟩
    rw [Fin.sum_univ_six]
    simp [sigmaT, basisElem]
    simp only [Algebra.smul_def, map_ofNat]
    rw [show sR * tR * sR * tR = sR * (tR * sR * tR) from by noncomm_ring]
    rw [tR_mul_sR_mul_tR_eq]
    rw [sR_mul_sR_mul_uRinv_mul_sR]
    exact uRinv_mul_sR_eq

end Work.Modular
