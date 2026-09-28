import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Vero.dualLat_nonempty
import Submission.Work.HP.Vero.first_case_bound
import Submission.Work.HP.Vero.gcdMinors2_posR
import Submission.Work.HP.Vero.second_case_bound
import Submission.Work.HP.Vero.dmin_two_mul

namespace Work.HP.Vero

open Work.HP

variable {n : ℕ}

/-- `dmin r S ≥ 0`: it is an infimum of covolumes. -/
lemma dmin_nonneg (r : ℕ) (S : Set (Fin (n + 1) → ℤ)) : 0 ≤ dmin r S := by
  rw [dmin]
  by_cases h : (setOf fun D : ℝ =>
      ∃ L : Submodule ℤ (Fin (n + 1) → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D).Nonempty
  · exact le_csInf h (by rintro D ⟨L, -, -, rfl⟩; exact detL_nonneg L)
  · have h' : (setOf fun D : ℝ =>
        ∃ L : Submodule ℤ (Fin (n + 1) → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    have : (0 : ℝ) ≤ sInf (∅ : Set ℝ) := by rw [Real.sInf_empty]
    convert this using 2
    exact h'

/-- Auxiliary form of `lamR_dual_Gam_two`, with the numerical input `𝔡₂·𝒢 ≤ wedgeNorm` and the
positivity of `𝒢` taken as hypotheses. -/
theorem lamR_dual_Gam_two_aux (n : ℕ) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y])
    (hAG : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * (gcdMinors2 x y : ℝ) ≤ wedgeNorm x y)
    (hG0 : (0 : ℝ) < (gcdMinors2 x y : ℝ)) :
    (1 / 3) * min (dmin 3 {x, y} / dmin 2 {x, y}) (dmin 2 {x, y} ^ 2 / (eNorm x * eNorm y))
      ≤ lamR (dualLat (realify (Gam 2 n x y))) 1 := by
  have hA0 : (0 : ℝ) ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := dmin_nonneg 2 _
  have hB0 : (0 : ℝ) ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) := dmin_nonneg 3 _
  have hW0 : (0 : ℝ) ≤ wedgeNorm x y := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) < eNorm x * eNorm y :=
    mul_pos (eNorm_pos_of_ne_zero (isPrim_ne_zero hx)) (eNorm_pos_of_ne_zero (isPrim_ne_zero hy))
  have hAG0 : (0 : ℝ) ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * (gcdMinors2 x y : ℝ) :=
    mul_nonneg hA0 hG0.le
  refine le_lamR_one _ (dualLat_nonempty hn x y hx hy hxy) ?_
  intro a ha ha0
  by_cases hspan : a ∈ Submodule.span ℝ {toR (veronese 2 n x), toR (veronese 2 n y),
      toR (veronese 2 n (x + y))}
  · -- first case
    have h1 := first_case_bound n hn x y hx hy hxy a ha ha0 hspan
    have hsq : (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2
        * (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2) ≤ (wedgeNorm x y) ^ 2 * 3 := by
      have h2 : (Real.sqrt 2 : ℝ) ≤ 3 := by
        rw [Real.sqrt_le_iff]; norm_num
      have h3 : ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) * (gcdMinors2 x y : ℝ)) ^ 2
          ≤ (wedgeNorm x y) ^ 2 := pow_le_pow_left₀ hAG0 hAG 2
      have h3' : (Real.sqrt 2) * ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2
            * (gcdMinors2 x y : ℝ) ^ 2) ≤ (Real.sqrt 2) * (wedgeNorm x y) ^ 2 := by
        have h4 : (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 * (gcdMinors2 x y : ℝ) ^ 2
            = ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) * (gcdMinors2 x y : ℝ)) ^ 2 :=
          (mul_pow _ _ 2).symm
        rw [h4]
        exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg 2)
      have h5 : (Real.sqrt 2) * (wedgeNorm x y) ^ 2 ≤ 3 * (wedgeNorm x y) ^ 2 := by
        nlinarith [h2, sq_nonneg (wedgeNorm x y)]
      nlinarith [h3', h5]
    have hm : min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
          / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 / (eNorm x * eNorm y))
        ≤ (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 / (eNorm x * eNorm y) :=
      min_le_right _ _
    calc (1 / 3) * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
            / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
          ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 / (eNorm x * eNorm y))
        ≤ (1 / 3) * ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 / (eNorm x * eNorm y)) :=
          mul_le_mul_of_nonneg_left hm (by norm_num)
      _ ≤ (wedgeNorm x y) ^ 2
            / (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2 * (eNorm x * eNorm y)) := by
          rw [show (1 / 3) * ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2
                / (eNorm x * eNorm y))
              = ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 / 3) / (eNorm x * eNorm y) from by
                ring]
          rw [show (wedgeNorm x y) ^ 2
                / (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2 * (eNorm x * eNorm y))
              = ((wedgeNorm x y) ^ 2 / (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2))
                  / (eNorm x * eNorm y) from by rw [div_div]]
          rw [div_le_div_iff_of_pos_right hN0]
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
          rw [show (wedgeNorm x y) ^ 2 / (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2) * 3
              = 3 * (wedgeNorm x y) ^ 2 / (Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2) from by ring]
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2 * (gcdMinors2 x y : ℝ) ^ 2)]
          nlinarith [hsq]
      _ ≤ rNorm a := h1
  · -- second case
    have h2 := second_case_bound hn x y hx hy hxy a ha hspan
    have hmin : min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
          / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        ((dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ 2 / (eNorm x * eNorm y))
        ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
      min_le_left _ _
    have hquot : (0 : ℝ) ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
        / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := div_nonneg hB0 hA0
    refine le_trans ?_ h2
    refine le_trans (mul_le_mul_of_nonneg_left hmin (by norm_num)) ?_
    exact mul_le_of_le_one_left hquot (by norm_num)

/-- For `n ≥ 2` and primitive, `ℤ`-linearly independent `x,y ∈ ℤ^{n+1}`, the first successive
minimum of the lattice dual to `Γ = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` is at least
`(1/3)·min{𝔡₃/𝔡₂, 𝔡₂²/(‖x‖‖y‖)}`, where `𝔡_r = dmin r {x,y}`; this is the combination of the
paper's "Lower bound first case" and "Lower bound second case" (Browning–Le Boudec–Sawin §3.3,
`d = 2`). -/
theorem lamR_dual_Gam_two (n : ℕ) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    (1 / 3) * min (dmin 3 {x, y} / dmin 2 {x, y}) (dmin 2 {x, y} ^ 2 / (eNorm x * eNorm y))
      ≤ lamR (dualLat (realify (Gam 2 n x y))) 1 :=
  lamR_dual_Gam_two_aux n hn x y hx hy hxy
    (dmin_two_mul x y hxy) (gcdMinors2_posR x y hxy)

end Work.HP.Vero
