import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixR.poisson_scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chi_lat1_periodization_mul`

The periodization of the corpus localization function `Submission.BoseGases.chi`
(`Submission/CubicChi.lean`: the smooth bump with `ContDiffBump.rOut = 1/2` and `∫χ² = 1`)
against the unit lattice `ℤ³` is *constant equal to `χ` itself* where `χ` does not vanish:

    `χ(y) · ∑_{d ∈ ℤ³} χ(y + d) = χ(y)²`   for every `y : ℝ³`.

The reason is that `χ` vanishes on the complement of the **open** ball of radius `1/2`
(`chi_eq_zero_of_norm_ge`: `ContDiffBump.zero_of_le_dist` with `rOut = 1/2`), and the open
balls of radius `1/2` around distinct lattice points are disjoint — indeed if
`‖y‖ < 1/2` and `d ≠ 0` then for a coordinate `i` with `d i ≠ 0`,
`|y i + d i| ≥ |d i| - |y i| > 1 - 1/2 = 1/2`, hence `‖y + d‖ > 1/2` and `χ(y + d) = 0`.
So every term of the lattice sum with `d ≠ 0` is killed by the prefactor `χ(y)`, and the sum
collapses to its `d = 0` term (`tsum_eq_single`).
-/

namespace Work.BoseBoxFock

/-- `χ` vanishes on the closed ball of radius `1/2` of the origin
(the sharp form of `Submission.BoseGases.chi_eq_zero_of_norm_gt`). -/
lemma chi_eq_zero_of_norm_ge (x : EuclideanSpace ℝ (Fin 3)) (hx : (1 : ℝ) / 2 ≤ ‖x‖) :
    Submission.BoseGases.chi x = 0 := by
  have hb : Submission.BoseGases.chiBase x = 0 := by
    have h := ContDiffBump.zero_of_le_dist Submission.BoseGases.chiBump (x := x) ?_
    · simpa [Submission.BoseGases.chiBase] using h
    · simpa [Submission.BoseGases.chiBump, dist_eq_norm] using hx
  simp [Submission.BoseGases.chi, hb]

theorem chi_lat1_periodization_mul (y : EuclideanSpace ℝ (Fin 3)) :
    ((Submission.BoseGases.chi y : ℝ) : ℂ) *
        (∑' d : Fin 3 → ℤ, ((Submission.BoseGases.chi (y + Work.BoseFixR.lat1 d) : ℝ) : ℂ))
      = ((Submission.BoseGases.chi y : ℝ) : ℂ) ^ 2 := by
  -- Every term of the lattice sum with `d ≠ 0` is annihilated by the prefactor `χ(y)`.
  have hkey : ∀ d : Fin 3 → ℤ, d ≠ 0 →
      (Submission.BoseGases.chi y : ℂ) *
        ((Submission.BoseGases.chi (y + Work.BoseFixR.lat1 d) : ℝ) : ℂ) = 0 := by
    intro d hd
    by_cases hy : Submission.BoseGases.chi y = 0
    · simp [hy]
    · -- `χ y ≠ 0` forces `‖y‖ < 1/2`, whence `‖y + d‖ > 1/2` for every `d ≠ 0`.
      have hynorm : ‖y‖ < 1 / 2 := by
        by_contra h
        exact hy (chi_eq_zero_of_norm_ge y (le_of_not_gt h))
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
      have hyi_le : |y i| ≤ ‖y‖ := by
        have h := PiLp.norm_apply_le y i
        simpa [Real.norm_eq_abs] using h
      have hyi : |y i| < 1 / 2 := lt_of_le_of_lt hyi_le hynorm
      have hdi : (1 : ℝ) ≤ |((d i : ℤ) : ℝ)| := by
        have h := Int.one_le_abs hi
        exact_mod_cast h
      -- the coordinate `i` of `y + d` already exceeds `1/2` in modulus
      have hcoord_abs : (1 : ℝ) / 2 < |y i + ((d i : ℤ) : ℝ)| := by
        have h := abs_add_le (((d i : ℤ) : ℝ) + y i) (-(y i))
        have h' : (((d i : ℤ) : ℝ) + y i) + (-(y i)) = ((d i : ℤ) : ℝ) := by ring
        rw [h', abs_neg] at h
        have h2 : |y i + ((d i : ℤ) : ℝ)| = |((d i : ℤ) : ℝ) + y i| := by rw [add_comm]
        rw [h2]
        linarith
      have hshift : (1 : ℝ) / 2 < ‖y + Work.BoseFixR.lat1 d‖ := by
        have h := PiLp.norm_apply_le (y + Work.BoseFixR.lat1 d) i
        have hcoord : (y + Work.BoseFixR.lat1 d).ofLp i = y i + ((d i : ℤ) : ℝ) := by
          simp [Work.BoseFixR.lat1_apply]
        rw [hcoord, Real.norm_eq_abs] at h
        linarith
      have hzd : Submission.BoseGases.chi (y + Work.BoseFixR.lat1 d) = 0 :=
        Submission.BoseGases.chi_eq_zero_of_norm_gt _ hshift
      simp [hzd]
  rw [← tsum_mul_left]
  rw [tsum_eq_single (0 : Fin 3 → ℤ) (fun d hd => hkey d hd)]
  have h0 : Work.BoseFixR.lat1 (0 : Fin 3 → ℤ) = 0 := by
    ext i; simp
  rw [h0, add_zero]
  ring

end Work.BoseBoxFock
