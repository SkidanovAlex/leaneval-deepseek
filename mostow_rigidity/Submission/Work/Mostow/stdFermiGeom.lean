import Mathlib
import Submission.Work.Mostow.fermiTwoDefs

/-!
# Geometry of the standard Fermi chart of `ℍ²`

This file proves `Work.Mostow.stdFermiGeom`, the collection of metric facts about the standard
geodesic `lineStd` of `E 2 = ℍ²` and its Fermi parametrisation
`stdFermi (s, r) = cosh r • lineStd s + sinh r • axisPerp`.

In coordinates `axis = e₀`, `axisPerp = e₁`, so
`stdFermi (s, r)` is the Euclidean vector `(cosh r · sinh s, sinh r)` and `lineStd s = (sinh s, 0)`.
All statements are direct computations in the hyperboloid model, using
`hdist u v = arcosh (tpart u * tpart v - ⟪u, v⟫)`.
-/

namespace Work.Mostow

open Submission.Mostow
open FermiTwo

/-- The inner product on `E 2` in coordinates. -/
lemma sfg_inner_two (x y : E 2) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- Inner product of two combinations of `axis` and `axisPerp`. -/
lemma sfg_inner_smul_pair (a b a' b' : ℝ) :
    inner ℝ (a • axis + b • axisPerp) (a' • axis + b' • axisPerp) = a * a' + b * b' := by
  rw [sfg_inner_two]; simp [axis, axisPerp]

/-- Squared norm of a combination of `axis` and `axisPerp`. -/
lemma sfg_norm_sq_pair (a b : ℝ) : ‖a • axis + b • axisPerp‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sfg_inner_smul_pair]; ring

/-- `tpart` of a combination of `axis` and `axisPerp`. -/
lemma sfg_tpart_pair (a b : ℝ) :
    tpart (a • axis + b • axisPerp) = Real.sqrt (1 + a ^ 2 + b ^ 2) := by
  rw [tpart, sfg_norm_sq_pair]; congr 1; ring

/-- `lineStd` written as a combination of the two basis vectors. -/
lemma sfg_lineStd_eq (s : ℝ) : lineStd s = Real.sinh s • axis + (0 : ℝ) • axisPerp := by
  simp [lineStd]

/-- `tpart` on the standard geodesic. -/
lemma sfg_tpart_lineStd (s : ℝ) : tpart (lineStd s) = Real.cosh s := by
  rw [sfg_lineStd_eq, sfg_tpart_pair]
  have h : 1 + Real.sinh s ^ 2 + (0 : ℝ) ^ 2 = Real.cosh s ^ 2 := by
    have := Real.cosh_sq s; nlinarith [this]
  rw [h, Real.sqrt_sq (Real.cosh_pos s).le]

/-- `tpart` on the standard Fermi chart. -/
lemma sfg_tpart_stdFermi (s r : ℝ) : tpart (stdFermi (s, r)) = Real.cosh r * Real.cosh s := by
  rw [stdFermi_apply, sfg_tpart_pair]
  have h : 1 + (Real.cosh r * Real.sinh s) ^ 2 + (Real.sinh r) ^ 2
      = (Real.cosh r * Real.cosh s) ^ 2 := by
    have h1 := Real.cosh_sq s; have h2 := Real.cosh_sq r; nlinarith [h1, h2]
  rw [h, Real.sqrt_sq (mul_nonneg (Real.cosh_pos r).le (Real.cosh_pos s).le)]

/-- First coordinate of a standard Fermi point. -/
lemma sfg_stdFermi_coord_zero (s r : ℝ) : (stdFermi (s, r)) 0 = Real.cosh r * Real.sinh s := by
  rw [stdFermi_apply]; simp [axis, axisPerp]

/-- Second coordinate of a standard Fermi point. -/
lemma sfg_stdFermi_coord_one (s r : ℝ) : (stdFermi (s, r)) 1 = Real.sinh r := by
  rw [stdFermi_apply]; simp [axis, axisPerp]

/-- Inner product of two points of the standard geodesic. -/
lemma sfg_inner_lineStd (s t : ℝ) :
    inner ℝ (lineStd s) (lineStd t) = Real.sinh s * Real.sinh t := by
  rw [sfg_lineStd_eq, sfg_lineStd_eq, sfg_inner_smul_pair]; ring

/-- Inner product of two standard Fermi points. -/
lemma sfg_inner_stdFermi (s r s' r' : ℝ) :
    inner ℝ (stdFermi (s, r)) (stdFermi (s', r'))
      = Real.cosh r * Real.sinh s * (Real.cosh r' * Real.sinh s')
        + Real.sinh r * Real.sinh r' := by
  rw [stdFermi_apply, stdFermi_apply, sfg_inner_smul_pair]

/-- Inner product of a standard Fermi point with a point of the geodesic. -/
lemma sfg_inner_stdFermi_lineStd (s r t : ℝ) :
    inner ℝ (stdFermi (s, r)) (lineStd t) = Real.cosh r * Real.sinh s * Real.sinh t := by
  rw [stdFermi_apply, sfg_lineStd_eq, sfg_inner_smul_pair]; ring

/-- Distance from a standard Fermi point to a point of the geodesic;
equal to `arcosh (cosh r · cosh (s − t))`. -/
lemma sfg_hdist_stdFermi_lineStd_gen (s r t : ℝ) :
    hdist (stdFermi (s, r)) (lineStd t) = Real.arcosh (Real.cosh r * Real.cosh (s - t)) := by
  rw [hdist, sfg_tpart_stdFermi, sfg_tpart_lineStd, sfg_inner_stdFermi_lineStd, Real.cosh_sub]
  congr 1; ring

/-- `|r| = arcosh (cosh r)`. -/
lemma sfg_abs_eq_arcosh_cosh (r : ℝ) : |r| = Real.arcosh (Real.cosh r) := by
  rw [← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg r)]

/-- Distance between two points of the standard geodesic. -/
lemma sfg_hdist_lineStd (s t : ℝ) : hdist (lineStd s) (lineStd t) = |s - t| := by
  rw [hdist, sfg_tpart_lineStd, sfg_tpart_lineStd, sfg_inner_lineStd, ← Real.cosh_sub]
  rw [← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg (s - t))]

/-- The foot `lineStd s` realises the distance from `stdFermi (s, r)` to the geodesic. -/
lemma sfg_hdist_stdFermi_lineStd_self (s r : ℝ) :
    hdist (stdFermi (s, r)) (lineStd s) = |r| := by
  rw [sfg_hdist_stdFermi_lineStd_gen, sub_self, Real.cosh_zero, mul_one, sfg_abs_eq_arcosh_cosh]

/-- `lineStd s` is the closest point of the geodesic to `stdFermi (s, r)`. -/
lemma sfg_hdist_stdFermi_lineStd_le (s r t : ℝ) :
    hdist (stdFermi (s, r)) (lineStd s) ≤ hdist (stdFermi (s, r)) (lineStd t) := by
  rw [sfg_hdist_stdFermi_lineStd_self, sfg_hdist_stdFermi_lineStd_gen, sfg_abs_eq_arcosh_cosh]
  have hy : 0 < Real.cosh r * Real.cosh (s - t) := mul_pos (Real.cosh_pos r) (Real.cosh_pos _)
  have hxy : Real.cosh r ≤ Real.cosh r * Real.cosh (s - t) := by
    have h := Real.one_le_cosh (s - t); nlinarith [Real.cosh_pos r]
  exact (Real.arcosh_le_arcosh (Real.cosh_pos r) hy).2 hxy

/-- The two-point distance formula in standard Fermi coordinates. -/
lemma sfg_hdist_stdFermi_stdFermi (s r s' r' : ℝ) :
    hdist (stdFermi (s, r)) (stdFermi (s', r'))
      = Real.arcosh (Real.cosh r * Real.cosh r' * Real.cosh (s - s')
          - Real.sinh r * Real.sinh r') := by
  rw [hdist, sfg_tpart_stdFermi, sfg_tpart_stdFermi, sfg_inner_stdFermi, Real.cosh_sub]
  congr 1; ring

/-- The normal coordinates `r` of two Fermi points differ by at most their distance. -/
lemma sfg_abs_sub_le_hdist (s r s' r' : ℝ) :
    |r - r'| ≤ hdist (stdFermi (s, r)) (stdFermi (s', r')) := by
  rw [sfg_hdist_stdFermi_stdFermi, sfg_abs_eq_arcosh_cosh]
  set A := Real.cosh r * Real.cosh r' * Real.cosh (s - s') - Real.sinh r * Real.sinh r'
  have hle : Real.cosh (r - r') ≤ A := by
    rw [Real.cosh_sub]
    have h := Real.one_le_cosh (s - s')
    have hp : 0 < Real.cosh r * Real.cosh r' := mul_pos (Real.cosh_pos r) (Real.cosh_pos r')
    nlinarith [h, hp]
  have hApos : 0 < A := lt_of_lt_of_le (Real.cosh_pos (r - r')) hle
  exact (Real.arcosh_le_arcosh (Real.cosh_pos (r - r')) hApos).2 hle

/-- Longitudinal displacement formula in standard Fermi coordinates. -/
lemma sfg_hdist_stdFermi_same_r (s r t : ℝ) (ht : 0 ≤ t) :
    hdist (stdFermi (s, r)) (stdFermi (s + t, r))
      = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r) := by
  rw [sfg_hdist_stdFermi_stdFermi]
  rw [show s - (s + t) = -t by ring, Real.cosh_neg]
  have hy : (0 : ℝ) ≤ Real.sinh (t / 2) * Real.cosh r :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos r).le
  have ht2 : Real.cosh t = 2 * Real.sinh (t / 2) ^ 2 + 1 := by
    have h1 := Real.cosh_two_mul (t / 2); have h2 := Real.cosh_sq (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h1
    nlinarith [h1, h2]
  have hmain : Real.cosh r * Real.cosh r * Real.cosh t - Real.sinh r * Real.sinh r
      = Real.cosh (2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r)) := by
    have h1 := Real.cosh_sq r
    have h2 := Real.cosh_two_mul (Real.arsinh (Real.sinh (t / 2) * Real.cosh r))
    have h3 := Real.cosh_sq (Real.arsinh (Real.sinh (t / 2) * Real.cosh r))
    rw [Real.sinh_arsinh] at h2
    rw [Real.sinh_arsinh] at h3
    nlinarith [h1, ht2, h2, h3]
  rw [hmain, Real.arcosh_cosh (mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr hy))]

/-- The Fermi chart restricts to the identity on the geodesic when `r = 0`. -/
lemma sfg_stdFermi_zero (s : ℝ) : stdFermi (s, 0) = lineStd s := by
  rw [stdFermi_apply, sfg_lineStd_eq]; simp

/-- The standard Fermi chart is injective. -/
lemma sfg_stdFermi_injective : Function.Injective stdFermi := by
  intro p q h
  obtain ⟨s, r⟩ := p
  obtain ⟨s', r'⟩ := q
  have h0 : Real.cosh r * Real.sinh s = Real.cosh r' * Real.sinh s' := by
    have := congrArg (fun x : E 2 => x 0) h
    simpa [stdFermi_apply, axis, axisPerp] using this
  have h1 : Real.sinh r = Real.sinh r' := by
    have := congrArg (fun x : E 2 => x 1) h
    simpa [stdFermi_apply, axis, axisPerp] using this
  have hr : r = r' := Real.sinh_injective h1
  have hs : s = s' := by
    have hsin : Real.sinh s = Real.sinh s' := by
      rw [hr] at h0
      exact mul_left_cancel₀ (Real.cosh_pos r').ne' h0
    exact Real.sinh_injective hsin
  rw [hs, hr]

/-- The standard Fermi chart is surjective. -/
lemma sfg_stdFermi_surjective : Function.Surjective stdFermi := by
  intro u
  refine ⟨(Real.arsinh (u 0 / Real.cosh (Real.arsinh (u 1))), Real.arsinh (u 1)), ?_⟩
  ext i
  fin_cases i
  · show (stdFermi (Real.arsinh (u 0 / Real.cosh (Real.arsinh (u 1))),
        Real.arsinh (u 1))) 0 = u 0
    rw [sfg_stdFermi_coord_zero, Real.sinh_arsinh, mul_div_cancel₀ _ (Real.cosh_pos _).ne']
  · show (stdFermi (Real.arsinh (u 0 / Real.cosh (Real.arsinh (u 1))),
        Real.arsinh (u 1))) 1 = u 1
    rw [sfg_stdFermi_coord_one, Real.sinh_arsinh]

theorem stdFermiGeom :
    (∀ s : ℝ, Work.Mostow.FermiTwo.stdFermi (s, 0) = Work.Mostow.FermiTwo.lineStd s) ∧
    (∀ s t : ℝ, Submission.Mostow.hdist (Work.Mostow.FermiTwo.lineStd s) (Work.Mostow.FermiTwo.lineStd t) = |s - t|) ∧
    (∀ s r : ℝ, Submission.Mostow.hdist (Work.Mostow.FermiTwo.stdFermi (s, r)) (Work.Mostow.FermiTwo.lineStd s) = |r|) ∧
    (∀ s r t : ℝ, Submission.Mostow.hdist (Work.Mostow.FermiTwo.stdFermi (s, r)) (Work.Mostow.FermiTwo.lineStd s)
        ≤ Submission.Mostow.hdist (Work.Mostow.FermiTwo.stdFermi (s, r)) (Work.Mostow.FermiTwo.lineStd t)) ∧
    (∀ s r s' r' : ℝ,
      Submission.Mostow.hdist (Work.Mostow.FermiTwo.stdFermi (s, r)) (Work.Mostow.FermiTwo.stdFermi (s', r'))
        = Real.arcosh (Real.cosh r * Real.cosh r' * Real.cosh (s - s') - Real.sinh r * Real.sinh r')) ∧
    (∀ s r s' r' : ℝ, |r - r'| ≤ Submission.Mostow.hdist (Work.Mostow.FermiTwo.stdFermi (s, r)) (Work.Mostow.FermiTwo.stdFermi (s', r'))) ∧
    (∀ s r t : ℝ, 0 ≤ t →
      Submission.Mostow.hdist (Work.Mostow.FermiTwo.stdFermi (s, r)) (Work.Mostow.FermiTwo.stdFermi (s + t, r))
        = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r)) ∧
    Function.Injective Work.Mostow.FermiTwo.stdFermi ∧
    Function.Surjective Work.Mostow.FermiTwo.stdFermi := by
  exact ⟨sfg_stdFermi_zero, sfg_hdist_lineStd, sfg_hdist_stdFermi_lineStd_self,
    sfg_hdist_stdFermi_lineStd_le, sfg_hdist_stdFermi_stdFermi, sfg_abs_sub_le_hdist,
    sfg_hdist_stdFermi_same_r, sfg_stdFermi_injective, sfg_stdFermi_surjective⟩

end Work.Mostow
