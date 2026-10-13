import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.EllipticEst.InteriorRegularity.Strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.VT

open Work.EllipticEst.InteriorRegularity

/-- If a smooth function `tt : E2 → ℂ` agrees with `θ ↦ tan θ` on an open set `U`,
then the cosine of the second coordinate cannot vanish on `U`.

Proof: the `ℂ`-valued function `y ↦ tt y * cos (y 1) - sin (y 1)` is continuous and
vanishes on `U ∩ {cos ≠ 0}`, a set whose closure contains `U`; hence it vanishes at every
point of `U` as well.  At a point of `U` with `cos (x 1) = 0` this would force
`sin (x 1) = 0`, contradicting `sin² + cos² = 1`. -/
theorem cosNeZeroOfEqTanOn {U : Set Work.EllipticEst.InteriorRegularity.E2}
    {tt : Work.EllipticEst.InteriorRegularity.E2 → ℂ} (hU : IsOpen U)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt)
    (htt1 : ∀ x ∈ U, tt x = (Real.tan (x 1) : ℂ)) :
    ∀ x ∈ U, Real.cos (x 1) ≠ 0 := by
  intro x hx hcos
  -- where the cosine vanishes the sine is `±1`
  have hsin : Real.sin (x 1) ≠ 0 := by
    rcases Real.cos_eq_zero_iff_sin_eq.mp hcos with h | h <;> rw [h] <;> norm_num
  -- the second basis vector has norm one
  have he1norm : ‖(e1 : E2)‖ = 1 := by
    simp [e1, EuclideanSpace.basisFun_apply]
  -- points of `U` with nonvanishing cosine accumulate at `x`
  have hxcl : x ∈ closure (U ∩ {z : E2 | Real.cos (z 1) ≠ 0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases Metric.isOpen_iff.mp hU x hx with ⟨ρ, hρpos, hρsub⟩
    set h : ℝ := min (min ε ρ) (Real.pi / 2) / 2 with hh
    have hpos : 0 < h := by
      rw [hh]
      have h1 : 0 < min (min ε ρ) (Real.pi / 2) :=
        lt_min (lt_min hε hρpos) (by linarith [Real.pi_pos])
      linarith
    have hltε : h < ε := by
      rw [hh]
      have h1 : min (min ε ρ) (Real.pi / 2) ≤ ε :=
        (min_le_left (min ε ρ) (Real.pi / 2)).trans (min_le_left ε ρ)
      linarith
    have hltρ : h < ρ := by
      rw [hh]
      have h1 : min (min ε ρ) (Real.pi / 2) ≤ ρ :=
        (min_le_left (min ε ρ) (Real.pi / 2)).trans (min_le_right ε ρ)
      linarith
    have hltπ : h < Real.pi := by
      rw [hh]
      have h1 : min (min ε ρ) (Real.pi / 2) ≤ Real.pi / 2 :=
        min_le_right (min ε ρ) (Real.pi / 2)
      linarith [Real.pi_pos]
    have hcoord : (x + h • e1) 1 = x 1 + h := by
      simp [e1, EuclideanSpace.basisFun_apply]
    have hsub : x + h • e1 - x = h • e1 := by abel
    have hdistL : dist (x + h • e1) x = h := by
      rw [dist_eq_norm, hsub, norm_smul, he1norm, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    have hdistR : dist x (x + h • e1) = h := by rw [dist_comm, hdistL]
    refine ⟨x + h • e1, ⟨?_, ?_⟩, ?_⟩
    · exact hρsub (Metric.mem_ball.mpr (by rw [hdistL]; exact hltρ))
    · rw [Set.mem_setOf_eq]
      rw [hcoord]
      rw [Real.cos_add]
      rw [hcos, zero_mul, zero_sub]
      intro hcontra
      exact (mul_ne_zero hsin (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hltπ)))
        (neg_eq_zero.mp hcontra)
    · rw [hdistR]; exact hltε
  -- the auxiliary continuous function
  have hFcont : Continuous (fun y : E2 =>
      tt y * (Real.cos (y 1) : ℂ) - (Real.sin (y 1) : ℂ)) := by
    have h1 : Continuous fun y : E2 => y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    have h2 : Continuous fun y : E2 => (Real.cos (y 1) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp h1)
    have h3 : Continuous fun y : E2 => (Real.sin (y 1) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_sin.comp h1)
    exact ((htts 0).continuous.mul h2).sub h3
  -- it vanishes on `U ∩ {cos ≠ 0}`
  have hF0 : ∀ y ∈ U ∩ {z : E2 | Real.cos (z 1) ≠ 0},
      tt y * (Real.cos (y 1) : ℂ) - (Real.sin (y 1) : ℂ) = 0 := by
    rintro y ⟨hyU, hyc⟩
    have hkey : (Real.tan (y 1) : ℂ) * (Real.cos (y 1) : ℂ) = (Real.sin (y 1) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ hyc]
    rw [htt1 y hyU, hkey, sub_self]
  -- hence it vanishes on `U`
  have hFx : tt x * (Real.cos (x 1) : ℂ) - (Real.sin (x 1) : ℂ) = 0 :=
    closure_minimal hF0 (isClosed_eq hFcont continuous_const) hxcl
  -- which is impossible when `cos (x 1) = 0`
  have hs0 : (Real.sin (x 1) : ℂ) = 0 := by
    have h := hFx
    rw [hcos] at h
    simpa only [Complex.ofReal_zero, mul_zero, zero_sub, neg_eq_zero] using h
  exact hsin (Complex.ofReal_eq_zero.mp hs0)

end Work.EllipticEst.InteriorRegularity.VT
